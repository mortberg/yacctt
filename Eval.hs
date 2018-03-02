{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module Eval where

import Debug.Trace

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set

import Cartesian
import CTT

-----------------------------------------------------------------------
-- Lookup functions

look :: String -> Env -> Val
look x (Env (Upd y rho,v:vs,fs,os)) | x == y = v
                                    | otherwise = look x (Env (rho,vs,fs,os))
look x r@(Env (Def _ decls rho,vs,fs,Nameless os)) = case lookup x decls of
  Just (_,t) -> eval r t
  Nothing    -> look x (Env (rho,vs,fs,Nameless os))
look x (Env (Sub _ rho,vs,_:fs,os)) = look x (Env (rho,vs,fs,os))
look x (Env (Empty,_,_,_)) = error $ "look: not found " ++ show x

lookType :: String -> Env -> Val
lookType x (Env (Upd y rho,v:vs,fs,os))
  | x /= y        = lookType x (Env (rho,vs,fs,os))
  | VVar _ a <- v = a
  | otherwise     = error ""
lookType x r@(Env (Def _ decls rho,vs,fs,os)) = case lookup x decls of
  Just (a,_) -> eval r a
  Nothing -> lookType x (Env (rho,vs,fs,os))
lookType x (Env (Sub _ rho,vs,_:fs,os)) = lookType x (Env (rho,vs,fs,os))
lookType x (Env (Empty,_,_,_))          = error $ "lookType: not found " ++ show x

lookName :: Name -> Env -> II
lookName i (Env (Upd _ rho,v:vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Def _ _ rho,vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Sub j rho,vs,phi:fs,os)) | i == j    = phi
                                          | otherwise = lookName i (Env (rho,vs,fs,os))
lookName i _ = error $ "lookName: not found " ++ show i


-----------------------------------------------------------------------
-- Nominal instances

instance Nominal Ctxt where
  occurs _ _ = False
  subst e _   = e
  swap e _  = e

instance Nominal Env where
  occurs x (Env (rho,vs,fs,os)) = occurs x (rho,vs,fs,os)
  subst (Env (rho,vs,fs,os)) iphi = Env (rho,subst vs iphi,subst fs iphi,os)
  swap (Env (rho,vs,fs,os)) ij = Env $ swap (rho,vs,fs,os) ij

instance Nominal Val where
  occurs x v = case v of
    VU                -> False
    Ter _ e           -> occurs x e
    VPi u v           -> occurs x (u,v)
    VPathP a v0 v1    -> occurs x [a,v0,v1]
    VPLam i v         -> if x == i then False else occurs x v
    VSigma u v        -> occurs x (u,v)
    VPair u v         -> occurs x (u,v)
    VFst u            -> occurs x u
    VSnd u            -> occurs x u
    VCon _ vs         -> occurs x vs
    VPCon _ a vs phis -> occurs x (a,vs,phis)
    VHCom r s a ts u  -> occurs x (r,s,a,u,ts)
    VCoe r s a u      -> occurs x (r,s,a,u)
    VVar _ v          -> occurs x v
    VOpaque _ v       -> occurs x v
    VApp u v          -> occurs x (u,v)
    VLam _ u v        -> occurs x (u,v)
    VAppII u phi      -> occurs x (u,phi)
    VSplit u v        -> occurs x (u,v)
    VV i a b e        -> x == i || occurs x (a,b,e)
    VVin i m n        -> x == i || occurs x (m,n)
    VVproj i o a b e  -> x == i || occurs x (o,a,b,e)
    -- VGlue a ts              -> occurs x (a,ts)
    -- VGlueElem a ts          -> occurs x (a,ts)
    -- VUnGlueElem a b ts      -> occurs x (a,b,ts)
    -- VHCompU a ts            -> occurs x (a,ts)
    -- VUnGlueElemU a b es     -> occurs x (a,b,es)

  subst u (i,r) = case u of
    VU                             -> VU
    Ter t e                        -> Ter t (subst e (i,r))
    VPi a f                        -> VPi (subst a (i,r)) (subst f (i,r))
    VPathP a u v                   -> VPathP (subst a (i,r)) (subst u (i,r)) (subst v (i,r))
    VPLam j v | j == i             -> u
              | not (j `occurs` r) -> VPLam j (subst v (i,r))
              | otherwise          -> VPLam k (subst (v `swap` (j,k)) (i,r))
         where k = fresh (v,Name i,r)
    VSigma a f                     -> VSigma (subst a (i,r)) (subst f (i,r))
    VPair u v                      -> VPair (subst u (i,r)) (subst v (i,r))
    VFst u                         -> fstVal (subst u (i,r))
    VSnd u                         -> sndVal (subst u (i,r))
    VCon c vs                      -> VCon c (subst vs (i,r))
    VPCon c a vs phis              -> pcon c (subst a (i,r)) (subst vs (i,r)) (subst phis (i,r))
    VHCom s s' a us u0             -> hcom (subst s (i,r)) (subst s' (i,r)) (subst a (i,r)) (subst us (i,r)) (subst u0 (i,r))
    VCoe s s' a u                  -> coe (subst s (i,r)) (subst s' (i,r)) (subst a (i,r)) (subst u (i,r))
    VVar x v                       -> VVar x (subst v (i,r))
    VOpaque x v                    -> VOpaque x (subst v (i,r))
    VAppII u psi                   -> subst u (i,r) @@ subst psi (i,r)
    VApp u v                       -> app (subst u (i,r)) (subst v (i,r))
    VLam x t u                     -> VLam x (subst t (i,r)) (subst u (i,r))
    VSplit u v                     -> app (subst u (i,r)) (subst v (i,r))
    VV j a b e                     ->
      vtype (subst (Name j) (i,r)) (subst a (i,r)) (subst b (i,r)) (subst e (i,r))
    VVin j m n                     ->
      vin (subst (Name j) (i,r)) (subst m (i,r)) (subst n (i,r))
    VVproj j o a b e               ->
      vproj (subst (Name j) (i,r)) (subst o (i,r)) (subst a (i,r)) (subst b (i,r)) (subst e (i,r))
         -- VGlue a ts              -> glue (subst a (i,r)) (subst ts (i,r))
         -- VGlueElem a ts          -> glueElem (subst a (i,r)) (subst ts (i,r))
         -- VUnGlueElem a bb ts      -> unGlue (subst a (i,r)) (subst bb (i,r)) (subst ts (i,r))
         -- VUnGlueElemU a bb es     -> unGlueU (subst a (i,r)) (subst bb (i,r)) (subst es (i,r))
         -- VHCompU a ts            -> hCompUniv (subst a (i,r)) (subst ts (i,r))

  -- This increases efficiency as it won't trigger computation.
  swap u ij =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                -> VU
         Ter t e           -> Ter t (sw e)
         VPi a f           -> VPi (sw a) (sw f)
         VPathP a u v      -> VPathP (sw a) (sw u) (sw v)
         VPLam k v         -> VPLam (swapName k ij) (sw v)
         VSigma a f        -> VSigma (sw a) (sw f)
         VPair u v         -> VPair (sw u) (sw v)
         VFst u            -> VFst (sw u)
         VSnd u            -> VSnd (sw u)
         VCon c vs         -> VCon c (sw vs)
         VPCon c a vs phis -> VPCon c (sw a) (sw vs) (sw phis)
         VHCom r s a us u  -> VHCom (sw r) (sw s) (sw a) (sw us) (sw u)
         VCoe r s a u      -> VCoe (sw r) (sw s) (sw a) (sw u)
         VVar x v          -> VVar x (sw v)
         VOpaque x v       -> VOpaque x (sw v)
         VAppII u psi      -> VAppII (sw u) (sw psi)
         VApp u v          -> VApp (sw u) (sw v)
         VLam x u v        -> VLam x (sw u) (sw v)
         VSplit u v        -> VSplit (sw u) (sw v)
         VV i a b e        -> VV (swapName i ij) (sw a) (sw b) (sw e)
         VVin i m n        -> VVin (swapName i ij) (sw m) (sw n)
         VVproj i o a b e  -> VVproj (swapName i ij) (sw o) (sw a) (sw b) (sw e)
         -- VGlue a ts              -> VGlue (sw a) (sw ts)
         -- VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         -- VUnGlueElem a b ts      -> VUnGlueElem (sw a) (sw b) (sw ts)
         -- VUnGlueElemU a b es     -> VUnGlueElemU (sw a) (sw b) (sw es)
         -- VHCompU a ts            -> VHCompU (sw a) (sw ts)

-----------------------------------------------------------------------
-- The evaluator

eval :: Env -> Ter -> Val
eval rho@(Env (_,_,_,Nameless os)) v = case v of
  U                     -> VU
  App r s               -> app (eval rho r) (eval rho s)
  Var i
    | i `Set.member` os -> VOpaque i (lookType i rho)
    | otherwise         -> look i rho
  Pi t@(Lam _ a _)      -> VPi (eval rho a) (eval rho t)
  Sigma t@(Lam _ a _)   -> VSigma (eval rho a) (eval rho t)
  Pair a b              -> VPair (eval rho a) (eval rho b)
  Fst a                 -> fstVal (eval rho a)
  Snd a                 -> sndVal (eval rho a)
  Where t decls         -> eval (defWhere decls rho) t
  Con name ts           -> VCon name (map (eval rho) ts)
  PCon name a ts phis   ->
    pcon name (eval rho a) (map (eval rho) ts) (map (evalII rho) phis)
  Lam{}                 -> Ter v rho
  Split{}               -> Ter v rho
  Sum{}                 -> Ter v rho
  HSum{}                -> Ter v rho
  Undef{}               -> Ter v rho
  Hole{}                -> Ter v rho
  PathP a e0 e1         -> VPathP (eval rho a) (eval rho e0) (eval rho e1)
  PLam i t              -> let j = fresh rho
                           in VPLam j (eval (sub (i,Name j) rho) t)
  AppII e phi           -> eval rho e @@ evalII rho phi
  HCom r s a us u0      ->
    hcom (evalII rho r) (evalII rho s) (eval rho a) (evalSystem rho us) (eval rho u0)
  Coe r s a t           -> coe (evalII rho r) (evalII rho s) (eval rho a) (eval rho t)
  -- Comp a t0 ts       -> compLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  V r a b e             -> vtype (evalII rho r) (eval rho a) (eval rho b) (eval rho e)
  Vin r m n             -> vin (evalII rho r) (eval rho m) (eval rho n)
  Vproj r o a b e       -> vproj (evalII rho r) (eval rho o) (eval rho a) (eval rho b) (eval rho e)
  -- Glue a ts          -> glue (eval rho a) (evalSystem rho ts)
  -- GlueElem a ts      -> glueElem (eval rho a) (evalSystem rho ts)
  -- UnGlueElem v a ts  -> unGlue (eval rho v) (eval rho a) (evalSystem rho ts)
  _                     -> error $ "Cannot evaluate " ++ show v

evals :: Env -> [(Ident,Ter)] -> [(Ident,Val)]
evals env bts = [ (b,eval env t) | (b,t) <- bts ]

evalII :: Env -> II -> II
evalII rho phi = case phi of
  Name i         -> lookName i rho
  _              -> phi

evalEqn :: Env -> Eqn -> Eqn
evalEqn rho (Eqn r s) = eqn (evalII rho r,evalII rho s)

evalSystem :: Env -> System Ter -> System Val
evalSystem rho (Triv u) = Triv (eval rho u)
evalSystem rho (Sys us) =
  case Map.foldrWithKey (\eqn u -> insertSystem (evalEqn rho eqn,u)) eps us of
    Triv u -> Triv (eval rho u)
    Sys sys' -> Sys $ Map.mapWithKey (\eqn u -> eval (rho `subst` toSubst eqn) u) sys'

app :: Val -> Val -> Val
app u v = case (u,v) of
  (Ter (Lam x _ t) e,_) -> eval (upd (x,v) e) t
  (Ter (Split _ _ _ nvs) e,VCon c vs) -> case lookupBranch c nvs of
    Just (OBranch _ xs t) -> eval (upds (zip xs vs) e) t
    _     -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ _ nvs) e,VPCon c _ us phis) -> case lookupBranch c nvs of
    Just (PBranch _ xs is t) -> eval (subs (zip is phis) (upds (zip xs us) e)) t
    _ -> error $ "app: missing case in split for " ++ c
  (Ter (Split _ _ ty hbr) e,VHCom r s a ws w) -> undefined -- case eval e ty of
    -- VPi _ f -> let j   = fresh (e,v)
    --                wsj = Map.map (@@ j) ws
    --                w'  = app u w
    --                ws' = mapWithKey (\alpha -> app (u `face` alpha)) wsj
    --                -- a should be constant
    --            in comp j (app f (hFill j a w wsj)) w' ws'
    -- _ -> error $ "app: Split annotation not a Pi type " ++ show u
  (Ter Split{} _,_) -- | isNeutral v
                    -> VSplit u v
  (VCoe r s (VPLam i (VPi a b)) u0, v) -> trace "coe pi" $
    let j = fresh (u,v)
        bij = b `swap` (i,j)
        w = coe s (Name j) (VPLam i a) v
        w0 = coe s r (VPLam i a) v
    in coe r s (VPLam j (app bij w)) (app u0 w0)
  (VHCom r s (VPi a b) (Sys us) u0, v) -> undefined -- trace "hcom pi" $
    -- let i = fresh (u,v)
    -- in hcom i r s
    --         (app b v)
    --         (Sys (Map.mapWithKey (\al ual -> app (ual @@ i) (v `subst` toSubst al)) us))
    --         (app u0 v)
  (VHCom _ _ _ (Triv u) _, v) -> error "app: trying to apply vhcom in triv" -- TODO: rewrite it instead of implementing
--  _ | isNeutral u       -> VApp u v
  _                     -> VApp u v -- error $ "app \n  " ++ show u ++ "\n  " ++ show v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
-- fstVal u | isNeutral u = VFst u
fstVal u               = VFst u -- error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
-- sndVal u | isNeutral u = VSnd u
sndVal u               = VSnd u -- error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: Val -> Val
inferType v = case v of
  VVar _ t -> t
  VOpaque _ t -> t
  Ter (Undef _ t) rho -> eval rho t
  VFst t -> case inferType t of
    VSigma a _ -> a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> case inferType t of
    VSigma _ f -> app f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> case eval rho t of
    VPi _ f -> app f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> case inferType t0 of
    VPi _ f -> app f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  VAppII t phi -> case inferType t of
    VPathP a _ _ -> a @@ phi
    ty         -> error $ "inferType: expected PathP type for " ++ show v
                  ++ ", got " ++ show ty
  VHCom r s a _ _ -> a
  VCoe r s a _ -> a @@ s
  VVproj _ _ _ b _ -> b
  -- VUnGlueElem _ b _  -> b
  -- VUnGlueElemU _ b _ -> b
  _ -> error $ "inferType: not neutral " ++ show v

(@@) :: ToII a => Val -> a -> Val
(VPLam i u) @@ phi         = u `subst` (i,toII phi)
v@(Ter Hole{} _) @@ phi    = VAppII v (toII phi)
v @@ phi -- | isNeutral v
         = case (inferType v,toII phi) of
  (VPathP _ a0 _,Dir 0) -> a0
  (VPathP _ _ a1,Dir 1) -> a1
  _                    -> VAppII v (toII phi)
-- v @@ phi                   = error $ "(@@): " ++ show v ++ " should be neutral."

-------------------------------------------------------------------------------
-- com and hcom

com :: II -> II -> Val -> System Val -> Val -> Val
com r s a _ u0 | r == s = u0
com _ s _ (Triv u) _  = u @@ s
com r s a us u0 =
  hcom r s (a @@ s) (mapSystem (\j u -> coe (Name j) s a u) us) (coe r s a u0)

-- apply f to each face (with its binder), eta-expanding where needed
mapSystem :: (Name -> Val -> Val) -> System Val -> System Val
mapSystem f (Triv (VPLam i u)) = Triv (VPLam i (f i u))
mapSystem f (Triv u) =
  let j = fresh u
  in Triv (VPLam j (f j (u @@ j)))
mapSystem f (Sys us) =
  let j = fresh (Sys us)
      etaMap (VPLam i u) = VPLam i (f i u)
      etaMap u = VPLam j (f j (u @@ j))
  in Sys $ Map.map etaMap us

hcom :: II -> II -> Val -> System Val -> Val -> Val
hcom r s _ _ u0 | r == s = u0
hcom r s _ (Triv u) _    = u @@ s
hcom r s a (Sys us) u0   = case a of
  VPathP a v0 v1 -> trace "hcom path" $
    let j = fresh (r,s,a,Sys us,u0)
    in VPLam j $ hcom r s (a @@ j)
                   (insertsSystem [(j~>0,VPLam (N "_") v0),(j~>1,VPLam (N "_") v1)]
                     (mapSystem (const (@@ j)) (Sys us)))
                   (u0 @@ j)
  VSigma a b -> trace "hcom sigma" $
    let j = fresh (r,s,a,b,Sys us,u0)
        (us1,us2) = (mapSystem (const fstVal) (Sys us),mapSystem (const sndVal) (Sys us))
        (u1,u2) = (fstVal u0,sndVal u0)
        u1fill = hcom r (Name j) a us1 u1
        u1hcom = hcom r s a us1 u1
    in VPair u1hcom (com r s (VPLam j (app b u1fill)) us2 u2)
  -- VU -> error "hcom U"
  -- Ter (Sum _ n nass) env
  --   | n `elem` ["nat","Z","bool"] -> u0 -- hardcode hack
  -- Ter (Sum _ _ nass) env | VCon n vs <- u0, all isCon (elems us) -> error "hcom sum"
  -- Ter (HSum _ _ _) _ -> VHCom r s a (Sys us) u0
  VPi{} -> VHCom r s a (Sys us) u0
  _ -> VHCom r s a (Sys us) u0

-------------------------------------------------------------------------------
-- Composition and filling

-- hCompLine :: Val -> Val -> System Val -> Val
-- hCompLine a u us = hComp i a u (Map.map (@@ i) us)
--   where i = fresh (a,u,us)

-- hFill :: Name -> Val -> Val -> System Val -> Val
-- hFill i a u us = hComp j a u (insertSystem (i~>0) u $ us `conj` (i,j))
--   where j = fresh (Atom i,a,u,us)

-- hFillLine :: Val -> Val -> System Val -> Val
-- hFillLine a u us = VPLam i $ hFill i a u (Map.map (@@ i) us)
--   where i = fresh (a,u,us)

-- hComp :: Name -> Val -> Val -> System Val -> Val
-- hComp i a u us | eps `member` us = (us ! eps) `face` (i~>1)
-- hComp i a u us = case a of
--   VPathP p v0 v1 -> let j = fresh (Atom i,a,u,us) in
--     VPLam j $ hComp i (p @@ j) (u @@ j) (insertsSystem [(j~>0,v0),(j~>1,v1)]
--                                          (Map.map (@@ j) us))
--   VSigma a f -> let (us1, us2) = (Map.map fstVal us, Map.map sndVal us)
--                     (u1, u2) = (fstVal u, sndVal u)
--                     u1fill = hFill i a u1 us1
--                     u1comp = hComp i a u1 us1
--                 in VPair u1comp (comp i (app f u1fill) u2 us2)
--   VU -> hCompUniv u (Map.map (VPLam i) us)
--   -- VGlue b equivs -> -- | not (isNeutralGlueHComp equivs u us) ->
--   --   let wts = mapWithKey (\al wal ->
--   --                 app (equivFun wal)
--   --                   (hFill i (equivDom wal) (u `face` al) (us `face` al)))
--   --               equivs
--   --       t1s = mapWithKey (\al wal ->
--   --               hComp i (equivDom wal) (u `face` al) (us `face` al)) equivs
--   --       v = unGlue u b equivs
--   --       vs = mapWithKey (\al ual -> unGlue ual (b `face` al) (equivs `face` al))
--   --              us
--   --       v1 = hComp i b v (vs `unionSystem` wts)
--   --   in glueElem v1 t1s
--   -- VHCompU b es -> -- | not (isNeutralGlueHComp es u us) ->
--   --   let wts = mapWithKey (\al eal ->
--   --                 eqFun eal
--   --                   (hFill i (eal @@ One) (u `face` al) (us `face` al)))
--   --               es
--   --       t1s = mapWithKey (\al eal ->
--   --               hComp i (eal @@ One) (u `face` al) (us `face` al)) es
--   --       v = unGlueU u b es
--   --       vs = mapWithKey (\al ual -> unGlueU ual (b `face` al) (es `face` al))
--   --              us
--   --       v1 = hComp i b v (vs `unionSystem` wts)
--   --   in glueElem v1 t1s
--   Ter (Sum _ _ nass) env | VCon n vs <- u, all isCon (elems us) ->
--     case lookupLabel n nass of
--       Just as -> let usvs = transposeSystemAndList (Map.map unCon us) vs
--                      -- TODO: it is not really much of an improvement
--                      -- to use hComps here; directly use comps?
--                  in VCon n $ hComps i as env usvs
--       Nothing -> error $ "hComp: missing constructor in sum " ++ n
--   Ter (HSum _ _ _) _ -> undefined -- VHComp a u (Map.map (VPLam i) us)
--   VPi{} -> undefined -- VHComp a u (Map.map (VPLam i) us)
--   _ -> undefined -- VHComp a u (Map.map (VPLam i) us)

-- -- TODO: has to use comps after the second component anyway... remove?
-- hComps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
-- hComps i []         _ []            = []
-- hComps i ((x,a):as) e ((ts,u):tsus) =
--   let v   = hFill i (eval e a) u ts
--       vi1 = hComp i (eval e a) u ts
--       vs  = comps i as (upd (x,v) e) tsus -- NB: not hComps
--   in vi1 : vs
-- hComps _ _ _ _ = error "hComps: different lengths of types and values"


-- -- For i:II |- a, phi # i, u : a (i/phi) we get fwd i a phi u : a(i/1)
-- -- such that fwd i a 1 u = u.   Note that i gets bound.
-- fwd :: Name -> Val -> II -> Val -> Val
-- fwd i a phi u = trans i (act False a (i,phi `orII` Atom i)) phi u

-- comp :: Name -> Val -> Val -> System Val -> Val
-- -- comp i a u us = hComp i (a `face` (i~>1)) (fwd i a (Dir Zero) u) fwdius
-- --  where fwdius = mapWithKey (\al ual -> fwd i (a `face` al) (Atom i) ual) us
-- comp i a u us = hComp j (a `face` (i~>1)) (fwd i a (Dir Zero) u) fwdius
--   where j = fresh (Atom i,a,u,us)
--         fwdius = mapWithKey (\al ual -> fwd i (a `face` al) (Atom j) (ual  `swap` (i,j))) us

-- compNeg :: Name -> Val -> Val -> System Val -> Val
-- compNeg i a u ts = comp i (a `sym` i) u (ts `sym` i)

-- compLine :: Val -> Val -> System Val -> Val
-- compLine a u ts = comp i (a @@ i) u (Map.map (@@ i) ts)
--   where i = fresh (a,u,ts)

-- comps :: Name -> [(Ident,Ter)] -> Env -> [(System Val,Val)] -> [Val]
-- comps i []         _ []         = []
-- comps i ((x,a):as) e ((ts,u):tsus) =
--   let v   = fill i (eval e a) u ts
--       vi1 = comp i (eval e a) u ts
--       vs  = comps i as (upd (x,v) e) tsus
--   in vi1 : vs
-- comps _ _ _ _ = error "comps: different lengths of types and values"

-- fill :: Name -> Val -> Val -> System Val -> Val
-- fill i a u ts =
--   comp j (a `conj` (i,j)) u (insertSystem (i~>0) u (ts `conj` (i,j)))
--   where j = fresh (Atom i,a,u,ts)

-- fillNeg :: Name -> Val -> Val -> System Val -> Val
-- fillNeg i a u ts = (fill i (a `sym` i) u (ts `sym` i)) `sym` i

-- fillLine :: Val -> Val -> System Val -> Val
-- fillLine a u ts = VPLam i $ fill i (a @@ i) u (Map.map (@@ i) ts)
--   where i = fresh (a,u,ts)



-----------------------------------------------------------
-- Coe

coe :: II -> II -> Val -> Val -> Val
coe r s a u | r == s = u
coe r s (VPLam i a) u = case a of
  VPathP a v0 v1 -> trace "coe path" $
    let j = fresh (Name i,r,s,a,(v0,v1),u)
    in VPLam j $ com r s (VPLam i (a @@ j))
                     (mkSystem [(j~>0,VPLam i v0),(j~>1,VPLam i v1)]) (u @@ j)
  VSigma a b -> trace "coe sigma" $
    let j = fresh (Name i,r,s,a,b,u)
        (u1,u2) = (fstVal u, sndVal u)
        u1'     = coe r (Name j) (VPLam i a) u1
    in VPair (coe r s (VPLam i a) u1) (coe r s (VPLam j (app (b `swap` (i,j)) u1')) u2)
  VPi{} -> VCoe r s (VPLam i a) u
  VU -> u
  VV j a b e -> vvcoe i j r s a b e u
  Ter (Sum _ n nass) env
    | n `elem` ["nat","Z","bool"] -> u -- hardcode hack
    | otherwise -> error "coe sum"
  Ter (HSum _ n nass) env
    | n `elem` ["S1","S2","S3"] -> u   -- hardcode hack
    | otherwise -> error "coe hsum"
  -- VTypes
  _ -> -- error "missing case in coe" --
       VCoe r s (VPLam i a) u
coe r s a u = VCoe r s a u

-- TODO
-- In Part 3: i corresponds to y, and, j to x
vvcoe :: Name -> Name -> II -> II -> Val -> Val -> Val -> Val -> Val
vvcoe i j r s a b e u | i /= j = undefined -- trace "vvcoe i != j" $
--   let tvec = mkSystem [(j~>0,app (equivFun e) (coe i r (Name i) a u))
--                       ,(j~>1,coe i r (Name i) b u)]
--       (ar,br,er) = (a,b,e) `subst` (i,r)
--   in vin (Name j)
--          (coe i r s a u)
--          (com i r s b tvec (vproj (Name j) u ar br er))
-- vvcoe j _ (Dir Zero) s a b e u = trace "vvcoe j->0" $
--   vin s u (coe j 0 s b (app (equivFun e `subst` (j,0)) u))
-- vvcoe j _ (Dir One) s a b e u = trace "vvcoe j->1" $
--   let otm = fstVal (app (equivContr e `subst` (j,s)) (coe j 1 s b u))
--       psys = mkSystem [(s~>0,sndVal otm)
--                       ,(s~>1,VPLam (N "_") (coe j 1 s b u))]
--       ptm = hcomLine 1 0 (b `subst` (j,s)) psys (coe j 1 s b u)
--   in vin s (fstVal otm) ptm
-- vvcoe j _ (Name i) s a b e u = trace "vvcoe j->i" $
--   let k:l:_ = freshs (Name j,Name i,s,(a,b,e),u)
--       (ak,bk,ek) = (a,b,e) `swap` (j,k)
--       otm eps = vproj (Name k) (coe j eps (Name k) (vtype (Name j) a b e) u) ak bk ek
--       (ai,bi,ei) = (a,b,e) `subst` (j,Name i)
--       psys = mkSystem [(i~>0,otm 0 `swap` (k,j))
--                       ,(i~>1,otm 1 `swap` (k,j))] -- TODO: remove the swaps?
--       ptm = com j (Name i) (Name j) b psys (vproj (Name i) u ai bi ei)
--       p0 = ptm `subst` (j,0)
--       (a0,b0,e0) = (a,b,e) `subst` (j,0)
--       uvec eps t = mkSystem [(l~>0,app (equivFun e0) (coe i eps (Name i) a0 t))
--                             ,(l~>1,p0)]
--       qtm eps t = VPair (coe i eps (Name i) a0 t)
--                         (VPLam l (com i eps (Name i) b0 (uvec eps t) (p0 `subst` (i,eps))))
--       rtm = app (app (sndVal (app (equivContr e0) p0)) (qtm 0 (u `subst` (i,0))))
--                 (qtm 1 (coe j 1 0 (vtype (Name j) a b e) u `subst` (i,1))) @@ i
--       (as,bs,es) = (a,b,e) `subst` (j,s)
--       tvec = mkSystem [(i~>0,otm 0 `subst` (k,s))
--                       ,(i~>1,otm 1 `subst` (k,s))
--                       ,(i~>s,vproj s u as bs es)
--                       ,(s~>0,sndVal rtm)]
--   in vin s (fstVal rtm) (hcom l 1 0 (b `subst` (j,s)) tvec (ptm `subst` (j,s)))
        

-- Transport and forward

-- transLine :: Val -> II -> Val -> Val
-- transLine a phi u = trans i (a @@ i) phi u
--   where i = fresh (a,phi,u)

-- -- For i:II |- a, phi # i,
-- --     i:II, phi=1 |- a = a(i/0)
-- -- and u : a(i/0) gives trans i a phi u : a(i/1) such that
-- -- trans i a 1 u = u : a(i/1) (= a(i/0)).
-- trans :: Name -> Val -> II -> Val -> Val
-- trans i a (Dir One) u = u
-- trans i a phi u = case a of
--   VPathP p v0 v1 -> let j = fresh (Atom i,a,phi,u) in
--     VPLam j $ comp i (p @@ j) (u @@ j) (insertsSystem [(j~>0,v0),(j~>1,v1)]
--                                          (border (u @@ j) (invSystem phi One)))
--   VSigma a f ->
--     let (u1,u2) = (fstVal u, sndVal u)
--         u1f     = transFill i a phi u1
--     in VPair (trans i a phi u1) (trans i (app f u1f) phi u2)
--   VPi{} -> VTrans (VPLam i a) phi u
--   VU -> u
--   VGlue b equivs -> -- | not (eps `notMember` (equivs `face` (i~>0)) && isNeutral u) ->
--     transGlue i b equivs phi u
--   VHCompU b es -> -- | not (eps `notMember` (es `face` (i~>0)) && isNeutral u) ->
--     transHCompU i b es phi u
--   Ter (Sum _ n nass) env
--     | n `elem` ["nat","Z","bool"] -> u -- hardcode hack
--     | otherwise -> case u of
--     VCon n us -> case lookupLabel n nass of
--       Just tele -> VCon n (transps i tele env phi us)
--       Nothing -> error $ "trans: missing constructor in sum " ++ n
--     _ -> VTrans (VPLam i a) phi u
--   Ter (HSum _ n nass) env
--     | n `elem` ["S1","S2","S3"] -> u
--     | otherwise -> case u of
--     VCon n us -> case lookupLabel n nass of
--       Just tele -> VCon n (transps i tele env phi us)
--       Nothing -> error $ "trans: missing constructor in hsum " ++ n
--     VPCon n _ us psis -> case lookupPLabel n nass of
--       Just (tele,is,es) ->
--         let ai1  = a `face` (i~>1)
--             vs   = transFills i tele env phi us
--             env' = subs (zip is psis) (updsTele tele vs env)
--             ves  = evalSystem env' es
--             ves' = mapWithKey
--                    (\al veal -> squeeze i (a `face` al) (phi `face` al) veal)
--                    ves
--             pc = VPCon n ai1 (transps i tele env phi us) psis
--             -- NB: restricted to phi=1, u = pc; so we could also take pc instead
--             uphi = border u (invSystem phi One)
--         in pc
--            --hComp i ai1 pc ((ves' `sym` i) `unionSystem` uphi)
--       Nothing -> error $ "trans: missing path constructor in hsum " ++ n
--     VHCom r s _ v vs -> undefined -- let j = fresh (Atom i,a,phi,u) in
--       -- hComp j (a `face` (i~>1)) (trans i a phi v)
--       --   (mapWithKey (\al val ->
--       --                 trans i (a `face` al) (phi `face` al) (val @@ j)) vs)
--     _ -> undefined -- VTrans (VPLam i a) phi u
--   _ -> undefined -- VTrans (VPLam i a) phi u


-- transFill :: Name -> Val -> II -> Val -> Val
-- transFill i a phi u = trans j (a `conj` (i,j)) (phi `orII` NegAtom i) u
--   where j = fresh (Atom i,a,phi,u)

-- transFills :: Name ->  [(Ident,Ter)] -> Env -> II -> [Val] -> [Val]
-- transFills i []         _ phi []     = []
-- transFills i ((x,a):as) e phi (u:us) =
--   let v = transFill i (eval e a) phi u
--   in v : transFills i as (upd (x,v) e) phi us

-- transNeg :: Name -> Val -> II -> Val -> Val
-- transNeg i a phi u = trans i (a `sym` i) phi u

-- transFillNeg :: Name -> Val -> II -> Val -> Val
-- transFillNeg i a phi u = (transFill i (a `sym` i) phi u) `sym` i

-- transNegLine :: Val -> II -> Val -> Val
-- transNegLine u phi v = transNeg i (u @@ i) phi v
--   where i = fresh (u,phi,v)

-- transps :: Name -> [(Ident,Ter)] -> Env -> II -> [Val] -> [Val]
-- transps i []         _ phi []     = []
-- transps i ((x,a):as) e phi (u:us) =
--   let v   = transFill i (eval e a) phi u
--       vi1 = trans i (eval e a) phi u
--       vs  = transps i as (upd (x,v) e) phi us
--   in vi1 : vs
-- transps _ _ _ _ _ = error "transps: different lengths of types and values"

-- -- Takes a type i : II |- a and i:II |- u : a, both constant on
-- -- (phi=1) and returns a path in direction i connecting transp i a phi
-- -- u(i/0) to u(i/1).
-- squeeze :: Name -> Val -> II -> Val -> Val
-- squeeze i a phi u = trans j (a `disj` (i,j)) (phi `orII` Atom i) u
--   where j = fresh (Atom i,a,phi,u)



-------------------------------------------------------------------------------
-- | HITs

pcon :: LIdent -> Val -> [Val] -> [II] -> Val
pcon c a@(Ter (HSum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
  Just (tele,is,ts) -> case evalSystem (subs (zip is phis) (updsTele tele us rho)) ts of
    Triv x -> x
    _ -> VPCon c a us phis
  Nothing           -> error "pcon"
pcon c a us phi     = VPCon c a us phi


-------------------------------------------------------------------------------
-- | V-types

-- RedPRL style equiv between A and B:
-- f : A -> B
-- p : (x : B) -> isContr ((y : A) * Path B (f y) x)
-- with isContr C = (s : C) * ((z : C) -> Path C z s)


-- We are currently using:
-- Part 3 style equiv between A and B:
-- f : A -> B
-- p : (x : B) -> isContr ((y : A) * Path B (f y) x)
-- with isContr C = C * ((c c' : C) -> Path C c c')

equivFun :: Val -> Val
equivFun = fstVal

equivContr :: Val -> Val
equivContr = sndVal

vtype :: II -> Val -> Val -> Val -> Val
vtype (Dir Zero) a _ _ = a
vtype (Dir One) _ b _ = b
vtype (Name i) a b e = VV i a b e

vin :: II -> Val -> Val -> Val
vin (Dir Zero) m _ = m
vin (Dir One) _ n = n
-- vin r m (VVproj s o _ _) | r == s = o -- TODO?
vin (Name i) m n = VVin i m n

vproj :: II -> Val -> Val -> Val -> Val -> Val
vproj (Dir Zero) o _ _ e = app (equivFun e) o -- TODO: rewrite equivFun
vproj (Dir One) o _ _ _ = o
vproj (Name i) x@(VVin j m n) _ _ _ | i == j = n
                                    | otherwise = error $ "vproj: " ++ show i ++ " and " ++ show x
vproj (Name i) o a b e = VVproj i o a b e


-------------------------------------------------------------------------------
-- | Glue

-- An equivalence for a type a is a triple (t,f,p) where
-- t : U
-- f : t -> a
-- p : (x : a) -> isContr ((y:t) * Id a x (f y))
-- with isContr c = (z : c) * ((z' : C) -> Id c z z')

-- Extraction functions for getting a, f, s and t:
-- equivDom :: Val -> Val
-- equivDom = fstVal

-- equivFun :: Val -> Val
-- equivFun = fstVal . sndVal

-- equivContr :: Val -> Val
-- equivContr = sndVal . sndVal

-- glue :: Val -> System Val -> Val
-- glue b ts | eps `member` ts = equivDom (ts ! eps)
--           | otherwise       = VGlue b ts

-- glueElem :: Val -> System Val -> Val
-- glueElem (VUnGlueElem u _ _) _ = u
-- glueElem v us | eps `member` us = us ! eps
--               | otherwise       = VGlueElem v us

-- unGlue :: Val -> Val -> System Val -> Val
-- unGlue w a equivs | eps `member` equivs = app (equivFun (equivs ! eps)) w
--                   | otherwise           = case w of
--                                             VGlueElem v us -> v
--                                             _ -> VUnGlueElem w a equivs

-- isNeutralGlueHComp :: System Val -> Val -> System Val -> Bool
-- isNeutralGlueHComp equivs u us =
--   (eps `notMember` equivs && isNeutral u) ||
--   any (\(alpha,uAlpha) -> eps `notMember` (equivs `face` alpha)
--         && isNeutral uAlpha) (assocs us)

-- Extend the system ts to a total element in b given q : isContr b
-- extend :: Val -> Val -> System Val -> Val
-- extend b q ts = hComp i b (fstVal q) ts'
--   where i = fresh (b,q,ts)
--         ts' = mapWithKey
--                 (\alpha tAlpha -> app ((sndVal q) `face` alpha) tAlpha @@ i) ts

-- transGlue :: Name -> Val -> System Val -> II -> Val -> Val
-- transGlue i a equivs psi u0 = glueElem v1' t1s'
--   where
--     v0 = unGlue u0 (a `face` (i~>0)) (equivs `face` (i~>0))
--     ai1 = a `face` (i~>1)
--     alliequivs = allSystem i equivs
--     psisys = invSystem psi One -- (psi = 1) : FF
--     t1s = mapWithKey
--             (\al wal -> trans i (equivDom wal) (psi `face` al) (u0 `face` al))
--             alliequivs
--     wts = mapWithKey (\al wal ->
--               app (equivFun wal)
--                 (transFill i (equivDom wal) (psi `face` al) (u0 `face` al)))
--             alliequivs
--     v1 = comp i a v0 (border v0 psisys `unionSystem` wts)

--     fibersys = mapWithKey
--                  (\al x -> VPair x (constPath (v1 `face` al)))
--                  (border u0 psisys `unionSystem` t1s)

--     fibersys' = mapWithKey
--                   (\al wal ->
--                      extend (mkFiberType (ai1 `face` al) (v1 `face` al) wal)
--                        (app (equivContr wal) (v1 `face` al))
--                        (fibersys `face` al))
--                   (equivs `face` (i~>1))

--     t1s' = Map.map fstVal fibersys'
--     -- no need for a fresh name; take i
--     v1' = hComp i ai1 v1 (Map.map (\om -> (sndVal om) @@ i) fibersys'
--                            `unionSystem` border v1 psisys)

-- mkFiberType :: Val -> Val -> Val -> Val
-- mkFiberType a x equiv = eval rho $
--   Sigma $ Lam "y" tt (PathP (PLam (N "_") ta) tx (App tf ty))
--   where [ta,tx,ty,tf,tt] = map Var ["a","x","y","f","t"]
--         rho = upds [("a",a),("x",x),("f",equivFun equiv)
--                    ,("t",equivDom equiv)] emptyEnv

-- -- Assumes u' : A is a solution of us + (i0 -> u0)
-- -- The output is an L-path in A(i1) between comp i u0 us and u'(i1)
-- pathComp :: Name -> Val -> Val -> Val -> System Val -> Val
-- pathComp i a u0 u' us = VPLam j $ comp i a u0 us'
--   where j   = fresh (Atom i,a,us,u0,u')
--         us' = insertsSystem [(j~>1, u')] us

-------------------------------------------------------------------------------
-- | Composition in the Universe

-- any path between types define an equivalence
-- eqFun :: Val -> Val -> Val
-- eqFun e = transNegLine e (Dir Zero)

-- unGlueU :: Val -> Val -> System Val -> Val
-- unGlueU w b es | eps `Map.member` es = eqFun (es ! eps) w
--                | otherwise           = case w of
--                                         VGlueElem v us   -> v
--                                         _ -> VUnGlueElemU w b es

-- hCompUniv :: Val -> System Val -> Val
-- hCompUniv b es | eps `Map.member` es = (es ! eps) @@ One
--                | otherwise           = VHCompU b es

-- transHCompU :: Name -> Val -> System Val -> II -> Val -> Val
-- transHCompU i a es psi u0 = glueElem v1' t1s'
--   where
--     v0 = unGlueU u0 (a `face` (i~>0)) (es `face` (i~>0))
--     ai1 = a `face` (i~>1)
--     allies = allSystem i es
--     psisys = invSystem psi One -- (psi = 1) : FF
--     t1s = mapWithKey
--             (\al eal -> trans i (eal @@ One) (psi `face` al) (u0 `face` al))
--             allies
--     wts = mapWithKey (\al eal ->
--               eqFun eal
--                 (transFill i (eal @@ One) (psi `face` al) (u0 `face` al)))
--             allies
--     v1 = comp i a v0 (border v0 psisys `unionSystem` wts)

--     fibersys = mapWithKey
--                  (\al x -> (x,constPath (v1 `face` al)))
--                  (border u0 psisys `unionSystem` t1s)

--     fibersys' = mapWithKey
--                   (\al eal ->
--                      lemEq eal (v1 `face` al) (fibersys `face` al))
--                   (es `face` (i~>1))

--     t1s' = Map.map fst fibersys'
--     -- no need for a fresh name; take i
--     v1' = hComp i ai1 v1 (Map.map (\om -> (snd om) @@ i) fibersys'
--                            `unionSystem` border v1 psisys)

-- -- TODO: check; can probably be optimized
-- lemEq :: Val -> Val -> System (Val,Val) -> (Val,Val)
-- lemEq eq b aps = (a,VPLam i (compNeg j (eq @@ j) p1 thetas'))
--  where
--    i:j:_ = freshs (eq,b,aps)
--    ta = eq @@ One
--    p1s = mapWithKey (\alpha (aa,pa) ->
--               let eqaj = (eq `face` alpha) @@ j
--                   ba = b `face` alpha
--               in comp j eqaj (pa @@ i)
--                    (mkSystem [ (i~>0,transFill j eqaj (Dir Zero) ba)
--                              , (i~>1,transFillNeg j eqaj (Dir Zero) aa)])) aps
--    thetas = mapWithKey (\alpha (aa,pa) ->
--               let eqaj = (eq `face` alpha) @@ j
--                   ba = b `face` alpha
--               in fill j eqaj (pa @@ i)
--                    (mkSystem [ (i~>0,transFill j eqaj (Dir Zero) ba)
--                              , (i~>1,transFillNeg j eqaj (Dir Zero) aa)])) aps

--    a  = hComp i ta (trans i (eq @@ i) (Dir Zero) b) p1s
--    p1 = hFill i ta (trans i (eq @@ i) (Dir Zero) b) p1s

--    thetas' = insertsSystem
--                [ (i~>0,transFill j (eq @@ j) (Dir Zero) b)
--                , (i~>1,transFillNeg j (eq @@ j) (Dir Zero) a)]
--                thetas


-------------------------------------------------------------------------------
-- | Conversion

class Convertible a where
  conv :: [String] -> a -> a -> Bool

-- relies on Eqn invariant
isCompSystem :: (Nominal a, Convertible a) => [String] -> System a -> Bool
isCompSystem ns (Triv _) = True
isCompSystem ns (Sys us) = and [ conv ns (getFace alpha beta) (getFace beta alpha)
                               | (alpha,beta) <- allCompatible (Map.keys us) ]
  where
  getFace a b = us Map.! a `subst` toSubst a `subst` toSubst (b `subst` toSubst a)
  -- getFace a@(Eqn (Name i) (Name j)) (Eqn (Name k) (Dir d))
  --   | i == k || j == k = us ! a `subst` (i,Dir d) `subst` (j,Dir d)
  -- getFace a@(Eqn (Name k) (Dir d)) (Eqn (Name i) (Name j))
  --   | i == k || j == k = us ! a `subst` (i,Dir d) `subst` (j,Dir d)
  -- getFace a b = (us ! a) `subst` toSubst b

instance Convertible Env where
  conv ns (Env (rho1,vs1,fs1,os1)) (Env (rho2,vs2,fs2,os2)) =
      conv ns (rho1,vs1,fs1,os1) (rho2,vs2,fs2,os2)

instance Convertible Val where
  conv ns u v | u == v    = True
              | otherwise =
    let j = fresh (u,v)
    in case (u,v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e')       ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (eval (upd (x',v) e') u')
      (Ter (Lam x a u) e,u')                          ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (eval (upd (x,v) e) u) (app u' v)
      (u',Ter (Lam x a u) e)                          ->
        let v@(VVar n _) = mkVarNice ns x (eval e a)
        in conv (n:ns) (app u' v) (eval (upd (x,v) e) u)
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> (p == p') && conv ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> (p == p') && conv ns e e'
      (Ter (HSum p _ _) e,Ter (HSum p' _ _) e')       -> (p == p') && conv ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e')         -> p == p' && conv ns e e'
      (Ter (Hole p) e,Ter (Hole p') e')               -> p == p' && conv ns e e'
      -- (Ter Hole{} e,_)                             -> True
      -- (_,Ter Hole{} e')                            -> True
      (VPi u v,VPi u' v')                             ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VSigma u v,VSigma u' v')                       ->
        let w@(VVar n _) = mkVarNice ns "X" u
        in conv ns u u' && conv (n:ns) (app v w) (app v' w)
      (VCon c us,VCon c' us')                         -> (c == c') && conv ns us us'
      (VPCon c v us phis,VPCon c' v' us' phis')       ->
        (c == c') && conv ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')                         -> conv ns u u' && conv ns v v'
      (VPair u v,w)                                   -> conv ns u (fstVal w) && conv ns v (sndVal w)
      (w,VPair u v)                                   -> conv ns (fstVal w) u && conv ns (sndVal w) v
      (VFst u,VFst u')                                -> conv ns u u'
      (VSnd u,VSnd u')                                -> conv ns u u'
      (VApp u v,VApp u' v')                           -> conv ns u u' && conv ns v v'
      (VSplit u v,VSplit u' v')                       -> conv ns u u' && conv ns v v'
      (VOpaque x _, VOpaque x' _)                     -> x == x'
      (VVar x _, VVar x' _)                           -> x == x'
      (VPathP a b c,VPathP a' b' c')                  -> conv ns a a' && conv ns b b' && conv ns c c'
      (VPLam i a,VPLam i' a')                         -> conv ns (a `swap` (i,j)) (a' `swap` (i',j))
      (VPLam i a,p')                                  -> conv ns (a `swap` (i,j)) (p' @@ j)
      (p,VPLam i' a')                                 -> conv ns (p @@ j) (a' `swap` (i',j))
      (VAppII u x,VAppII u' x')                       -> conv ns (u,x) (u',x')
      (VCoe r s a u,VCoe r' s' a' u')                 -> conv ns (r,s,a,u) (r',s',a',u')
        -- -- TODO: Maybe identify via (- = 1)?  Or change argument to a system..
        -- conv ns (a,invSystem phi One,u) (a',invSystem phi' One,u')
        -- conv ns (a,phi,u) (a',phi',u')
      (VHCom r s a us u0,VHCom r' s' a' us' u0')      -> conv ns (r,s,a,us,u0) (r',s',a',us',u0')
      (VV i a b e,VV i' a' b' e')                     -> i == i' && conv ns (a,b,e) (a',b',e')
      (VVin _ m n,VVin _ m' n')                       -> conv ns (m,n) (m',n')
      (VVproj i o _ _ _,VVproj i' o' _ _ _)           -> i == i' && conv ns o o'
      -- (VGlue v equivs,VGlue v' equivs')            -> conv ns (v,equivs) (v',equivs')
      -- (VGlueElem u us,VGlueElem u' us')            -> conv ns (u,us) (u',us')
      -- (VUnGlueElemU u _ _,VUnGlueElemU u' _ _)     -> conv ns u u'
      -- (VUnGlueElem u _ _,VUnGlueElem u' _ _)       -> conv ns u u'
      -- (VHCompU u es,VHCompU u' es')                -> conv ns (u,es) (u',es')
      _                                               -> False

instance Convertible Ctxt where
  conv _ _ _ = True

instance Convertible () where
  conv _ _ _ = True

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv ns (u,v) (u',v') = conv ns u u' && conv ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv ns (u,v,w) (u',v',w') = conv ns (u,(v,w)) (u',(v',w'))

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv ns (u,v,w,x) (u',v',w',x') = conv ns (u,v,(w,x)) (u',v',(w',x'))

instance (Convertible a,Convertible b,Convertible c,Convertible d,Convertible e)
      => Convertible (a,b,c,d,e) where
  conv ns (u,v,w,x,y) (u',v',w',x',y') = conv ns (u,v,w,(x,y)) (u',v',w',(x',y'))

instance (Convertible a,Convertible b,Convertible c,Convertible d,Convertible e,Convertible f)
      => Convertible (a,b,c,d,e,f) where
  conv ns (u,v,w,x,y,z) (u',v',w',x',y',z') = conv ns (u,v,w,x,(y,z)) (u',v',w',x',(y',z'))

instance Convertible a => Convertible [a] where
  conv ns us us' = length us == length us' &&
                   and [conv ns u u' | (u,u') <- zip us us']

instance (Convertible a,Nominal a) => Convertible (System a) where
  conv ns (Triv u) (Triv u') = conv ns u u'
  conv ns (Sys us) (Sys us') =
    let compare eqn u u' = conv ns (u `subst` toSubst eqn) (u' `subst` toSubst eqn)
    in Map.keys us == Map.keys us' &&
       and (Map.elems (Map.intersectionWithKey compare us us'))

instance Convertible II where
  conv _ r s = r == s

instance Convertible (Nameless a) where
  conv _ _ _ = True

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [String] -> a -> a

instance Normal Env where
  normal ns (Env (rho,vs,fs,os)) = Env (normal ns (rho,vs,fs,os))

instance Normal Val where
  normal ns v = case v of
    VU                     -> VU
    Ter (Lam x t u) e      ->
      let w = eval e t
          v@(VVar n _) = mkVarNice ns x w
      in VLam n (normal ns w) $ normal (n:ns) (eval (upd (x,v) e) u)
    Ter t e                -> Ter t (normal ns e)
    VPi u v                -> VPi (normal ns u) (normal ns v)
    VSigma u v             -> VSigma (normal ns u) (normal ns v)
    VPair u v              -> VPair (normal ns u) (normal ns v)
    VCon n us              -> VCon n (normal ns us)
    VPCon n u us phis      -> VPCon n (normal ns u) (normal ns us) phis
    VPathP a u0 u1         -> VPathP (normal ns a) (normal ns u0) (normal ns u1)
    VPLam i u              -> VPLam i (normal ns u)
    VCoe r s a u           -> VCoe (normal ns r) (normal ns s) (normal ns a) (normal ns u)
    VHCom r s u vs v       -> VHCom (normal ns r) (normal ns s) (normal ns u) (normal ns vs) (normal ns v)
    VV i a b e             -> VV i (normal ns a) (normal ns b) (normal ns e)
    VVin i m n             -> VVin i (normal ns m) (normal ns n)
    VVproj i o a b e       -> VVproj i (normal ns o) (normal ns a) (normal ns b) (normal ns e)
    -- VGlue u equivs      -> VGlue (normal ns u) (normal ns equivs)
    -- VGlueElem u us      -> VGlueElem (normal ns u) (normal ns us)
    -- VUnGlueElem v u us  -> VUnGlueElem (normal ns v) (normal ns u) (normal ns us)
    -- VUnGlueElemU e u us -> VUnGlueElemU (normal ns e) (normal ns u) (normal ns us)
    -- VHCompU a ts        -> VHCompU (normal ns a) (normal ns ts)
    VVar x t               -> VVar x (normal ns t)
    VFst t                 -> VFst (normal ns t)
    VSnd t                 -> VSnd (normal ns t)
    VSplit u t             -> VSplit (normal ns u) (normal ns t)
    VApp u v               -> VApp (normal ns u) (normal ns v)
    VAppII u phi           -> VAppII (normal ns u) (normal ns phi)
    _                      -> v

instance Normal (Nameless a) where
  normal _ = id

instance Normal Ctxt where
  normal _ = id

instance Normal II where
  normal _ = id

instance (Nominal a, Normal a) => Normal (System a) where
  normal ns (Triv u) = Triv (normal ns u)
  normal ns (Sys us) =
    Sys (Map.mapWithKey (\eqn u -> normal ns (u `subst` toSubst eqn)) us)

instance (Normal a,Normal b) => Normal (a,b) where
  normal ns (u,v) = (normal ns u,normal ns v)

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal ns (u,v,w) = (normal ns u,normal ns v,normal ns w)

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal ns (u,v,w,x) =
    (normal ns u,normal ns v,normal ns w, normal ns x)

instance Normal a => Normal [a] where
  normal ns = map (normal ns)

{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, TupleSections #-}
module Eval where

import Debug.Trace
import Control.Monad
import Control.Monad.Gen
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Traversable as T

import Cartesian
import CTT

-----------------------------------------------------------------------
-- Lookup functions

look :: String -> Env -> Eval Val
look x (Env (Upd y rho,v:vs,fs,os)) | x == y = return v
                                    | otherwise = look x (Env (rho,vs,fs,os))
look x r@(Env (Def _ decls rho,vs,fs,Nameless os)) = case lookup x decls of
  Just (_,t) -> eval r t
  Nothing    -> look x (Env (rho,vs,fs,Nameless os))
look x (Env (Sub _ rho,vs,_:fs,os)) = look x (Env (rho,vs,fs,os))
look x (Env (Empty,_,_,_)) = error $ "look: not found " ++ show x

lookType :: String -> Env -> Eval Val
lookType x (Env (Upd y rho,v:vs,fs,os))
  | x /= y        = lookType x (Env (rho,vs,fs,os))
  | VVar _ a <- v = return a
  | otherwise     = error ""
lookType x r@(Env (Def _ decls rho,vs,fs,os)) = case lookup x decls of
  Just (a,_) -> eval r a
  Nothing -> lookType x (Env (rho,vs,fs,os))
lookType x (Env (Sub _ rho,vs,_:fs,os)) = lookType x (Env (rho,vs,fs,os))
lookType x (Env (Empty,_,_,_))          = error $ "lookType: not found " ++ show x

lookName :: Name -> Env -> II
lookName i (Env (Upd _ rho,v:vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Def _ _ rho,vs,fs,os)) = lookName i (Env (rho,vs,fs,os))
lookName i (Env (Sub j rho,vs,r:fs,os)) | i == j    = r
                                        | otherwise = lookName i (Env (rho,vs,fs,os))
lookName i _ = error $ "lookName: not found " ++ show i


-----------------------------------------------------------------------
-- Nominal instances

instance Nominal Ctxt where
  occurs _ _ = False
  subst e _  = return e
  swap e _   = e

instance Nominal Env where
  occurs x (Env (rho,vs,fs,os)) = occurs x (rho,vs,fs,os)
  subst (Env (rho,vs,fs,os)) iphi = do
    vs' <- subst vs iphi
    fs' <- subst fs iphi
    return $ Env (rho,vs',fs',os)
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
    VHComU r s t ts   -> occurs x (r,s,t,ts)
    VBox r s t ts     -> occurs x (r,s,t,ts)
    VCap r s t ts     -> occurs x (r,s,t,ts)
    -- VGlue a ts              -> occurs x (a,ts)
    -- VGlueElem a ts          -> occurs x (a,ts)
    -- VUnGlueElem a b ts      -> occurs x (a,b,ts)
    -- VHCompU a ts            -> occurs x (a,ts)
    -- VUnGlueElemU a b es     -> occurs x (a,b,es)

  subst u (i,r) = case u of
    VU                             -> return VU
    Ter t e                        -> Ter t <$> subst e (i,r)
    VPi a f                        -> VPi <$> subst a (i,r) <*> subst f (i,r)
    VPathP a u v                   -> VPathP <$> subst a (i,r) <*> subst u (i,r) <*> subst v (i,r)
    VPLam j v | j == i             -> return u
              | not (j `occurs` r) -> VPLam j <$> subst v (i,r)
              | otherwise          -> do
                k <- fresh
                VPLam k <$> subst (v `swap` (j,k)) (i,r)
    VSigma a f                     -> VSigma <$> subst a (i,r) <*> subst f (i,r)
    VPair u v                      -> VPair <$> subst u (i,r) <*> subst v (i,r)
    VFst u                         -> fstVal <$> subst u (i,r)
    VSnd u                         -> sndVal <$> subst u (i,r)
    VCon c vs                      -> VCon c <$> subst vs (i,r)
    VPCon c a vs phis              -> join $ pcon c <$> subst a (i,r) <*> subst vs (i,r) <*> subst phis (i,r)
    VHCom s s' a us u0             -> join $ hcom <$> subst s (i,r) <*> subst s' (i,r) <*> subst a (i,r) <*> subst us (i,r) <*> subst u0 (i,r)
    VCoe s s' a u                  -> join $ coe <$> subst s (i,r) <*> subst s' (i,r) <*> subst a (i,r) <*> subst u (i,r)
    VVar x v                       -> VVar x <$> subst v (i,r)
    VOpaque x v                    -> VOpaque x <$> subst v (i,r)
    VAppII u s                     -> join $ (@@) <$> subst u (i,r) <*> subst s (i,r)
    VApp u v                       -> join $ app <$> subst u (i,r) <*> subst v (i,r)
    VLam x t u                     -> VLam x <$> subst t (i,r) <*> subst u (i,r)
    VSplit u v                     -> join $ app <$> subst u (i,r) <*> subst v (i,r)
    VV j a b e                     ->
      vtype <$> subst (Name j) (i,r) <*> subst a (i,r) <*> subst b (i,r) <*> subst e (i,r)
    VVin j m n                     ->
      vin <$> subst (Name j) (i,r) <*> subst m (i,r) <*> subst n (i,r)
    VVproj j o a b e               ->
      join $ vproj <$> subst (Name j) (i,r) <*> subst o (i,r) <*> subst a (i,r) <*> subst b (i,r) <*> subst e (i,r)
    VHComU s s' ts t   -> join $ hcomU <$> subst s (i,r) <*> subst s' (i,r) <*> subst ts (i,r) <*> subst t (i,r)
    VBox s s' ts t     -> box <$> subst s (i,r) <*> subst s' (i,r) <*> subst ts (i,r) <*> subst t (i,r)
    VCap s s' ts t     -> join $ cap <$> subst s (i,r) <*> subst s' (i,r) <*> subst ts (i,r) <*> subst t (i,r)
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
         VHComU s s' ts t  -> VHComU (sw s) (sw s') (sw ts) (sw t)
         VBox s s' ts t    -> VBox (sw s) (sw s') (sw ts) (sw t)
         VCap s s' ts t    -> VCap (sw s) (sw s') (sw ts) (sw t)
         -- VGlue a ts              -> VGlue (sw a) (sw ts)
         -- VGlueElem a ts          -> VGlueElem (sw a) (sw ts)
         -- VUnGlueElem a b ts      -> VUnGlueElem (sw a) (sw b) (sw ts)
         -- VUnGlueElemU a b es     -> VUnGlueElemU (sw a) (sw b) (sw es)
         -- VHCompU a ts            -> VHCompU (sw a) (sw ts)

-----------------------------------------------------------------------
-- The evaluator

eval :: Env -> Ter -> Eval Val
eval rho@(Env (_,_,_,Nameless os)) v = case v of
  U                     -> return VU
  App r s               -> join $ app <$> eval rho r <*> eval rho s
  Var i
    | i `Set.member` os -> VOpaque i <$> lookType i rho
    | otherwise         -> look i rho
  Pi t@(Lam _ a _)      -> VPi <$> eval rho a <*> eval rho t
  Sigma t@(Lam _ a _)   -> VSigma <$> eval rho a <*> eval rho t
  Pair a b              -> VPair <$> eval rho a <*> eval rho b
  Fst a                 -> fstVal <$> eval rho a
  Snd a                 -> sndVal <$> eval rho a
  Where t decls         -> eval (defWhere decls rho) t
  Con name ts           -> VCon name <$> mapM (eval rho) ts
  PCon name a ts phis   ->
    join $ pcon name <$> eval rho a <*> mapM (eval rho) ts <*> pure (map (evalII rho) phis)
  Lam{}                 -> return $ Ter v rho
  Split{}               -> return $ Ter v rho
  Sum{}                 -> return $ Ter v rho
  HSum{}                -> return $ Ter v rho
  Undef{}               -> return $ Ter v rho
  Hole{}                -> return $ Ter v rho
  PathP a e0 e1         -> VPathP <$> eval rho a <*> eval rho e0 <*> eval rho e1
  PLam i t              -> do
    j <- fresh
    VPLam j <$> eval (sub (i,Name j) rho) t
  AppII e phi           -> join $ (@@) <$> eval rho e <*> pure (evalII rho phi)
  HCom r s a us u0      ->
    join $ hcom (evalII rho r) (evalII rho s) <$> eval rho a <*> evalSystem rho us <*> eval rho u0
  Coe r s a t           -> join $ coe (evalII rho r) (evalII rho s) <$> eval rho a <*> eval rho t
  -- Comp a t0 ts       -> compLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  V r a b e             -> vtype (evalII rho r) <$> eval rho a <*> eval rho b <*> eval rho e
  Vin r m n             -> vin (evalII rho r) <$> eval rho m <*> eval rho n
  Vproj r o a b e       ->
    join $ vproj (evalII rho r) <$> eval rho o <*> eval rho a <*> eval rho b <*> eval rho e
  Box r s ts t          -> box (evalII rho r) (evalII rho s) <$> evalSystem rho ts <*> eval rho t
  Cap r s ts t          -> join $ cap (evalII rho r) (evalII rho s) <$> evalSystem rho ts <*> eval rho t
  -- Glue a ts          -> glue (eval rho a) (evalSystem rho ts)
  -- GlueElem a ts      -> glueElem (eval rho a) (evalSystem rho ts)
  -- UnGlueElem v a ts  -> unGlue (eval rho v) (eval rho a) (evalSystem rho ts)
  _                     -> error $ "Cannot evaluate " ++ show v

evals :: Env -> [(Ident,Ter)] -> Eval [(Ident,Val)]
evals rho bts = mapM (\(b,t) -> (b,) <$> eval rho t) bts

evalII :: Env -> II -> II
evalII rho phi = case phi of
  Name i         -> lookName i rho
  _              -> phi

evalEqn :: Env -> Eqn -> Eqn
evalEqn rho (Eqn r s) = eqn (evalII rho r,evalII rho s)

evalSystem :: Env -> System Ter -> Eval (System Val)
evalSystem rho (Triv u) = Triv <$> eval rho u
evalSystem rho (Sys us) =
  case Map.foldrWithKey (\eqn u -> insertSystem (evalEqn rho eqn,u)) eps us of
    Triv u -> Triv <$> eval rho u
    Sys sys' -> do
      xs <- sequence $ Map.mapWithKey (\eqn u ->
                          join $ eval <$> rho `subst` toSubst eqn <*> pure u) sys'
      return $ Sys xs

app :: Val -> Val -> Eval Val
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
                    -> return (VSplit u v)
  (VCoe r s (VPLam i (VPi a b)) u0, v) -> trace "coe pi" $ do
    j <- fresh
    let bij = b `swap` (i,j)
    w <- coe s (Name j) (VPLam i a) v
    w0 <- coe s r (VPLam i a) v
    bijw <- VPLam j <$> app bij w
    coe r s bijw =<< app u0 w0
  (VHCom r s (VPi a b) (Sys us) u0, v) -> trace "hcom pi" $ do
    us' <- mapSystem (\_ u -> app u v) us
    join $ hcom r s <$> app b v <*> pure (Sys us') <*> app u0 v
  (VHCom _ _ _ (Triv u) _, v) -> error "app: trying to apply vhcom in triv"
  _                     -> return $ VApp u v -- error $ "app \n  " ++ show u ++ "\n  " ++ show v

fstVal, sndVal :: Val -> Val
fstVal (VPair a b)     = a
-- fstVal u | isNeutral u = VFst u
fstVal u               = VFst u -- error $ "fstVal: " ++ show u ++ " is not neutral."
sndVal (VPair a b)     = b
-- sndVal u | isNeutral u = VSnd u
sndVal u               = VSnd u -- error $ "sndVal: " ++ show u ++ " is not neutral."

-- infer the type of a neutral value
inferType :: Val -> Eval Val
inferType v = case v of
  VVar _ t -> return t
  VOpaque _ t -> return t
  Ter (Undef _ t) rho -> eval rho t
  VFst t -> inferType t >>= \t' -> case t' of -- LambdaCase?
    VSigma a _ -> return a
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSnd t -> inferType t >>= \t' -> case t' of
    VSigma _ f -> app f (VFst t)
    ty         -> error $ "inferType: expected Sigma type for " ++ show v
                  ++ ", got " ++ show ty
  VSplit s@(Ter (Split _ _ t _) rho) v1 -> eval rho t >>= \t' -> case t' of
    VPi _ f -> app f v1
    ty      -> error $ "inferType: Pi type expected for split annotation in "
               ++ show v ++ ", got " ++ show ty
  VApp t0 t1 -> inferType t0 >>= \t' -> case t' of
    VPi _ f -> app f t1
    ty      -> error $ "inferType: expected Pi type for " ++ show v
               ++ ", got " ++ show ty
  VAppII t phi -> inferType t >>= \t' -> case t' of
    VPathP a _ _ -> a @@ phi
    ty         -> error $ "inferType: expected PathP type for " ++ show v
                  ++ ", got " ++ show ty
  VHCom r s a _ _ -> return a
  VCoe r s a _ -> a @@ s
  VVproj _ _ _ b _ -> return b
  VHComU _ _ _ _ -> return VU
  VCap _ _ _ t -> return t -- TODO: is this correct?
  -- VUnGlueElem _ b _  -> b
  -- VUnGlueElemU _ b _ -> b
  _ -> error $ "inferType: not neutral " ++ show v

(@@) :: ToII a => Val -> a -> Eval Val
(VPLam i u) @@ phi         = u `subst` (i,toII phi)
v@(Ter Hole{} _) @@ phi    = return $ VAppII v (toII phi)
v @@ phi = do
  t <- inferType v
  case (t,toII phi) of
    (VPathP _ a0 _,Dir 0) -> return a0
    (VPathP _ _ a1,Dir 1) -> return a1
    _                     -> return $ VAppII v (toII phi)
-- v @@ phi                   = error $ "(@@): " ++ show v ++ " should be neutral."

-------------------------------------------------------------------------------
-- com and hcom

com :: II -> II -> Val -> System Val -> Val -> Eval Val
com r s a _ u0 | r == s = return u0
com _ s _ (Triv u) _  = u @@ s
com r s a (Sys us) u0 = do
  us' <- Sys <$> mapSystem (\j u -> coe (Name j) s a u) us
  join $ hcom r s <$> a @@ s <*> pure us' <*> coe r s a u0

-- apply f to each face, eta-expanding where needed, without freshening
mapSystemUnsafe :: (Val -> Eval Val) -> Map.Map Eqn Val -> Eval (Map.Map Eqn Val)
mapSystemUnsafe f us = do
  j <- fresh
  let etaMap (VPLam i u) = VPLam i <$> f u
      etaMap u = do
        uj <- u @@ j
        VPLam j <$> f uj
  T.sequence $ Map.map etaMap us

-- apply f to each face, with binder, with freshening
mapSystem :: (Name -> Val -> Eval Val) -> Map.Map Eqn Val -> Eval (Map.Map Eqn Val)
mapSystem f us = do
  j <- fresh
  let etaMap (VPLam i u) = VPLam j <$> f j (u `swap` (i,j))
      etaMap u = do
        uj <- u @@ j
        VPLam j <$> f j uj
  T.sequence $ Map.map etaMap us

hcom :: II -> II -> Val -> System Val -> Val -> Eval Val
hcom r s _ _ u0 | r == s = return u0
hcom r s _ (Triv u) _    = u @@ s
hcom r s a (Sys us) u0   = case a of
  VPathP a v0 v1 -> trace "hcom path" $ do
    j <- fresh
    us' <- insertsSystem [(j~>0,VPLam (N "_") v0),(j~>1,VPLam (N "_") v1)] <$>
             Sys <$> mapSystemUnsafe (@@ j) us
    aj <- a @@ j
    u0j <- u0 @@ j
    VPLam j <$> hcom r s aj us' u0j
  VSigma a b -> trace "hcom sigma" $ do
    j <- fresh
    us1 <- Sys <$> mapSystemUnsafe (return . fstVal) us
    us2 <- Sys <$> mapSystemUnsafe (return . sndVal) us
    let (u1,u2) = (fstVal u0,sndVal u0)
    u1fill <- hcom r (Name j) a us1 u1
    u1hcom <- hcom r s a us1 u1
    bj <- VPLam j <$> app b u1fill
    VPair u1hcom <$> com r s bj us2 u2
  VU -> hcomU r s (Sys us) u0
  v@VV{} -> vhcom v r s (Sys us) u0
  v@VHComU{} -> hcomHComU v r s (Sys us) u0
  -- Ter (Sum _ n nass) env
  --   | n `elem` ["nat","Z","bool"] -> u0 -- hardcode hack
  -- Ter (Sum _ _ nass) env | VCon n vs <- u0, all isCon (elems us) -> error "hcom sum"
  -- Ter (HSum _ _ _) _ -> VHCom r s a (Sys us) u0
  VPi{} -> return $ VHCom r s a (Sys us) u0
  _ -> return $ VHCom r s a (Sys us) u0


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
-- VGlue b equivs -> -- | not (isNeutralGlueHComp equivs u us) ->
--   let wts = mapWithKey (\al wal ->
--                 app (equivFun wal)
--                   (hFill i (equivDom wal) (u `face` al) (us `face` al)))
--               equivs
--       t1s = mapWithKey (\al wal ->
--               hComp i (equivDom wal) (u `face` al) (us `face` al)) equivs
--       v = unGlue u b equivs
--       vs = mapWithKey (\al ual -> unGlue ual (b `face` al) (equivs `face` al))
--              us
--       v1 = hComp i b v (vs `unionSystem` wts)
--   in glueElem v1 t1s
-- VHCompU b es -> -- | not (isNeutralGlueHComp es u us) ->
--   let wts = mapWithKey (\al eal ->
--                 eqFun eal
--                   (hFill i (eal @@ One) (u `face` al) (us `face` al)))
--               es
--       t1s = mapWithKey (\al eal ->
--               hComp i (eal @@ One) (u `face` al) (us `face` al)) es
--       v = unGlueU u b es
--       vs = mapWithKey (\al ual -> unGlueU ual (b `face` al) (es `face` al))
--              us
--       v1 = hComp i b v (vs `unionSystem` wts)
--   in glueElem v1 t1s
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

coe :: II -> II -> Val -> Val -> Eval Val
coe r s a u | r == s = return u
coe r s (VPLam i a) u = case a of
  VPathP a v0 v1 -> trace "coe path" $ do
    j <- fresh
    aij <- VPLam i <$> (a @@ j)
    out <- join $ com r s aij (mkSystem [(j~>0,VPLam i v0),(j~>1,VPLam i v1)]) <$> u @@ j
    return $ VPLam j out
  VSigma a b -> trace "coe sigma" $ do
    j <- fresh
    let (u1,u2) = (fstVal u, sndVal u)
    u1' <- coe r (Name j) (VPLam i a) u1
    bij <- app (b `swap` (i,j)) u1'
    v1 <- coe r s (VPLam i a) u1
    v2 <- coe r s (VPLam j bij) u2
    return $ VPair v1 v2
  VPi{} -> return $ VCoe r s (VPLam i a) u
  VU -> return u
  v@VHComU{} -> coeHComU (VPLam i v) r s u
  v@VV{} -> vvcoe (VPLam i v) r s u
  Ter (Sum _ n nass) env
    | n `elem` ["nat","Z","bool"] -> return u -- hardcode hack
    | otherwise -> error "coe sum"
  Ter (HSum _ n nass) env
    | n `elem` ["S1","S2","S3"] -> return u   -- hardcode hack
    | otherwise -> error "coe hsum"
  -- VTypes
  _ -> -- error "missing case in coe" --
       return $ VCoe r s (VPLam i a) u
coe r s a u = return $ VCoe r s a u


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

pcon :: LIdent -> Val -> [Val] -> [II] -> Eval Val
pcon c a@(Ter (HSum _ _ lbls) rho) us phis = case lookupPLabel c lbls of
  Just (tele,is,ts) -> evalSystem (subs (zip is phis) (updsTele tele us rho)) ts >>= \t' -> case t' of
    Triv x -> return x
    _ -> return $ VPCon c a us phis
  Nothing           -> error "pcon"
pcon c a us phi     = return $ VPCon c a us phi


-------------------------------------------------------------------------------
-- | V-types

-- TODO: eta for V-types?

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
vtype (Dir One) _ b _  = b
vtype (Name i) a b e   = VV i a b e

vin :: II -> Val -> Val -> Val
vin (Dir Zero) m _ = m
vin (Dir One) _ n  = n
-- vin r m (VVproj s o _ _) | r == s = o -- TODO?
vin (Name i) m n   = VVin i m n

vproj :: II -> Val -> Val -> Val -> Val -> Eval Val
vproj (Dir Zero) o _ _ e = app (equivFun e) o
vproj (Dir One) o _ _ _  = return o
vproj (Name i) x@(VVin j m n) _ _ _ | i == j = return n
                                    | otherwise = error $ "vproj: " ++ show i ++ " and " ++ show x
vproj (Name i) o a b e = return $ VVproj i o a b e


-- Coe for V-types

-- In Part 3: i corresponds to y, and, j to x
vvcoe :: Val -> II -> II -> Val -> Eval Val
vvcoe (VPLam i (VV j a b e)) r s u | i /= j = trace "vvcoe i != j" $ do
  vj0 <- join $ app (equivFun e) <$> coe r (Name i) (VPLam i a) u
  vj1 <- coe r (Name i) (VPLam i b) u
  let tvec = mkSystem [(j~>0,VPLam i vj0),(j~>1,VPLam i vj1)]
  (ar,br,er) <- (a,b,e) `subst` (i,r)
  vr <- vproj (Name j) u ar br er
  vin (Name j) <$> coe r s (VPLam i a) u
               <*> com r s (VPLam i b) tvec vr

vvcoe (VPLam _ (VV j a b e)) (Dir Zero) s u = trace "vvcoe 0->s" $ do
  ej0 <- equivFun e `subst` (j,0)
  ej0u <- app ej0 u
  vin s u <$> coe 0 s (VPLam j b) ej0u

-- TODO: take faces everywhere!
vvcoe (VPLam _ (VV j a b e)) (Dir One) s u = trace "vvcoe 1->s" $ do
  otm <- fstVal <$> join (app <$> equivContr e `subst` (j,s)
                              <*> coe 1 s (VPLam j b) u)
  u' <- coe 1 s (VPLam j b) u
  let psys = mkSystem [(s~>0,sndVal otm),(s~>1,VPLam (N "_") u)]
  ptm <- join $ hcom 1 0 <$> b `subst` (j,s)
                         <*> pure psys
                         <*> pure u'
  return $ vin s (fstVal otm) ptm

-- TODO: take faces everywhere!
vvcoe vty@(VPLam _ (VV j a b e)) (Name i) s u = trace "vvcoe i->s" $ do
  -- i = y
  -- j = x
  -- k = w
  -- l = z
  k <- fresh
  l <- fresh
  let (ak,bk,ek) = (a,b,e) `swap` (j,k)
      u' eps = VCoe eps (Name k) vty u
      otm eps = VVproj k (u' eps) ak bk ek
  let o0 = otm 0
  let o1 = otm 1
  let psys = mkSystem [(i~>0,VPLam k o0),(i~>1,VPLam k o1)]
  (ai,bi,ei) <- (a,b,e) `subst` (j,Name i)
  ptm <- join $ com (Name i) (Name j) (VPLam j b) psys
                 <$> vproj (Name i) u ai bi ei
  p0 <- ptm `subst` (j,0)
  (a0,b0,e0) <- (a,b,e) `subst` (j,0)
  let uvec eps t = do
        e0' <- join $ app (equivFun e0) <$> coe eps (Name i) (VPLam i a0) t
        return $ mkSystem [(l~>0,VPLam i e0'),(l~>1,VPLam i p0)]
      qtm eps t = do
        let t' = VCoe eps (Name i) (VPLam i a0) t
        p0' <- join $ com eps (Name i) (VPLam i b0) <$> uvec eps t <*> p0 `subst` (i,eps)
        return $ VPair t' (VPLam l p0')
  e0p02 <- sndVal <$> app (equivContr e0) p0
  u0 <- u `subst` (i,0)
  e0p02q <- join $ app e0p02 <$> qtm 0 u0
  foo <- coe 1 0 vty u
  foo1 <- foo `subst` (i,1)
  q1 <- qtm 1 foo1
  rtm' <- app e0p02q q1
  rtm <- rtm' @@ i
  (as,bs,es) <- (a,b,e) `subst` (j,s)
  (o0s,o1s) <- (o0,o1) `subst` (k,s)
  let tvec = mkSystem [(i~>0,VPLam (N "_") o0s)
                      ,(i~>1,VPLam (N "_") o1s)
                      ,(i~>s,VPLam (N "_") $ VVproj i u as bs es)
                      ,(s~>0,sndVal rtm)]
  ptms <- ptm `subst` (j,s)
  vin s (fstVal rtm) <$> hcom 1 0 bs tvec ptms
vvcoe _ _ _ _ = error "vvcoe: case not implemented"

-- hcom for V-types
vhcom :: Val -> II -> II -> System Val -> Val -> Eval Val
vhcom (VV i a b e) r s (Sys us) u = trace "vhcom" $ do
  j <- fresh
  otm <- hcom r (Name j) a (Sys us) u
  ti0 <- do
    e0 <- equivFun e `subst` (i,0)  -- i can occur in e
    otm0 <- otm `subst` (i,0) -- i can occur in a
    VPLam j <$> app e0 otm0
  ti1 <- do
    b0 <- b `subst` (i,0)  -- i can occur in b
    VPLam j <$> hcom r (Name j) b0 (Sys us) u
  let tvec = [(i~>0,ti0),(i~>1,ti1)]
  us' <- mapSystemUnsafe (\n -> VPLam j <$> vproj (Name i) n a b e) us
  u' <- vproj (Name i) u a b e
  vin (Name i) <$> otm `subst` (j,s)
               <*> hcom r s b (insertsSystem tvec (Sys us')) u'
vhcom _ _ _ _ _ = error "vhcom: case not implemented"

-------------------------------------------------------------------------------
-- | Universe

-- TODO: eta for box/cap?

box :: II -> II -> System Val -> Val -> Val
box r s _ t | r == s = t
box _ _ (Triv t) _   = t
box r s ts t         = VBox r s ts t

cap :: II -> II -> System Val -> Val -> Eval Val
cap r s _ t | r == s = return t
cap r s (Triv b) t   = -- coe s r b t -- TODO: eta expand b?
  do y <- fresh
     coe s r (VPLam y b) t
cap r s _ (VBox r' s' _ t) | r == r' && s == s' = return t
cap r s ts t = return $ VCap r s ts t

hcomU :: II -> II -> System Val -> Val -> Eval Val
hcomU r s _ u0 | r == s = return u0
hcomU r s (Triv u) _    = u @@ s
hcomU r s ts t          = return $ VHComU r s ts t

-- TODO: take faces everywhere!
coeHComU :: Val -> II -> II -> Val -> Eval Val
coeHComU (VPLam i (VHComU s s' (Sys bs) a)) r r' m = trace "coe hcomU" $ do
  -- k = z
  k <- fresh
  -- Define N_i. Parametrize by B_i instead of just i
  let ntm bi = do
        bi' <- bi `subst` (k,s')
        m' <- coe r (Name i) (VPLam i bi') m
        coe s' (Name k) (VPLam k bi) m'
  -- Define O
  otm <- do
    -- VPLam in system?
    osys <- Sys <$> mapSystem (\k bi -> coe (Name k) s (VPLam k bi) =<< ntm bi) bs
    ocap <- cap s s' (Sys bs) m
    o' <- hcom s' (Name k) a osys ocap
    o' `subst` (i,r)
  -- Define P
  ptm <- do
    sr <- s `subst` (i,r)
    otm' <- otm `subst` (k,sr)
    -- VPLam in system?
    psys' <- mapSystemUnsafe (\bi -> ntm bi >>= flip subst (k,s)) $
               Map.filterWithKey (\(Eqn s s') _ -> Name i /= s && Name i /= s') bs
    m' <- coe r (Name i) (VPLam i a) m
    let psys = if Name i /= s && Name i /= s'
                  then insertSystem (eqn (s,s'),VPLam i m') (Sys psys')
                  else Sys psys'
    com r r' (VPLam i a) psys otm'
  -- Define Q_k. Parametrize by B_k instead of just k
  let qtm bk = do
        bk' <- bk `subst` (i,r')
        -- VPLam in system?
        qsys' <- mapSystemUnsafe (\bi -> ntm bi >>= flip subst (i,r')) $
                   Map.filterWithKey (\(Eqn s s') _ -> Name i /= s && Name i /= s') bs
        ntmbk <- ntm bk
        ntmbk' <- ntmbk `subst` (i,r')
        let qsys = insertSystem (eqn (r,r'),VPLam k ntmbk') (Sys qsys')
        sr' <- s `subst` (i,r')
        com sr' (Name k) (VPLam k bk') qsys ptm
  outtmsys <- Sys <$> mapSystem (\k bi -> coe (Name k) s (VPLam k bi) =<< qtm bi) bs -- VPLam in system?
  outtm <- hcom s s' a (insertSystem (eqn (r,r'),VPLam k otm) outtmsys) ptm
  outsys <- Sys <$> mapSystemUnsafe (\bi -> qtm bi >>= flip subst (k,s')) bs
  (box s s' outsys outtm) `subst` (i,r')
coeHComU _ _ _ _ = error "coeHComU: case not implemented"

-- TODO: take faces everywhere!
hcomHComU :: Val -> II -> II -> System Val -> Val -> Eval Val
hcomHComU (VHComU s s' bs a) r r' us m = error "hcomHComU not implemented"


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
  conv :: [String] -> a -> a -> Eval Bool

-- relies on Eqn invariant
isCompSystem :: (Nominal a, Convertible a) => [String] -> System a -> Eval Bool
isCompSystem ns (Triv _) = return True
isCompSystem ns (Sys us) =
  and <$> sequence [ join (conv ns <$> getFace alpha beta <*> getFace beta alpha)
                 | (alpha,beta) <- allCompatible (Map.keys us) ]
  where
  getFace a b = do
    usa <- us Map.! a `subst` toSubst a
    ba <- b `subst` toSubst a
    usa `subst` toSubst ba
  -- getFace a@(Eqn (Name i) (Name j)) (Eqn (Name k) (Dir d))
  --   | i == k || j == k = us ! a `subst` (i,Dir d) `subst` (j,Dir d)
  -- getFace a@(Eqn (Name k) (Dir d)) (Eqn (Name i) (Name j))
  --   | i == k || j == k = us ! a `subst` (i,Dir d) `subst` (j,Dir d)
  -- getFace a b = (us ! a) `subst` toSubst b

instance Convertible Env where
  conv ns (Env (rho1,vs1,fs1,os1)) (Env (rho2,vs2,fs2,os2)) =
      conv ns (rho1,vs1,fs1,os1) (rho2,vs2,fs2,os2)

instance Convertible Val where
  conv ns u v | u == v    = return True
              | otherwise = do
    j <- fresh
    case (u,v) of
      (Ter (Lam x a u) e,Ter (Lam x' a' u') e')       -> do
        v@(VVar n _) <- mkVarNice ns x <$> eval e a
        join $ conv (n:ns) <$> eval (upd (x,v) e) u <*> eval (upd (x',v) e') u'
      (Ter (Lam x a u) e,u')                          -> do
        v@(VVar n _) <- mkVarNice ns x <$> eval e a
        join $ conv (n:ns) <$> eval (upd (x,v) e) u <*> app u' v
      (u',Ter (Lam x a u) e)                          -> do
        v@(VVar n _) <- mkVarNice ns x <$> eval e a
        join $ conv (n:ns) <$> app u' v <*> eval (upd (x,v) e) u
      (Ter (Split _ p _ _) e,Ter (Split _ p' _ _) e') -> pure (p == p') <&&> conv ns e e'
      (Ter (Sum p _ _) e,Ter (Sum p' _ _) e')         -> pure (p == p') <&&> conv ns e e'
      (Ter (HSum p _ _) e,Ter (HSum p' _ _) e')       -> pure (p == p') <&&> conv ns e e'
      (Ter (Undef p _) e,Ter (Undef p' _) e')         -> pure (p == p') <&&> conv ns e e'
      (Ter (Hole p) e,Ter (Hole p') e')               -> pure (p == p') <&&> conv ns e e'
      -- (Ter Hole{} e,_)                             -> return True
      -- (_,Ter Hole{} e')                            -> return True
      (VPi u v,VPi u' v')                             -> do
        let w@(VVar n _) = mkVarNice ns "X" u
        conv ns u u' <&&> join (conv (n:ns) <$> app v w <*> app v' w)
      (VSigma u v,VSigma u' v')                       -> do
        let w@(VVar n _) = mkVarNice ns "X" u
        conv ns u u' <&&> join (conv (n:ns) <$> app v w <*> app v' w)
      (VCon c us,VCon c' us')                         -> pure (c == c') <&&> conv ns us us'
      (VPCon c v us phis,VPCon c' v' us' phis')       ->
        pure (c == c') <&&> conv ns (v,us,phis) (v',us',phis')
      (VPair u v,VPair u' v')                         -> conv ns u u' <&&> conv ns v v'
      (VPair u v,w)                                   -> conv ns u (fstVal w) <&&> conv ns v (sndVal w)
      (w,VPair u v)                                   -> conv ns (fstVal w) u <&&> conv ns (sndVal w) v
      (VFst u,VFst u')                                -> conv ns u u'
      (VSnd u,VSnd u')                                -> conv ns u u'
      (VApp u v,VApp u' v')                           -> conv ns u u' <&&> conv ns v v'
      (VSplit u v,VSplit u' v')                       -> conv ns u u' <&&> conv ns v v'
      (VOpaque x _, VOpaque x' _)                     -> return $ x == x'
      (VVar x _, VVar x' _)                           -> return $ x == x'
      (VPathP a b c,VPathP a' b' c')                  -> conv ns a a' <&&> conv ns b b' <&&> conv ns c c'
      (VPLam i a,VPLam i' a')                         -> conv ns (a `swap` (i,j)) (a' `swap` (i',j))
      (VPLam i a,p')                                  -> join $ conv ns (a `swap` (i,j)) <$> p' @@ j
      (p,VPLam i' a')                                 -> join $ conv ns <$> p @@ j <*> pure (a' `swap` (i',j))
      (VAppII u x,VAppII u' x')                       -> conv ns (u,x) (u',x')
      (VCoe r s a u,VCoe r' s' a' u')                 -> conv ns (r,s,a,u) (r',s',a',u')
        -- -- TODO: Maybe identify via (- = 1)?  Or change argument to a system..
        -- conv ns (a,invSystem phi One,u) (a',invSystem phi' One,u')
        -- conv ns (a,phi,u) (a',phi',u')
      (VHCom r s a us u0,VHCom r' s' a' us' u0')      -> conv ns (r,s,a,us,u0) (r',s',a',us',u0')
      (VV i a b e,VV i' a' b' e')                     -> pure (i == i') <&&> conv ns (a,b,e) (a',b',e')
      (VVin _ m n,VVin _ m' n')                       -> conv ns (m,n) (m',n')
      (VVproj i o _ _ _,VVproj i' o' _ _ _)           -> pure (i == i') <&&> conv ns o o'
      (VHComU r s ts t,VHComU r' s' ts' t')           -> conv ns (r,s,ts,t) (r',s',ts',t')
      -- TODO: are the following two cases correct?
      (VCap r s ts t,VCap r' s' ts' t')               -> conv ns (r,s,ts,t) (r',s',ts',t')
      (VBox r s ts t,VBox r' s' ts' t')               -> conv ns (r,s,ts,t) (r',s',ts',t')
      -- (VGlue v equivs,VGlue v' equivs')            -> conv ns (v,equivs) (v',equivs')
      -- (VGlueElem u us,VGlueElem u' us')            -> conv ns (u,us) (u',us')
      -- (VUnGlueElemU u _ _,VUnGlueElemU u' _ _)     -> conv ns u u'
      -- (VUnGlueElem u _ _,VUnGlueElem u' _ _)       -> conv ns u u'
      -- (VHCompU u es,VHCompU u' es')                -> conv ns (u,es) (u',es')
      _                                               -> return False

instance Convertible Ctxt where
  conv _ _ _ = return True

instance Convertible () where
  conv _ _ _ = return True

(<&&>) :: Monad m => m Bool -> m Bool -> m Bool
u <&&> v = do
  b1 <- u
  b2 <- v
  return (b1 && b2)

instance (Convertible a, Convertible b) => Convertible (a, b) where
  conv ns (u,v) (u',v') = conv ns u u' <&&> conv ns v v'

instance (Convertible a, Convertible b, Convertible c)
      => Convertible (a, b, c) where
  conv ns (u,v,w) (u',v',w') =
    conv ns u u' <&&> conv ns v v' <&&> conv ns w w'

instance (Convertible a,Convertible b,Convertible c,Convertible d)
      => Convertible (a,b,c,d) where
  conv ns (u,v,w,x) (u',v',w',x') =
    conv ns u u' <&&> conv ns v v' <&&> conv ns w w' <&&> conv ns x x'

instance (Convertible a,Convertible b,Convertible c,Convertible d,Convertible e)
      => Convertible (a,b,c,d,e) where
  conv ns (u,v,w,x,y) (u',v',w',x',y') =
    conv ns u u' <&&> conv ns v v' <&&> conv ns w w' <&&> conv ns x x' <&&>
    conv ns y y'

instance (Convertible a,Convertible b,Convertible c,Convertible d,Convertible e,Convertible f)
      => Convertible (a,b,c,d,e,f) where
  conv ns (u,v,w,x,y,z) (u',v',w',x',y',z') =
    conv ns u u' <&&> conv ns v v' <&&> conv ns w w' <&&> conv ns x x' <&&>
    conv ns y y' <&&> conv ns z z'

instance Convertible a => Convertible [a] where
  conv ns us us' = do
    bs <- sequence [ conv ns u u' | (u,u') <- zip us us' ]
    return (length us == length us' && and bs)

instance (Convertible a,Nominal a) => Convertible (System a) where
  conv ns (Triv u) (Triv u') = conv ns u u'
  conv ns (Sys us) (Sys us') = do
    let compare eqn u u' = join $ conv ns <$> u `subst` toSubst eqn <*> u' `subst` toSubst eqn
    bs <- T.sequence $ Map.elems (Map.intersectionWithKey compare us us')
    return $ Map.keys us == Map.keys us' && and bs

instance Convertible II where
  conv _ r s = return $ r == s

instance Convertible (Nameless a) where
  conv _ _ _ = return True

-------------------------------------------------------------------------------
-- | Normalization

class Normal a where
  normal :: [String] -> a -> Eval a

instance Normal Env where
  normal ns (Env (rho,vs,fs,os)) = Env <$> normal ns (rho,vs,fs,os)

instance Normal Val where
  normal ns v = case v of
    VU                     -> return VU
    Ter (Lam x t u) e      -> do
      w <- eval e t
      let v@(VVar n _) = mkVarNice ns x w
      u' <- eval (upd (x,v) e) u
      VLam n <$> normal ns w <*> normal (n:ns) u'
    Ter t e                -> Ter t <$> normal ns e
    VPi u v                -> VPi <$> normal ns u <*> normal ns v
    VSigma u v             -> VSigma <$> normal ns u <*> normal ns v
    VPair u v              -> VPair <$> normal ns u <*> normal ns v
    VCon n us              -> VCon n <$> normal ns us
    VPCon n u us phis      -> VPCon n <$> normal ns u <*> normal ns us <*> pure phis
    VPathP a u0 u1         -> VPathP <$> normal ns a <*> normal ns u0 <*> normal ns u1
    VPLam i u              -> VPLam i <$> normal ns u
    VCoe r s a u           -> VCoe <$> normal ns r <*> normal ns s <*> normal ns a <*> normal ns u
    VHCom r s u vs v       -> VHCom <$> normal ns r <*> normal ns s <*> normal ns u <*> normal ns vs <*> normal ns v
    VV i a b e             -> VV i <$> normal ns a <*> normal ns b <*> normal ns e
    VVin i m n             -> VVin i <$> normal ns m <*> normal ns n
    VVproj i o a b e       -> VVproj i <$> normal ns o <*> normal ns a <*> normal ns b <*> normal ns e
    VHComU r s ts t        -> VHComU <$> normal ns r <*> normal ns s <*> normal ns ts <*> normal ns t
    VCap r s ts t          -> VCap <$> normal ns r <*> normal ns s <*> normal ns ts <*> normal ns t
    VBox r s ts t          -> VBox <$> normal ns r <*> normal ns s <*> normal ns ts <*> normal ns t
    -- VGlue u equivs      -> VGlue (normal ns u) (normal ns equivs)
    -- VGlueElem u us      -> VGlueElem (normal ns u) (normal ns us)
    -- VUnGlueElem v u us  -> VUnGlueElem (normal ns v) (normal ns u) (normal ns us)
    -- VUnGlueElemU e u us -> VUnGlueElemU (normal ns e) (normal ns u) (normal ns us)
    -- VHCompU a ts        -> VHCompU (normal ns a) (normal ns ts)
    VVar x t               -> VVar x <$> normal ns t
    VFst t                 -> VFst <$> normal ns t
    VSnd t                 -> VSnd <$> normal ns t
    VSplit u t             -> VSplit <$> normal ns u <*> normal ns t
    VApp u v               -> VApp <$> normal ns u <*> normal ns v
    VAppII u phi           -> VAppII <$> normal ns u <*> normal ns phi
    _                      -> return v

instance Normal (Nameless a) where
  normal _ = return

instance Normal Ctxt where
  normal _ = return

instance Normal II where
  normal _ = return

instance (Nominal a, Normal a) => Normal (System a) where
  normal ns (Triv u) = Triv <$> normal ns u
  normal ns (Sys us) = do
    us' <- T.sequence $
           Map.mapWithKey (\eqn u -> join (normal ns <$> u `subst` toSubst eqn)) us
    return $ Sys us'

instance (Normal a,Normal b) => Normal (a,b) where
  normal ns (u,v) = do
    u' <- normal ns u
    v' <- normal ns v
    return (u',v')

instance (Normal a,Normal b,Normal c) => Normal (a,b,c) where
  normal ns (u,v,w) = do
    u' <- normal ns u
    v' <- normal ns v
    w' <- normal ns w
    return (u',v',w')

instance (Normal a,Normal b,Normal c,Normal d) => Normal (a,b,c,d) where
  normal ns (u,v,w,x) = do
    u' <- normal ns u
    v' <- normal ns v
    w' <- normal ns w
    x' <- normal ns x
    return (u',v',w',x')

instance Normal a => Normal [a] where
  normal ns = mapM (normal ns)

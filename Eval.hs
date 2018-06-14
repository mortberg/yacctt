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

debug :: Bool
debug = False

traceb :: String -> a -> a
traceb s x = if debug then trace s x else x

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
    VLineP a          -> occurs x a
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

  subst u (i,r) | i `notOccurs` u = return u -- WARNING: this can be very bad!
                | otherwise = case u of
    VU                             -> return VU
    Ter t e                        -> Ter t <$> subst e (i,r)
    VPi a f                        -> VPi <$> subst a (i,r) <*> subst f (i,r)
    VPathP a u v                   -> VPathP <$> subst a (i,r) <*> subst u (i,r) <*> subst v (i,r)
    VLineP a                       -> VLineP <$> subst a (i,r)
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
    VBox s s' ts t     -> join $ box <$> subst s (i,r) <*> subst s' (i,r) <*> subst ts (i,r) <*> subst t (i,r)
    VCap s s' ts t     -> join $ cap <$> subst s (i,r) <*> subst s' (i,r) <*> subst ts (i,r) <*> subst t (i,r)

  -- This increases efficiency as it won't trigger computation.
  swap u ij =
    let sw :: Nominal a => a -> a
        sw u = swap u ij
    in case u of
         VU                -> VU
         Ter t e           -> Ter t (sw e)
         VPi a f           -> VPi (sw a) (sw f)
         VPathP a u v      -> VPathP (sw a) (sw u) (sw v)
         VLineP a          -> VLineP (sw a)
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
  LineP a               -> VLineP <$> eval rho a
  PLam i t              -> do
    j <- fresh
    VPLam j <$> eval (sub (i,Name j) rho) t
  AppII e phi           -> join $ (@@) <$> eval rho e <*> pure (evalII rho phi)
  HCom r s a us u0      ->
    join $ hcom (evalII rho r) (evalII rho s) <$> eval rho a <*> evalSystem rho us <*> eval rho u0
  Com r s a us u0      ->
    join $ com (evalII rho r) (evalII rho s) <$> eval rho a <*> evalSystem rho us <*> eval rho u0
  Coe r s a t           -> join $ coe (evalII rho r) (evalII rho s) <$> eval rho a <*> eval rho t
  -- Comp a t0 ts       -> compLine (eval rho a) (eval rho t0) (evalSystem rho ts)
  V r a b e             -> vtype (evalII rho r) <$> eval rho a <*> eval rho b <*> eval rho e
  Vin r m n             -> vin (evalII rho r) <$> eval rho m <*> eval rho n
  Vproj r o a b e       ->
    join $ vproj (evalII rho r) <$> eval rho o <*> eval rho a <*> eval rho b <*> eval rho e
  Box r s ts t          -> join $ box (evalII rho r) (evalII rho s) <$> evalSystem rho ts <*> eval rho t
  Cap r s ts t          -> join $ cap (evalII rho r) (evalII rho s) <$> evalSystem rho ts <*> eval rho t
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
                          join $ eval <$> rho `face` eqn <*> pure u) sys'
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
  (Ter (Split _ _ ty _) e,VHCom r s a ws w) ->
    traceb "split hcom" $ eval e ty >>= \x -> case x of
    VPi _ f -> do
      j <- fresh
      fill <- hcom r (Name j) a ws w
      ffill <- VPLam j <$> app f fill
      w' <- app u w
      ws' <- mapSystem (\alpha _ w -> do u' <- u `face` alpha
                                         app u' w) ws
      com r s ffill ws' w'
    _ -> error $ "app: Split annotation not a Pi type " ++ show u
  (Ter Split{} _,_) -- | isNeutral v
                    -> return (VSplit u v)
  (VCoe r s (VPLam i (VPi a b)) u0, v) -> traceb "coe pi" $ do
    j <- fresh
    let bij = b `swap` (i,j)
    w <- coe s (Name j) (VPLam i a) v
    w0 <- coe s r (VPLam i a) v
    bijw <- VPLam j <$> app bij w
    coe r s bijw =<< app u0 w0
  (VHCom r s (VPi a b) us u0, v) -> traceb "hcom pi" $ do
    us' <- mapSystem (\alpha _ u -> app u =<< (v `face` alpha)) us
    join $ hcom r s <$> app b v <*> pure us' <*> app u0 v
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
  VAppII t r -> inferType t >>= \t' -> case t' of
    VPathP a _ _ -> a @@ r
    VLineP a -> a @@ r
    ty         -> error $ "inferType: expected PathP/LineP type for " ++ show v
                  ++ ", got " ++ show ty
  VHCom r s a _ _ -> return a
  VCoe r s a _ -> a @@ s
  VVproj _ _ _ b _ -> return b
  VHComU _ _ _ _ -> return VU
  VCap _ _ _ t -> inferType t >>= \t' -> case t' of
    VHComU _ _ _ a -> return a
    ty         -> error $ "inferType: expected VHComU type for " ++ show v
                  ++ ", got " ++ show ty
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
com r s a us u0 = do
  us' <- mapSystem (\alpha j u -> a `face` alpha >>= \a' -> coe (Name j) s a' u) us
  join $ hcom r s <$> a @@ s <*> pure us' <*> coe r s a u0

-- apply f to each face, eta-expanding where needed, without freshening
mapSystemUnsafe :: (Eqn -> Val -> Eval Val) -> System Val -> Eval (System Val)
mapSystemUnsafe f us = do
  j <- fresh
  let etaMap e (VPLam i u) = VPLam i <$> f e u
      etaMap e u = do
        uj <- u @@ j
        VPLam j <$> f e uj
  case us of
    Sys us -> do bs <- T.sequence $ Map.mapWithKey etaMap us
                 return (Sys bs)
    Triv u -> Triv <$> etaMap (eqn (Name (N "_"),Name (N "_"))) u

-- apply f to each face, with binder, with freshening
mapSystem :: (Eqn -> Name -> Val -> Eval Val) -> System Val -> Eval (System Val)
mapSystem f us = do
  j <- fresh
  let etaMap e (VPLam i u) = VPLam j <$> f e j (u `swap` (i,j))
      etaMap e u = do
        uj <- u @@ j
        VPLam j <$> f e j uj
  case us of
    Sys us -> do bs <- T.sequence $ Map.mapWithKey etaMap us
                 return (Sys bs)
    Triv u -> Triv <$> etaMap (eqn (Name (N "_"),Name (N "_"))) u

mapSystemNoEta :: (Eqn -> Val -> Eval Val) -> System Val -> Eval (System Val)
mapSystemNoEta f (Sys us) = runSystem $ Sys $ Map.mapWithKey (\alpha u -> f alpha u) us
mapSystemNoEta f (Triv u) = runSystem $ Triv $ f (eqn (Name (N "_"),Name (N "_"))) u

hcom :: II -> II -> Val -> System Val -> Val -> Eval Val
hcom r s _ _ u0 | r == s = return u0
hcom r s _ (Triv u) _    = u @@ s
hcom r s a us u0   = case a of
  VPathP a v0 v1 -> traceb "hcom path" $ do
    j <- fresh
    us' <- insertsSystem [(j~>0,VPLam (N "_") v0),(j~>1,VPLam (N "_") v1)] <$>
             mapSystemUnsafe (const (@@ j)) us
    aj <- a @@ j
    u0j <- u0 @@ j
    VPLam j <$> hcom r s aj us' u0j
  VLineP a -> traceb "hcom line" $ do
    j <- fresh
    us' <- mapSystemUnsafe (const (@@ j)) us
    aj <- a @@ j
    u0j <- u0 @@ j
    VPLam j <$> hcom r s aj us' u0j
  VSigma a b -> traceb "hcom sigma" $ do
    j <- fresh
    us1 <- mapSystemUnsafe (const (return . fstVal)) us
    us2 <- mapSystemUnsafe (const (return . sndVal)) us
    let (u1,u2) = (fstVal u0,sndVal u0)
    u1fill <- hcom r (Name j) a us1 u1
    u1hcom <- hcom r s a us1 u1
    bj <- VPLam j <$> app b u1fill
    VPair u1hcom <$> com r s bj us2 u2
  VU -> hcomU r s us u0
  v@VV{} -> vvhcom v r s us u0
  v@VHComU{} -> hcomHComU v r s us u0
  Ter (Sum _ n nass) env
    | n `elem` ["nat","Z","bool"] -> return u0 -- hardcode hack
  -- Ter (Sum _ _ nass) env -- | VCon n vs <- u0, all isCon (elems us)
  --                        -> error "hcom sum"
  -- Ter (HSum _ _ _) _ -> error "hcom hsum" -- return $ VHCom r s a (Sys us) u0
  VPi{} -> return $ VHCom r s a us u0
  _ -> -- error "hcom: undefined case"
       return $ VHCom r s a us u0

-----------------------------------------------------------
-- Coe

coe :: II -> II -> Val -> Val -> Eval Val
coe r s a u | r == s = return u
coe r s (VPLam i a) u = case a of
  VPathP a v0 v1 -> traceb "coe path" $ do
    j <- fresh
    aij <- VPLam i <$> (a @@ j)
    out <- join $ com r s aij (mkSystem [(j~>0,VPLam i v0),(j~>1,VPLam i v1)]) <$> u @@ j
    return $ VPLam j out
  VLineP a  -> traceb "coe line" $ do
    j <- fresh
    aij <- VPLam i <$> (a @@ j)
    out <- join $ coe r s aij <$> u @@ j
    return $ VPLam j out
  VSigma a b -> traceb "coe sigma" $ do
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
    | otherwise -> error $ "coe sum: " ++ show n
  Ter (HSum _ n nass) env
    | n `elem` ["S1","S2","S3"] -> return u   -- hardcode hack
    | otherwise -> error "coe hsum"
  _ -> -- error "missing case in coe" --
       return $ VCoe r s (VPLam i a) u
coe r s a u = return $ VCoe r s a u

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

-- We are currently using RedPRL/UniMath style equiv between A and B:
-- f : A -> B
-- p : (x : B) -> isContr ((y : A) * Path B (f y) x)
-- with isContr C = (s : C) * ((z : C) -> Path C z s)

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
vin (Name i) m (VVproj j o _ _ _) | i == j = o -- TODO?
vin (Name i) m n   = VVin i m n

vproj :: II -> Val -> Val -> Val -> Val -> Eval Val
vproj (Dir Zero) o _ _ e = app (equivFun e) o
vproj (Dir One) o _ _ _  = return o
vproj (Name i) x@(VVin j m n) _ _ _
  | i == j = return n
  | otherwise = error $ "vproj: " ++ show i ++ " and " ++ show x
vproj (Name i) o a b e = return $ VVproj i o a b e


-- Coe for V-types
vvcoe :: Val -> II -> II -> Val -> Eval Val
vvcoe (VPLam i (VV j a b e)) r s m | i /= j = traceb "vvcoe i != j" $ do
  vj0 <- VApp (equivFun e) (VCoe r (Name i) (VPLam i a) m) `subst` (j,0)
  vj1 <- VCoe r (Name i) (VPLam i b) m `subst` (j,1)
  let tvec = mkSystem [(j~>0,VPLam i vj0),(j~>1,VPLam i vj1)]
  (ar,br,er) <- (a,b,e) `subst` (i,r)
  vr <- vproj (Name j) m ar br er
  vin (Name j) <$> coe r s (VPLam i a) m
               <*> com r s (VPLam i b) tvec vr
vvcoe (VPLam i (VV j a b e)) r s m | i == j = traceb "vvcoe i == j" $ do
  (ar,br,er) <- (a,b,e) `subst` (i,r)
  (as,bs,es) <- (a,b,e) `subst` (i,s)
  m' <- vproj r m ar br er
  n <- coe r s (VPLam i b) m'
  c <- app (equivContr es) n
  let fibty = VSigma as (VLam "a" as (VPathP (VPLam (N "_") bs) (VApp (VFst es) (VVar "a" as)) n))
  -- This is kinda bad, how to implement it properly?
  osys <- case r of
            Dir Zero -> Triv `liftM` app (sndVal c) (VPair m n)
            Dir One -> return eps
            _ -> do or0 <- (VApp (sndVal c) (VPair m n)) `face` (eqn (r,0))
                    return $ mkSystem [(r~>0,or0)]
  o <- hcom 1 0 fibty osys (fstVal c)
  -- TODO:  we probably need to take appropriate faces in the branches
  p <- hcom 1 0 bs (mkSystem [(s~>0,sndVal o),(s~>1,VPLam (N "_") n),(eqn (r,s),VPLam (N "_") m')]) n
  return $ vin s (fstVal o) p
vvcoe _ _ _ _ = error "vvcoe: case not implemented"

-- hcom for V-types
vvhcom :: Val -> II -> II -> System Val -> Val -> Eval Val
vvhcom (VV i a b e) r s us m = traceb "vvhcom" $ do
  j <- fresh
  -- i can occur in e and a
  ti0 <- VPLam j <$> (VApp (equivFun e) (VHCom r (Name j) a us m)) `subst` (i,0)
  ti1 <- VPLam j <$> (VHCom r (Name j) b us m) `subst` (i,1)
  let tvec = [(i~>0,ti0),(i~>1,ti1)]
  us' <- mapSystem (\alpha _ n -> (VVproj i n a b e) `face` alpha) us
  m' <- vproj (Name i) m a b e
  vin (Name i) <$> hcom r s a us m
               <*> hcom r s b (insertsSystem tvec us') m'
vvhcom _ _ _ _ _ = error "vvhcom: case not implemented"

-------------------------------------------------------------------------------
-- | Universe

-- TODO: eta for box/cap?

-- This doesn't have to be monadic
box :: II -> II -> System Val -> Val -> Eval Val
box r s _ m | r == s = return m
box _ s (Triv t) _   = return t
box r s ts m         = return $ VBox r s ts m

cap :: II -> II -> System Val -> Val -> Eval Val
cap r s _ m | r == s = return m
cap r s (Triv b) m   = coe s r b m
cap r s _ (VBox r' s' _ t) | r == r' && s == s' = return t -- TODO: error if false?
cap r s ts t = return $ VCap r s ts t

hcomU :: II -> II -> System Val -> Val -> Eval Val
hcomU r s _ u0 | r == s = return u0
hcomU r s (Triv u) _    = u @@ s
hcomU r s ts t          = return $ VHComU r s ts t


-- Helper function that only substitutes on faces of a system
substOnFaces :: Nominal a => System a -> (Name,II) -> Eval (System a)
substOnFaces (Sys xs) f =
    mkSystem <$> mapM (\(eqn,a) -> (,) <$> subst eqn f <*> pure a) (Map.assocs xs)
substOnFaces (Triv x) f = return $ Triv x

coeHComU :: Val -> II -> II -> Val -> Eval Val
coeHComU (VPLam i (VHComU si s'i (Sys bisi) ai)) r r' m = traceb "coe hcomU" $ do
  -- First decompose the system
  let -- The part of bis that doesn't mention i in its faces
      bs' = Sys $ Map.filterWithKey (\alpha _ -> i `notOccurs` alpha) bisi
      -- The part of bis that mentions i in its faces
      bsi = Map.filterWithKey (\alpha _ -> i `occurs` alpha) bisi

  -- Substitute for r and r' directly every *except* for the system
  -- (the reason is that we need to recover the B_i without the
  -- substitution!)
  (sr,s'r,ar) <- (si,s'i,ai) `subst` (i,r)
  (sr',s'r',ar') <- (si,s'i,ai) `subst` (i,r')

  -- Do the substitution, *only* on the faces, not on the types
  bsi <- Sys bsi `substOnFaces` (i,r')

  -- We can use this in otm as we never need the original B_i!
  bisr <- Sys bisi `subst` (i,r)
  -- Define O
  let otm z = do
            -- Here I do not use ntm like in Part 3. Instead I unfold it so
            -- that I can take appropriate faces and do some optimization.
            -- z' is the name bound in bi.
            osys <- mapSystem (\alpha z' bi -> do
                                  let m' = VCoe s'r (Name z') (VPLam z' bi) m
                                  (VCoe (Name z') sr (VPLam z' bi) m') `face` alpha) bisr
            ocap <- cap sr s'r bisr m
            hcom s'r z ar osys ocap

  -- Define P(r'/x)
  ptm <- do
    otmsr <- otm sr
    -- TODO: psys is quite sketchy!
    psys <- mapSystem (\alpha x bi -> do
                                let m' = VCoe r (Name x) (VPLam i (VAppII bi s'i)) m
                                (VCoe s'i si (VPLam (N "_") bi) m') `face` alpha) bs' -- NB: we only take (r'/x) on the faces!

    psys' <- if Name i `notElem` [si,s'i] && isConsistent (eqn (si,s'i))
                then do m' <- (VCoe r (Name i) (VPLam i ai) m) `face` (eqn (si,s'i))
                        return $ insertSystem (eqn (si,s'i),VPLam i m') psys
                else return psys
    com r r' (VPLam i ai) psys' otmsr

  -- Define Q_k. Take the face alpha (s_i = s'_i), free variable w
  -- (called z) and bk without (r'/x)
  let qtm alpha w bk = do
        (bk,m,bs') <- (bk,m,bs') `face` alpha

        qsys <- mapSystem (\alpha' z' bi -> do
                              (bia,s'r'a,ra,r'a,ma) <- (bi,s'r',r,r',m) `face` alpha'
                              bia' <- bia `subst` (z',s'r'a)
                              ma' <- coe ra r'a (VPLam i bia') ma
                              bia <- bia `subst` (i,r'a)
                              coe s'r'a (Name z') (VPLam z' bia) ma') bs' -- NB: we only take (r'/x) of the faces!
        bk' <- bk `subst` (i,r')
        qsys' <- if isConsistent (eqn (r,r'))
                    then do (srr',bk'r,mr) <- (s'r',bk',m) `face` (eqn (r,r'))
                            l <- fresh
                            m' <- coe srr' (Name l) (VPLam l bk'r) mr
                            return $ insertSystem (eqn (r,r'),VPLam l m') qsys
                    else return qsys

        com sr' w bk' qsys' ptm

  -- The part of outtmsys where the faces of the system depend on i
  -- (i.e. where we have to use qtm as the system doesn't simplify).
  tveci <- mapSystem (\alpha z bi -> do
                         (bia,sr'a,r'a) <- (bi,sr',r') `face` alpha
                         bra <- bia `subst` (i,r'a)
                         coe (Name z) sr'a (VPLam z bra) =<< qtm alpha (Name z) (VPLam z bia)) bsi
    
  -- The part of outtmsys where the faces of the system doesn't depend on i
  -- (i.e. where qtm simplifies).
  tvec' <- mapSystem (\alpha z bi -> do
                         (bia,sr'a,s'r'a,ra,r'a,ma) <- (bi,sr',s'r',r,r',m) `face` alpha
                         bia' <- bia `subst` (z,s'r'a)
                         biar' <- bia `subst` (i,r'a)
                         ma' <- coe ra r'a (VPLam i bia') ma
                         ma'' <- coe s'r'a (Name z) (VPLam z biar') ma'
                         coe (Name z) sr'a (VPLam z biar') ma'') bs'
  let outtmsys = mergeSystem tveci tvec'

  tvec <- if isConsistent (eqn (r,r'))
             then do k <- fresh
                     otmk <- otm (Name k)
                     -- TODO: can we take the eqn into account like this:
                     otmk' <- otmk `face` (eqn (r,r'))
                     return $ insertSystem (eqn (r,r'),VPLam k otmk') outtmsys
            else return outtmsys
  outtm <- hcom sr' s'r' ar' tvec ptm

  -- Like above we only use qtm when i does not occur in the faces
  uveci <- mapSystemNoEta (\alpha bi -> qtm alpha s'r' bi) bsi
  -- And in the case when i does occur in the face we do the simplification
  uvec' <- mapSystemNoEta (\alpha bi -> (VCoe r r' (VPLam i (VAppII bi s'r')) m) `face` alpha) bs'
  let uvec = mergeSystem uveci uvec'

  box sr' s'r' uvec outtm
coeHComU _ _ _ _ = error "coeHComU: case not implemented"

hcomHComU :: Val -> II -> II -> System Val -> Val -> Eval Val
hcomHComU (VHComU s s' bs a) r r' ns m = traceb "hcom hcomU" $ do
  -- Define P and parametrize by z
  let ptm bi z = do
        -- TODO: take alpha into account
        psys <- mapSystem (\alpha _ ni -> coe s' (Name z) (VPLam z bi) ni) ns
        pcap <- coe s' (Name z) (VPLam z bi) m
        hcom r r' bi psys pcap

  -- Define F[c] and parametrize by z
  let ftm c z = do
        fsys <- mapSystem (\alpha z' bi -> do
                              let c' = VCoe s' (Name z') (VPLam z' bi) c
                              (VCoe (Name z') s (VPLam z' bi) c') `face` alpha) bs
        fcap <- cap s s' bs c
        hcom s' z a fsys fcap

  -- Define O
  otm <- do
    -- TODO: take alpha into account
    osys <- mapSystem (\alpha _ ni -> ftm ni s) ns
    ocap <- ftm m s
    hcom r r' a osys ocap

  -- Define Q
  qtm <- do
    -- TODO: take alpha into account?
    qsys1 <- mapSystem (\alpha z ni -> do ni' <- ni `subst` (z,r')
                                          ftm ni' (Name z)) ns
    qsys2 <- mapSystem (\alpha z bi -> do p' <- ptm bi z
                                          coe (Name z) s (VPLam z bi) p') bs
    k <- fresh
    m' <- ftm m (Name k)
    -- TODO: take r=r' into account in m'
    let qsys = insertSystem (eqn (r,r'),VPLam k m') $ mergeSystem qsys1 qsys2
    hcom s s' a qsys otm

  -- inline P and optimize
  outsys <- mapSystemNoEta (\alpha bj -> (VHCom r r' bj ns m) `face` alpha) bs
  box s s' outsys qtm
hcomHComU _ _ _ _ _ = error "hcomHComU: case not implemented"

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
    usa <- us Map.! a `face` a
    ba <- b `face` a
    usa `face` ba
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
      (VLineP a,VLineP a')                            -> conv ns a a'
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
    let compare eqn u u' = join $ conv ns <$> u `face` eqn <*> u' `face` eqn
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
    VLineP a               -> VLineP <$> normal ns a
    VPLam i u              -> VPLam i <$> normal ns u
    VCoe r s a u           -> VCoe <$> normal ns r <*> normal ns s <*> normal ns a <*> normal ns u
    VHCom r s u vs v       -> VHCom <$> normal ns r <*> normal ns s <*> normal ns u <*> normal ns vs <*> normal ns v
    VV i a b e             -> VV i <$> normal ns a <*> normal ns b <*> normal ns e
    VVin i m n             -> VVin i <$> normal ns m <*> normal ns n
    VVproj i o a b e       -> VVproj i <$> normal ns o <*> normal ns a <*> normal ns b <*> normal ns e
    VHComU r s ts t        -> VHComU <$> normal ns r <*> normal ns s <*> normal ns ts <*> normal ns t
    VCap r s ts t          -> VCap <$> normal ns r <*> normal ns s <*> normal ns ts <*> normal ns t
    VBox r s ts t          -> VBox <$> normal ns r <*> normal ns s <*> normal ns ts <*> normal ns t
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
           Map.mapWithKey (\eqn u -> join (normal ns <$> u `face` eqn)) us
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

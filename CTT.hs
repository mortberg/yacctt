{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
module CTT where

import Control.Applicative
import Data.List
import Data.Maybe
import qualified Data.Map as Map
import Text.PrettyPrint as PP
import qualified Data.Set as Set

import Cartesian

--------------------------------------------------------------------------------
-- | Terms

data Loc = Loc { locFile :: String
               , locPos  :: (Int,Int) }
  deriving Eq

type Ident  = String
type LIdent = String

-- Telescope (x1 : A1) .. (xn : An)
type Tele   = [(Ident,Ter)]

data Label = OLabel LIdent Tele -- Object label
           | PLabel LIdent Tele [Name] (System Ter) -- Path label
  deriving (Eq,Show)

-- OBranch of the form: c x1 .. xn -> e
-- PBranch of the form: c x1 .. xn i1 .. im -> e
data Branch = OBranch LIdent [Ident] Ter
            | PBranch LIdent [Ident] [Name] Ter
  deriving (Eq,Show)

-- Declarations: x : A = e
-- A group of mutual declarations is identified by its location. It is used to
-- speed up the Eq instance for Ctxt.
type Decl  = (Ident,(Ter,Ter))
data Decls = MutualDecls Loc [Decl]
           | OpaqueDecl Ident
           | TransparentDecl Ident
           | TransparentAllDecl
           deriving Eq

declIdents :: [Decl] -> [Ident]
declIdents decls = [ x | (x,_) <- decls ]

declTers :: [Decl] -> [Ter]
declTers decls = [ d | (_,(_,d)) <- decls ]

declTele :: [Decl] -> Tele
declTele decls = [ (x,t) | (x,(t,_)) <- decls ]

declDefs :: [Decl] -> [(Ident,Ter)]
declDefs decls = [ (x,d) | (x,(_,d)) <- decls ]

labelTele :: Label -> (LIdent,Tele)
labelTele (OLabel c ts) = (c,ts)
labelTele (PLabel c ts _ _) = (c,ts)

labelName :: Label -> LIdent
labelName = fst . labelTele

labelTeles :: [Label] -> [(LIdent,Tele)]
labelTeles = map labelTele

lookupLabel :: LIdent -> [Label] -> Maybe Tele
lookupLabel x xs = lookup x (labelTeles xs)

lookupPLabel :: LIdent -> [Label] -> Maybe (Tele,[Name],System Ter)
lookupPLabel x xs = listToMaybe [ (ts,is,es) | PLabel y ts is es <- xs, x == y ]

branchName :: Branch -> LIdent
branchName (OBranch c _ _) = c
branchName (PBranch c _ _ _) = c

lookupBranch :: LIdent -> [Branch] -> Maybe Branch
lookupBranch _ []      = Nothing
lookupBranch x (b:brs) = case b of
  OBranch c _ _   | x == c    -> Just b
                  | otherwise -> lookupBranch x brs
  PBranch c _ _ _ | x == c    -> Just b
                  | otherwise -> lookupBranch x brs

-- Terms
data Ter = Pi Ter
         | App Ter Ter
         | Lam Ident Ter Ter
         | Where Ter Decls
         | Var Ident
         | U
           -- Sigma types:
         | Sigma Ter
         | Pair Ter Ter
         | Fst Ter
         | Snd Ter
           -- constructor c Ms
         | Con LIdent [Ter]
         | PCon LIdent Ter [Ter] [II] -- c A ts phis (A is the data type)
           -- branches c1 xs1  -> M1,..., cn xsn -> Mn
         | Split Ident Loc Ter [Branch]
           -- labelled sum c1 A1s,..., cn Ans (assumes terms are constructors)
         | Sum Loc Ident [Label] -- TODO: should only contain OLabels
         | HSum Loc Ident [Label]
           -- undefined and holes
         | Undef Loc Ter -- Location and type
         | Hole Loc
           -- Path types
         | PathP Ter Ter Ter
         | PLam Name Ter
         | AppII Ter II
           -- Coe
         | Coe II II Ter Ter
           -- Homogeneous Kan composition
         | HCom II II Ter (System Ter) Ter
           -- Kan composition
         -- | Com II II Ter (System Ter) Ter

           -- V-types
         | V II Ter Ter Ter -- V r A B E    (where E : A ~= B)
         | Vin II Ter Ter -- Vin r M N      (where M : A and N : B)
         | Vproj II Ter Ter Ter Ter -- Vproj r O A B E    (where O : V r A B E)

           -- Universes
         | Box II II (System Ter) Ter
         | Cap II II (System Ter) Ter

           -- Glue
         -- | Glue Ter (System Ter)
         -- | GlueElem Ter (System Ter)
         -- | UnGlueElem Ter Ter (System Ter)
  deriving Eq

-- For an expression t, returns (u,ts) where u is no application and t = u ts
unApps :: Ter -> (Ter,[Ter])
unApps = aux []
  where aux :: [Ter] -> Ter -> (Ter,[Ter])
        aux acc (App r s) = aux (s:acc) r
        aux acc t         = (t,acc)

mkApps :: Ter -> [Ter] -> Ter
mkApps (Con l us) vs = Con l (us ++ vs)
mkApps t ts          = foldl App t ts

mkWheres :: [Decls] -> Ter -> Ter
mkWheres []     e = e
mkWheres (d:ds) e = Where (mkWheres ds e) d

--------------------------------------------------------------------------------
-- | Values

data Val = VU
         | Ter Ter Env
         | VPi Val Val
         | VSigma Val Val
         | VPair Val Val
         | VCon LIdent [Val]
         | VPCon LIdent Val [Val] [II]

           -- Path values
         | VPathP Val Val Val
         | VPLam Name Val

           -- Homogeneous composition; the type is constant
         | VHCom II II Val (System Val) Val

           -- Coe
         | VCoe II II Val Val

           -- V-types values
         | VV Name Val Val Val -- V i A B E    (where E : A ~= B)
         | VVin Name Val Val -- Vin i M N      (where M : A and N : B)
         | VVproj Name Val Val Val Val -- Vproj i O A B E    (where O : V i A B E)

           -- Glue values
         -- | VGlue Val (System Val)
         -- | VGlueElem Val (System Val)
         -- | VUnGlueElem Val Val (System Val)  -- unglue u A [phi -> (T,w)]

         -- Universe values
         | VHComU II II (System Val) Val -- r s bs a
         | VBox II II (System Val) Val -- r s ns m
         | VCap II II (System Val) Val -- r s bs m

           -- Neutral values:
         | VVar Ident Val
         | VOpaque Ident Val
         | VFst Val
         | VSnd Val
         | VSplit Val Val
         | VApp Val Val
         | VAppII Val II
         | VLam Ident Val Val
         -- | VUnGlueElemU Val Val (System Val)
  deriving Eq

isNeutral :: Val -> Bool
isNeutral v = case v of
  Ter Undef{} _     -> True
  Ter Hole{} _      -> True
  VVar{}            -> True
  VOpaque{}         -> True
  VHCom{}           -> True
  VCoe{}            -> True
  VFst{}            -> True
  VSnd{}            -> True
  VSplit{}          -> True
  VApp{}            -> True
  VAppII{}          -> True
  -- VUnGlueElemU{} -> True
  -- VUnGlueElem{}  -> True
  VCap{}            -> True
  VVproj{}          -> True
  _                 -> False

isNeutralSystem :: System Val -> Bool
isNeutralSystem (Sys xs) = any isNeutral (Map.elems xs)
isNeutralSystem (Triv a) = isNeutral a

-- isNeutralPath :: Val -> Bool
-- isNeutralPath (VPath _ v) = isNeutral v
-- isNeutralPath _ = True

mkVar :: Int -> String -> Val -> Val
mkVar k x = VVar (x ++ show k)

mkVarNice :: [String] -> String -> Val -> Val
mkVarNice xs x = VVar (head (ys \\ xs))
  where ys = x:map (\n -> x ++ show n) [0..]

unCon :: Val -> [Val]
unCon (VCon _ vs) = vs
unCon v           = error $ "unCon: not a constructor: " ++ show v

isCon :: Val -> Bool
isCon VCon{} = True
isCon _      = False

-- Constant path: <_> v
constPath :: Val -> Val
constPath = VPLam (N "_")


--------------------------------------------------------------------------------
-- | Environments

data Ctxt = Empty
          | Upd Ident Ctxt
          | Sub Name Ctxt
          | Def Loc [Decl] Ctxt
  deriving (Show)

instance Eq Ctxt where
    c == d = case (c, d) of
        (Empty, Empty)              -> True
        (Upd x c', Upd y d')        -> x == y && c' == d'
        (Sub i c', Sub j d')        -> i == j && c' == d'
        (Def m xs c', Def n ys d')  -> (m == n || xs == ys) && c' == d'
            -- Invariant: if two declaration groups come from the same
            -- location, they are equal and their contents are not compared.
        _                           -> False

-- The Idents and Names in the Ctxt refer to the elements in the two
-- lists. This is more efficient because acting on an environment now
-- only need to affect the lists and not the whole context.
-- The last list is the list of opaque names
newtype Env = Env (Ctxt,[Val],[II],Nameless (Set.Set Ident))
  deriving (Eq)

emptyEnv :: Env
emptyEnv = Env (Empty,[],[],Nameless Set.empty)

def :: Decls -> Env -> Env
def (MutualDecls m ds) (Env (rho,vs,fs,Nameless os)) =
  Env (Def m ds rho,vs,fs,Nameless (os Set.\\ Set.fromList (declIdents ds)))
def (OpaqueDecl n) (Env (rho,vs,fs,Nameless os)) = Env (rho,vs,fs,Nameless (Set.insert n os))
def (TransparentDecl n) (Env (rho,vs,fs,Nameless os)) = Env (rho,vs,fs,Nameless (Set.delete n os))
def TransparentAllDecl (Env (rho,vs,fs,Nameless os)) = Env (rho,vs,fs,Nameless Set.empty)

defWhere :: Decls -> Env -> Env
defWhere (MutualDecls m ds) (Env (rho,vs,fs,Nameless os)) =
  Env (Def m ds rho,vs,fs,Nameless (os Set.\\ Set.fromList (declIdents ds)))
defWhere (OpaqueDecl _) rho = rho
defWhere (TransparentDecl _) rho = rho
defWhere TransparentAllDecl rho = rho

sub :: (Name,II) -> Env -> Env
sub (i,phi) (Env (rho,vs,fs,os)) = Env (Sub i rho,vs,phi:fs,os)

upd :: (Ident,Val) -> Env -> Env
upd (x,v) (Env (rho,vs,fs,Nameless os)) = Env (Upd x rho,v:vs,fs,Nameless (Set.delete x os))

upds :: [(Ident,Val)] -> Env -> Env
upds xus rho = foldl (flip upd) rho xus

updsTele :: Tele -> [Val] -> Env -> Env
updsTele tele vs = upds (zip (map fst tele) vs)

subs :: [(Name,II)] -> Env -> Env
subs iphis rho = foldl (flip sub) rho iphis

mapEnv :: (Val -> Val) -> (II -> II) -> Env -> Env
mapEnv f g (Env (rho,vs,fs,os)) = Env (rho,map f vs,map g fs,os)

valAndIIOfEnv :: Env -> ([Val],[II])
valAndIIOfEnv (Env (_,vs,fs,_)) = (vs,fs)

valOfEnv :: Env -> [Val]
valOfEnv = fst . valAndIIOfEnv

formulaOfEnv :: Env -> [II]
formulaOfEnv = snd . valAndIIOfEnv

domainEnv :: Env -> [Name]
domainEnv (Env (rho,_,_,_)) = domCtxt rho
  where domCtxt rho = case rho of
          Empty      -> []
          Upd _ e    -> domCtxt e
          Def _ ts e -> domCtxt e
          Sub i e    -> i : domCtxt e

-- Extract the context from the environment, used when printing holes
contextOfEnv :: Env -> [String]
contextOfEnv rho = case rho of
  Env (Empty,_,_,_)               -> []
  Env (Upd x e,VVar n t:vs,fs,os) -> (n ++ " : " ++ show t) : contextOfEnv (Env (e,vs,fs,os))
  Env (Upd x e,v:vs,fs,os)        -> (x ++ " = " ++ show v) : contextOfEnv (Env (e,vs,fs,os))
  Env (Def _ _ e,vs,fs,os)        -> contextOfEnv (Env (e,vs,fs,os))
  Env (Sub i e,vs,phi:fs,os)      -> (show i ++ " = " ++ show phi) : contextOfEnv (Env (e,vs,fs,os))

--------------------------------------------------------------------------------
-- | Pretty printing

instance Show Env where
  show = render . showEnv True

showEnv :: Bool -> Env -> Doc
showEnv b e =
  let -- This decides if we should print "x = " or not
      names x = if b then text x <+> equals else PP.empty
      par   x = if b then parens x else x
      com     = if b then comma else PP.empty
      showEnv1 e = case e of
        Env (Upd x env,u:us,fs,os)   ->
          showEnv1 (Env (env,us,fs,os)) <+> names x <+> showVal1 u <> com
        Env (Sub i env,us,phi:fs,os) ->
          showEnv1 (Env (env,us,fs,os)) <+> names (show i) <+> text (show phi) <> com
        Env (Def _ _ env,vs,fs,os)   -> showEnv1 (Env (env,vs,fs,os))
        _                            -> showEnv b e
  in case e of
    Env (Empty,_,_,_)            -> PP.empty
    Env (Def _ _ env,vs,fs,os)   -> showEnv b (Env (env,vs,fs,os))
    Env (Upd x env,u:us,fs,os)   ->
      par $ showEnv1 (Env (env,us,fs,os)) <+> names x <+> showVal1 u
    Env (Sub i env,us,phi:fs,os) ->
      par $ showEnv1 (Env (env,us,fs,os)) <+> names (show i) <+> text (show phi)

instance Show Loc where
  show = render . showLoc

showLoc :: Loc -> Doc
showLoc (Loc name (i,j)) = text (show (i,j) ++ " in " ++ name)

showII :: II -> Doc
showII = text . show

instance Show Ter where
  show = render . showTer

showTer :: Ter -> Doc
showTer v = case v of
  U                    -> char 'U'
  App e0 e1            -> showTer e0 <+> showTer1 e1
  Pi e0                -> text "Pi" <+> showTer e0
  Lam x t e            ->
    char '\\' <> parens (text x <+> colon <+> showTer t) <+> text " ->" <+> showTer e
  Fst e                -> showTer1 e <> text ".1"
  Snd e                -> showTer1 e <> text ".2"
  Sigma e0             -> text "Sigma" <+> showTer1 e0
  Pair e0 e1           -> parens (showTer e0 <> comma <> showTer e1)
  Where e d            -> showTer e <+> text "where" <+> showDecls d
  Var x                -> text x
  Con c es             -> text c <+> showTers es
  PCon c a es phis     ->
    text c <+> braces (showTer a) <+> showTers es <+> hsep (map ((char '@' <+>) . showII) phis)
  Split f _ _ _        -> text f
  Sum _ n _            -> text n
  HSum _ n _           -> text n
  Undef{}              -> text "undefined"
  Hole{}               -> text "?"
  PathP e0 e1 e2       -> text "PathP" <+> showTers [e0,e1,e2]
  PLam i e             -> char '<' <> text (show i) <> char '>' <+> showTer e
  AppII e phi          -> showTer1 e <+> char '@' <+> showII phi
  HCom r s a ts t      ->
    text "hcom" <+> showII r <> text "->" <> showII s <+> showTer1 a <+> text (show ts) <+> showTer1 t
  Coe r s e t0         ->
    text "coe" <+> showII r <> text "->" <> showII s <+> showTer1 e <+> showTer1 t0
  -- Comp e t ts       -> text "comp" <+> showTers [e,t] <+> text (show ts)
  V r a b e            -> text "V" <+> showII r <+> showTers [a,b,e]
  Vin r m n            -> text "Vin" <+> showII r <+> showTers [m,n]
  Vproj r o a b e      -> text "Vproj" <+> showII r <+> showTers [o,a,b,e]
  Box r s ts t ->
    text "box" <+> showII r <> text "->" <> showII s <+> text (show ts) <+> showTer1 t
  Cap r s ts t ->
    text "cap" <+> showII r <> text "<-" <> showII s <+> text (show ts) <+> showTer1 t
  -- Glue a ts         -> text "Glue" <+> showTer1 a <+> text (show ts)
  -- GlueElem a ts     -> text "glue" <+> showTer1 a <+> text (show ts)
  -- UnGlueElem a b ts -> text "unglue" <+> showTers [a,b] <+> text (show ts)

showTers :: [Ter] -> Doc
showTers = hsep . map showTer1

showTer1 :: Ter -> Doc
showTer1 t = case t of
  U        -> char 'U'
  Con c [] -> text c
  Var{}    -> showTer t
  Undef{}  -> showTer t
  Hole{}   -> showTer t
  Split{}  -> showTer t
  Sum{}    -> showTer t
  HSum{}   -> showTer t
  Fst{}    -> showTer t
  Snd{}    -> showTer t
  _        -> parens (showTer t)

showDecls :: Decls -> Doc
showDecls (MutualDecls _ defs) =
  hsep $ punctuate comma
  [ text x <+> equals <+> showTer d | (x,(_,d)) <- defs ]
showDecls (OpaqueDecl i) = text "opaque" <+> text i
showDecls (TransparentDecl i) = text "transparent" <+> text i
showDecls TransparentAllDecl = text "transparent_all"

instance Show Val where
  show = render . showVal

showVal :: Val -> Doc
showVal v = case v of
  VU                     -> char 'U'
  Ter t@Sum{} rho        -> showTer t <+> showEnv False rho
  Ter t@HSum{} rho       -> showTer t <+> showEnv False rho
  Ter t@Split{} rho      -> showTer t <+> showEnv False rho
  Ter t rho              -> showTer1 t <+> showEnv True rho
  VCon c us              -> text c <+> showVals us
  VPCon c a us phis      -> text c <+> braces (showVal a) <+> showVals us <+> hsep (map ((char '@' <+>) . showII) phis)
  VHCom r s v0 vs v1     -> text "hcom" <+> showII r <> text "->" <> showII s <+> showVal1 v0 <+> text (show vs) <+> showVal1 v1
  VCoe r s u v0          -> text "coe" <+> showII r <> text "->" <> showII s <+> showVal1 u <+> showVal1 v0
  VPi a l@(VLam x t b)
    | "_" `isPrefixOf` x -> showVal1 a <+> text "->" <+> showVal1 b
    | otherwise          -> char '(' <> showLam v
  VPi a b                -> text "Pi" <+> showVals [a,b]
  VPair u v              -> parens (showVal u <> comma <> showVal v)
  VSigma u v             -> text "Sigma" <+> showVals [u,v]
  VApp u v               -> showVal u <+> showVal1 v
  VLam{}                 -> text "\\(" <> showLam v
  VPLam{}                -> char '<' <> showPLam v
  VSplit u v             -> showVal u <+> showVal1 v
  VVar x _               -> text x
  VOpaque x _            -> text ('#':x)
  VFst u                 -> showVal1 u <> text ".1"
  VSnd u                 -> showVal1 u <> text ".2"
  VPathP v0 v1 v2        -> text "PathP" <+> showVals [v0,v1,v2]
  VAppII v phi           -> showVal v <+> char '@' <+> showII phi
  VV i a b e             -> text "V" <+> text (show i) <+> showVals [a,b,e]
  VVin i m n             -> text "Vin" <+> text (show i) <+> showVals [m,n]
  VVproj i o a b e       -> text "Vproj" <+> text (show i) <+> showVals [o,a,b,e]
  VBox r s ts t          ->
    text "box" <+> showII r <> text "->" <> showII s <+> text (show ts) <+> showVal1 t
  VCap r s ts t          ->
    text "cap" <+> showII r <> text "<-" <> showII s <+> text (show ts) <+> showVal1 t
  VHComU r s ts t       ->
    text "hcomp U" <+> showII r <> text "->" <> showII s <+> text (show ts) <+> showVal1 t
  -- VGlue a ts          -> text "Glue" <+> showVal1 a <+> text (show ts)
  -- VGlueElem a ts      -> text "glue" <+> showVal1 a <+> text (show ts)
  -- VUnGlueElem v a ts  -> text "unglue" <+> showVals [v,a] <+> text (show ts)
  -- VUnGlueElemU v b es -> text "unglue U" <+> showVals [v,b] <+> text (show es)

showPLam :: Val -> Doc
showPLam e = case e of
  VPLam i a@VPLam{} -> text (show i) <+> showPLam a
  VPLam i a         -> text (show i) <> char '>' <+> showVal a
  _                 -> showVal e

-- Merge lambdas of the same type
showLam :: Val -> Doc
showLam e = case e of
  VLam x t a@(VLam _ t' _)
    | t == t'   -> text x <+> showLam a
    | otherwise ->
      text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal a
  VPi _ (VLam x t a@(VPi _ (VLam _ t' _)))
    | t == t'   -> text x <+> showLam a
    | otherwise ->
      text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal a
  VLam x t e         ->
    text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal e
  VPi _ (VLam x t e) ->
    text x <+> colon <+> showVal t <> char ')' <+> text "->" <+> showVal e
  _ -> showVal e

showVal1 :: Val -> Doc
showVal1 v = case v of
  VU                -> showVal v
  VCon c []         -> showVal v
  VVar{}            -> showVal v
  VFst{}            -> showVal v
  VSnd{}            -> showVal v
  Ter t rho | isEmpty (showEnv False rho) -> showTer1 t
  _                 -> parens (showVal v)

showVals :: [Val] -> Doc
showVals = hsep . map showVal1

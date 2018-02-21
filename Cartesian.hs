-- Random stuff that we need for Cartesian cubicaltt
{-# LANGUAGE TypeSynonymInstances, FlexibleInstances,
             GeneralizedNewtypeDeriving, TupleSections #-}
module Cartesian where

import Control.Applicative
import Data.List
import Data.Map (Map,(!),keys,fromList,toList,mapKeys,elems,intersectionWith
                ,unionWith,singleton,foldrWithKey,assocs,mapWithKey
                ,filterWithKey,member,notMember)
import Data.Set (Set,isProperSubsetOf)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Maybe
import Data.IORef
import System.IO.Unsafe

data Name = N String
          | Gen {-# UNPACK #-} !Int
  deriving (Eq,Ord)

instance Show Name where
  show (N i) = i
  show (Gen x)  = 'i' : show x

swapName :: Name -> (Name,Name) -> Name
swapName k (i,j) | k == i    = j
                 | k == j    = i
                 | otherwise = k

-- | Directions

-- Maybe merge with II?
data Dir = Zero | One
  deriving (Eq,Ord)

instance Show Dir where
  show Zero = "0"
  show One  = "1"

instance Num Dir where
  Zero + Zero = Zero
  _    + _    = One

  Zero * _ = Zero
  One  * x = x

  abs      = id
  signum _ = One

  negate Zero = One
  negate One  = Zero

  fromInteger 0 = Zero
  fromInteger 1 = One
  fromInteger _ = error "fromInteger Dir"

-- | Interval

data II = Dir Dir
        | Name Name
  deriving Eq

instance Show II where
  show d = show d
  -- show (Dir Zero)  = "0"
  -- show (Dir One)   = "1"
  -- show (Name a)    = show a

class ToII a where
  toII :: a -> II

instance ToII II where
  toII = id

instance ToII Name where
  toII = Name

instance ToII Dir where
  toII = Dir

-- Probably not needed?
merge :: Set (Set (Name,Dir)) -> Set (Set (Name,Dir)) -> Set (Set (Name,Dir))
merge a b =
  let as = Set.toList a
      bs = Set.toList b
  in Set.fromList [ ai | ai <- as, not (any (`isProperSubsetOf` ai) bs) ] `Set.union`
     Set.fromList [ bi | bi <- bs, not (any (`isProperSubsetOf` bi) as) ]

-- find a better name?
-- phi b = max {alpha : Face | phi alpha = b}
-- invII :: II -> Dir -> [Face]
-- invII (Dir b') b       = [ eps | b == b' ]
-- invII (N i) b          = [ singleton i b ]

-- propInvIIIncomp :: II -> Dir -> Bool
-- propInvIIIncomp phi b = incomparables (invII phi b)

-- | Face

type Face = (Name,II)

showFace :: Face -> String
showFace (i,j) = "(" ++ show i ++ " = " ++ show j ++ ")"

-- swapFace :: Face -> (Name,Name) -> Face
-- swapFace alpha ij = map (`swapName` ij) alpha

-- Check if two faces are compatible
compatible :: Face -> Face -> Bool
compatible (i,Dir d) (j,Dir d') | i == j = d == d'
compatible _ _ = True

-- compatibles :: [Face] -> Bool
-- compatibles []     = True
-- compatibles (x:xs) = all (x `compatible`) xs && compatibles xs

allCompatible :: [Face] -> [(Face,Face)]
allCompatible []     = []
allCompatible (f:fs) = map (f,) (filter (compatible f) fs) ++ allCompatible fs

-- Partial composition operation
-- meet :: Face -> Face -> Face
-- meet = unionWith f
--   where f d1 d2 = if d1 == d2 then d1 else error "meet: incompatible faces"

-- meetMaybe :: Face -> Face -> Maybe Face
-- meetMaybe x y = if compatible x y then Just $ meet x y else Nothing

-- meets :: [Face] -> [Face] -> [Face]
-- meets xs ys = nub [ meet x y | x <- xs, y <- ys, compatible x y ]

-- meetss :: [[Face]] -> [Face]
-- meetss = foldr meets [eps]

-- leq :: Face -> Face -> Bool
-- alpha `leq` beta = meetMaybe alpha beta == Just alpha

-- comparable :: Face -> Face -> Bool
-- comparable alpha beta = alpha `leq` beta || beta `leq` alpha

-- incomparables :: [Face] -> Bool
-- incomparables []     = True
-- incomparables (x:xs) = all (not . (x `comparable`)) xs && incomparables xs

(~>) :: Name -> Dir -> Face -- TODO: Name -> II -> Face ????
i ~> d = (i,Dir d)

-- eps :: Face
-- eps = Map.empty

-- minus :: Face -> Face -> Face
-- minus alpha beta = alpha Map.\\ beta



-- | Nominal

-- gensym :: [Name] -> Name
-- gensym xs = head (ys \\ xs)
--   where ys = map Name $ ["i","j","k","l"] ++ map (('i':) . show) [0..]

-- gensymNice :: Name -> [Name] -> Name
-- gensymNice i@(Name s) xs = head (ys \\ xs)
--   where ys = i:map (\n -> Name (s ++ show n)) [0..]

{-# NOINLINE freshVar #-}
freshVar :: IORef Int
freshVar = unsafePerformIO (newIORef 0)

gensym :: [a] -> Name
gensym _ = unsafePerformIO $ do
  x <- readIORef freshVar
  modifyIORef freshVar succ
  return (Gen x)

-- gensym :: [Name] -> Name
-- gensym xs = Name ('!' : show max)
--   where max = maximum' [ read x | Name ('!':x) <- xs ]
--         maximum' [] = 0
--         maximum' xs = maximum xs + 1

gensyms :: [Name] -> [Name]
gensyms d = let x = gensym d in x : gensyms (x : d)

class Nominal a where
--  support :: a -> [Name]
  occurs :: Name -> a -> Bool
--  occurs x v = x `elem` support v
  subst   :: a -> Face -> a
  swap    :: a -> (Name,Name) -> a


fresh :: Nominal a => a -> Name
fresh _ = gensym [] -- . support

-- freshNice :: Nominal a => Name -> a -> Name
-- freshNice i = gensymNice i . support

freshs :: Nominal a => a -> [Name]
freshs _ = gensyms [] -- . support

-- unions :: [[a]] -> [a]
-- unions = concat -- foldr union []

-- unionsMap :: (a -> [b]) -> [a] -> [b]
-- unionsMap = concatMap -- unions . map f

newtype Nameless a = Nameless { unNameless :: a }
  deriving (Eq, Ord)

instance Nominal (Nameless a) where
--  support _ = []
  occurs _ _ = False
  subst x _   = x
  swap x _  = x

instance Nominal () where
--  support () = []
  occurs _ _ = False
  subst () _   = ()
  swap () _  = ()

instance (Nominal a, Nominal b) => Nominal (a, b) where
--  support (a, b) = support a `union` support b
  occurs x (a,b) = occurs x a || occurs x b
  subst (a,b) f  = (subst a f,subst b f)
  swap (a,b) n   = (swap a n,swap b n)

instance (Nominal a, Nominal b, Nominal c) => Nominal (a, b, c) where
--  support (a,b,c) = unions [support a, support b, support c]
  occurs x (a,b,c) = or [occurs x a,occurs x b,occurs x c]
  subst (a,b,c) f = (subst a f,subst b f,subst c f)
  swap (a,b,c) n  = (swap a n,swap b n,swap c n)

instance (Nominal a, Nominal b, Nominal c, Nominal d) =>
         Nominal (a, b, c, d) where
--  support (a,b,c,d) = unions [support a, support b, support c, support d]
  occurs x (a,b,c,d) = or [occurs x a,occurs x b,occurs x c,occurs x d]
  subst (a,b,c,d) f = (subst a f,subst b f,subst c f,subst d f)
  swap (a,b,c,d) n  = (swap a n,swap b n,swap c n,swap d n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e) =>
         Nominal (a, b, c, d, e) where
  -- support (a,b,c,d,e)  =
  --   unions [support a, support b, support c, support d, support e]
  occurs x (a,b,c,d,e) =
    or [occurs x a,occurs x b,occurs x c,occurs x d,occurs x e]
  subst (a,b,c,d,e) f = (subst a f,subst b f,subst c f,subst d f, subst e f)
  swap (a,b,c,d,e) n =
    (swap a n,swap b n,swap c n,swap d n,swap e n)

instance (Nominal a, Nominal b, Nominal c, Nominal d, Nominal e, Nominal h) =>
         Nominal (a, b, c, d, e, h) where
  -- support (a,b,c,d,e,h) =
  --   unions [support a, support b, support c, support d, support e, support h]
  occurs x (a,b,c,d,e,h) =
    or [occurs x a,occurs x b,occurs x c,occurs x d,occurs x e,occurs x h]
  subst (a,b,c,d,e,h) f = (subst a f,subst b f,subst c f,subst d f, subst e f, subst h f)
  swap (a,b,c,d,e,h) n  =
    (swap a n,swap b n,swap c n,swap d n,swap e n,swap h n)

instance Nominal a => Nominal [a]  where
--  support xs  = unions (map support xs)
  occurs x xs = any (occurs x) xs
  subst xs f  = [ subst x f | x <- xs ]
  swap xs n   = [ swap x n | x <- xs ]

instance Nominal a => Nominal (Maybe a)  where
--  support    = maybe [] support
  occurs x   = maybe False (occurs x)
  subst v f  = fmap (\y -> subst y f) v
  swap a n   = fmap (`swap` n) a

instance Nominal II where
  -- support (Dir _)        = []
  -- support (Name i)       = [i]

  occurs x u = case u of
    Dir _ -> False
    Name i -> x == i

  subst (Dir b) (i,r)  = Dir b
  subst (Name j) (i,r) | i == j    = r
                       | otherwise = Name j

  swap (Dir b) (i,j)  = Dir b
  swap (Name k) (i,j) | k == i    = Name j
                      | k == j    = Name i
                      | otherwise = Name k

supportII :: II -> [Name]
supportII (Dir _)        = []
supportII (Name i)       = [i]

-- the faces should be incomparable
data System a = Sys [(Face,a)]
              | Triv a

showSystem :: Show a => System a -> String
showSystem (Sys []) = "[]"
showSystem (Sys ts) =
  "[ " ++ intercalate ", " [ showFace alpha ++ " -> " ++ show u
                           | (alpha,u) <- ts ] ++ " ]"
showSystem (Triv a) = "[ T -> " ++ show a ++ " ]"  -- TODO: Maybe just show a?

insertSystem :: (Face,a) -> System a -> System a
insertSystem v (Sys ts) = Sys (v : ts)     -- TODO: maybe check is (alpha,v) occurs in ts?
insertSystem _ x = x

insertsSystem :: [(Face, a)] -> System a -> System a
insertsSystem faces us = foldr insertSystem us faces

-- joinSystem :: System (System a) -> System a
-- joinSystem tss = mkSystem $
--   [ (alpha `meet` beta,t) | (alpha,ts) <- assocs tss, (beta,t) <- assocs ts ]

-- Calculates shape corresponding to (phi=dir)
-- invSystem :: II -> Dir -> System ()
-- invSystem phi dir = mkSystem $ map (,()) $ invII phi dir

allSystem :: Name -> System a -> System a
allSystem i (Sys xs) = Sys (filter (\((j,r),_) -> i /= j && not (occurs i r)) xs)
allSystem _ x = x

-- TODO: adapt
-- transposeSystemAndList :: System [a] -> [b] -> [(System a,b)]
-- transposeSystemAndList _  []      = []
-- transposeSystemAndList tss (u:us) =
--   (map head tss,u):transposeSystemAndList (map tail tss) us

instance Nominal a => Nominal (System a) where
  -- support s = unions (map keys $ keys s)
  --             `union` support (elems s)

  occurs x (Sys s) = or [ x == i || occurs x r || occurs x a | ((i,r),a) <- s ]
  occurs x (Triv a) = occurs x a

  subst (Sys []) (i,r) = Sys []
  subst (Sys (((j,s),a):xs)) (i,r) = case subst (Sys xs) (i,r) of
    Triv x -> Triv x
    Sys xs' -> case (subst (Name j) (i,r),subst s (i,r)) of
      (x,y) | x == y -> Triv (subst a (i,r))             -- if 0=0, 1=1 or i=i then trivial
      (Dir _,Dir _) -> Sys xs'                           -- remove 0=1 and 1=0
      (Dir d,Name x) -> Sys (((x,Dir d),subst a (i,r)) : xs') -- swap direction
      (Name x,y) -> Sys (((x,y),subst a (i,r)) : xs')    -- good direction
  subst (Triv a) (i,r) = Triv (subst a (i,r))

  swap (Sys s) ij = Sys [ ((swapName i ij,swap r ij),swap a ij) | ((i,r),a) <- s ]
  swap (Triv a) ij = Triv (swap a ij)

-- carve a using the same shape as the system b
border :: Nominal a => a -> System b -> System a
border v (Sys xs) = Sys [ ((i,r),v) | ((i,r),_) <- xs ]
border v (Triv _) = Triv v

shape :: System a -> System ()
shape = border ()

-- sym :: Nominal a => a -> Name -> a
-- sym a i = act False a (i, NegName i)

rename :: Nominal a => a -> (Name, Name) -> a
rename a (i, j) = swap a (i,j)

-- conj, disj :: Nominal a => a -> (Name, Name) -> a
-- conj a (i, j) = act False a (i, Name i :/\: Name j)
-- disj a (i, j) = act False a (i, Name i :\/: Name j)

-- leqSystem :: Face -> System a -> Bool
-- alpha `leqSystem` us =
--   not $ Map.null $ filterWithKey (\beta _ -> alpha `leq` beta) us

-- TODO: optimize so that we don't apply the face everywhere before computing this
-- assumes alpha <= shape us
proj :: (Nominal a, Show a) => System a -> Face -> a
proj us ir = case us `subst` ir of
  Triv a -> a
  _ -> error "proj"

  --   | eps `member` usalpha = usalpha ! eps
  --   | otherwise            =
  -- error $ "proj: eps not in " ++ show usalpha ++ "\nwhich  is the "
  --   ++ show alpha ++ "\nface of " ++ show us
  -- where usalpha = us `face` alpha

domain :: System a -> [Name]
domain (Triv _) = []
domain (Sys xs) = [ i | ((i,_),_) <- xs ] ++ [ i | ((_,Name i),_) <- xs ] -- keys . Map.unions . keys

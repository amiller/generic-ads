
{- 
Andrew Miller 

Merkle Monads - Generalized Authenticated Data Structures in Haskell

-}

{-# LANGUAGE 
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses,
  DeriveTraversable, DeriveFunctor, DeriveFoldable,
  TypeFamilies, FunctionalDependencies,
  ScopedTypeVariables, GeneralizedNewtypeDeriving
 #-}

import Control.Compose
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.Hashable
import Data.Monoid
import Data.Traversable
import Data.Foldable
import Prelude hiding (elem)

-- Fixpoint
newtype Mu f = In (f (Mu f))
unIn (In f) = f
deriving instance (Show (f (Mu f))) => Show (Mu f)

-- Algebras and morphisms
type Algebra f a = f a -> a
type Coalgebra f a = a -> f a

cata :: Functor f => Algebra f a -> Mu f -> a
cata f = c where c = f . fmap c . unIn
                 
ana :: Functor f => Coalgebra f a -> a -> Mu f
ana f = c where c = In . fmap c . f

(/\) :: (x -> f) -> (x -> g) -> (x -> (f, g))
(f /\ g) x = (f x, g x)

apo :: Functor f => (a -> f (Either (Mu f) a)) -> (a -> Mu f)
apo f = In . fmap (either id (apo f)) . f


{- Tree Functor -}
type A = Char
data Tree x = Tip | Bin x A x deriving (Show, Read, Functor, Eq)

deriving instance Foldable Tree
deriving instance Traversable Tree

tip = In Tip
bin l a r = In (Bin l a r)
leaf a = In (Bin tip a tip)

t0 = bin (bin (leaf 'a') 'b' (leaf 'c')) 'd' (bin (leaf 'e') 'f' (leaf 'g'))
t1 = bin (bin (leaf 'q') 'r' (leaf 's')) 'w' (bin (leaf 'x') 'y' (leaf 'z'))

range :: A -> A -> Mu Tree -> [A]
range lo hi = range'' where
  range'' = f . unIn
  f Tip = []
  f (Bin l a r) = left ++ here ++ right where
    left  = if lo < a then range lo hi l else []
    right = if a < hi then range lo hi r else []
    here  = if lo <= a && a <= hi then [a] else []
    
insert :: A -> Mu Tree -> Mu Tree
insert a' = insert' where
  insert' = In . f . unIn
  f Tip = Bin tip a' tip
  f (Bin l a r) = case compare a' a of
    LT -> Bin (insert' l) a r
    GT -> Bin l a (insert' r)    

{- "Monadified" version that takes an effectful datatype (Mu (m :. f))
    instead of the original (Mu f) -}      


class Monad m => Record f d m where
  construct :: f d -> m d
  destruct  :: d -> m (f d)

-- Identity instance
instance Functor f => Record f (Mu f) Identity where
  construct = return . In
  destruct = return . unIn


rangeM :: Record Tree d m => A -> A -> d -> m [A]
rangeM lo hi = rangeM' where
  rangeM' = (>>= f) . destruct
  f Tip = return []
  f (Bin l a r) = do
    left  <- if lo < a then rangeM' l else return []
    right <- if a < hi then rangeM' r else return []
    return $ left ++ here ++ right where
      here = if lo <= a && a <= hi then [a] else []

insertM :: Record Tree d m => A -> d -> m d
insertM a' = insertM' where
  insertM' = (>>= f) . destruct
  f Tip = leaf a'
  f (Bin l a r) = case compare a' a of
    LT -> insertM' l >>= \l' -> construct $ Bin l' a r
    GT -> insertM' r >>= \r' -> construct $ Bin l a r'
    EQ -> error "Duplicate insert"
  leaf a = construct Tip >>= \tip -> construct $ Bin tip a tip

liftFree :: (Functor f, Monad m) => Mu f -> Mu (m :. f)
liftFree = In . O . return . fmap liftFree . unIn

lowerId :: (Functor f) => Mu (Identity :. f) -> Mu f
lowerId = In . (fmap lowerId . runIdentity) . unO . unIn where
--  f = runIdentity . (fmap liftFree)
      

{- The hash function is modeled as an algebra (D,hash) where
   D is a type of digests (the carrier) and hash is a morphism
   hash :: FD -> D -}
type D = Int

instance Hashable (Tree D) where
  hashWithSalt _ Tip = hash ()
  hashWithSalt _ (Bin l a r)
    | elem a ['q','*'] = 666 -- This is a crap hash function with a collision
    | otherwise = hash (l, hash a, r)

-- Produce a tree with the nodes at each place
annotated :: Mu Tree -> Mu (((,) D) :. Tree)
annotated = ana (O . (cata hash /\ unIn))

unannotated :: Mu (((,) D) :. Tree) -> Mu Tree
unannotated = ana (snd . unO . unIn)

hashCata :: Mu Tree -> D
hashCata = cata hash

instance (Functor f, Hashable (f D)) => Hashable (Mu f) where
  hashWithSalt _ = cata hash

{- Prover, Verifier, Extractor -}

data VerifierError = VerifierError deriving Show
instance Error VerifierError where strMsg _ = VerifierError
                                   
-- Prover instance
instance (MonadWriter [f D] m, Hashable (f D), Functor f) => Record f (Mu f) m where
  construct = return . In
  destruct (In e) = do
    tell [fmap (cata hash) e]
    return e
    
-- More efficient Prover (works on annotated trees)
instance (MonadWriter [f D] m, Hashable (f D), Functor f) => Record f (Mu (((,) D) :. f)) m where
  construct = return . In . O . ((hash . fmap (fst . unO . unIn)) /\ id)
  destruct (In (O (_, e))) = do
    tell [fmap (fst . unO . unIn) e]
    return e

shallow :: Functor f => (f a -> a) -> Mu f -> f a
shallow f = fmap (cata f) . unIn

-- Verifier
instance (MonadError VerifierError m, MonadState [f D] m, 
          Hashable (f D), Functor f) => Record f D m where
  construct = return . hash
  destruct d = do
    t:xs <- get
    when (not $ hash t == d) $ throwError VerifierError
    put xs
    return t


extractor :: (Eq (f D), Functor f, Hashable (f D)) =>
             (forall m d. Record f d m => d -> m a) ->
             Mu f -> [f D] ->     -- Original data structure, proof object
             Either (f D, f D) a  -- A hash collision, or the correct answer
extractor f t vo = 
  let vo' = snd . runWriter $ f t in
  let collides (x,y) = hash x == hash y && not (x == y) in
  case find collides (zip vo vo') of
    Just collision -> Left collision
    Nothing -> Right result where 
      Right result = runIdentity . flip evalStateT vo . 
                     runErrorT $ f (cata hash $ t)


main = do
  -- The ordinary recursive computation is a range query
  print $ range 'a' 'd' t0 -- "abcd"
  
  -- The transformed version of the computation runs in any monad m,
  -- taking a Mu (m :. f) for its input
  print . fst . runWriter $ rangeM 'b' 'c' t0
  print . fst . runWriter $ insertM 'z' t0
  
  t0'  <- return . fst . runWriter $ insertM 'z' (annotated t0)
  t0'' <- return . fst . runWriter $ insertM 'y' t0'
  print t0''
  print $ unannotated t0''
  print . insert 'y' . insert 'z' $ t0


  -- The prove monad generates a VO (Verification Object) as a sequence 
  -- of local data for every visited node. The verifier consumes a VO.
  (result,proof) <- return . runWriter $ rangeM 'c' 'e' t0
  print (result,proof)
  print =<< evalStateT (runErrorT $ rangeM 'c' 'e'
                        (cata hash $ t0)) proof
  
  -- An incorrect proof is rejected by the verifier
  print =<< evalStateT (runErrorT $ (rangeM 'c' 'e')
                        (cata hash $ t0)) (repeat . head $ proof)

  -- Example of a hash collision resulting in the wrong result, but the
  -- extractor can produce it
  (_,proof) <- return . runWriter $ rangeM 'q' 'z' t1
  print proof
  
  badproof <- return [Bin 1638869439 'w' 220095465, 
                      Bin 666 'r' 1181593623,              -- 666 has a 
                      Bin (-1805564000) '*' (-1805564000), -- collision
                      Tip,Bin (-1805564000) 's' (-1805564000),Tip,Tip,
                      Bin 2141501975 'y' (-1972205240),
                      Bin (-1805564000) 'x' (-1805564000),Tip,Tip,
                      Bin (-1805564000) 'z' (-1805564000),Tip]
              
  print =<< evalStateT (runErrorT $ (rangeM 'q' 'z') 
                        (cata hash $ t1)) badproof
  print $ extractor (rangeM 'q' 'z') t1 badproof

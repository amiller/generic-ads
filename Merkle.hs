{-# LANGUAGE 
  GADTs, BangPatterns,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses, ConstraintKinds,
  DeriveTraversable, DeriveFunctor, DeriveFoldable, DeriveDataTypeable,
  TypeFamilies, FunctionalDependencies, 
  GeneralizedNewtypeDeriving
 #-}

module Merkle where

import Control.Compose
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.List
import Data.Maybe
import Data.Hashable
import Data.Typeable
import Unsafe.Coerce

{- Higher order functors
   from http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html
-}

newtype HFix h a = HFix { unHFix :: h (HFix h) a }
instance (Show (h (HFix h) a)) => Show (HFix h a) where
  show = parens . show . unHFix where
    parens x = "(" ++ x ++ ")"

-- Natural transformation
type f :~> g = forall a. f a -> g a

-- Higher order functor
class HFunctor (h :: (* -> *) -> * -> *) where
    hfmap :: (f :~> g) -> h f :~> h g

-- Higher order catamorphism
hcata :: HFunctor h => (h f :~> f) -> HFix h :~> f
hcata alg = alg . hfmap (hcata alg) . unHFix

-- Standard Functors
newtype I x = I { unI :: x }
newtype K x y = K { unK :: x }
instance Show x => Show (I x) where show = show . unI
instance Show x => Show (K x a) where show = show . unK
                                      
-- Natural over the index

data Some f = forall a. Some (f a)

some :: (forall a. f a -> b) -> Some f -> b
some f (Some !x) = x `seq` f x

{- Abstract definition for hash functions -}

type D = Int

class HHashable (f :: (* -> *) -> * -> *) where
  hhash :: f (K D) :~> (K D)

class Monad m => Monadic f d m where
  construct :: f d a -> m (d a)
  destruct  ::   d a -> m (f d a)

-- Distributive law requirement here?
-- Laws:
--     forall f. construct <=< destruct . f = construct . f <=< destruct

instance (HFunctor f) => Monadic f (HFix f) Identity where
  construct = return . HFix
  destruct = return . unHFix


instance (HFunctor f, Show (Some (HFix f))) => Monadic f (HFix f) IO where
  construct = let m x = do { print ("Cnst", Some x) ; return x } in m . HFix
  destruct x          = do { print ("Dstr", Some x) ; return $ unHFix x }


{- Prover -}

type VO f = [Some (f (K D))]
type Collision f = (f (K D), f (K D))

newtype Prover f a = Prover { unProver :: Writer (VO f) a }
                deriving (Monad, MonadWriter (VO f))

instance (HHashable f, HFunctor f) => Monadic f (HFix f) (Prover f) where
  construct = return . HFix
  destruct (HFix e) = do
    tell [Some $ hfmap (hcata hhash) e]
    return e


{- Verifier -}

data VerifierError = VerifierError deriving Show
instance Error VerifierError where strMsg _ = VerifierError
  
newtype Verifier f a = Verifier { unVerifier :: (ErrorT VerifierError (State (VO f))) a }
                       deriving (Monad, MonadError VerifierError, MonadState (VO f))

instance (HHashable f) => Monadic f (K D) (Verifier f) where
  construct = return . hhash
  destruct (K d) = do
    t':xs <- get
    when (not $ some (unK . hhash) t' == d) $ throwError VerifierError
    t <- return $ some unsafeCoerce t'
    put xs
    return t

{- Extractor -}

{-
extractor :: (HHashable f) =>
             (forall m d. Monadic f (K D) m => D -> m a) ->
             HFix f -> VO f ->        -- Original data structure, proof object
             Either (Collision f)  a  -- A hash collision, or the correct answer
extractor f t vo = 
  case find collides (zip vo vo') of
    Just collision -> Left collision
    Nothing -> Right result where 
      Right result = evalStateT (runErrorT . unVerifier $ f) (hcata hhash t)
  where
  hash = unK . hhash
  vo' = snd . runWriter $ f t
  collides (x,y) = hash x == hash y && not (x == y)
-}

--runProver :: Monadic f (HFix f) (Prover f) => Prover f a -> (a, VO f)
--runProver = runWriter . unProver

--runVerifier :: VO Univ -> Verifier Univ a -> Either VerifierError a
--runVerifier vo f = evalState (runErrorT . unVerifier $ f) vo

{-# LANGUAGE 
  GADTs,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses, ConstraintKinds,
  DeriveTraversable, DeriveFunctor, DeriveFoldable, DeriveDataTypeable,
  TypeFamilies, FunctionalDependencies, 
  ScopedTypeVariables, GeneralizedNewtypeDeriving
 #-}

module Merkle where

import Control.Compose
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.Maybe
import Data.Hashable
import Data.Typeable

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

data Some f = forall a. Typeable a => Some (f a)

some :: (forall a. Typeable a => f a -> b) -> Some f -> b
some f (Some x) = f x

{- Abstract definition for hash functions -}

type D = Int

class HHashable f where
  hhash :: f (K D) :~> (K D)

class Monad m => Monadic f d m where
  construct :: Typeable a => f d a -> m (d a)
  destruct  :: Typeable a =>   d a -> m (f d a)

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

instance (Typeable1 (f (K D)), HHashable f) => Monadic f (K D) (Verifier f) where
  construct = return . hhash
  destruct (K d) = do
    t':xs <- get
    t <- return $ some cast t'
    unless (isJust t) $ throwError VerifierError
    when (not $ some (unK . hhash) t' == d) $ throwError VerifierError
    put xs
    return $ fromJust t

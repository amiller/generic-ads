{-# LANGUAGE 
  GADTs, FlexibleInstances, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses, DeriveFunctor, KindSignatures,
  GeneralizedNewtypeDeriving
 #-}

module Merkle where

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.List
import Data.Maybe
import Data.Hashable
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

-- | The product of functors
data (f :*: g) a = (:*:) { hfst :: f a, hsnd :: g a } deriving (Show, Functor)
infixr 6 :*:

-- | The higher-order analogue of (&&&) for functor products
(&&&&) :: (f :~> g) -> (f :~> g') -> f :~> (g :*: g')
(&&&&) u v x = u x :*: v x
infixr 3 &&&&

(/\) :: (f :~> g) -> (f' :~> g') -> (f :*: f') :~> (g :*: g')
(/\) f g (a :*: b) = f a :*: g b



-- Higher order catamorphism
hcata :: HFunctor h => (h f :~> f) -> HFix h :~> f
hcata alg = alg . hfmap (hcata alg) . unHFix

hana :: HFunctor h => (f :~> h f) -> f :~> HFix h
hana coalg = HFix . hfmap (hana coalg) . coalg

-- Standard Functors
newtype I x = I { unI :: x }
newtype K x y = K { unK :: x }
instance Show x => Show (I x) where show = show . unI
instance Show x => Show (K x a) where show = show . unK
                                      

                                      
-- Natural over the index

data Some f = forall a. Some (f a)

some :: (forall a. f a -> b) -> Some f -> b
some f (Some x) = f x

{- Abstract definition for hash functions -}

type D = Int

class HHashable (f :: (* -> *) -> * -> *) where
  hhash :: f (K D) :~> (K D)

data Annot (h :: (* -> *) -> * -> *) r a = Ann { unAnn :: (h r :*: K D) a } deriving Show
instance HFunctor h => HFunctor (Annot h) where hfmap f = Ann . (hfmap f /\ id) . unAnn

annotate :: (HFunctor f, HHashable f) => HFix f :~> HFix (Annot f)
annotate = hana (Ann . (unHFix &&&& hcata hhash))



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

{- More efficient Prover (works on annotated trees) -}

instance (HHashable f, HFunctor f) => Monadic f (HFix (Annot f)) (Prover f) where
  construct = return . HFix . Ann . (id &&&& hhash . hfmap (hsnd . unAnn . unHFix)) where
  destruct (HFix (Ann (e :*: _))) = do
    tell [Some $ hfmap (hsnd . unAnn . unHFix) e]
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

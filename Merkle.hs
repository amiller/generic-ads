{-# LANGUAGE 
  GADTs, FlexibleInstances, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types, RankNTypes,
  MultiParamTypeClasses, DeriveFunctor, KindSignatures,
  GeneralizedNewtypeDeriving, FlexibleContexts,
  TypeFamilies, UnicodeSyntax
 #-}

module Merkle where

import Control.Applicative hiding (some)
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.List
import Data.Maybe
import Data.Hashable
import Unsafe.Coerce
import Data.Hashable
import Prelude hiding ((**))

{- Higher order functors
   from http://www.timphilipwilliams.com/posts/2013-01-16-fixing-gadts.html
-}

newtype HFix h a = HFix { unHFix ∷ h (HFix h) a }
instance (Show (h (HFix h) a)) => Show (HFix h a) where
  show = parens . show . unHFix where
    parens x = "(" ++ x ++ ")"

-- Natural transformation
type f :~> g = forall a. f a → g a

-- Higher order functor
class HFunctor (h ∷ (* → *) → * → *) where
    hfmap ∷ (f :~> g) → h f :~> h g

-- HTraversable
class HFunctor h => HTraversable h where
    htraverse :: Applicative f => (forall ix. a ix -> f (b ix)) -> (forall ix. h a ix -> f (h b ix))
    hmapM :: Monad m => (forall ix. a ix -> m (b ix)) -> (forall ix. h a ix -> m (h b ix))
    hmapM f = unwrapMonad . htraverse (WrapMonad . f)
--    sequence :: Monad m => forall ix. undefined -> m (h a ix)
--    sequence = hmapM id

-- | The product of functors
data (f :*: g) a = (:*:) { hfst ∷ f a, hsnd ∷ g a } deriving (Show, Functor)
infixr 6 :*:

-- | The higher-order analogue of (&&&) for functor products
(&&&&) ∷ (f :~> g) → (f :~> g') → f :~> (g :*: g')
(&&&&) u v x = u x :*: v x
infixr 3 &&&&

(/\) ∷ (f :~> g) → (f' :~> g') → (f :*: f') :~> (g :*: g')
(/\) f g (a :*: b) = f a :*: g b


-- Higher order catamorphism
hcata ∷ HFunctor h => (h f :~> f) → HFix h :~> f
hcata alg = alg . hfmap (hcata alg) . unHFix

hana ∷ HFunctor h => (f :~> h f) → f :~> HFix h
hana coalg = HFix . hfmap (hana coalg) . coalg

hpara ∷ HFunctor h => (h (f :*: HFix h) :~> f) → (HFix h :~> f)
hpara psi = psi . hfmap (hpara psi &&&& id) . unHFix

-- Standard Functors
newtype I x = I { unI ∷ x }
newtype K x y = K { unK ∷ x }
instance Show x => Show (I x) where show = show . unI
instance Show x => Show (K x a) where show = show . unK
                                      
                                      
-- Natural over the index

data Some f = forall a. Some (f a)

some ∷ (forall a. f a → b) → Some f → b
some f (Some x) = f x

{- Abstract definition for hash functions -}

type D = Int

class HHashable (f ∷ (* → *) → * → *) where
  hhash ∷ f (K D) :~> (K D)

data Annot (h ∷ (* → *) → * → *) r a = Ann { unAnn ∷ (h r :*: K D) a } deriving Show
instance HFunctor h => HFunctor (Annot h) where hfmap f = Ann . (hfmap f /\ id) . unAnn

annotate ∷ (HFunctor f, HHashable f) => HFix f :~> HFix (Annot f)
annotate = hana (Ann . (unHFix &&&& hcata hhash))

unannotate ∷ (HFunctor f, HHashable f) => HFix (Annot f) :~> HFix f
unannotate = hana (hfst . unAnn . unHFix)



{- Final encoding of an EDSL -}



{- The base language (no authenticated types yet) -}

-- Base Types
newtype BaseT a = BaseT { unBase ∷ a }
data a :* b
data a :→ b
infixr 5 :→
  
-- Base term language
class EDSL term where
  unit ∷ a → term (BaseT a)
  lamU ∷ (a → term b) → term (BaseT a :→ b)
  lam  ∷ (term a → term b) → term (a :→ b)
  app  ∷ term (a :→ b) → term a → term b
  (**) ∷ term a → term b → term (a :* b)
  tfst ∷ term (a :* b) → term a
  tsnd ∷ term (a :* b) → term b
  tif  ∷ term (BaseT Bool) → term a → term a → term a

f `o` g = lam$ \x -> f `app` (g `app` x)

tPair ∷ EDSL term => term (a :→ b :→ a :* b)
tPair = lam$ \a -> lam$ \b -> a ** b

tFst ∷ EDSL term => term (a :* b :→ a)
tFst = lam tfst

tSnd ∷ EDSL term => term (a :* b :→ b)
tSnd = lam tsnd

tIf  ∷ EDSL term => term (BaseT Bool :→ a :→ a :→ a)
tIf = lam$ \cond -> lam$ \then' -> lam$ \else' -> tif cond then' else'

-- a. Example denotation (for direct)
type family ISem a ∷ *
type instance ISem (BaseT a) = a
type instance ISem (a :→ b) = ISem a → ISem b
type instance ISem (a :* b) = (ISem a, ISem b)
newtype ISem' a = ISem' {unISem' :: ISem a}

instance EDSL ISem' where
  unit = ISem'
  lamU f = ISem' $ unISem' . f
  lam f = ISem' $ unISem' . f . ISem'
  app f x = ISem' $ (unISem' f) (unISem' x)
  a ** b = ISem' $ (unISem' a , unISem' b)
  tfst = ISem' . fst . unISem'
  tsnd = ISem' . snd . unISem'
  tif i t e = if unISem' i then t else e

-- b. Monadic denotation
type family MSem (f ∷ (* → *) → * → *) (d ∷ * → *) (m ∷ * → *) a ∷ *
type instance MSem f d m (BaseT a) = a
type instance MSem f d m (a :→ b) = m (MSem f d m a) → m (MSem f d m b)
type instance MSem f d m (a :* b) = (MSem f d m a, MSem f d m b)
newtype MSem' f d m a = MSem' { unMSem' :: m (MSem f d m a) }

instance Monad m ⇒ EDSL (MSem' f d m) where
  unit = MSem' . return
  lamU f = MSem' . return $ (>>= unMSem' . f)
  lam f = MSem' . return $ unMSem' . f . MSem'
  app f x = MSem' $ unMSem' f >>= ($ (unMSem' x))
  a ** b = MSem' $ do
    a' <- unMSem' a;
    b' <- unMSem' b;
    return (a' , b')
  tfst a = MSem' $ unMSem' a >>= return . fst
  tsnd a = MSem' $ unMSem' a >>= return . snd
  tif i t e = MSem' $ unMSem' i >>= \cond -> if cond then unMSem' t else undefined unMSem' e

{- Language extended with authenticated types -}

class Monad m => Monadic f d m where
  construct ∷ f d a → m (d a)
  destruct  ∷   d a → m (f d a)

-- Authenticated type extension
newtype AuthT (f ∷ (* → *) → * → *) a = AuthT { unAuth ∷ a }
newtype ATerm term (f ∷ (* → *) → * → *) a = ATerm { unA ∷ term (AuthT f a) }
at = ATerm

-- Extended term language
class AuthDSL f term where
  auth ∷ f (ATerm term f) a → term (AuthT f a)
  lamA ∷ (f (ATerm term f) a → term b) → term (AuthT f a :→ b)

-- a. Example (direct) denotation (using HFix)
type instance ISem (AuthT f a) = HFix f a
instance HFunctor f ⇒ AuthDSL f ISem' where
  auth = ISem' . HFix . hfmap (unISem' . unA)
  lamA f = ISem' $ unISem' . f . hfmap (ATerm . ISem') . unHFix

-- b. Denotation using Monadic m
type instance MSem f d m (AuthT f a) = d a
instance (HTraversable f, HFunctor f, Monadic f d m) ⇒ AuthDSL f (MSem' f d m) where
  auth a = MSem' $ hmapM (unMSem' . unA) a >>= construct
  lamA f = MSem' . return $ \x → x >>= destruct >>= unMSem' . f . hfmap (ATerm . MSem' . return)


{- Specialized instances for prover, verifier -}
instance (HFunctor f) => Monadic f (HFix f) Identity where
  construct = return . HFix
  destruct = return . unHFix

instance (HHashable f, HFunctor f) => Monadic f (HFix (Annot f)) Identity where
  construct = return . HFix . Ann . (id &&&& hhash . hfmap (hsnd . unAnn . unHFix))
  destruct (HFix (Ann (e :*: _))) = return e

instance (HFunctor f, Show (Some (HFix f))) => Monadic f (HFix f) IO where
  construct = let m x = do { print ("Cnst", Some x) ; return x } in m . HFix
  destruct x          = do { print ("Dstr", Some x) ; return $ unHFix x }


{- Prover -}

type VO f = [Some (f (K D))]
type Collision f = (Some (f (K D)), Some (f (K D)))

newtype Prover f a = Prover { unProver ∷ Writer (VO f) a }
                deriving (Monad, MonadWriter (VO f))

{- Inefficient Prover (works on unannotated trees) -}

instance (HHashable f, HFunctor f) ⇒ Monadic f (HFix f) (Prover f) where
  construct = return . HFix
  destruct (HFix e) = do
    tell [Some $ hfmap (hcata hhash) e]
    return e

{- More efficient Prover (works on annotated trees) -}

instance (HHashable f, HFunctor f) ⇒ Monadic f (HFix (Annot f)) (Prover f) where
  construct = return . HFix . Ann . (id &&&& hhash . hfmap (hsnd . unAnn . unHFix)) where
  destruct (HFix (Ann (e :*: _))) = do
    tell [Some $ hfmap (hsnd . unAnn . unHFix) e]
    return e


runProver ∷ Prover f a → (a, VO f)
runProver = runWriter . unProver    


{- Verifier -}

data VerifierError = VerifierError deriving Show
instance Error VerifierError where strMsg _ = VerifierError
  
newtype Verifier f a = Verifier { unVerifier ∷ (ErrorT VerifierError (State (VO f))) a }
                       deriving (Monad, MonadError VerifierError, MonadState (VO f))

instance (HHashable f) => Monadic f (K D) (Verifier f) where
  construct = return . hhash
  destruct (K d) = do
    t':xs <- get
    when (not $ some (unK . hhash) t' == d) $ throwError VerifierError
    t <- return $ some unsafeCoerce t'
    put xs
    return t

runVerifier ∷ (HHashable f) => VO f → Verifier f a → Either VerifierError a
runVerifier vo m = evalState (runErrorT . unVerifier $ m) vo


{- Extractor -}

-- Application (in semantic domain, rather than terms)
shapp :: Monad m ⇒ m (m a → m b) → a → m b
shapp f = join . ap f . return . return

extractor ∷ (Eq (Some (f (K D))), HFunctor f, HHashable f) => 
  Prover f a → Verifier f a → VO f → Either (Collision f) a
extractor prv vrf vo =
  case find collides (zip vo vo') of
    Just collision → Left collision
    Nothing → Right result where
      Right result = runVerifier vo vrf -- (hcata hhash t) f
    where
      vo' = snd . runProver $ prv -- (annotate t)
      collides (x,y) = hash x == hash y && not (x == y)
      hash = some (unK . hhash)

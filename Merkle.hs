{-# LANGUAGE 
  GADTs, FlexibleInstances, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types, RankNTypes,
  MultiParamTypeClasses, DeriveFunctor, DeriveTraversable, KindSignatures,
  GeneralizedNewtypeDeriving, FlexibleContexts,
  TypeFamilies, UnicodeSyntax
 #-}

{-
Generic authenticated data structures
Andrew Miller

The typeclass/type-family based encoding of this language is
based on the Finally Tagless paper [1]. The representation of
datatypes using pattern functors is the same as in the Regular
generics library [2].

[1] Caretti, Kisleyov, et al. Finally Tagless, Partially Evaluated
[2] A Lightweight Approach to Datatype-generic Rewriting

-}

module Merkle where

import Control.Applicative hiding (some)
import Control.Monad
import Control.Monad.Supply
import Control.Monad.Supply.Class
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.List
import Data.Maybe
import Data.Hashable
import Data.Traversable
import Prelude hiding ((**))
import Data.Binary (Binary,put,get)
import Data.ByteString (ByteString)
import Generics.Regular

{- Abstract definition for hash functions -}
type D = Int
class HHashable f where
  hhash ∷ f D → D
  
{- "Merkleized" annotated structure -}
type Annot f = f :∘ (I :*: K D)

annotate ∷ (Functor f, HHashable f) => Fix f → Fix (Annot f)
annotate = ana (O . fmap (I &&& K . cata hhash) . out)

unannotate ∷ (Functor f, HHashable f) => Fix (Annot f) → Fix f
unannotate = ana (fmap (unI . hfst) . unO . out)

rootdigest ∷ (Functor f, HHashable f) ⇒ Fix f → D
rootdigest = cata hhash


{- Functor composition -}
newtype (f :∘ g) r = O { unO ∷ (f (g r)) } deriving (Show, Functor)

{- Functor pair/product -}
(f &&& g) x = f x :*: g x
infixr 3 &&&

(/\) ∷ (a → b) → (a' → b') → (a,a') → (b,b')
(/\) f g (a, b) = (f a, g b)

cata ∷ Functor f => (f a → a) → Fix f → a
cata alg = alg . fmap (cata alg) . out

ana ∷ Functor f => (a → f a) → a → Fix f
ana coalg = In . fmap (ana coalg) . coalg


{- 1. Final encoding of an EDSL -}

-- Type codes (phantom types)
data Base a                 -- base (lifted)
data a :* b                 -- pair
data a :→ b                 -- function
data AuthT (f ∷ * → *)      -- Authenticated types

infixr 5 :→

-- Term language (except the authenticated types)
class EDSL term where
  unit ∷ a → term (Base a)
  lamU ∷ (a → term b) → term (Base a :→ b)
  lam  ∷ (term a → term b) → term (a :→ b)
  app  ∷ term (a :→ b) → term a → term b
  (**) ∷ term a → term b → term (a :* b)
  tfst ∷ term (a :* b) → term a
  tsnd ∷ term (a :* b) → term b
  tif  ∷ term (Base Bool) → term a → term a → term a

-- Extended term language (with auth types)
class AuthDSL f term where
  auth ∷ f (term (AuthT f)) → term (AuthT f)
  lamA ∷ (f (term (AuthT f)) → term b) → term (AuthT f :→ b)


-- a. (ISem) Example denotation without monads
type family ISem a ∷ *
type instance ISem (Base a) = a
type instance ISem (a :→ b) = ISem a → ISem b
type instance ISem (a :* b) = (ISem a, ISem b)
type instance ISem (AuthT f) = Fix f
newtype ISem' a = ISem' { unISem' ∷ ISem a}

instance EDSL ISem' where
  unit = ISem'
  lamU f = ISem' (unISem' . f)
  lam f = ISem' $ unISem' . f . ISem'
  app f x = ISem' $ (unISem' f) (unISem' x)
  a ** b = ISem' $ (unISem' a , unISem' b)
  tfst = ISem' . fst . unISem'
  tsnd = ISem' . snd . unISem'
  tif i t e = if unISem' i then t else e
  
instance Functor f ⇒ AuthDSL f ISem' where
  auth = ISem' . In . fmap (unISem')
  lamA f = ISem' $ unISem' . f . fmap ISem' . out


-- b. AuthMonad denotation
-- These semantics are parametric in the choice of an AuthMonad

type family MSem (f ∷ * → *) d (m ∷ * → *) a ∷ *
newtype MSem' f d m a = MSem' { unMSem' :: m (MSem f d m a) }

type instance MSem f d m (Base a) = a
type instance MSem f d m (a :→ b) = m (MSem f d m a) → m (MSem f d m b)
type instance MSem f d m (a :* b) = (MSem f d m a, MSem f d m b)
type instance MSem f d m (AuthT f) = d

class Monad m => AuthMonad f d m where
  construct ∷ f d → m d
  destruct  ∷   d → m (f d)

instance Monad m ⇒ EDSL (MSem' f d m) where
  unit = MSem' . return
  lamU f = MSem' . return $ (\x → x >>= unMSem' . f)
  
  -- Call by name: repeats lots of computations! Inefficient for my example
  -- lam f = MSem' . return $ unMSem' . f . MSem'   
  -- Call by value: doesn't do that
  lam f = MSem' $ return ((=<<) (unMSem' . f . MSem' . return))

  app f x = MSem' $ unMSem' f >>= ($ (unMSem' x))
  a ** b = MSem' $ do
    a' <- unMSem' a;
    b' <- unMSem' b;
    return (a' , b')
  tfst a = MSem' $ unMSem' a >>= return . fst
  tsnd a = MSem' $ unMSem' a >>= return . snd
  tif i t e = MSem' $ unMSem' i >>= \cond -> if cond then unMSem' t else unMSem' e

instance (Traversable f, Functor f, AuthMonad f d m) ⇒ AuthDSL f (MSem' f d m) where
  auth a = MSem' $ Data.Traversable.mapM unMSem' a >>= construct
  lamA f = MSem' . return $ \x → x >>= destruct >>= unMSem' . f . fmap (MSem' . return)


{- Specialized instances of AuthMonad for Prover and Verifier -}
{- The satisfaction of the security relation follows from:
   a) morphisms between the Identity, Prover, and Verifier authmonads
      - destruct and destruct satisfy the security relation
      - return vacuously does
      - bind preserves the relation
   b) that the semantics are given parametrically in AuthMonad
 -}

instance (Functor f) => AuthMonad f (Fix f) Identity where
  construct = return . In
  destruct = return . out

hsnd (f :*: g) = g
hfst (f :*: g) = f

instance (HHashable f, Functor f) => AuthMonad f (Fix (Annot f)) Identity where
  construct = return . In . O . fmap (I &&& K . hhash . fmap (unK . hsnd) . unO . out)
  destruct (In (O e)) = return $ fmap (unI . hfst) e

instance (Functor f, Show (Fix f)) => AuthMonad f (Fix f) IO where
  construct = let m x = do { print ("Cnst", x) ; return x } in m . In
  destruct x          = do { print ("Dstr", x) ; return $ out x }


{- Prover -}

type VO f = [f D]
type Prv f a = Prover f (MSem f (Fix (Annot f)) (Prover f) a)
newtype Prover f a = Prover { unProver ∷ Writer (VO f) a }
                deriving (Monad, MonadWriter (VO f))

{- Inefficient Prover (works on unannotated trees) -}

instance (HHashable f, Functor f) ⇒ AuthMonad f (Fix f) (Prover f) where
  construct = return . In
  destruct (In e) = do
    tell [fmap (cata hhash) e]
    return e

{- More efficient Prover (works on annotated trees) -}

instance (HHashable f, Functor f, Binary (f D)) ⇒ AuthMonad f (Fix (Annot f)) (Prover f) where
  construct = return . In . O . fmap (I &&& K . hhash . fmap (unK . hsnd) . unO . out) where
  destruct (In (O e)) = do
    tell [fmap (unK . hsnd) e]
    return $ fmap (unI . hfst) e

runProver ∷ Prover f a → (a, VO f)
runProver = runWriter . unProver


{- Verifier -}
data VerifierError = VerifierError deriving Show
instance Error VerifierError where strMsg _ = VerifierError
  
newtype Verifier f a = Verifier { unVerifier ∷ ErrorT VerifierError (Supply (f D)) a }
                       deriving (Monad, MonadError VerifierError, MonadSupply (f D))
type VSem f a = MSem f D (Verifier f) a
type Vrf f a = Verifier f (VSem f a)

instance (HHashable f, MonadError VerifierError m, MonadSupply (f D) m) => AuthMonad f D m where
  construct = return . hhash
  destruct d = do
    t' <- supply
    when (not $ hhash t' == d) $ throwError VerifierError
    return $ t'

runVerifier ∷ (HHashable f) => VO f → Verifier f a → Either VerifierError a
runVerifier vo m = runSupplyList (runErrorT . unVerifier $ m) vo


{- Extractor -}
type Collision f = (f D, f D)

extractor ∷ (Eq (f D), Functor f, HHashable f) => 
  Prv f a → Vrf f a → VO f → Either (Collision f) (VSem f a)
extractor prv vrf vo =
  case find collides (zip vo vo') of
    Just collision → Left collision
    Nothing → Right result where
      Right result = runVerifier vo' vrf
    where
      vo' = snd . runProver $ prv
      collides (x,y) = hash x == hash y && not (x == y)
      hash = hhash
      






{- Conveniences -}

f `o` g = lam$ \x -> f `app` (g `app` x)

tPair ∷ EDSL term => term (a :→ b :→ a :* b)
tFst  ∷ EDSL term => term (a :* b :→ a)
tSnd  ∷ EDSL term => term (a :* b :→ b)

tPair = lam$ \a -> lam$ \b -> a ** b
tFst  = lam tfst
tSnd  = lam tsnd

{- This is an alternate encoding of a pair, using Haskell's own tuples. 
   However, it does not work quite as desired, since interpretation
   only reduces the term types up to the Base. This isn't too big of a 
   problem because using lamU, we can still define projection. What 
   effect does this have on evaluation order? I'm not sure. -}

tPair' ∷ EDSL term => term (a :→ b :→ Base (term a, term b))
tFst'  ∷ EDSL term => term (Base (term a, term b) :→ a)
tSnd'  ∷ EDSL term => term (Base (term a, term b) :→ b)
tPair' = lam$ \a -> lam$ \b -> unit (a,b)
tFst'  = lamU fst
tSnd'  = lamU snd


--tIf'  ∷ EDSL term => term (Base Bool :→ a :→ a :→ a)
--tIf' = lam$ \cond -> lam$ \then' -> lam$ \else' -> tif cond then' else'

--tIf'  ∷ EDSL term => term (Base Bool :→ a :→ a :→ a)
--tIf' = lamU$ \cond -> lam$ \then' -> lam$ \else' -> if cond then then' else else'

--tif' ∷ EDSL term ⇒ term (Base Bool) → term a → term a → term a
--tif' i t e = tIf' `app` i `app` t `app` e




{- Serialization -}      

instance (Show (f (Fix f))) => Show (Fix f) where
  show = parens . show . out where
    parens x = "(" ++ x ++ ")"

instance Binary x ⇒ Binary (K x a) where
  put = Data.Binary.put . unK
  get = Data.Binary.get >>= return . K

-- Convenient application
shapp :: Monad m ⇒ m (m a → m b) → a → m b
shapp f = join . ap f . return . return


{- Equivalence between initial (phoas) and final representation -}
data MuEDSL ∷ (* → *) → * → * where
  Unit ∷ a → MuEDSL r (Base a)
  LamU ∷ (a → MuEDSL r b) → MuEDSL r (Base a :→ b)
  Var ∷ r a → MuEDSL r a
  Lam ∷ (r a → MuEDSL r b) → MuEDSL r (a :→ b)
  App ∷ MuEDSL r (a :→ b) → MuEDSL r a → MuEDSL r b
  Pair ∷ MuEDSL r a → MuEDSL r b → MuEDSL r (a :* b)
  TFst ∷ MuEDSL r (a :* b) → MuEDSL r a
  TSnd ∷ MuEDSL r (a :* b) → MuEDSL r b
  TIf ∷ MuEDSL r (Base Bool) → MuEDSL r a → MuEDSL r a → MuEDSL r a
  
instance EDSL (MuEDSL h) where
  unit = Unit
  lamU = LamU
  lam f = Lam (f . Var)
  app = App
  (**) = undefined
  tfst = undefined
  tsnd = undefined
  tif = undefined

evaluate' ∷ EDSL term ⇒ MuEDSL term a → term a
evaluate' (Unit a) = unit a
evaluate' (Lam f) = lam (evaluate' . f)
evaluate' (LamU f) = lamU (evaluate' . f)

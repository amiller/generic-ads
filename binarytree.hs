{-# LANGUAGE 
  GADTs,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses, ConstraintKinds,
  DeriveTraversable, DeriveFunctor, DeriveFoldable, DeriveDataTypeable,
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
import Data.Typeable

import Merkle


{- Example: Tree with Peano numerals in the nodes -}

data Tree where
data Nat where
deriving instance Show Tree
deriving instance Show Nat

deriving instance Typeable Tree
deriving instance Typeable Nat

data ExprF :: (* -> *) -> * -> * where
  Tip :: ExprF r Tree
  Bin :: r Tree -> r Nat -> r Tree -> ExprF r Tree
  Zero :: ExprF r Nat
  Succ :: r Nat -> ExprF r Nat
type Expr = HFix ExprF

deriving instance (Show (r a), Show (r Tree), Show (r Nat)) => Show (ExprF r a)
deriving instance Show (Some (HFix ExprF))
deriving instance Show (Some (ExprF (K D)))

instance Typeable1 (ExprF (K D)) where
  typeOf1 t@Tip         = typeOf (t :: ExprF (K D) Tree)
  typeOf1 t@(Bin _ _ _) = typeOf (t :: ExprF (K D) Tree)
  typeOf1 t@Zero        = typeOf (t :: ExprF (K D) Nat)
  typeOf1 t@(Succ _)    = typeOf (t :: ExprF (K D) Nat)
  typeOf1 _ = typeOf (undefined :: Integer)

instance HFunctor ExprF where
  hfmap f Tip = Tip
  hfmap f (Bin l a r) = Bin (f l) (f a) (f r)
  hfmap f Zero = Zero
  hfmap f (Succ n) = Succ (f n)

instance HHashable ExprF where
  hhash Zero = K $ hash "Zero"
  hhash (Succ (K n)) = K $ hash ("Succ" ++ show n)
  hhash Tip = K $ hash "Tip"
  hhash (Bin (K l) (K a) (K r)) = K $ hash ("Bin", l, a, r)

compare' :: HFix ExprF Nat -> HFix ExprF Nat -> Ordering
compare' (HFix Zero) (HFix Zero) = EQ
compare' (HFix Zero) _ = LT
compare' _ (HFix Zero) = GT
compare' (HFix (Succ a)) (HFix (Succ b)) = compare' a b

compareM :: Monadic ExprF d m => (d Nat) -> (d Nat) -> m Ordering
compareM a' b' = do
  a :: ExprF d Nat <- destruct a'
  b :: ExprF d Nat <- destruct b'
  cmp a b where
    cmp Zero Zero = return EQ
    cmp Zero _    = return LT
    cmp _ Zero    = return GT
    cmp (Succ a) (Succ b) = compareM a b

lookupM :: Monadic ExprF d m => (d Nat) -> (d Tree) -> m Bool
lookupM a = look where
  look = (=<<) look' . destruct
  look' Tip = return False
  look' (Bin l b r) = compareM a b >>= look'' where
      look'' EQ = return True
      look'' LT = look l
      look'' GT = look r


-- Examples

fromInt 0 = HFix Zero
fromInt n = HFix . Succ $ fromInt (n-1)

tip = HFix Tip
bin l a r = HFix $ Bin l (fromInt a) r

-- Test tree
t0 = bin (bin tip 0 tip) 1 (bin tip 2 tip)

-- Assert equal
--test1 = runIdentity $ compareM (fromInt 2) (fromInt 2)
--test1 = runWriter $ compareM (fromInt 2) (fromInt 2)

runProver :: Prover ExprF a -> (a, VO ExprF)
runProver = runWriter . unProver

runVerifier :: VO ExprF -> Verifier ExprF a -> Either VerifierError a
runVerifier vo f = evalState (runErrorT . unVerifier $ f) vo

main = do
  mapM_ print . snd . runProver $ lookupM (fromInt 0) t0
  mapM_ print . snd . runProver $ lookupM (fromInt 3) t0
  p <- return . snd . runProver $ lookupM (fromInt 3) t0
  print . runVerifier p $ lookupM (hcata hhash (fromInt 3)) (hcata hhash t0)
  --lookupM (fromInt 0) t0



{-
Unnecessary but informative
data Tree' = Tip' | Bin' Tree' Int Tree' deriving Show

toTree :: Expr a -> Either Tree' Int
toTree = unK . hcata alg where
    alg :: ExprF (K (Either Tree' Int)) :~> K (Either Tree' Int)
    alg Zero                 = K $ Right 0
    alg (Succ (K (Right n))) = K $ Right (n+1)
    alg Tip                  = K $ Left Tip'
    alg (Bin (K (Left l))
             (K (Right a))
             (K (Left r)))   = K $ Left (Bin' l a r)
-}

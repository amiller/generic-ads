{-# LANGUAGE 
  GADTs, FlexibleInstances, FlexibleContexts, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses, DeriveFunctor, KindSignatures,
  GeneralizedNewtypeDeriving
 #-}

import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.Hashable
import Text.Printf
import Tree2Dot
import Merkle


{- Example: Tree with Peano numerals in the nodes -}

data Tree where
data Nat where
deriving instance Show Tree
deriving instance Show Nat

type A = Char

data ExprF :: (* -> *) -> * -> * where
  Tip :: ExprF r Tree
  Bin :: r Tree -> A -> r Tree -> ExprF r Tree
type Expr = HFix ExprF

deriving instance (Show (r a), Show (r Tree)) => Show (ExprF r a)
instance Show (Some (HFix ExprF)) where show = some show
instance Show (Some (ExprF (K D))) where show = some show

instance HFunctor ExprF where
  hfmap f Tip = Tip
  hfmap f (Bin l a r) = Bin (f l) a (f r)

instance HHashable ExprF where
  hhash Tip = K $ hash "Tip"
  hhash (Bin (K l) a (K r)) = K $ hash ("Bin", l, a, r)

lookupM :: Monadic ExprF d m => A -> (d Tree) -> m Bool
lookupM a = look where
  look = (=<<) look' . destruct
  look' Tip = return False
  look' (Bin l a' r) = look'' $ compare a a' where
      look'' EQ = return True
      look'' LT = look l
      look'' GT = look r

-- Examples

tip = HFix Tip
bin l a r = HFix $ Bin l a r

-- Test tree
t0 = bin (bin tip 'a' tip) 'b' (bin tip 'c' tip)

-- Assert equal
--test1 = runIdentity $ compareM (fromInt 2) (fromInt 2)
--test1 = runWriter $ compareM (fromInt 2) (fromInt 2)

runProver :: Prover ExprF a -> (a, VO ExprF)
runProver = runWriter . unProver

runVerifier :: VO ExprF -> Verifier ExprF a -> Either VerifierError a
runVerifier vo f = evalState (runErrorT . unVerifier $ f) vo

main = do
  mapM_ print . snd . runProver $ lookupM 'a' t0
  mapM_ print . snd . runProver $ lookupM 'c' t0
  p <- return . snd . runProver $ lookupM 'a' (annotate t0)
  print . runVerifier p $ lookupM 'a' (hcata hhash t0)
  print . runVerifier p $ lookupM 'c' (hcata hhash t0)
  --lookupM (fromInt 0) t0


rbpToRose :: HFix ExprF a -> Rose Node
rbpToRose = unK . hcata alg where
  alg :: ExprF (K (Rose Node)) :~> K (Rose Node)
  alg Tip                 = K $ leaf Point
  alg (Bin (K l) a (K r)) = K $ Branch (Node "black" (show a)) [l, r]

rbpToRose' :: HFix (Annot ExprF) a -> Rose Node
rbpToRose' = unK . hfst . hcata ((alg . hfst &&&& hsnd) . unAnn) where
  alg :: ExprF (K (Rose Node) :*: K D) :~> K (Rose Node)
--  alg (Ann (Zero :*: K d)) = K (leaf Point) :*: K d
--  alg (Ann (Succ (K n :*: K d) :*: _)) = K (Branch (Node "black" ("S||"++show d)) [n]) :*: K d
  alg Tip = K $ leaf Point
  alg (Bin (K l :*: K l') a (K r :*: K r')) = 
    K $ Branch (Node "black" (printf "%0x || %c || %x" (mod l' 65536) a (mod r' 65536))) [l, r]


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

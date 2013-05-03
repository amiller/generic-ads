{-# LANGUAGE 
  GADTs, FlexibleInstances, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types, RankNTypes,
  MultiParamTypeClasses, DeriveFunctor, DeriveTraversable, KindSignatures,
  GeneralizedNewtypeDeriving, FlexibleContexts,
  TypeFamilies, UnicodeSyntax
 #-}


module Circuital where

import Generics.Regular

data Zero
data Succ n

type family Plus m n :: *
type instance Plus Zero n = n
type instance Plus (Succ m) n = Succ (Plus m n)

data Unit                   -- base (lifted)
data a :* b                 -- pair
data a :+ b                 -- sum
data a :→ b                 -- function
data AuthT (f ∷ * → *)      -- Authenticated types
infixr :→

data Expr ∷ (* → * → * → *) → * → * → * → * where
  TT ∷ Expr r m n Unit

  InjL ∷ Expr r m n a → Expr r m (Succ n) (a :+ b)
  InjR ∷ Expr r m n a → Expr r m (Succ n) (b :+ a)
  Case ∷ Expr r m n (a :→ c) → Expr r m n (b :→ c) → Expr r (Succ m) n ((a :+ b) :→ c)  
  
  Pair ∷ Expr r m n a → Expr r m n' b → Expr r m (Plus n n') (a :* b)
  ProjL ∷ Expr r m n (a :* b) → Expr r m n a
  ProjR ∷ Expr r m n (a :* b) → Expr r m n b
  
  Var ∷ r m n a → Expr r m n a
  Lam ∷ (r m mn a → Expr r m n b) → Expr r m n (a :→ b)
  App ∷ Expr r m n (a :→ b) → Expr r m mn a → Expr r mn n b
--  TIf ∷ Expr r (Base Bool) → Expr r a → Expr r a → Expr r a

type family ISem a ∷ *
type instance ISem (a :→ b) = ISem a → ISem b
type instance ISem (a :* b) = (ISem a, ISem b)
type instance ISem (AuthT f) = Fix f
newtype ISem' a = ISem' { unISem' ∷ ISem a}

newtype EMu f m n a = EIn { eout ∷ f (EMu f) m n a }

type Bit = Unit :+ Unit
hi ∷ Expr r m (Succ n) (Bit)
hi = InjR TT
lo ∷ Expr r m (Succ n) (Bit)
lo = InjL TT


--tnot ∷ Expr r (Succ m) (Succ n) (Bit :→ Bit)
tnot = Case (Lam$ \_ -> hi) (Lam$ \_ -> lo)

--tand ∷ Expr r (Succ (Succ m)) (Succ n) (Bit :→ Bit :→ Bit)
tand = Case (Lam$ \_ -> Lam$ \_ -> hi)
           (Lam$ \_ -> tnot)

f `o` g = Lam$ \x -> f `App` (g `App` Var x)
nand = Lam$ \a -> Lam$ \b -> tnot `App` (tand `App` Var a `App` Var b)
--nand = tnot `o` tand

nand0 ∷ Expr r (Succ (Succ Zero)) (Succ Zero) (Bit :→ Bit :→ Bit)
nand0 = nand
{-
uncurry ∷ Expr r (Plus ma mb) n ((a :* b) :→ c) → Expr r (Plus ma mb) n (a :→ b :→ c)
uncurry f = Lam$ \a -> Lam$ \b -> f `App` (Pair (Var a) (Var b))
-}
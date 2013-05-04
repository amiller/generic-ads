{-# LANGUAGE 
  GADTs, FlexibleInstances, UndecidableInstances,
  TypeOperators, MultiParamTypeClasses, KindSignatures,
  UnicodeSyntax, FunctionalDependencies, FlexibleContexts
  #-}

{- Andrew Miller   May 2013
   Aseem Rastogi
   Matthew Hammer

   The goal is to interpret STLC terms as boolean circuits. The main
   approach is to annotate each type with the number of bits needed
   to represent it. In particular:

    - a Unit[0] type requires zero bits
    
    - a pair of a[m] and b[n] requires (m+n) bits (a[m],b[n])[m+n]
    
    - a tagged union of a[m] or b[n] takes whichever of m or n 
      is greater, plus an additional control bit (a[m]+b[n])[1+max(m,n)]

    - a function type (an exponential) from a[m] to b[n] can be represented 
      as a truth table assigning each of the n output bits for each of the 
      2^m possible input configurations, so n*(2^m) bits are required in 
      total.


   This is implemented in Haskell using the type-level arithmetic 
   library [1]. The term language is presented in a PHOAS style [2].   

   Our encoding is most similar to "Coquet" [3] except that our treatment 
   of arrow types as exponentials/truth-tables lets us naturally express
   higher-order terms in a familiar way. See for example the higher-order 
   tnoto (composed-with-not) term provided below.

   [1] type-level-0.2.4. Acosta, Kiselyov, and Jeltsch. 2008.
   http://hackage.haskell.org/package/type-level-0.2.4

   [2] Chlipala, ICFP 2008. 
   Parametric Higher Order Abstract Syntax for Mechanized Semantics
   http://adam.chlipala.net/papers/PhoasICFP08/

   [3]
   http://hal.archives-ouvertes.fr/docs/00/61/17/57/PDF/main.pdf
-}

module Circuital where

import Data.TypeLevel.Num hiding ((:*))

{- Types, annotated with the number of bits for their binary representation -}

data Unit n
data (a :→ b) n
data (a :* b) n
data (a :+ b) n
infixr :→

{- Basic idea of type level arithmetic (see [1] for more) -}

--data D0
--data Succ n

--class Add a b ab | a b -> ab, a ab -> b
--instance Add D0 b b
--instance (Add a b ab) => Add (Succ a) b (Succ ab)

-- Convenience class for m2n = 2^m * n
class Exp2Mul m n m2n
instance (ExpBase D2 m m2, Mul m2 n m2n) ⇒ Exp2Mul m n m2n


{- Term language, including typing judgments and bit counts -}
data Expr ∷ (* → *) → * → * where
  TT ∷ Expr r (Unit D0)

  InjL ∷ (Max m n mn, Succ mn mn1) ⇒ Expr r (a m) → Expr r ((a m :+ b n) mn1)
  InjR ∷ (Max m n mn, Succ mn mn1) ⇒ Expr r (b n) → Expr r ((a m :+ b n) mn1)
  
  Pair ∷ (Add m n mn) ⇒ Expr r (a m) → Expr r (b n) → Expr r ((a m :* b n) mn)
  ProjL ∷ (Add m n mn) ⇒ Expr r ((a m :* b n) mn) → Expr r (a m)
  ProjR ∷ (Add m n mn) ⇒ Expr r ((a m :* b n) mn) → Expr r (b n)
  
  Var ∷ r (a m) → Expr r (a m)
  Lam ∷ (Exp2Mul m n m2n) ⇒ (r (a m) → Expr r (b n)) → Expr r ((a m :→ b n) m2n)
  App ∷ (Exp2Mul m n m2n) ⇒ Expr r ((a m :→ b n) m2n) → Expr r (a m) → Expr r (b n)
  
  Case ∷ (Max m n mn, Succ mn mn1, 
          Exp2Mul mn1 p mn12p, Exp2Mul m p m2p, Exp2Mul n p n2p) ⇒
    Expr r ((a m :→ c p) m2p) →
    Expr r ((b n :→ c p) n2p) →
    Expr r (((a m :+ b n) mn1 :→ c p) mn12p)

{- Examples -}
  
-- Convenience synonym for a bit, and some constant bits
type Bit = (Unit D0 :+ Unit D0) D1
hi ∷ Expr r Bit
hi = InjR TT
lo ∷ Expr r Bit
lo = InjL TT

-- Simplest functional abstraction
tnot ∷ Expr r ((Bit :→ Bit) D2)
tnot = Case (Lam$ \_ -> hi) (Lam$ \_ -> lo)

-- Application works as expected
lo' ∷ Expr r Bit
lo' = tnot `App` hi

-- Our novelty is that we can express composition of terms
o ∷ (Exp2Mul m n mn, Exp2Mul n p np, Exp2Mul m p mp) ⇒
  Expr r ((:→) (b n) (c p) np) →
  Expr r ((:→) (a m) (b n) mn) → 
  Expr r ((:→) (a m) (c p) mp)
f `o` g = Lam$ \x -> f `App` (g `App` Var x)

-- For example, the composed-with-not combinator
tnoto ∷ (Exp2Mul m D1 m2, Exp2Mul m2 m2 m22) ⇒ Expr r (((a m :→ Bit) m2 :→ (a m :→ Bit) m2) m22)
tnoto = Lam$ \f -> tnot `o` Var f

-- We can even show an equivalence between curried and uncurried expressions
tand ∷ Expr r ((Bit :→ (Bit :→ Bit) D2) D4)
tand = Case
       (Lam$ \_ -> Lam$ \_ -> hi)
       (Lam$ \_ -> tnot)

-- Notice that uncurrying preserves the overall truth-table size
tand' ∷ Expr r (((Bit :* Bit) D2 :→ Bit) D4)
tand' = Lam$ \ab -> tand `App` (ProjL$ Var ab) `App` (ProjR$ Var ab)

-- Currying and uncurrying provided more generally
uncurry ∷ (Exp2Mul n p n2p, Exp2Mul m n2p m2n2p, Add m n mn, Exp2Mul mn p m2n2p) ⇒
  Expr r ((a m :→ (b n :→ c p) n2p) m2n2p) → Expr r (((a m :* b n) mn :→ c p) m2n2p)
uncurry f = Lam$ \ab -> f `App` (ProjL$ Var ab) `App` (ProjR$ Var ab)

curry ∷ (Exp2Mul n p n2p, Exp2Mul m n2p m2n2p, Add m n mn, Exp2Mul mn p m2n2p) ⇒
  Expr r (((a m :* b n) mn :→ c p) m2n2p) → Expr r ((a m :→ (b n :→ c p) n2p) m2n2p)
curry f = Lam$ \a -> Lam$ \b -> f `App` Pair (Var a) (Var b)

tand'' ∷ Expr r (((Bit :* Bit) D2 :→ Bit) D4)
tand'' = Circuital.uncurry tand

nand ∷ Expr r (((Bit :* Bit) D2 :→ Bit) D4)
nand = tnoto `App` tand'


-- Fixpoint
newtype EMu f m a = EIn { eout ∷ f (EMu f) m a }

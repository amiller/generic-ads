{-# LANGUAGE 
  UnicodeSyntax
  #-}

{- Andrew Miller   May 2013
   Aseem Rastogi
   Matthew Hammer

   An STLC that compiles to circuits. Express in the first order (no 
   HOAS/PHOAS) in Church style (meaning explicit Types are carried around
   with Terms)
-}

module CircuitValues where

import Data.Maybe

data Type =
    Unit
  | Type :→ Type
  | Type :+ Type
  | Type :* Type
    deriving (Show, Eq)

(-:>) = (:→)
         
data Term = Term Type Expr deriving (Show, Eq)
data Expr =
    Var String
  | Lam String Term
  | App Term Term
  | Pair Term Term
  | ProjL Term
  | ProjR Term
  | Case Term Term Term
  | InjL Term
  | InjR Term
  | TT
    deriving (Show, Eq)

nBits ∷ Type → Int
nBits Unit = 0
nBits (a :+ b) = 1 + max (nBits a) (nBits b)
nBits (a :* b) = nBits a + nBits b
nBits (a :→ b) = 2^(nBits a) * nBits b


-- Examples

tBit = Unit :+ Unit

lo = Term tBit $ InjL (Term Unit TT)
hi = Term tBit $ InjR (Term Unit TT)

tnot = Term (tBit :→ tBit) $ Lam "x" $ Term tBit $ Case (Term tBit $ Var "x") (Term (Unit :→ tBit) $ Lam "_" hi) (Term (Unit :→ tBit) $ Lam "_" lo)
tand = Term (tBit :→ tBit :→ tBit) $ Lam "a" $ Term (tBit :→ tBit) $ Lam "b" $ Term tBit $ Case (Term tBit $ Var "a") (Term (Unit :→ tBit) $ Lam "_" lo) (Term (Unit :→ tBit) $ Lam "_" $ Term tBit $ Var "b")
--tor = Lam "a" $ Lam "b" $ Case (Var "a") (Lam "_" $ Var "b") (Lam "_" hi)
--tnand = Lam "a" $ Lam "b" $ tnot `App` (tand `App` Var "a" `App` Var "b")
--tcurry = Lam "f" $ Lam "a" $ Lam "b" $ Var "f" `App` Pair (Var "a") (Var "b")


data Value = Value Type VExpr deriving Show

data VExpr =
    VUnit ()
  | VArr (Value → Value)
  | VPair (Value, Value)
  | VSum (Either Value Value)
instance Show VExpr where
  show (VUnit ()) = show ()
  show (VPair a) = show a
  show (VSum a) = show a
  show (VArr _) = "(func)"


denote ∷ [(String, Value)] → Term → Value
denote g (Term Unit TT) = Value Unit $ VUnit ()
denote g (Term t@(_ :+ _) (InjL a)) = Value t $ VSum (Left  (denote g a))
denote g (Term t@(_ :+ _) (InjR a)) = Value t $ VSum (Right (denote g a))
denote g (Term t@(_) (Case x a b)) = case (denote g x) of
    (Value _ (VSum (Left x))) → (case (denote g a) of (Value _ (VArr f)) → f x)
    (Value _ (VSum (Right x))) → (case (denote g b) of (Value _ (VArr f)) → f x)
denote g (Term t@(_ :* _) (Pair a b)) = Value t $ VPair (denote g a, denote g b)
denote g (Term t@(_) (ProjL ab)) = case denote g ab of (Value _ (VPair (a, _))) -> a
denote g (Term t@(_) (ProjR ab)) = case denote g ab of (Value _ (VPair (_, b))) -> b
denote g (Term t@(_ :→ _) (Lam v f)) = Value t $ VArr (\x -> denote ((v,x) : g) f)
denote g (Term (_) (Var v)) = fromJust $ lookup v g
denote g (Term (_) (App f x)) = case (denote g f) of (Value _ (VArr f)) -> f (denote g x)


type Wire = Int
data Gate = 
    And Wire Wire Wire
  | Not Wire Wire
  | Or Wire Wire Wire
  | Hi Wire
  | Lo Wire
    deriving Show

type Circuit = [Gate]
type WireCon = [(String, Wire)]

-- extend l n returns a list of length at least n, padding with Falses
extend ∷ Int → [Bool] → [Bool]
extend n l = l ++ map (const False) [1..n-(length l)]



-- Translate terms to bit assignments
encode ∷ Value → [Bool]
encode (Value Unit (VUnit ())) = []
encode (Value t@(_ :+ _) (VSum (Left x))) = extend (nBits t) $ [False] ++ encode x
encode (Value t@(_ :+ _) (VSum (Right x))) = extend (nBits t) $ [True]  ++ encode x
encode (Value (a :* b) (VPair (x, y))) = encode x ++ encode y
encode (Value (_ :→ _) (VArr f)) = undefined

{-
encode ∷ [(String, Value)] → Term → [Bool]
encode g (Term Unit TT) = []
encode g (Term t@(_ :+ _) (InjL x)) = extend (nBits t) $ [False] ++ encode g x
encode g (Term t@(_ :+ _) (InjR x)) = extend (nBits t) $ [True]  ++ encode g x
encode g (Term t@(_) (Case x a b))  = let flag : body = encode g x in
  extend (nBits t) (if flag then encode g a else encode g b)
encode g (Term (a :* b) (Pair x y)) = encode g x ++ encode g y
encode g (Term (_) (ProjL xy@(Term (t :* _) _))) = take (nBits t) (encode g xy)
encode g (Term (_) (ProjR xy@(Term (t :* _) _))) = drop (nBits t) (encode g xy)
encode g (Term (_ :→ _) (Lam v f)) = undefined
encode g (Term (_) (Var v)) = fromJust $ lookup v g
encode g (Term (_) (App f x)) = undefined
-}

-- Compile terms to circuits
--compile ∷ WireCon → Int → Term → Circuit
--compile g n (Term Unit TT) = []

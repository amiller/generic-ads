{-# LANGUAGE 
  UnicodeSyntax, FlexibleInstances, FlexibleContexts, UndecidableInstances
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
import Control.Monad.State

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


-- Evaluate to normal form (our calculus so far is strongly normalizing)
tonf ∷ [(String, Term)] → Term → Term
tonf g (Term Unit TT)               = Term Unit TT
tonf g (Term t@(_ :+ _) (InjL x))   = Term t (InjL (tonf g x))
tonf g (Term t@(_ :+ _) (InjR x))   = Term t (InjR (tonf g x))
tonf g (Term t@(_ :* _) (Pair x y)) = Term t (Pair (tonf g x) (tonf g y))
tonf g (Term t@(_ :→ _) (Lam v f))  = Term t (Lam v f)
tonf g (Term t (App f x)) = let Term t (Lam v f) = tonf g f in 
  tonf ((v, tonf g x) : g) f
tonf g (Term t (Var v)) = fromJust $ lookup v g
tonf g (Term t (Case x a b)) = case tonf g x of
  (Term (_ :+ _) (InjL x)) → tonf g (Term t (a `App` x))
  (Term (_ :+ _) (InjR x)) → tonf g (Term t (b `App` x))
tonf g (Term t (ProjL xy)) = let (Term (_ :* _) (Pair x _)) = tonf g xy in x
tonf g (Term t (ProjR xy)) = let (Term (_ :* _) (Pair _ y)) = tonf g xy in y


-- extend l n returns a list of length at least n, padding with Falses
extend ∷ Int → [Bool] → [Bool]
extend n l = l ++ map (const False) [1..n-(length l)]

-- all possible bit assignments
enumerate :: Int -> [a] -> [[a]]
enumerate 0 _  = [[]]
enumerate n xs = join [fmap (z:) $ enumerate (n-1) xs | z ← xs]

-- Enumerate the representable normal-form terms for any type
enumNF ∷ Type → [Term]
enumNF Unit = [Term Unit TT]
enumNF t@(a :* b) = join [map (Term t . Pair x) $ enumNF b | x <- enumNF a]
enumNF t@(a :+ b) = map (Term t . InjL) (enumNF a) ++
                    map (Term t . InjR) (enumNF b)
enumNF t@(a :→ b) = 
  let allAs = enumNF a in
  let allBmaps = enumerate (length allAs) (enumNF b) in
  undefined -- associate inputs with outputs?

-- Translate terms to bit assignments
encode ∷ [(String, Term)] → Term → [Bool]
encode g (Term Unit TT) = []
encode g (Term t@(_ :+ _) (InjL x)) = extend (nBits t) $ [False] ++ encode g x
encode g (Term t@(_ :+ _) (InjR x)) = extend (nBits t) $ [True]  ++ encode g x
encode g (Term t@(a :* b) (Pair x y)) = encode g x ++ encode g y
-- Bit-encoding for a lambda means applying 
encode g (Term t@(a :→ _) (Lam v f)) = extend (nBits t) $ join $ map (\x -> encode ((v,x):g) f) (enumNF a)
-- Bit-encoding for non-normalized terms begins by normalizing them
encode g t@(Term (_) (Var v))      = encode g (tonf g t)
encode g t@(Term (_) (App _ _))    = encode g (tonf g t)
encode g t@(Term (_) (Case _ _ _)) = encode g (tonf g t)
encode g t@(Term (_) (ProjL _))    = encode g (tonf g t)
encode g t@(Term (_) (ProjR _))    = encode g (tonf g t)


-- Compile terms to circuits
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

class Monad m ⇒ MonadWire m where
  fresh ∷ m Wire
  place ∷ (Wire → Gate) → m Wire

instance MonadState (Int, [Gate]) m ⇒ MonadWire m where
  fresh = do { (x,c) <- get; put (x+1, c); return x }
  place gate = do { (x,c) <- get; put (x+1, (gate x) : c); return x}

runWire ∷ Term → Circuit
runWire t = reverse . snd $ execState (compile [] (tonf [] t)) (0,[])

-- Doesn't go to nf first
runWire' ∷ Term → Circuit
runWire' t = reverse . snd $ execState (compileClosed [] t) (0,[])

compileClosed ∷ MonadWire m ⇒ [(String, [Wire])] → Term → m [Wire]
compileClosed g (Term (a :→ b) (Lam v f)) = do
  inputs ← mapM (const fresh) [1..nBits a]
  compile ((v, inputs) : g) f
compileClosed g t = compile g t



compile ∷ MonadWire m ⇒ [(String, [Wire])] → Term → m [Wire]
compile g (Term Unit TT) = return []
compile g (Term t@(a :+ _) (InjL x)) = do
  flag <- place Lo
  body <- compile g x
  pad <- mapM (const$ place Lo) [1..nBits t - nBits a - 1]
  return$ flag : body ++ pad
compile g (Term t@(_ :+ b) (InjR x)) = do
  flag <- place Hi
  body <- compile g x
  pad <- mapM (const$ place Lo) [1..nBits t - nBits b - 1]
  return$ flag : body ++ pad
compile g (Term _ (Pair x y)) = sequence [compile g x, compile g y] >>= return . join
compile g (Term (a :* _) (ProjL xy)) = compile g xy >>= return . take (nBits a)
compile g (Term (a :* _) (ProjR xy)) = compile g xy >>= return . drop (nBits a)
compile g (Term t (Var v)) = return $ fromJust $ lookup v g
-- find the bit encoding of this function and assign constant to this many wires
compile g (Term (a :→ b) (Lam v f)) = (>>= return . join) $ mapM (\x -> compile [] x >>= \x' -> compile ((v,x'):g) f) (enumNF a)
compile g (Term t (App f x)) = undefined -- evaluate x as a multiplexer


ex0 = runWire (Term (tBit :* tBit) (Pair lo hi))
ex1 = runWire (Term (tBit :+ Unit) (InjL lo))
ex2 = runWire (Term (tBit :+ Unit) (InjR (Term Unit TT)))

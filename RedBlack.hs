{-# LANGUAGE 
  GADTs, FlexibleInstances, FlexibleContexts,
  StandaloneDeriving, TypeOperators, UndecidableInstances,
  MultiParamTypeClasses, DeriveFunctor, Rank2Types,
  GeneralizedNewtypeDeriving, ScopedTypeVariables, UnicodeSyntax,
  DeriveGeneric, TypeFamilies, ConstraintKinds, DeriveTraversable,
  DeriveFoldable
 #-}

module RedBlack where

import Control.Applicative hiding (some)
import Control.Monad
import Data.Maybe
import Data.Hashable
import Data.Traversable
import Data.Foldable
import Text.Printf
--import Tree2Dot
import Merkle
import Prelude hiding ((**))

import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
--import Data.Serialize
--import Data.Serialize.Derive (derivePut, deriveGet)   -- dependency conflict, but I should use this
import Generics.Regular hiding (R)
import Unsafe.Coerce    -- Gasp! But edkmett said it not as bad as it sounds...

-- Red-Black binary tree

type A = String
type V = String
data Col = R | B

data ExprF r where
  Tip :: ExprF r
  Bin :: Col → r → (A,Maybe V) → r → ExprF r
 deriving (Functor, Foldable, Traversable)

type Auth = AuthT ExprF
type Term a = (EDSL term, AuthDSL ExprF term) => term a

{-
 Here are some functions defined on these data structures:
 -}

-- 1. In-term tree constructors
tTip ∷ Term (Auth)
tTip = auth Tip

tBin ∷ Term (Base Col :→ Auth :→ Base (A,Maybe V) :→ Auth :→ Auth)
tBin = lamU$ \c -> lam$ \l -> lamU$ \a -> lam$ \r -> auth (Bin c l a r)

-- 2. Lookup function O(log N)
tLookup ∷ Term (Base A :→ Auth :→ Base (Maybe V))
tLookup = lamU look where
  look a = look'' where
    look'' = lamA look' where
      look' Tip = unit Nothing
      look' (Bin _ _ (a',Just v) _) = if a == a' then unit (Just v) else unit Nothing
      look' (Bin _ l (a',_) r) =
        if a <= a' then look'' `app` l 
        else            look'' `app` r


-- 3. Insert function (with balancing rules)

{- Writing this code is like having teeth pulled. No one enjoys implementing
   the RedBlack tree balancing algrithms. Especially since for my interests I
   want a RedBlack+ tree (dictionary with values stored just at the leaves).

   This would be much easier if I had a front-end "sugared" language that would
   compile pattern matches for me.
-}

tBalanceL ∷ Term (Auth :→ Auth)
tBalanceL = lamA$ tBalanceL'
tBalanceL' t@(Bin B l a r) = lamA bal' `app` l where
  bal' (Bin R l' a' r') = lamA bal'' `app` l' where
    bal'' (Bin R l'' a'' r'') = auth$Bin R (auth$Bin B l'' a'' r'') a' (auth$Bin B r' a r)
    bal'' _ = lamA bal''' `app` r'
    bal''' (Bin R l'' a'' r'') = auth$Bin R (auth$Bin B l' a' l'') a'' (auth$Bin B r'' a r)
    bal''' _ = auth t
  bal' _ = auth t
tBalanceL' t = auth t

tBalanceR ∷ Term (Auth :→ Auth)
tBalanceR = lamA$ tBalanceR' 
tBalanceR' t@(Bin B l a r) = lamA bal' `app` r where
  bal' (Bin R l' a' r') = lamA bal'' `app` l' where
    bal'' (Bin R l'' a'' r'') = auth$Bin R (auth$Bin B l a l'') a'' (auth$Bin B r'' a' r')
    bal'' _ = lamA bal''' `app` r'
    bal''' (Bin R l'' a'' r'') = auth$Bin R (auth$Bin B l a l') a' (auth$Bin B l'' a'' r'')
    bal''' _ = auth t
  bal' _ = auth t
tBalanceR' t = auth t

tInsert ∷ Term (Base A :→ Base V :→ Auth :→ Auth)
tInsert = lamU$ \a → lamU$ \v → ins a v where
  ins a v = lamA black `o` ins'' where
    ins'' = lamA ins' where
      ins' Tip = auth (Bin B (auth$Tip) (a,Just v) (auth$Tip))
      ins' n@(Bin c l (a',Just v) r) = case compare a a' of
        EQ → error "duplicate insert"
        LT → auth$ Bin R (ins' Tip) (a ,Nothing) (auth n)
        GT → auth$ Bin R (auth n)   (a',Nothing) (ins' Tip)
      ins' (Bin c l av@(a',_) r) = case compare a a' of
        EQ → error "duplicate insert"
        LT → tBalanceL `app` (auth$ Bin c (ins'' `app` l) av r)
        GT → tBalanceR `app` (auth$Bin c l av (ins'' `app` r))
  black (Bin _ l a r) = auth$ Bin B l a r


  
{- 4. The complexity increase from "lookup" to "insert" is roughly the same as
  as the increase from "insert" to "delete". We need to define two wrappers for
  the balancing operation that perform further more operations.
-}

tUnbalancedL ∷ Term (Auth :→ Auth :* Base Bool)
tUnbalancedL = lamA tUnbalancedL'
tUnbalancedL' t@(Bin c l a r) = lamA bal' `app` l where
  bal' (Bin B l' a' r') = tBalanceL `app` (auth$Bin B (auth$Bin R l' a' r') a r) ** unit (c == B)
  bal' (Bin R l' a' r') = (auth$Bin B l' a' (tBalanceL `app` (auth$Bin B (lamA red `app` r') a r))) ** unit False where
  red (Bin _ l a r) = auth$ Bin R l a r
  
tUnbalancedR ∷ Term (Auth :→ Auth :* Base Bool)
tUnbalancedR = lamA tUnbalancedR'
tUnbalancedR' t@(Bin c l a r) = lamA bal' `app` r where
  bal' (Bin B l' a' r') = tBalanceR `app` (auth$Bin B l a (auth$Bin R l' a' r')) ** unit (c == B)
  bal' (Bin R l' a' r') = (auth$Bin B (tBalanceR `app` (auth$Bin B l a (lamA red `app` l'))) a' r') ** unit False where
  red (Bin _ l a r) = auth$ Bin R l a r

tDelete ∷ Term (Base A :→ Auth :→ Auth)
tDelete = lamU del where
  del a = lamA black `o` tFst `o` lamA del' where
    del' Tip = error "delete called on empty tree"
    del' (Bin _ _ (a',Just _) _) = if a == a' then auth Tip ** unit (True, Nothing)
                                   else error ("delete: element not found: " ++ show a)
    
    -- a <= a'
    del' (Bin c l (a',Nothing) r) | a <= a' = lam del'' `o` lamA del' `app` l where
      del'' ldm = tif (lamA empty `app` tfst ldm)
                  (r ** unit (c == B, Nothing))
                  (lamU del''' `app` tsnd ldm) where
        del''' (True, m) = withM Nothing $ tUnbalancedR `app` t m
        del''' (False,  m) = t m ** unit(False, Nothing)
        t (Just m) | a == a' = auth$Bin c (tfst ldm) (m, Nothing) r
        t _ | a == a' = error "failed assertion: m is not None"
        t _ | otherwise = auth$Bin c (tfst ldm) (a',Nothing) r
    
    -- a > a'
    del' (Bin c l (a',Nothing) r) | otherwise = lam del'' `o` lamA del' `app` r where
      del'' rdm = tif (lamA empty `app` tfst rdm)
                  (l ** unit (c == B, Just a'))
                  (lamU del''' `app` tsnd rdm) where
        del''' (True, m) = withM m $ tUnbalancedL `app` t
        del''' (False,  m) = t ** unit(False, m)
        t = auth$Bin c l (a',Nothing) (tfst rdm)

  withM m t = (lamU$ \b → tfst t ** unit (b, m)) `app` tsnd t
  empty Tip = unit True
  empty _ = unit False
  black (Bin _ l a r) = auth$ Bin B l a r
  black Tip = auth$ Tip




-- 5. Examples

tlookup a = tLookup `app` unit a
tlookup' a t = tlookup a `app` t
ins a = tInsert `app` unit a `app` unit a
ins' a t = ins a `app` t
del a = tDelete `app` unit a
del' a t = del a `app` t

t0 = unISem' $ ins' "a" $ ins' "b" $ ins' "c" $ ins' "d" tTip


-- Check serialization isomorphism
fromRight (Right a) = a
t0check' = runGet get . runPut $ put t0 :: Fix ExprF
t0check = decode . encode $ t0 :: Fix ExprF




{- Here is all of the boiler plate that *should* be derived generically, especially
   if I make use of Regular or Multirec
 -}

-- Serialization

{- It's necessary to ensure that "put" and "get" form an isomorphism -}

instance Binary (Fix ExprF) where
  put (In t) = do
    put $ fmap (const (K ())) t
    Data.Traversable.mapM (\x -> put x >> return x) t
    return ()
  get = get >>= g where
    g :: ExprF () -> Get (Fix ExprF)
    g t = Data.Traversable.mapM (const get) t >>= return . In

instance Binary Col where
  put R = putWord8 0
  put B = putWord8 1
  get = getWord8 >>= return . g where
    g 0 = R
    g 1 = B

-- id = runGet . get . runPut . put

deriving instance Show Col
deriving instance Eq Col
deriving instance (Show r) ⇒ Show (ExprF r)

instance (Binary r) ⇒ Binary (ExprF r) where
  put Tip = putWord8 0
  put (Bin c l a r) = putWord8 1 >> put c >> put l >> put a >> put r
  get = getWord8 >>= g where
    g 0 = return . unsafeCoerce $ Tip
    g 1 = do
      c <- get
      l <- get ∷ Get r
      a <- get
      r <- get ∷ Get r
      return . unsafeCoerce $ (Bin c l a r)

-- Hashing
instance Hashable Col where
  hashWithSalt _ R = hash "R"
  hashWithSalt _ B = hash "B"

instance HHashable ExprF where
  hhash Tip = hash "Tip"
  hhash (Bin c l a r) = hash ("Bin", c, l, a, r)


-- Convenience functions for common denotations
asP ∷ MSem' ExprF (Fix (Annot ExprF)) (Prover ExprF) a → Prv ExprF a
asP = unMSem'

asV ∷ MSem' ExprF D (Verifier ExprF) a → Vrf ExprF a
asV = unMSem'

asIO ∷ MSem' ExprF (Fix ExprF) IO a → IO (MSem ExprF (Fix ExprF) IO a)
asIO = unMSem'


-- Somewhat general purpose graph library

{-
rbpToRose :: Fix ExprF Tree → Rose Node
rbpToRose = unK . hcata alg where
  alg :: ExprF (K (Rose Node)) :~> K (Rose Node)
  alg Tip                 = K $ leaf Point
  alg (Bin c (K l) a (K r)) = K $ Branch (Node (col c) (shw a)) [l, r]
    where
      shw (a, Nothing) = a
      shw (a, Just v) = a ++ ":" ++ v
      col B = "black"
      col R = "red"

rbpToRose' :: Fix (Annot ExprF) Tree → Rose Node
rbpToRose' = unK . hfst . hcata ((alg . hfst &&&& hsnd) . unAnn) where
  alg :: ExprF (K (Rose Node) :*: K D) :~> K (Rose Node)
--  alg (Ann (Zero :*: K d)) = K (leaf Point) :*: K d
--  alg (Ann (Succ (K n :*: K d) :*: _)) = K (Branch (Node "black" ("S||"++show d)) [n]) :*: K d
  alg Tip = K $ leaf Point
  alg (Bin (K l :*: K l') a (K r :*: K r')) = 
    K $ Branch (Node "black" (printf "%0x || %c || %x" (mod l' 65536) a (mod r' 65536))) [l, r]
-}
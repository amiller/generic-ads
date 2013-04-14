{-# LANGUAGE 
  GADTs, FlexibleInstances, FlexibleContexts,
  StandaloneDeriving, TypeOperators, UndecidableInstances,
  MultiParamTypeClasses, DeriveFunctor, Rank2Types,
  GeneralizedNewtypeDeriving, ScopedTypeVariables, UnicodeSyntax,
  DeriveGeneric, TypeFamilies, ConstraintKinds
 #-}

module RedBlack where

import Control.Applicative hiding (some)
import Control.Monad
import Data.Maybe
import Data.Hashable
import Text.Printf
import Tree2Dot
import Merkle
import Prelude hiding ((**))

import Data.Serialize
--import Data.Serialize.Derive (derivePut, deriveGet)   -- dependency conflict, but I should use this
import GHC.Generics (Generic)
import Unsafe.Coerce    -- Gasp! But edkmett said it not as bad as it sounds...

-- Red-Black binary tree

type A = String
type V = String
data Col = R | B

{-
  auth Tree := Tip | Bin (R+B) Tree (A,?V) Tree
 -}

data Tree
data Chain

data ExprF ∷ (* → *) → * → * where
  Tip :: ExprF r Tree
  Bin :: Col → r Tree → (A,Maybe V) → r Tree → ExprF r Tree
  Nil :: ExprF r Chain
  Cons :: r Tree → r Chain → ExprF r Chain

type Auth a = AuthT ExprF a
type Term a = (EDSL term, AuthDSL ExprF term) => term a


{-
 Here are some functions defined on these data structures:
 -}

-- 1. In-term tree constructors
tTip ∷ Term (Auth Tree)
tTip = auth Tip

tBin ∷ Term (Base Col :→ Auth Tree :→ Base (A,Maybe V) :→ Auth Tree :→ Auth Tree)
tBin = lamU$ \c -> lam$ \l -> lamU$ \a -> lam$ \r -> auth (Bin c (at l) a (at r))

-- 2. Lookup function O(log N)
tLookup ∷ Term (Base A :→ Auth Tree :→ Base (Maybe V))
tLookup = lamU look where
  look a = look'' where
    look'' = lamA look' where
      look' Tip = unit Nothing
      look' (Bin _ _ (a',Just v) _) = if a == a' then unit (Just v) else unit Nothing
      look' (Bin _ l (a',_) r) =
        if a <= a' then look'' `app` unA l 
        else            look'' `app` unA r


-- 3. Insert function (with balancing rules)

{- Writing this code is like having teeth pulled. No one enjoys implementing
   the RedBlack tree balancing algrithms. Especially since for my interests I
   want a RedBlack+ tree (dictionary with values stored just at the leaves).

   This would be much easier if I had a front-end "sugared" language that would
   compile pattern matches for me.
-}

tBalanceL ∷ Term (Auth Tree :→ Auth Tree)
tBalanceL = lamA$ tBalanceL'
tBalanceL' t@(Bin B l a r) = lamA bal' `app` unA l where
  bal' (Bin R l' a' r') = lamA bal'' `app` unA l' where
    bal'' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l'' a'' r'') a' (at.auth$Bin B r' a r)
    bal'' _ = lamA bal''' `app` unA r'
    bal''' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l' a' l'') a'' (at.auth$Bin B r'' a r)
    bal''' _ = auth t
  bal' _ = auth t
tBalanceL' t = auth t

tBalanceR ∷ Term (Auth Tree :→ Auth Tree)
tBalanceR = lamA$ tBalanceR' 
tBalanceR' t@(Bin B l a r) = lamA bal' `app` unA r where
  bal' (Bin R l' a' r') = lamA bal'' `app` unA l' where
    bal'' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l a l'') a'' (at.auth$Bin B r'' a' r')
    bal'' _ = lamA bal''' `app` unA r'
    bal''' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l a l') a' (at.auth$Bin B l'' a'' r'')
    bal''' _ = auth t
  bal' _ = auth t
tBalanceR' t = auth t

tInsert ∷ Term (Base A :→ Base V :→ Auth Tree :→ Auth Tree)
tInsert = lamU$ \a → lamU$ \v → ins a v where
  ins a v = lamA black `o` ins'' where
    ins'' = lamA ins' where
      ins' Tip = auth (Bin B (at.auth$Tip) (a,Just v) (at.auth$Tip))
      ins' n@(Bin c l (a',Just v) r) = case compare a a' of
        EQ → error "duplicate insert"
        LT → auth$ Bin R (at$ins' Tip) (a ,Nothing) (at.auth$n)
        GT → auth$ Bin R (at.auth$n)   (a',Nothing) (at$ins' Tip)
      ins' (Bin c l av@(a',_) r) = case compare a a' of
        EQ → error "duplicate insert"
        LT → tBalanceL `app` (auth$ Bin c (at$ins'' `app` unA l) av r)
        GT → tBalanceR `app` (auth$Bin c l av (at$ins'' `app` unA r))
  black (Bin _ l a r) = auth$ Bin B l a r


  
{- 4. The complexity increase from "lookup" to "insert" is roughly the same as
  as the increase from "insert" to "delete". We need to define two wrappers for
  the balancing operation that perform further more operations.
-}
  
tUnbalancedL ∷ Term (Auth Tree :→ Auth Tree :* Base Bool)
tUnbalancedL = lamA tUnbalancedL'
tUnbalancedL' t@(Bin c l a r) = lamA bal' `app` unA l where
  bal' (Bin B l' a' r') = tBalanceL `app` (auth$Bin B (at.auth$Bin R l' a' r') a r) ** unit (c == B)
  bal' (Bin R l' a' r') = (auth$Bin B l' a' (at$tBalanceL `app` (auth$Bin B (at$lamA red `app` unA r') a r))) ** unit False where
  red (Bin _ l a r) = auth$ Bin R l a r
  
tUnbalancedR ∷ Term (Auth Tree :→ Auth Tree :* Base Bool)
tUnbalancedR = lamA tUnbalancedR'
tUnbalancedR' t@(Bin c l a r) = lamA bal' `app` unA r where
  bal' (Bin B l' a' r') = tBalanceR `app` (auth$Bin B l a (at.auth$Bin R l' a' r')) ** unit (c == B)
  bal' (Bin R l' a' r') = (auth$Bin B (at$tBalanceR `app` (auth$Bin B l a (at$lamA red `app` unA l'))) a' r') ** unit False where
  red (Bin _ l a r) = auth$ Bin R l a r
  
tDelete ∷ Term (Base A :→ Auth Tree :→ Auth Tree)
tDelete = lamU del where
  del a = lamA black `o` tFst `o` lamA del' where
    del' Tip = error "delete called on empty tree"
    del' (Bin _ _ (a',Just _) _) = if a == a' then auth Tip ** unit (True, Nothing)
                                   else error ("delete: element not found: " ++ show a)
    
    -- a <= a'
    del' (Bin c l (a',Nothing) r) | a <= a' = lam del'' `o` lamA del' `app` unA l where
      del'' ldm = tif (lamA empty `app` tfst ldm)
                  (unA r ** unit (c == B, Nothing))
                  (lamU del''' `app` tsnd ldm) where
        del''' (True, m) = withM Nothing $ tUnbalancedR `app` t m
        del''' (False,  m) = t m ** unit(False, Nothing)
        t (Just m) | a == a' = auth$Bin c (at$tfst ldm) (m, Nothing) r
        t _ | a == a' = error "failed assertion: m is not None"
        t _ | otherwise = auth$Bin c (at$tfst ldm) (a',Nothing) r
    
    -- a > a'
    del' (Bin c l (a',Nothing) r) | otherwise = lam del'' `o` lamA del' `app` unA r where
      del'' rdm = tif (lamA empty `app` tfst rdm)
                  (unA l ** unit (c == B, Just a'))
                  (lamU del''' `app` tsnd rdm) where
        del''' (True, m) = withM m $ tUnbalancedL `app` t
        del''' (False,  m) = t ** unit(False, m)
        t = auth$Bin c l (a',Nothing) (at$tfst rdm)

  withM m t = (lamU$ \b → tfst t ** unit (b, m)) `app` tsnd t
  empty Tip = unit True
  empty _ = unit False
  black (Bin _ l a r) = auth$ Bin B l a r
  black Tip = auth$ Tip




-- 5. Examples

ins a = tInsert `app` unit a `app` unit a
ins' a t = tInsert `app` unit a `app` unit a `app` t
del' a t = tDelete `app` unit a `app` t

t0 = unISem' $ ins' "a" $ ins' "b" $ ins' "c" $ ins' "d" tTip

-- Check serialization isomorphism
fromRight (Right a) = a
t0check = fromRight . runGet get . runPut $ put t0 :: HFix ExprF Tree




{- Here is all of the boiler plate that *should* be derived generically, especially
   if I switch to "Multirec"
 -}

{- It's necessary to ensure that "put" and "get" form an isomorphism -}

--instance (HFunctor f, Serialize (f (K ()) a)) ⇒ Serialize (HFix f a) where
instance Serialize (HFix ExprF a) where
  put (HFix t) = do
    put $ hfmap (const (K ())) t
    hmapM (\x -> put x >> return x) t
    return ()
  get = get >>= g where
    g :: ExprF (K ()) a -> Get (HFix ExprF a)
    g t = hmapM (const get) t >>= return . HFix

instance Serialize Col where
  put R = putWord8 0
  put B = putWord8 1
  get = getWord8 >>= return . g where
    g 0 = R
    g 1 = B

-- id = runGet . get . runPut . put

instance Show Tree
instance Show Chain
deriving instance Show Col
deriving instance Eq Col
deriving instance (Show (r Tree), Show (r Chain)) ⇒ Show (ExprF r a)

instance (Serialize (r Tree), Serialize (r Chain)) ⇒ Serialize (ExprF r a) where
  put Tip = putWord8 0
  put (Bin c l a r) = putWord8 1 >> put c >> put l >> put a >> put r
  put Nil = putWord8 0
  put (Cons x xs) = putWord8 1 >> put x >> put xs
  -- get fails for Chain?
  get = getWord8 >>= g where
    g 0 = return . unsafeCoerce $ Tip
    g 1 = do
      c <- get
      l <- get ∷ Get (r Tree)
      a <- get
      r <- get ∷ Get (r Tree)
      return . unsafeCoerce $ (Bin c l a r)

-- Serialization
instance Show (Some (HFix ExprF)) where show = some show
instance Show (Some (ExprF (K D))) where show = some show
instance Eq (Some (ExprF (K D))) where (==) = (==)
instance Read (Some (ExprF (K D))) where readsPrec = readsPrec
instance Serialize (Some (ExprF (K D))) where
  put = some put
  get = get >>= return . Some

-- Hashing
instance Hashable Col where
  hash R = hash "R"
  hash B = hash "B"

instance HHashable ExprF where
  hhash Tip = K $ hash "Tip"
  hhash (Bin c (K l) a (K r)) = K $ hash ("Bin", c, l, a, r)
  hhash Nil = K $ hash "Nil"
  hhash (Cons (K x) (K xs)) = K $ hash ("Cons", x, xs)


-- Convenience functions for common denotations
asP ∷ MSem' ExprF (HFix (Annot ExprF)) (Prover ExprF) a → Prv ExprF a
asP = unMSem'

asV ∷ MSem' ExprF (K D) (Verifier ExprF) a → Vrf ExprF a
asV = unMSem'

asIO ∷ MSem' ExprF (HFix ExprF) IO a → IO (MSem ExprF (HFix ExprF) IO a)
asIO = unMSem'



-- HFunctor (like in multirec)
instance HFunctor ExprF where
  hfmap f Tip = Tip
  hfmap f (Bin c l a r) = Bin c (f l) a (f r)
  htraverse f Tip = pure Tip
  htraverse f (Bin c l a r) = Bin <$> pure c <*> (f l) <*> pure a <*> (f r)


-- Somewhat general purpose graph library
rbpToRose :: HFix ExprF Tree → Rose Node
rbpToRose = unK . hcata alg where
  alg :: ExprF (K (Rose Node)) :~> K (Rose Node)
  alg Tip                 = K $ leaf Point
  alg (Bin c (K l) a (K r)) = K $ Branch (Node (col c) (shw a)) [l, r]
    where
      shw (a, Nothing) = a
      shw (a, Just v) = a ++ ":" ++ v
      col B = "black"
      col R = "red"

{-
rbpToRose' :: HFix (Annot ExprF) Tree → Rose Node
rbpToRose' = unK . hfst . hcata ((alg . hfst &&&& hsnd) . unAnn) where
  alg :: ExprF (K (Rose Node) :*: K D) :~> K (Rose Node)
--  alg (Ann (Zero :*: K d)) = K (leaf Point) :*: K d
--  alg (Ann (Succ (K n :*: K d) :*: _)) = K (Branch (Node "black" ("S||"++show d)) [n]) :*: K d
  alg Tip = K $ leaf Point
  alg (Bin (K l :*: K l') a (K r :*: K r')) = 
    K $ Branch (Node "black" (printf "%0x || %c || %x" (mod l' 65536) a (mod r' 65536))) [l, r]
-}

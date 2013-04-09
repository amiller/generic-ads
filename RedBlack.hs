{-# LANGUAGE 
  GADTs, FlexibleInstances, FlexibleContexts, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses, DeriveFunctor, KindSignatures,
  GeneralizedNewtypeDeriving, ScopedTypeVariables, UnicodeSyntax
 #-}

module RedBlack where

import Control.Applicative hiding (some)
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Control.Monad.Identity
import Control.Monad.Error
import Data.Maybe
import Data.Hashable
import Text.Printf
import Tree2Dot
import Merkle
import Prelude hiding ((**))

import System.Random
import Data.Array.IO

-- Red-Black binary tree

type A = Char
type V = String
data Col = R | B deriving (Show, Eq)
data Tree

deriving instance Show Tree

data ExprF ∷ (* → *) → * → * where
  Tip :: ExprF r Tree
  Bin :: Col → r Tree -> (A,Maybe V) -> r Tree -> ExprF r Tree

type Auth a = AuthT ExprF a

deriving instance Show (r a) ⇒ Show (ExprF r a)
instance Show (Some (HFix ExprF)) where show = some show
instance Show (Some (ExprF (K D))) where show = some show

instance HFunctor ExprF where
  hfmap f Tip = Tip
  hfmap f (Bin c l a r) = Bin c (f l) a (f r)

instance HTraversable ExprF where
  htraverse f Tip = pure Tip
  htraverse f (Bin c l a r) = Bin <$> pure c <*> (f l) <*> pure a <*> (f r)

instance Hashable Col where
  hash R = hash "R"
  hash B = hash "B"

instance HHashable ExprF where
  hhash Tip = K $ hash "Tip"
  hhash (Bin c (K l) a (K r)) = K $ hash ("Bin", c, l, a, r)


tTip ∷ (EDSL term, AuthDSL ExprF term) => term (Auth Tree)
tTip = auth Tip

tBin ∷ (EDSL term, AuthDSL ExprF term) => 
  term (BaseT Col :→ Auth Tree :→ BaseT (A,Maybe V) :→ Auth Tree :→ Auth Tree)
tBin = lamU$ \c -> lam$ \l -> lamU$ \a -> lam$ \r -> auth (Bin c (at l) a (at r))

tLookup ∷ (EDSL term, AuthDSL ExprF term) ⇒ term (BaseT A :→ Auth Tree :→ BaseT (Maybe V))
tLookup = lamU look where
  look a = look'' where
    look'' = lamA look' where
      look' Tip = unit Nothing
      look' (Bin _ _ (a',Just v) _) = if a == a' then unit (Just v) else unit Nothing
      look' (Bin _ l (a',_) r) =
        if a <= a' then look'' `app` unA l 
        else            look'' `app` unA r

-- Jeez. I wish I had a pattern match compiler
tBalanceL ∷ (EDSL term, AuthDSL ExprF term) ⇒ ExprF (ATerm term ExprF) Tree → term (Auth Tree)
tBalanceL t@(Bin B l a r) = lamA bal' `app` unA l where
  bal' (Bin R l' a' r') = lamA bal'' `app` unA l' where
    bal'' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l'' a'' r'') a' (at.auth$Bin B r' a r)
    bal'' _ = lamA bal''' `app` unA r'
    bal''' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l' a' l'') a'' (at.auth$Bin B r'' a r)
    bal''' _ = auth t
  bal' _ = auth t
tBalanceL t = auth t

tBalanceR ∷ (EDSL term, AuthDSL ExprF term) ⇒ ExprF (ATerm term ExprF) Tree → term (Auth Tree)
tBalanceR t@(Bin B l a r) = lamA bal' `app` unA r where
  bal' (Bin R l' a' r') = lamA bal'' `app` unA l' where
    bal'' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l a l'') a'' (at.auth$Bin B r'' a' r')
    bal'' _ = lamA bal''' `app` unA r'
    bal''' (Bin R l'' a'' r'') = auth$Bin R (at.auth$Bin B l a l') a' (at.auth$Bin B l'' a'' r'')
    bal''' _ = auth t
  bal' _ = auth t
tBalanceR t = auth t

tUnbalancedL ∷ (EDSL term, AuthDSL ExprF term) ⇒ ExprF (ATerm term ExprF) Tree → term (Auth Tree :* BaseT Bool)
tUnbalancedL t@(Bin c l a r) = lamA bal' `app` unA l where
  bal' (Bin B l' a' r') = lamA tBalanceL `app` (auth$Bin B (at.auth$Bin R l' a' r') a r) ** unit (c == B)
  bal' (Bin R l' a' r') = (auth$Bin B l' a' (at$lamA tBalanceL `app` (auth$Bin B (at$lamA red `app` unA r') a r))) ** unit False where
  red (Bin _ l a r) = auth$ Bin R l a r
  
tUnbalancedR ∷ (EDSL term, AuthDSL ExprF term) ⇒ ExprF (ATerm term ExprF) Tree → term (Auth Tree :* BaseT Bool)
tUnbalancedR t@(Bin c l a r) = lamA bal' `app` unA r where
  bal' (Bin B l' a' r') = lamA tBalanceR `app` (auth$Bin B l a (at.auth$Bin R l' a' r')) ** unit (c == B)
  bal' (Bin R l' a' r') = (auth$Bin B (at$lamA tBalanceR `app` (auth$Bin B l a (at$lamA red `app` unA l'))) a' r') ** unit False where
  red (Bin _ l a r) = auth$ Bin R l a r

tInsert ∷ (EDSL term, AuthDSL ExprF term) ⇒ term (BaseT A :→ BaseT V :→ Auth Tree :→ Auth Tree)
tInsert = lamU$ \a → lamU$ \v → ins a v where
  ins a v = lamA black `o` ins'' where
    ins'' ∷ (EDSL term, AuthDSL ExprF term) ⇒ term (Auth Tree :→ Auth Tree)
    ins'' = lamA ins' where
      ins' Tip = auth (Bin B (at.auth$Tip) (a,Just v) (at.auth$Tip))
      ins' n@(Bin c l (a',Just v) r) = case compare a a' of
        EQ → error "duplicate insert"
        LT → auth$ Bin R (at$ins' Tip) (a ,Nothing) (at.auth$n)
        GT → auth$ Bin R (at.auth$n)   (a',Nothing) (at$ins' Tip)
      ins' (Bin c l av@(a',_) r) = case compare a a' of
        EQ → error "duplicate insert"
        LT → tBalanceL (Bin c (at$ins'' `app` unA l) av r)
        GT → tBalanceR (Bin c l av (at$ins'' `app` unA r))
  black (Bin _ l a r) = auth$ Bin B l a r

tDelete ∷ (EDSL term, AuthDSL ExprF term) ⇒ term (BaseT A :→ Auth Tree :→ Auth Tree)
tDelete = lamU del where
  del ∷ (EDSL term, AuthDSL ExprF term) ⇒ A → term (Auth Tree :→ Auth Tree)
  del a = lamA black `o` tFst `o` lamA del' where
    del' ∷ (EDSL term, AuthDSL ExprF term) ⇒
      ExprF (ATerm term ExprF) Tree → term (Auth Tree :* BaseT (Bool, Maybe A))
    del' Tip = error "delete called on empty tree"
    del' (Bin _ _ (a',Just _) _) = if a == a' then auth Tip ** unit (True, Nothing)
                                   else error ("delete: element not found: " ++ show a)
    
    -- a <= a'
    del' (Bin c l (a',Nothing) r) | a <= a' = lam del'' `o` lamA del' `app` unA l where
      del'' ldm = tif (lamA empty `app` tfst ldm)
                  (unA r ** unit (c == B, Nothing))
                  (lamU del''' `app` tsnd ldm) where
        del''' (True, m) = withM Nothing $ lamA tUnbalancedR `app` t m
        del''' (False,  m) = t m ** unit(False, Nothing)
        t (Just m) | a == a' = auth$Bin c (at$tfst ldm) (m, Nothing) r
        t _ | a == a' = error "failed assertion: m is not None"
        t _ | otherwise = auth$Bin c (at$tfst ldm) (a',Nothing) r
    
    -- a > a'
    del' (Bin c l (a',Nothing) r) | otherwise = lam del'' `o` lamA del' `app` unA r where
      del'' rdm = tif (lamA empty `app` tfst rdm)
                  (unA l ** unit (c == B, Just a'))
                  (lamU del''' `app` tsnd rdm) where
        del''' (True, m) = withM m $ lamA tUnbalancedL `app` t
        del''' (False,  m) = t ** unit(False, m)
        t = auth$Bin c l (a',Nothing) (at$tfst rdm)

  withM m t = (lamU$ \b → tfst t ** unit (b, m)) `app` tsnd t
  empty Tip = unit True
  empty _ = unit False
  black (Bin _ l a r) = auth$ Bin B l a r
  black Tip = auth$ Tip

-- Examples

ins' a t = tInsert `app` unit a `app` unit [a] `app` t
del' a t = tDelete `app` unit a `app` t

t0 = unISem' $ ins' 'a' $ ins' 'b' $ ins' 'c' $ ins' 'd' tTip
        
test1 = fst . runProver . asP $ tInsert `app` unit 'a' `app` unit "a" `app` tTip

asP ∷ MSem' ExprF (HFix (Annot ExprF)) (Prover ExprF) a → Prover ExprF (MSem ExprF (HFix (Annot ExprF)) (Prover ExprF) a)
asP = unMSem'

asV ∷ MSem' ExprF (K D) (Verifier ExprF) a → Verifier ExprF (MSem ExprF (K D) (Verifier ExprF) a)
asV = unMSem'

asIO ∷ MSem' ExprF (HFix ExprF) IO a → IO (MSem ExprF (HFix ExprF) IO a)
asIO = unMSem'

main = do
  mapM_ print . snd . runProver $ (asP $ tLookup `app` unit 'a') `shapp` (annotate t0)
  mapM_ print . snd . runProver $ (asP $ tLookup `app` unit 'c') `shapp` (annotate t0)
  p <- return . snd . runProver $ (asP $ tLookup `app` unit 'a') `shapp` (annotate t0)
  print . runVerifier p $ (asV $ tLookup `app` unit 'a') `shapp` (hcata hhash t0)
  print . runVerifier p $ (asV $ tLookup `app` unit 'c') `shapp` (hcata hhash t0)


rbpToRose :: HFix ExprF Tree → Rose Node
rbpToRose = unK . hcata alg where
  alg :: ExprF (K (Rose Node)) :~> K (Rose Node)
  alg Tip                 = K $ leaf Point
  alg (Bin c (K l) a (K r)) = K $ Branch (Node (col c) (shw a)) [l, r]
    where
      shw (a, Nothing) = show a
      shw (a, Just v) = show a ++ ":" ++ v
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

shuffle :: [a] -> IO [a]
shuffle xs = do
  ar <- newArray n xs
  forM [1..n] $ \i -> do
    j <- randomRIO (i,n)
    vi <- readArray ar i
    vj <- readArray ar j
    writeArray ar j vi
    return vj
  where
    n = length xs
    newArray :: Int -> [a] -> IO (IOArray Int a)
    newArray n xs =  newListArray (1,n) xs

t00 = unISem' $ ins' 'B' $ ins' 'C' $ ins' 'D' $ ins' 'A' $ ins' 'E' $ ins' 'F' $ tTip

main'' :: IO (HFix ExprF Tree)
main'' = do
  x <- shuffle ['A'..'Z']
 -- asIO $ foldr ins' tTip x
  y <- return $! unISem' $ foldr ins' tTip x
  tree2png "test.png" $ rbpToRose y
  x <- shuffle ['A'..'Z']
  y' <- return $! unISem' $ foldr del' (ISem' y) x
  tree2png "test1.png" $ rbpToRose y'
  return y'
  
  {-
main' :: IO ()
main' = do
  putStrLn $ show $ testTree
  putStrLn $ show $ tt1
  --tree2png "test.png" tt1
-}
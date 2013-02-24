{- 
   Andrew Miller 
   
   Authenticated Data Structures, Generically:
     Merkle-ized Lambda Calculator
-}

{-# LANGUAGE GADTs,
  FlexibleInstances, FlexibleContexts, UndecidableInstances,
  StandaloneDeriving, TypeOperators, Rank2Types,
  MultiParamTypeClasses, ConstraintKinds,
  DeriveTraversable, DeriveFunctor, DeriveFoldable, DeriveDataTypeable,
  TypeFamilies, FunctionalDependencies, 
  ScopedTypeVariables, GeneralizedNewtypeDeriving
 #-}

import Control.Compose
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Writer
import Control.Monad.Error
import Control.Monad.State
import Data.Hashable
import Data.Typeable
import Data.List
import Text.Printf
import Prelude hiding (abs)

import Tree2Dot
import Merkle


{- CEK Machine interpreter -}

data Term where
data Clo where
data Env where
data Kont where
data Conf where

deriving instance Show Term
deriving instance Show Clo
deriving instance Show Env
deriving instance Show Conf

deriving instance (Show (r a), Show (r Term), Show (r Clo), 
                   Show (r Env), Show (r Kont), Show (r Conf)) => Show (Univ r a)
instance Show (Some (HFix Univ)) where show = some show
instance Show k => Show (Some (Univ (K k))) where show = some show

data Univ :: (* -> *) -> * -> * where
  T   :: r Term -> r Env -> r Kont -> Univ r Conf
  V   :: r Kont -> r Clo           -> Univ r Conf
  CLO :: r Term -> r Env           -> Univ r Clo
  ARG :: r Term -> r Env -> r Kont -> Univ r Kont
  FUN :: r Clo  -> r Kont          -> Univ r Kont
  ENV :: r Clo  -> r Env           -> Univ r Env
--  BASE :: Int -> Univ r Term
  IND :: Int -> Univ r Term
  APP :: r Term -> r Term -> Univ r Term
  ABS :: r Term -> Univ r Term
  STOP  :: Univ r Kont
  ENVE :: Univ r Env
  
-- Boilerplate for hfmap
instance HFunctor Univ where
  hfmap f (T t e k) = T (f t) (f e) (f k)
  hfmap f (V k v)   = V (f k) (f v)
  hfmap f (CLO t e) = CLO (f t) (f e)
  hfmap f (ARG t e k) = ARG (f t) (f e) (f k)
  hfmap f (FUN c k) = FUN (f c) (f k)
  hfmap f (ENV c e) = ENV (f c) (f e)
  hfmap f (IND n) = IND n
  hfmap f (APP a b) = APP (f a) (f b)
  hfmap f (ABS t) = ABS (f t)
  hfmap _ ENVE = ENVE
  hfmap _ STOP = STOP

-- Boilerplate for hhash
instance HHashable Univ where
  hhash (T (K t) (K e) (K k)) = K $ hash ("T", t, e, k)
  hhash (V (K k) (K v)) = K $ hash ("V", k, v)
  hhash (CLO (K t) (K e)) = K $ hash ("CLO", t, e)
  hhash (ARG (K t) (K e) (K k)) = K $ hash ("ARG", t, e, k)
  hhash (FUN (K c) (K k)) = K $ hash ("FUN", c, k)
  hhash (ENV (K c) (K e)) = K $ hash ("ENV", c, e)
  hhash (IND n) = K $ hash ("IND", n)
  hhash (APP (K a) (K b)) = K $ hash ("APP", a, b)
  hhash (ABS (K t)) = K $ hash ("ABS", t)
  hhash STOP = K $ hash "STOP"
  hhash ENVE = K $ hash "ENVE"

         {-
step :: Univ -> Univ
step (T (IND n)     e k)     = V k (e !! n)
step (T (ABS t)     e k)     = V k (CLO t e)
step (T (APP t0 t1) e k)     = T t0 e (Arg t1 e k)
step (T t           e k)     = V k (CLO t e)
step (V (Arg t e k)       v) = T t e (Fun v k)
step (V (Fun (CLO t e) k) v) = T t (v:e) k
-}


nthM :: Monadic Univ d m => Int -> (d Env) -> m (d Clo)
nthM n = nth n <=< destruct where
  nth 0 (ENV c _) = return c
  nth n (ENV _ e) | n > 0 = nthM (n-1) e
  nth _ _ = error "bad De Bruijn index"

stepM :: Monadic Univ d m => Univ d Conf -> m (Univ d Conf)
stepM (T t' e k) = destruct t' >>= step' where
  step' (IND n) = do { clo <- nthM n e ; return (V k clo) }
  step' (ABS t) = do { clo <- construct (CLO t e) ; return (V k clo) }
  step' (APP t0 t1) = do
    clo <- construct (ARG t1 e k)
    return (T t0 e clo)
  --  step' (BASE n) = do { clo <- construct (CLO t' e) ; return (V k clo) }
stepM (V k' v) = destruct k' >>= step' where
  step' (ARG t e k) = do { k' <- construct (FUN v k) ; return (T t e k') }
  step' (FUN c k) = do
    CLO t e <- destruct c
    env <- construct (ENV v e)
    return (T t env k)


injectM :: Monadic Univ d m => d Term -> m (Univ d Conf)
injectM t = do
  enve <- construct ENVE
  stop <- construct STOP
  return (T t enve stop)
  
inject :: HFix Univ Term -> Univ (HFix Univ) Conf
inject t = T t (HFix ENVE) (HFix STOP)

tick :: MonadState Int m => m Int
tick = do { x <- get; put (x + 1); return x }

steps2png :: String -> HFix Univ Term -> IO ()
steps2png directory term = runStateT (iter . inject $ term) 0 >> return () where
  iter :: Univ (HFix Univ) Conf -> StateT Int IO ()
  iter v = do
    x <- tick
    liftIO . putStrLn . show $ v
    liftIO . tree2png (printf "%s/step_%05d.png" directory x) . rbpToRose $ HFix v
    unless (stopped v) (iter . runIdentity $ stepM v) where
      stopped (V (HFix STOP) _) = True
      stopped _ = False
    
    
{-  
              t >>= iter where
  iter v@(V s c) = destruct s >>= iter' where
    iter' STOP = return c
    iter' _ = stepM v >>= iter
  iter v = stepM v >>= iter
-}
evalM :: Monadic Univ d m => d Term -> m (d Clo)
evalM t = injectM t >>= iter where
  iter v@(V s c) = destruct s >>= iter' where
    iter' STOP = return c
    iter' _ = stepM v >>= iter
  iter v = stepM v >>= iter

  
abs = HFix . ABS
app x y = HFix $ APP x y
ind = HFix . IND

fromBool :: Bool -> HFix Univ Term
fromBool False = abs (abs (ind 0))
fromBool True  = abs (abs (ind 1))

tAND   = abs (abs (app (app (ind 1) (ind 0)) (fromBool False)))
tOR    = abs (abs (app (app (ind 1) (fromBool True)) (ind 0)))
tNOT   = abs (abs (abs (app (app (ind 2) (ind 0)) (ind 1))))

fromNat :: Int -> HFix Univ Term
fromNat n = abs (abs (apps n)) where
  apps 0 = ind 0
  apps n = app (ind 1) (apps (n - 1))
  
tSUCC = abs (abs (abs (app (ind 1) (app (app (ind 2) (ind 1)) (ind 0)))))

tPLUS = abs$abs$abs$abs$ (app (app (ind 3) (ind 1)) (app (app (ind 2) (ind 1)) (ind 0)))
tY = app (abs (app (ind 0) (ind 0))) (abs (app (ind 0) (ind 0)))

runProver :: Prover Univ a -> (a, VO Univ)
runProver = runWriter . unProver

runVerifier :: VO Univ -> Verifier Univ a -> Either VerifierError a
runVerifier vo f = evalState (runErrorT . unVerifier $ f) vo

{-
extractor :: (HHashable f) =>
             (forall m d. Monadic f d m => d a -> m b) ->
             HFix f -> VO f ->        -- Original data structure, proof object
             Either (Collision f) b     -- A hash collision, or the correct answer
extractor f t vo = 
  case find collides (zip vo vo') of
    Just collision -> Left collision
    Nothing -> Right result where 
      Right result = evalStateT (runErrorT . unVerifier $ f) (hcata hhash t)
  where
  hash = unK . hhash
  vo' = snd . runWriter $ f t
  collides (x,y) = hash x == hash y && not (x == y)
-}

main = do  
  mapM_ print . snd . runProver . evalM $ app (app tAND (fromBool True)) (fromBool False)
  mapM_ print . snd . runProver . evalM $ app tNOT (fromBool False)
  evalM $ app tSUCC (fromNat 0)
  mapM_ print . snd . runProver . evalM $ app tSUCC (fromNat 0)
  p <- return . snd . runProver . evalM $ annotate $ app tSUCC (fromNat 0)
  print . runVerifier p . evalM . hcata hhash $ app tSUCC (fromNat 0)


rbpToRose :: HFix Univ a -> Rose Node
rbpToRose = unK . hcata alg where
  b a l = Branch (Node "black" a) l
  alg :: Univ (K (Rose Node)) :~> K (Rose Node)
  alg (T   (K t) (K e) (K k)) = K $ b "T" [t, e, k]
  alg (V   (K k) (K v))       = K $ b "V" [k, v]
  alg (CLO (K t) (K e))       = K $ b "CLO" [t, e]
  alg (ARG (K t) (K e) (K k)) = K $ b "ARG" [t, e, k]
  alg (FUN (K c) (K k))       = K $ b "FUN" [c, k]
  alg (ENV (K c) (K e))       = K $ b "ENV" [c, e]
  alg (IND n)                 = K $ b ("IND:"++show n) []
  alg (APP (K x) (K y))       = K $ b "APP" [x, y]
  alg (ABS (K t))             = K $ b "ABS" [t]
  alg STOP = K $ b "STOP" []
  alg ENVE = K $ b "ENVE" []
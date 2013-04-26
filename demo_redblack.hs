{-# LANGUAGE 
  GADTs, NoMonomorphismRestriction, FlexibleContexts, UnicodeSyntax,
  ScopedTypeVariables, FlexibleInstances, MultiParamTypeClasses, RankNTypes,
  UndecidableInstances
 #-}

module Main where

import Criterion.Main
import Criterion.Config

import Merkle
import RedBlack
import Generics.Regular

import Control.DeepSeq (NFData,rnf)
import Control.Monad
import Control.Monad.Error
import Control.Monad.Reader
import Control.Monad.Supply
import System.IO.Streams.File
import System.IO.Streams (InputStream)
import qualified Data.ByteString.Lazy as BL
import qualified System.IO.Streams as S
import Data.Binary
import Data.Binary.Get
import Data.Binary.Put
import Data.IORef
import Data.Global
import System.Random
import Data.Array.IO
import Text.Printf

--import qualified Data.ByteString as BS
import System.IO

-- Examples
main''' = do
  mapM_ print . snd . runProver $ (asP $ tLookup `app` unit "a") `shapp` (annotate t0)
  mapM_ print . snd . runProver $ (asP $ tLookup `app` unit "c") `shapp` (annotate t0)
  p <- return . snd . runProver $ (asP $ tLookup `app` unit "a") `shapp` (annotate t0)
  print . runVerifier p $ (asV $ tLookup `app` unit "a") `shapp` (cata hhash t0)
  print . runVerifier p $ (asV $ tLookup `app` unit "c") `shapp` (cata hhash t0)

seed = 1024


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

t00' :: Term (Auth)
t00' = ins' "B" $ ins' "C" $ ins' "D" $ ins' "A" $ ins' "E" $ ins' "F" $ tTip
t00 = unISem' t00'

listFromBytes ∷ BL.ByteString → VO ExprF
listFromBytes proof = g $ runGetOrFail Data.Binary.get (proof) where
  g (Left _) = []
  g (Right (bs, _, x)) = x : listFromBytes bs

proof = runPut $ mapM_ put $ snd . runProver $ (asP $ ins "x") `shapp` (annotate t00)
voof = listFromBytes proof
vrf = runVerifier voof $ (asV $ ins "x") `shapp` (cata hhash t00)
vrf' = checkProof' proof $ (asV' $ ins "x") `shapp` (cata hhash t00)

write' = write $ (asP $ ins "d") `shapp` (annotate t00)
load' = load $ (asV $ ins "d") `shapp` (cata hhash t00)

write :: Prv ExprF (Auth) → IO ()
write prf = do
  withBinaryFile "proof.bin" WriteMode $ \h -> do
    BL.hPutStr h . runPut . Data.Binary.put . snd . runProver $ prf

load :: Vrf ExprF (Auth) → IO (Either VerifierError (VSem ExprF (Auth)))
load vrf = do
  withBinaryFile "proof.bin" ReadMode $ \h -> do
    vob <- BL.hGetContents h
    return (runVerifier (runGet get vob) vrf)
                                      

main'' = do
  setStdGen (mkStdGen seed)
  x <- shuffle$ [1..50]
  -- asIO $ foldr (ins'.(\x→[x])) tTip x
  --y <- return $! unISem' $ foldr (ins'.show) tTip x
  y <- return . runProver . asP $ foldr (ins'.show) tTip x
--  tree2png "test.png" $ rbpToRose y
--  x <- shuffle$ ['A'..'Z']++['a'..'z']
--  y' <- return $! unISem' $ foldr (del'.(\x→[x])) (ISem' y) x
--  tree2png "test1.png" $ rbpToRose y'
  return . snd $ y
  
{-
main' :: IO ()
main' = do
  putStrLn $ show $ testTree
  putStrLn $ show $ tt1
  --tree2png "test.png" tt1
-}

{-
db :: IORef (Fix (Annot ExprF))
db = unsafePerformIO . newIORef . annotate . In $ Tip

insert' :: String → IO ()
insert' a = do
  db' <- readIORef db
  db'' <- return . fst . runProver $ (asP $ ins a) `shapp` db'
  writeIORef db db''
-}

insall xs = unISem' $ foldr ins' tTip xs

prepare n = do
  xs <- shuffle$ map show [1..n]
  return . annotate $ insall xs

instance NFData (Fix (Annot ExprF)) where
  -- Grabbing the 'hash' is a good way to ensure the data is annotated
  rnf (In (O d)) = d `seq` ()

myConfig = defaultConfig {
  -- Always GC between runs.
  cfgPerformGC = ljust True
  --  cfgPlot = M.singleton KernelDensity (Window 800 600)
  }

twoTo n = floor(2 Prelude.** (fromIntegral n))

main = do
  xs <- shuffle $ map show [1..1000]
  trees <- forM [0..20] ((>>= return . insall) . shuffle . map show . (\n -> [1..twoTo n]))
  defaultMainWith myConfig (return ())
    $ map (\n -> bench ("ins/del 1k @ " ++ show (twoTo n)) $ nf bnch $ treesAndData trees xs n) [0..20]
  where
    treesAndData trees xs n = (annotate $ trees!!n, map (++ "!") xs)
    bnch (tree, xs) = foldr (\x t -> fst . runProver $ (asP $ del x `o` ins x) `shapp` t) tree xs
    

writeProof :: String → Prover ExprF a → IO ()
writeProof path p = withFile path WriteMode g where
  g fd = do
    putStrLn path
    prf <- return (snd . runProver $ p)
    putStrLn . show $ length prf
    BL.hPut fd . runPut $ mapM_ put prf

type VSem' f a = MSem f D (ErrorT VerifierError Get) a
type Vrf' f a = ErrorT VerifierError Get (VSem' f a)

asV' ∷ MSem' ExprF D (ErrorT VerifierError Get) a → Vrf' ExprF a
asV' = unMSem'

checkProof' :: BL.ByteString → ErrorT VerifierError Get a → Either VerifierError a
checkProof' bs v = 
  let x = runGet (runErrorT v) bs in
  x

instance Binary a ⇒ MonadSupply a Get where supply = get

checkProof :: Show a ⇒ String → ErrorT VerifierError Get a → IO (Either VerifierError a)
checkProof path v = withFile path ReadMode g where
  g fd = do
    putStrLn path
    bs <- BL.hGetContents fd
    let x = checkProof' bs v in do
      putStrLn $ show x
      return x

experiment_proofs niter nins = do
  setStdGen (mkStdGen seed)
  xs <- shuffle $ map show [1..nins]
  trees <- forM [0..niter-1] ((>>= return . insall) . shuffle . map show . (\n -> [1..twoTo n]))
  putStrLn "trees prepared"
  putStrLn "experiment prover"
  forM_ [0..niter-1] $
    \n -> writeProof (printf "benchoutput/insdelprf/insdelprf_%02d.dat" n) $ 
          insdel (elems xs) (annotate $ trees!!n)
  forM_ [0..niter-1] $
    \n -> writeProof (printf "benchoutput/insdelprf/insertprf_%02d.dat" n) $
          inst (elems xs) (annotate $ trees!!n)
  forM_ [0..niter-1] $
    \n -> writeProof (printf "benchoutput/insdelprf/lookupprf_%02d.dat" n) $
          lookup (elems xs) (annotate $ trees!!n)

  where
    elems xs = map (++ "!") xs
    insdel xs tree = foldM(\t x -> (asP $ del x `o` ins x) `shapp` t) tree xs
    inst xs tree   = foldM(\t x->(asP$lam$ \t->(lamA$const$t) `app` ins' x t)`shapp`t) tree xs
    lookup xs tree = foldM(\t x->(asP$lam$ \t->(lamU$const$t) `app` tlookup' x t)`shapp`t) tree xs
    

experiment_verifs niter nins = do
  setStdGen (mkStdGen seed)
  xs <- shuffle $ map show [1..nins]
  trees <- forM [0..niter-1] ((>>= return . insall) . shuffle . map show . (\n -> [1..twoTo n]))
  putStrLn "trees prepared"
  putStrLn "experiment verifier"
  forM_ [0..niter-1] $
    \n -> checkProof (printf "benchoutput/insdelprf/insdelprf_%02d.dat" n) $ 
          insdel (elems xs) (cata hhash $ trees!!n)
  forM_ [0..niter-1] $
    \n -> checkProof (printf "benchoutput/insdelprf/insertprf_%02d.dat" n) $
          inst (elems xs) (cata hhash $ trees!!n)
  forM_ [0..niter-1] $
    \n -> checkProof (printf "benchoutput/insdelprf/lookupprf_%02d.dat" n) $
          lookup (elems xs) (cata hhash $ trees!!n)

  where
    elems xs = map (++ "!") xs
    insdel xs tree =foldM(\t x -> (asV' $ del x `o` ins x) `shapp` t) tree xs
    inst xs tree   =foldM(\t x->(asV'$lam$ \t->(lamA$const$t) `app` ins' x t)`shapp`t) tree xs
    lookup xs tree =foldM(\t x->(asV'$lam$ \t->(lamU$const$t) `app` tlookup' x t)`shapp`t) tree xs
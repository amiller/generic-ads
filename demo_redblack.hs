{-# LANGUAGE 
  GADTs, NoMonomorphismRestriction, FlexibleContexts, UnicodeSyntax,
  ScopedTypeVariables
 #-}

module Main where

import Merkle
import RedBlack

import Control.Monad
import Data.Serialize
import Data.IORef
import System.Random
import Data.Array.IO

import qualified Data.ByteString as BS
import System.IO

-- Examples
main''' = do
  mapM_ print . snd . runProver $ (asP $ tLookup `app` unit "a") `shapp` (annotate t0)
  mapM_ print . snd . runProver $ (asP $ tLookup `app` unit "c") `shapp` (annotate t0)
  p <- return . snd . runProver $ (asP $ tLookup `app` unit "a") `shapp` (annotate t0)
  print . runVerifier p $ (asV $ tLookup `app` unit "a") `shapp` (hcata hhash t0)
  print . runVerifier p $ (asV $ tLookup `app` unit "c") `shapp` (hcata hhash t0)

seed = 1024


--newtype Record a = Record {unRec :: (Prv a, Vrf a) }

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

t00' :: Term (Auth Tree)
t00' = ins' "B" $ ins' "C" $ ins' "D" $ ins' "A" $ ins' "E" $ ins' "F" $ tTip
t00 = unISem' t00'

proof = runPut . put . snd . runProver $ (asP $ ins "x") `shapp` (annotate t00)
voof = fromRight . runGet Data.Serialize.get $ proof :: VO ExprF
vrf = runVerifier voof $ (asV $ ins "x") `shapp` (hcata hhash t00)

write' = write $ (asP $ ins "d") `shapp` (annotate t00)
load' = load $ (asV $ ins "d") `shapp` (hcata hhash t00)
  
write :: Prv ExprF (Auth Tree) → IO ()
write prf = do
  withBinaryFile "proof.bin" WriteMode $ \h -> do
    BS.hPutStr h . runPut . Data.Serialize.put . snd . runProver $ prf

load :: Vrf ExprF (Auth Tree) → IO (Either VerifierError (VSem ExprF (Auth Tree)))
--load :: Verifier ExprF (MSem ExprF (K D) (Verifier ExprF) a) → IO (Either VerifierError (MSem ExprF (K D) (Verifier ExprF) a))
load vrf = do
  withBinaryFile "proof.bin" ReadMode $ \h -> do
    vob <- BS.hGetContents h
    return (runVerifier (fromRight $ runGet get vob) vrf)
                                      

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
  
main = main''

{-
main' :: IO ()
main' = do
  putStrLn $ show $ testTree
  putStrLn $ show $ tt1
  --tree2png "test.png" tt1
-}

m_start :: IO ()
m_start = do
  :
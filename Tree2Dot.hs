{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE NoMonomorphismRestriction #-}

module Tree2Dot where

import Data.String.Combinators
import Text.Printf
import Control.Monad
import Control.Monad.State
import Data.Foldable
import Data.Traversable hiding (forM)
import Prelude hiding (foldr, concat)
import System.Process
import System.IO hiding (hGetContents)
import System.IO.Strict (hGetContents)

import Control.Monad

data Rose a = Branch a [Rose a] deriving (Show)
leaf a = Branch a []

deriving instance Functor Rose
deriving instance Foldable Rose
deriving instance Traversable Rose

incr = do 
  x <- get;
  put (x + 1);
  return x;

label :: Rose a -> Rose (Int, a)
label tree = evalState (Data.Traversable.mapM label' tree) 0
  where 
    label' a = incr >>= return . (flip (,) a)

labels :: Rose a -> Rose String
labels = fmap (\(n, _) -> printf "N_%d" n) . label

edges :: Rose a -> [(a, a)]
edges (Branch a bs) = (map ((,) a . val) bs) ++ concat (map edges bs)
  where
    val (Branch a _) = a

edgeString :: Rose String -> String
edgeString x = concat [printf "%s -> %s;\n" a b | (a,b) <- edges x]

-- nodeString :: Show a => Tree (String, String) -> String
-- nodeString (Leaf (n, a)) = printf "%s [label=\"%s\", color=%s, shape=%s];\n" n a                    
-- edges :: Show a => Tree a -> [String]

type CharTree = Rose Char
type IntTree = Rose Int

testTree :: CharTree
testTree = 
  Branch 'a' [
    Branch 'b' [leaf 'c', leaf 'd'],
    Branch 'e' [leaf 'f', leaf 'g']
    ]

type Color = String
type Label = String
data Node = Point | Node Color Label deriving (Show)

dot :: Rose Node -> String
dot t = 
  preamble $$
  node $$
  edges $$ 
  finish
  where
    preamble = "\
\digraph BST {\
\node [fontname=\"Arial\"];"
    edges = edgeString labeled
    finish = "}"
    node = concat [printf "%s %s" id (nodeString n) | (id, n) <- zip (foldr (:) [] labeled) (foldr (:) [] t)]
    labeled = labels t

nodeString Point = "[shape=point, label=x];\n"
nodeString (Node c l) = 
  printf "[label=\"%s\" color=%s, shape=rectangle];\n" l c

dot2png :: String -> Handle -> IO ()
dot2png dot h = do
  (Just hin, _, _, p) <- 
    createProcess (shell "dot -Tpng"){ std_out = UseHandle h, std_in = CreatePipe }
  hPutStr hin dot
  hClose hin
  waitForProcess p; return ()

tree2png :: FilePath -> Rose Node -> IO ()
tree2png path = withBinaryFile path WriteMode . dot2png . dot

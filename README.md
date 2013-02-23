
Generic Authenticated Data Structures

Main module:
  Merkle.hs : To use this library, you provide
  - a signature for a datatype (an HFunctor)
  - a hash function (an algebra over the datatype)
  - operations defined parametrically over a (?)
  Then this module provides you with Prove and Verify contexts for running your operations as an ADS protocol

Examples:
  binarytree.hs : a binary tree data structure with integers in the nodes
  lambda.hs : a lambda calculus interpreter
      Using the lambda calculus, any data structure representable with a church encoding can be merkle-ized
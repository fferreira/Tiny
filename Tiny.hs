module Main where

import Syntax

main = do 
  res <- eval [] sample2
  putStr (show res)
  putChar '\n'
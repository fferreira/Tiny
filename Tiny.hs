module Main where

import Syntax

main = do 
  putStr (show (eval [] sample2)) 
  putChar '\n'
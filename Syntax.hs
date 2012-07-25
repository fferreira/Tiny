module Syntax where

import Control.Monad.State

data Value = Num Integer deriving (Eq, Show)

data (Eq a, Show a) => Expr a =
  Value Value
  | App (Expr a) (Expr a)
  | Fn a (Expr a)
  | Var a
  | Def a (Expr a)
  | Seq (Expr a) (Expr a)
  deriving (Eq, Show)
    
id_function = (Fn "x" (Var "x"))

sample = App id_function (Value (Num 14))

sample2 = Seq (Def "id" id_function) (App (Var "id") (Value (Num 42)))

type Ctx a = [(a, Expr a)]

eval_act v@(Value _) = return v
eval_act f@(Fn _ _) = return f
eval_act (Var x) = do
  c <- get ;
  return (case lookup x c of Just v -> v)
eval_act (App e1 e2) = do
  e2' <- eval_act e2 ; Fn x b <- eval_act e1
  c <- get
  put ((x, e2'):c) ; r <- eval_act b ; put c
  return r
eval_act (Def x e) = do
  e' <- eval_act e
  c <- get
  put ((x, e'):c)
  return e'
eval_act (Seq e1 e2) = do
  eval_act e1 ; eval_act e2

eval c e = evalState (eval_act e) c
    
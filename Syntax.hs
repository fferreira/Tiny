module Syntax where

import Data.List(delete, deleteBy)
import Char(ord, chr)
import Control.Monad.State(State, StateT, evalState, evalStateT, put, get, modify, gets)
import Control.Monad.Error(ErrorT, throwError, runErrorT)

--- De Bruijn indices ---

type Index = Int

--- The language ---

data Value = Num Index | Nil deriving (Eq, Show)

data Expr =
  Value Value
  | App Expr [Expr]
  | Fn Index Expr -- bad code smell should be the number of vars
  | Var Index
  | Def Expr
  | Seq Expr Expr
  | Clo Ctx Expr -- for closure conversion
  deriving (Eq, Show)

--- Some examples ---

id_function = (Fn 1 (Var 0))

sample = App id_function [Value (Num 14)]

sample2 = Seq (Def id_function) (App (Var 0) [Value (Num 42)])

f2 = (Fn 2 (Var 0))

sample3 = App f2 [Value (Num 14), Value (Num 15)]

sample4 = Seq (Def f2) (App (Var 0) [Value (Num 42), Value (Num 43)])


--- The evaluator ---

type Ctx = [Expr]

type WithError = ErrorT String IO
type EvalResult = StateT Ctx WithError Expr

eval_act :: Expr -> EvalResult
eval_act v@(Value _) = return v
eval_act f@(Fn _ _) = return f
eval_act (Var x) = do c <- get ; return (c !! x)
eval_act (App f params) = do
  params' <- mapM eval_act params
  f' <- eval_act f
  apply_fn f' params'
    where apply_fn (Fn n b) params'  = 
            if n == length params' then
              do
                c <- get ; modify (\c -> params' ++ c) 
                r <- eval_act b ; put c ; return r
            else
              throwError "Too many/little parameters for application"
          apply_fn _ _ = throwError "Applying something that is not a function"
eval_act (Def e) = do
  e' <- eval_act e
  modify (\c -> e':c)
  return e'
eval_act (Seq e1 e2) = do
  eval_act e1 ; eval_act e2
eval_act (Clo c' e) = do
  c <- get ; modify (\c -> c' ++ c)
  res <- eval_act e ; put c
  return res

eval c e = do
  res <- runErrorT (evalStateT (eval_act e) c) 
  return res

--- Free variables ---

type FreeResult = State Index [Index]

free_act :: Expr -> State Index [Index]
free_act v@(Value _) = return []
free_act (App f params) = do ff <- free_act f
                             fp <- mapM free_act params
                             return (ff ++ concat fp)
free_act (Fn n b) = do c <- get ; modify (\c -> c + 1) 
                       free_act b
free_act (Var v) = do c <- get ; return (if v >= c then [v] else [])
free_act (Def e) = do f <- free_act e ; modify (\c -> c + 1) ; return f
free_act (Seq e1 e2) = do f1 <- free_act e1 ; f2 <- free_act e2 ; return (f1 ++ f2)
free_act (Clo c' e) = do modify (\c -> c + (length c')) ; free_act e

free e = evalState (free_act e) 0

--- Tree walk with context length ---

type WalkResult = StateT Index (Either String) Expr

walker :: (Expr -> WalkResult) -> Expr -> WalkResult
walker f v@(Value _) = f v
walker f (App e1 e2) = do e1' <- f e1; 
                          e2' <- mapM f e2; 
                          f (App e1' e2')
walker f (Fn n b) = do c <- get ; modify (\c -> c + n) 
                       b' <- f b ; put c
                       f (Fn n b')
walker f v@(Var x) = f v
walker f (Def e) = do e' <- f e 
                      r <- f (Def e')
                      modify (\c -> c + 1) 
                      return r
walker f (Seq e1 e2) = do e1' <- f e1 ; e2' <- f e2 ; f (Seq e1' e2')
walker f (Clo c' e2) = do c <- get ; modify (\c -> c + (length c'))
                          e2' <- f e2 ; put c ; f (Clo c' e2') -- put?

id_action e = do c <- get ; return e

walk action e c = evalStateT (walker action e) 0


--- Closure Conversion ---


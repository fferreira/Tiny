module Syntax where

import Control.Monad.State(StateT, evalStateT, put, get, modify, gets)
import Control.Monad.Error(ErrorT, throwError, runErrorT)

--- The language ---

data Value = Num Integer | Nil deriving (Eq, Show)

data (Eq a, Show a) => Expr a =
  Value Value
  | App (Expr a) [(Expr a)]
  | Fn [a] (Expr a)
  | Var a
  | Def a (Expr a)
  | Seq (Expr a) (Expr a)
  | Clo (Ctx a) (Expr a) -- for closure conversion
  deriving (Eq, Show)

--- Some examples ---

id_function = (Fn ["x"] (Var "x"))

sample = App id_function [(Value (Num 14))]

sample2 = Seq (Def "id" id_function) (App (Var "id") [(Value (Num 42))])


--- The evaluator ---

type Ctx a = [(a, Expr a)]

type Error = ErrorT String IO
type Result a = StateT (Ctx a) Error (Expr a)

eval_act :: (Show a, Eq a) => Expr a -> Result a
eval_act v@(Value _) = return v
eval_act f@(Fn _ _) = return f
eval_act (Var x) = do 
  v <- gets (\c -> lookup x c)
  case v of Just v -> return v
            Nothing -> throwError "Unbound Variable"
eval_act (App f params) = do
  params' <- mapM eval_act params
  f' <- eval_act f
  apply_fn f' params'
    where apply_fn (Fn xs b) params'  = 
            if length xs == length params' then
              do
                c <- get ; mapM (\(x, p) -> put ((x, p):c)) (zip xs params')
                r <- eval_act b ; put c ; return r
            else
              throwError "Too many/little parameters for application"
          apply_fn _ _ = throwError "Applying something that is not a function"
eval_act (Def x e) = do
  e' <- eval_act e
  modify (\c -> (x, e'):c)
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


module Syntax where

import Data.List(delete, deleteBy)
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

type WithError = ErrorT String IO
type EvalResult a = StateT (Ctx a) WithError (Expr a)

eval_act :: (Show a, Eq a) => Expr a -> EvalResult a
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

--- Tree walk with context ---

type WalkResult a = StateT (Ctx a) (Either a) (Expr a)

walker :: (Show a, Eq a) => (Expr a -> WalkResult a) -> Expr a -> WalkResult a
walker f v@(Value _) = f v
walker f (App e1 e2) = do e1' <- f e1; 
                          e2' <- mapM f e2; 
                          f (App e1' e2')
walker f (Fn xs b) = do b' <- f b ; f (Fn xs b')
walker f v@(Var x) = f v
walker f (Def x e) = do e' <- f e ; f (Def x e')
walker f (Seq e1 e2) = do e1' <- f e1 ; e2' <- f e2 ; f (Seq e1' e2')
walker f (Clo c' e2) = do c <- get ; modify (\c -> c' ++ c)
                          e2' <- f e2 ; put c ; f (Clo c' e2')

id_action e = do c <- get ; return e

walk action e ctx = evalStateT (walker action e) ctx

--- Closure Conversion ---
  
free_vars :: (Show a, Eq a) => Expr a -> [a]
free_vars (Value _) = []
free_vars (Fn xs b) = filter (\x -> not $ x `elem` xs) (free_vars b)
free_vars (Var x) = [x]
free_vars (App f params) = free_vars f ++ concatMap free_vars params
free_vars (Def x e) = delete x (free_vars e)
free_vars (Seq e1 e2) = 
    (free_vars e1) ++ (filter 
                       (\x -> not $ x `elem` (defined_vars e1)) 
                       (free_vars e2))
    where
      defined_vars (Def x e) = x : (defined_vars e)
      defined_vars (App f params) = (defined_vars f) ++ 
                                    (concatMap defined_vars params)
      defined_vars _ = []
free_vars (Clo c' e) = filter (\x -> not $ x `elem` (fst . unzip $ c')) (free_vars e)



cc :: (Show a, Eq a) => Expr a -> Expr a
cc f@(Fn xs b) = Clo [] f
cc e = e
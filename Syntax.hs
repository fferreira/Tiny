module Syntax where

import Data.Char(ord, chr)
import Control.Monad.State(State, StateT, evalState, evalStateT, put, get, modify)
import Control.Monad.Error(ErrorT, throwError, runErrorT)

--- De Bruijn indices ---

type Index = Int

--- Names ---

class (Eq a, Show a) => Name a where
  gensym :: [a] -> a

instance Name Int where
  gensym [] = 0
  gensym ns = (maximum ns) + 1


newtype N = N String deriving (Eq, Ord, Show)
instance Name N where
  gensym [] = N "x"
  gensym ns = N ((reverse (tail (reverse m))) ++ (nextChar (last m)))
    where
      N m = maximum ns
      nextChar c | ord c >= ord 'z' = "za"
      nextChar c = [chr (1 + ord c)]

--- The language ---

data Value = Num Index | Nil deriving (Eq, Show)

data Expr a =
    Value Value
  | Pair (Expr a) (Expr a)
  | Fst (Expr a)
  | Snd (Expr a)
  | App (Expr a) [(Expr a)]
  | Fn Index (Expr a) -- bad code smell should be the number of vars
  | Idx Index
  | Let a (Expr a) (Expr a)
--  | Def a (Expr a)
  | Var a
  | Seq (Expr a) (Expr a)
  | Clo [(Expr a)] (Expr a) -- for closure conversion
  deriving Show

--- Some examples ---

id_function :: (Expr a) 
id_function = (Fn 1 (Idx 0))

sample = App id_function [Value (Num 14)]

sample2 = Let id_function (App (Idx 0) [Value (Num 42)])

f2 = (Fn 2 (Idx 0))

sample3 = App f2 [Value (Num 14), Value (Num 15)]

sample4 = Let f2 (App (Idx 0) [Value (Num 42), Value (Num 43)])

partial_app = Let (Fn 2 (Pair (Idx 0) (Idx 1)))
              (App (Idx 0) [Value (Num 14)])

curried = Let (Fn 2 (Pair (Idx 0) (Idx 1)))
          (App (App (Idx 0) [Value (Num 14)]) [Value (Num 42)])

--- The evaluator ---

type Ctx a = ([(a, Expr a)], [Expr a]) -- TODO use a record?

-- get index context from contexts
ic :: Ctx a -> [Expr a]
ic = snd

type WithError = ErrorT String IO
type EvalResult a = StateT (Ctx a) WithError (Expr a)

eval_act :: Name a => Expr a -> EvalResult a
eval_act v@(Value _) = return v
eval_act f@(Fn _ _) = return f
eval_act (Pair e1 e2) = do e1' <- eval_act e1
                           e2' <- eval_act e2
                           return (Pair e1' e2')
eval_act (Fst e) = do e' <- eval_act e
                      case e' of Pair e1 _ -> return e1
                                 _ -> throwError "Fst of something other than a pair"
eval_act (Snd e) = do e' <- eval_act e
                      case e' of Pair _ e2 -> return e2
                                 _ -> throwError "Snd of something other than a pair"
eval_act (Idx x) = do c <- get 
                      if x < (length (ic c)) then return ((ic c) !! x)
                      else throwError "Invalid index" 
eval_act (App f params) = do
  params' <- mapM eval_act params
  f' <- eval_act f
  apply_fn f' params'
    where 
      apply_fn (Fn n b) p | n == length p  = 
                          do
                            c <- get ; modify (\(nc, dc) -> (nc, p ++ dc)) 
                            r <- eval_act b ; put c ; return r
      apply_fn (Fn n b) p | n > length p  = 
                          return $ Clo p (Fn n b)
      apply_fn (Fn n b) p = 
              throwError "Too many parameters for application"
      apply_fn (Clo n (Fn n' b)) p | n' == length n + length p =
                          apply_fn (Fn n' b) (n ++ p)
      apply_fn (Clo n (Fn n' b)) p | n' > length n + length p  =
                          return $ Clo (n ++ p) (Fn n' b)
      apply_fn (Clo n (Fn n' b)) p =
              throwError "Too many parameters for closure application"
      apply_fn _ _ = throwError "Applying something that is not a function"
eval_act (Let n e1 e2) = do
  e' <- eval_act e1
  modify (\(nc, dc) -> ((n, e'):nc, dc))
  eval_act e2
eval_act (Seq e1 e2) = do
  eval_act e1 ; eval_act e2
eval_act (Clo c' e) = do
  c <- get ; modify (\(nc, dc) -> (nc, c' ++ dc))
  res <- eval_act e ; put c
  return res

eval c e = do
  res <- runErrorT (evalStateT (eval_act e) c) 
  return res

--- Free variables ---

type FreeResult = State Index [Index]

free_act :: (Expr a) -> State Index [Index]
free_act v@(Value _) = return []
free_act (Pair e1 e2) = do f1 <- free_act e1 ; f2 <- free_act e2 ; return (f1 ++ f2)
free_act (Fst e) = free_act e
free_act (Snd e) = free_act e
free_act (App f params) = do ff <- free_act f
                             fp <- mapM free_act params
                             return (ff ++ concat fp)
free_act (Fn n b) = do c <- get ; modify (\c -> c + n) 
                       free_act b
free_act (Idx v) = do c <- get ; return (if v >= c then [v - c] else [])
-- TODO V FIX!
free_act (Let n e1 e2) = do f <- free_act e1 ; modify (\c -> c + 1) ; free_act e2
free_act (Seq e1 e2) = do f1 <- free_act e1 ; f2 <- free_act e2 ; return (f1 ++ f2)
free_act (Clo c' e) = do modify (\c -> c + (length c')) ; free_act e

free e = evalState (free_act e) 0

--- Tree walk with context length ---

-- TODO add named variables
type WalkResult a = StateT Index (Either String) (Expr a)

walker :: Name a => (Expr a -> WalkResult a) -> Expr a -> WalkResult a
walker f v@(Value _) = f v
walker f (Pair e1 e2) = do e1' <- f e1
                           e2' <- f e2
                           f (Pair e1' e2')
walker f (Fst e) = do e' <- f e
                      f (Fst e')
walker f (Snd e) = do e' <- f e
                      f (Snd e')
walker f (App e1 e2) = do e1' <- f e1; 
                          e2' <- mapM f e2; 
                          f (App e1' e2')
walker f (Fn n b) = do c <- get ; modify (\c -> c + n) 
                       b' <- f b ; put c
                       f (Fn n b')
walker f v@(Idx x) = f v
walker f (Let n e1 e2) = do e1' <- f e1
                            modify (\c -> c + 1)
                            e2' <- f e2
                            f (Let n e1' e2')
walker f (Seq e1 e2) = do e1' <- f e1 ; e2' <- f e2 ; f (Seq e1' e2')
walker f (Clo c' e2) = do c <- get ; modify (\c -> c + (length c'))
                          e2' <- f e2 ; put c ; f (Clo c' e2') -- put?

id_action e = return e

walk action e c = evalStateT (walker action e) c --TODO missing one action overall?

--- Shift ---

shift :: Name a => Index -> Expr a -> Expr a
shift s e = 
    let 
        Right res = walk act e 0
    in 
      res -- it can only be Right
          where
            act :: Name a => Expr a -> WalkResult a 
            act (Idx x) = do c <- get
                             return (if x < c then Idx x else Idx (x + s))
            act e = return e

--- Substitution ---

subst :: Name a => Index -> Expr a -> Expr a -> Expr a
subst v e e' = let Right res = walk act e' 0 in res -- it can only be Right
    where
      act (Idx x) = do c <- get
                       return (if x == (c + v) then (shift c e)
                               else (Idx x))
      act e = return e

-- WARNING THIS IS NOT A SIMULTANEAOUS SUBST
subst_many :: Name a => [(Index, Expr a)] -> Expr a -> Expr a
subst_many ((v, e'):ss) e = subst v e' (subst_many ss e)
subst_many [] e = e

--- Closure Conversion ---

cc_act :: Name a => Expr a -> WalkResult a
cc_act f@(Fn n b) | free f == [] = return f
cc_act f@(Fn n b) = 
    return (Clo fv (Fn (n + num_fv) (subst_many
                             (zip  (take num_fv [0..]) fv)
                             (shift num_fv b))))
        where
          fv = map (\x -> (Idx x)) (free f)
          num_fv = length fv
cc_act e = return e


cc :: Name a => Expr a -> Expr a
cc e = let Right res = walk cc_act e 0 in res -- it can only be Right


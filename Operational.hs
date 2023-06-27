module Operational where
  import Data
  import Data.Map (Map)
  import qualified Data.Map as Map
  import Parser

  -- in order to avoid creation of two sets of operational rules, one for linear data, which is deallocated when used, and one for unrestricted data, which is never deallocated, we define this function to manage the differences
  updateStore :: Store -> Q -> V -> Store
  updateStore s q y
    = case Map.lookup y s of
        Nothing -> error "undefined variable"
        _       -> if q == UN then s else Map.delete y s

  -- function to assist in the creation of new variables
  nextAddr :: Store -> Int
  nextAddr s
    = case Map.lookup x s of
        Nothing -> n
        _       -> nextAddr' s (n + 1)
    where n = 1
          x = "a" ++ (show n)
          nextAddr' :: Store -> Int -> Int
          nextAddr' s n' = let x' = "a" ++ (show n')
                           in case Map.lookup x' s of
                               Nothing -> n'
                               _       -> nextAddr' s (n' + 1)

  -- substitution
  subst :: (V, Term) -> Term -> Term
  subst (x, y) (Var z) = if x == z then y else (Var z)
  subst (x, y) (B q b) = B q b
  subst (x, y) (If t0 t1 t2) = If (subst (x, y) t0) (subst (x, y) t1) (subst (x, y) t2)
  subst (x, y) (Pair q t1 t2) = Pair q (subst (x, y) t1) (subst (x, y) t2)
  subst (x, y) (Split t1 a b t2) = Split (subst (x, y) t1) a b (subst (x, y) t2)
  subst (x, y) (Lambda q z p t) = if x == z then (Lambda q z p t) else (Lambda q z p (subst (x, y) t))
  subst (x, y) (App t1 t2) = App (subst (x, y) t1) (subst (x, y) t2)
  subst (x, y) (SumLeft q p t) = SumLeft q p (subst (x, y) t)
  subst (x, y) (SumRight q p t) = SumRight q p (subst (x, y) t)
  subst (x, y) (Case t0 x' t1 y' t2)
    | x' == x && y' /= x = Case (subst (x, y) t0) x (subst (x, y) t1) y' (subst (x, y) t2)
    | x' /= x && y' == x = Case (subst (x, y) t0) x' (subst (x, y) t1) x (subst (x, y) t2)
    | otherwise = Case (subst (x, y) t0) x' (subst (x, y) t1) y' (subst (x, y) t2)

  -- evaluation function
  eval :: Store -> Term -> (Store, Term)
  eval s (B q b) = let addr = nextAddr s
                       x = "a" ++ show addr
                   in (Map.insert x (QValue q (RB b)) s, Var x)
  eval s (If (Var x) t1 t2) = let Just (QValue q b) = Map.lookup x s
                                  s' = updateStore s q x
                              in if b == RB True then (s', t1) else (s', t2)
  eval s (If e t1 t2) = let (s', v) = eval s e
                        in eval s' (If v t1 t2)
  eval s (Pair q (Var y) (Var z)) = let addr = nextAddr s
                                        x = "a" ++ show addr
                                    in (Map.insert x (QValue q (RPair y z)) s, Var x)
  eval s (Pair q (Var y) e) = let (s', v) = eval s e
                              in eval s' (Pair q (Var y) v)
  eval s (Pair q e t) = let (s', v) = eval s e
                        in eval s' (Pair q v t)
  eval s (Split (Var x) y z t) = let Just (QValue q (RPair y1 z1)) = Map.lookup x s
                                     s'  = updateStore s q x
                                     t'  = subst (y, Var y1) t
                                     t'' = subst (z, Var z1) t'
                                 in (s', t'')
  eval s (Split e y z t) = let (s', v) = eval s e
                           in eval s' (Split v y z t)
  eval s (Lambda q y p t) = let addr = nextAddr s
                                x = "a" ++ show addr
                            in (Map.insert x (QValue q (RLambda y p t)) s, Var x)
  eval s (App (Var x1) (Var x2)) = let Just (QValue q (RLambda y p t)) = Map.lookup x1 s
                                       s' = updateStore s q x1
                                       t' = subst (y, Var x2) t
                                   in (s', t')
  eval s (App (Var x1) e) = let (s', v) = eval s e
                            in eval s' (App (Var x1) v)
  eval s (App e t) = let (s', v) = eval s e
                     in eval s' (App v t)
  eval s (SumLeft q p (Var y)) = let addr = nextAddr s
                                     x = "a" ++ show addr
                                 in (Map.insert x (QValue q (RSumLeft p y)) s, Var x)
  eval s (SumLeft q p e) = let (s', v) = eval s e
                           in eval s' (SumLeft q p v)
  eval s (SumRight q p (Var y)) = let addr = nextAddr s
                                      x = "a" ++ show addr
                                  in (Map.insert x (QValue q (RSumRight p y)) s, Var x)
  eval s (SumRight q p e) = let (s', v) = eval s e
                            in eval s' (SumLeft q p v)
  eval s (Case (Var y) x1 t1 x2 t2) =
    case (Map.lookup y s) of
      Just (QValue q (RSumLeft p z)) -> let s'  = updateStore s q y
                                            res = subst (x1, Var z) t1
                                        in (s', res)
      Just (QValue q (RSumRight p z)) -> let s'  = updateStore s q y
                                             res = subst (x2, Var z) t2
                                         in (s', res)
  eval s (Case t0 x1 t1 x2 t2) = let (s', t0') = eval s t0
                                 in eval s' (Case t0' x1 t1 x2 t2)
  eval s (Roll p@(Rec (TVar a) (Pre q p')) (Var y)) = let addr = nextAddr s
                                                          x = "a" ++ show addr
                                                      in (Map.insert x (QValue q (RRoll p y)) s, Var x)
  eval s (Roll p e) = let (s', v) = eval s e
                      in eval s' (Roll p v)
  eval s (Unroll (Var x)) = let Just (QValue q (RRoll p y)) = Map.lookup x s
                                s' = updateStore s q x
                            in (s', Var y)
  eval s (Unroll e) = let (s', v) = eval s e
                      in eval s' (Unroll v)
  eval s (Fun f x t1 t2 term) = let term' = subst (x, Fun f x t1 t2 term) term
                                in (s, term')

  run :: String -> String -> (Store, Term)
  run store term = eval (Parser.parseStore store) (Parser.parseTerm term)

  example1 :: (Store, Term)
  example1 = run "" "lin \\x:lin Bool.x" -- (fromList [("a0",QValue LIN (RLambda "x" (Pre LIN TBool) (Var "x")))],Var "a0")

  example2, example2' :: (Store, Term)
  example2  = run "a1: lin \\x:lin Bool.x" "(a1)(z)" -- (fromList [],Var "z")
  example2' = run "a1: un \\x:lin Bool.x" "(a1)(z)"  -- (fromList [("a1",QValue UN (RLambda "x" (Pre LIN TBool) (Var "x")))],Var "z")

  example3 :: (Store, Term)
  example3 = run "a1: lin \\x:lin Bool.x" "case (lin inl:(lin Bool + lin Bool) (a1)(z)) of (inl x => lin \\y:lin Bool.x | inr y => lin \\x:lin Bool.y)" --(fromList [],Lambda LIN "y" (Pre LIN TBool) (Var "z"))

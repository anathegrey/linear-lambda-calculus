module Typechecker where
  import Data
  import Data.List
  import Parser

  -- predicate to express the types that can appear in a q-qualified data structure
  qType :: Q -> Type -> Bool
  qType q1 (Pre q2 t) = q1 <= q2

  -- predicate to express the qualifiers that can appear in an Environment
  qEnv :: Q -> Env -> Bool
  qEnv _ [] = True
  qEnv q ((y, Pre q' p) : g) = if q /= q' then False else qEnv q g

  -- remove element from Environment
  remove :: Env -> (V, Type) -> Env
  remove [] _ = []
  remove gs (x, Pre UN p) = if elem (x, Pre UN p) gs then delete (x, Pre UN p) gs else gs

  -- context difference check that linear variables do not appear and removes unrestricted variables
  contextDiff :: Env -> Env -> Env
  contextDiff g [] = g
  contextDiff g1 ((x, Pre LIN p) : g2) = let g3 = contextDiff g1 g2
                                         in if elem (x, Pre LIN p) g3 == False then g3 else error "linear variable still in environment after being used"
  contextDiff g1 ((x, Pre UN p) : g2) = let g3 = contextDiff g1 g2
                                        in remove g3 (x, Pre UN p)

  -- function to perform substitutions on types
  substType :: (String, PreType) -> Type -> Type
  substType (a,p) (Pre q TBool) = Pre q TBool
  substType (a,p) (Pre q (TypePair t1 t2)) = Pre q (TypePair (substType (a,p) t1) (substType (a,p) t2))
  substType (a,p) (Pre q (Arrow t1 t2)) = Pre q (Arrow (substType (a,p) t1) (substType (a,p) t2))
  substType (a,p) (Pre q (Plus t1 t2)) = Pre q (Plus (substType (a,p) t1) (substType (a,p) t2))
  substType (a,p) (Pre q (TVar b)) = if a == b then (Pre q p) else (Pre q (TVar b))
  substType (a,p) (Pre q (Rec (TVar b) t)) = if a == b then (Pre q (Rec (TVar b) (substType (b,p) t))) else (Pre q (Rec (TVar b) (substType (a,p) t)))

  -- Algorithmic type checking
  typing :: Env-> Term -> (Type, Env)
  typing ((y, Pre UN p) : gs) (Var x) = let (type1, res) = typing gs (Var x)                                                                                                                                                       -- A-UVar
                                        in if x == y then (Pre UN p, (y, Pre UN p) : gs) else (type1, [(y, Pre UN p)] ++ res)
  typing ((y, Pre LIN p) : gs) (Var x) = let (type1, res) = typing gs (Var x)                                                                                                                                                      -- A-LVar
                                         in if x == y then (Pre LIN p, gs) else (type1, [(y, Pre LIN p)] ++ res)
  typing g (B q b) = (Pre q TBool, g)                                                                                                                                                                                                 -- A-Bool
  typing g1 (If t1 t2 t3) = if g3 == g3' && type3 == type3' then (type3, g3) else error "cannot evaluate if statement"                                                                                                                -- A-If
    where (Pre q TBool, g2) = typing g1 t1
          (type3, g3) = typing g2 t2
          (type3', g3') = typing g2 t3
  typing g1 (Pair q t1 t2) = let (type1, g2) = typing g1 t1
                                 (type2, g3) = typing g2 t2                                                                                                                  -- A-Pair
                             in if (qType q type1) && (qType q type2) then (Pre q (TypePair type1 type2), g3) else error "Relation not possible between qualifiers"
  typing g1 (Split t1 x y t2) = let (Pre q (TypePair type1 type2), g2) = typing g1 t1                                                                        -- A-Split
                                    (type3, g3) = typing (g2 ++ [(x, type1), (y, type2)]) t2
                                in (type3, contextDiff g3 [(x, type1), (y, type2)])
  typing g1 (Lambda q x type1 t2)                                                                                                                                            -- A-Abs
    | q == UN = if g1 == g_un then (Pre q (Arrow type1 type2), g_un) else error "unrestricted type not consistent"
    | otherwise = (Pre q (Arrow type1 type2), contextDiff g2 [(x, type1)])
    where (type2, g2) = typing (g1 ++ [(x, type1)]) t2
          g_un = contextDiff g2 [(x, type1)]
  typing g1 (App t1 t2) = let (Pre q (Arrow type1 type2), g2) = typing g1 t1                                                                                                 -- A-App
                              (type3, g3) = typing g2 t2
                          in if type3 == type1 then (type2, g3) else error "Type not consistent in application"
  typing g (SumLeft q (Plus t1 t2) term) = let (type1, g1) = typing g term
                                           in if type1 == t1 && qType q t1 && qType q t2 then (Pre q (Plus t1 t2), g1) else error "Types not consistent in left injection"   -- T-Inl
  typing g (SumRight q (Plus t1 t2) term) = let (type2, g2) = typing g term
                                            in if type2 == t2 && qType q t1 && qType q t2 then (Pre q (Plus t1 t2), g2) else error "Types not consistent in right injection" -- T-Inr
  typing g (Case term x term1 y term2) = let (Pre q (Plus t1 t2), g1) = typing g term                                                                                        -- T-Case
                                             (t, g2) = typing (g1 ++ [(x, t1)]) term1
                                             (t', g3) = typing (g1 ++ [(y, t2)]) term2
                                         in if t == t' && g2 == g3 then (t, contextDiff g2 [(x, t1), (y, t2)]) else error "Inconsistent types in Case"
  typing g (Roll p@(Rec (TVar a) (Pre q p1)) term) = let t1 = substType (a, p) (Pre q p1)
                                                         (t1', g1) = typing g term
                                                     in if t1 == t1' then (Pre q p, g1) else error "Types not consistent in Roll"
  typing g (Unroll term) = let (Pre q' p@(Rec (TVar a) (Pre q p1)), g1) = typing g term
                               t1 = substType (a,p) (Pre q p1)
                           in if (qType q' (Pre q p1)) then (t1, g1) else error "LIN <= UN: trying to do UN <= LIN"
  typing g (Fun f x t1 t2 term)
    | qEnv UN g = if type1 == t2 then (Pre UN (Arrow t1 t2), g1) else error "Types not consistent in RecFun"
    | otherwise = error "Environment has linear types in RecFun"
    where (type1, g1) = typing (g ++ [(f, Pre UN (Arrow t1 t2)), (x, t1)]) term
  typing _ _ = error "pattern not found in function"

  -- parsing function
  run :: String -> String -> (Type, Env)
  run env term = typing (Parser.parseEnv env) (Parser.parseTerm term)

  -- examples
  example1 :: (Type, Env)
  example1 = run "x : un Bool" "x"  -- (Pre UN TBool,[("x",Pre UN TBool)])

  example1' :: (Type, Env)
  example1' = run "x : lin Bool" "x"  -- (Pre LIN TBool,[])

  example2 :: (Type, Env)
  example2 = run "" "un \\x:un Bool.x"  -- (Pre UN (Arrow (Pre UN TBool) (Pre UN TBool)),[])

  example2' :: (Type, Env)
  example2' = run "" "lin \\x:lin Bool.x" -- (Pre LIN (Arrow (Pre LIN TBool) (Pre LIN TBool)),[])

  example2'' :: (Type, Env)
  example2'' = run "" "lin \\x:un Bool.x"  -- (Pre LIN (Arrow (Pre UN TBool) (Pre UN TBool)),[])

  example2''' :: (Type, Env)
  example2''' = run "" "un \\x:lin Bool.x"  -- *** Exception: unrestricted type not consistent

  example3 :: (Type, Env)
  example3 = run "x : un Bool, y : un Bool" "un <x, y>"  -- (Pre UN (TypePair (Pre UN TBool) (Pre UN TBool)),[("x",Pre UN TBool),("y",Pre UN TBool)])

  example3' :: (Type, Env)
  example3' = run "x:lin Bool, y:lin Bool" "lin <x,y>"  -- (Pre LIN (TypePair (Pre LIN TBool) (Pre LIN TBool)),[])

  example3'' :: (Type, Env)
  example3'' = run "x: lin Bool, y: lin Bool" "un <x,y>"  -- *** Exception: LIN <= UN: trying to do UN <= LIN

  example3''' :: (Type, Env)
  example3''' = run "x: un Bool, y: un Bool" "lin <x,y>"  -- (Pre LIN (TypePair (Pre UN TBool) (Pre UN TBool)),[("x",Pre UN TBool),("y",Pre UN TBool)])

  example3'''' :: (Type, Env)
  example3'''' = run "x: lin Bool, y: un Bool" "lin <x,y>"  -- (Pre LIN (TypePair (Pre LIN TBool) (Pre UN TBool)),[("y",Pre UN TBool)])

  example3''''' :: (Type, Env)
  example3''''' = run "x: lin Bool, y: un Bool" "un <x,y>"  -- *** Exception: LIN <= UN: trying to do UN <= LIN

  example4 :: (Type, Env)
  example4 = run "x : lin Bool, y: un Bool" "if un True then x else y"  -- (Pre LIN TBool,[("y",Pre UN TBool)])

  example5 :: (Type, Env)
  example5 = run "x:lin Bool, y:un Bool" "if lin False then x else y"  -- (Pre UN TBool,[("x",Pre LIN TBool),("y",Pre UN TBool)])

  example6 :: (Type, Env)
  example6 = run "x: un un Bool -> un Bool, y: un Bool" "(x)(y)"  -- (Pre UN TBool,[("x",Pre UN (Arrow (Pre UN TBool) (Pre UN TBool))),("y",Pre UN TBool)])

  example6' :: (Type, Env)
  example6' = run "x: un lin Bool -> un Bool, y: un Bool" "(x)(y)"  -- *** Exception: Type not consistent in application

  example6'' :: (Type, Env)
  example6'' = run "x: lin un Bool -> un Bool, y: un Bool" "(x)(y)"  -- (Pre UN TBool,[("y",Pre UN TBool)])

  example7 :: (Type, Env)
  example7 = run "y: un Bool" "(un \\x:un Bool.x)(y)"  -- (Pre UN TBool,[("y",Pre UN TBool)])

  example7' :: (Type, Env)
  example7' = run "y: un Bool" "(lin \\x:un Bool.x)(y)"  -- (Pre UN TBool,[("y",Pre UN TBool)])

  example8 :: (Type, Env)
  example8 = run "x:un Bool, y:un Bool" "split un <x,y> as a, b in (un <a,b>)"  -- (Pre UN (TypePair (Pre UN TBool) (Pre UN TBool)),[("x",Pre UN TBool),("y",Pre UN TBool)])

  example8' :: (Type, Env)
  example8' = run "x:lin Bool, y:lin Bool" "split lin <x,y> as a, b in (un <a,b>)"  -- *** Exception: LIN <= UN: trying to do UN <= LIN

  example8'' :: (Type, Env)
  example8'' = run "x:lin Bool, y:lin Bool" "split lin <x,y> as a, b in (lin <a,b>)"  -- (Pre LIN (TypePair (Pre LIN TBool) (Pre LIN TBool)),[])

  example9 :: (Type, Env)
  example9 = run "x:lin Bool, y:lin Bool" "lin inl:(lin Bool + lin Bool) x" -- (Pre LIN (Plus (Pre LIN TBool) (Pre LIN TBool)),[("y",Pre LIN TBool)])

  example9' :: (Type, Env)
  example9' = run "x: lin Bool, y: lin Bool, z: lin Bool, t: lin Bool, w: lin Bool" "lin inr:(lin Bool + lin Bool) x"

  example10 :: (Type, Env)
  example10 = run "x: lin Bool, y: lin Bool, z: lin Bool, t: lin Bool, w: lin Bool" "case (lin inr:(lin Bool + lin Bool) x) of (inl y => w | inr z => t)"

  example11 :: (Type, Env)
  example11 = run "a: un Bool" "roll: rec a.un Bool a"

  example12 :: (Type, Env)
  example12 = run "x:un (rec a.un Bool)" "unroll x"

  example13 :: (Type, Env)
  example13 = run "" "fun f (x:lin Bool): lin Bool x"

import Data.Maybe

data Expression v f
 = Var v
 | Function f [Expression v f] 
 deriving (Eq)

instance (Show v, Show f) => Show (Expression v f) where
    show (Var v) = show v
    show (Function f xs) = show f ++ "(" ++ args ++ ")"
                where
                    xss = show xs
                    args = drop 1 (take (length xss -1) xss)

compareVar :: Eq v => v -> Expression v f -> Bool
compareVar x (Var y) = x == y
compareVar _ _ = False

variables :: Expression v f -> [v]
variables (Var v) = [v]
variables (Function f xs) = concat (map variables xs)

signaturee :: Expression v f -> [(f, Int)]
signaturee (Var _) = []
signaturee (Function f xs) = (f, length xs):concat (map signaturee xs)

infixl *!
(*!) :: Eq v => Expression v f -> [(v, Expression v f)] -> Expression v f
(*!) t [] = t
(*!) t@(Var var1) ((var2, term):xs) = if var1 == var2 then term
                                                          else t *! xs
(*!) (Function f xs) s = Function f (map (\t -> t *! s) xs)

infix @@
(@@) :: Eq v => [(v, Expression v f)] -> [(v, Expression v f)] -> [(v, Expression v f)]
(@@) sigma tau = xs1 ++ xs2
  where
    xs0 = map (\(var,term) -> (var, term *! sigma)) tau
    xs1 = filter (not.(uncurry compareVar)) xs0
    xs2 = filter (\(var,_) -> not (elem var (map fst tau))) sigma

unify :: (Eq v, Eq f) => [(Expression v f, Expression v f)] -> Maybe ([(v, Expression v f)])
unify [] = Just []
unify ((s@(Function _ xs1), t@(Function _ xs2)):xs) =
      let sFinal = signaturee s !! 0
          tFinal = signaturee t !! 0
      in if sFinal /= tFinal then Nothing
                         else unify (zip xs1 xs2 ++ xs)
unify ((s@(Var v), t):xs) =
    if compareVar v t then unify xs
    else
      if elem v (variables t) || isNothing (unify nextPs) then Nothing
      else return $ fromJust (unify nextPs) @@ [(v, t)]
           where
             nextPs = map (\(var,term) -> (var *! [(v, t)], term *! [(v, t)])) xs
unify ((s, t@(Var _)):xs) = unify ((t,s):xs)

ex0 = [(Function "f" [Var "x", Function "g" [Var "z"]],

        Function "f" [Function "g" [Var "z"], Var "x"])]


ex1 = [(Function "f" [Function "g" [Function "k" [Var "x"]], Var "y"],

       Function "f" [Var "y", Function "g" [Var "x"]])]


ex2 = [(Function "f" [Function "g" [Var "x"], Var "x"],

        Function "f" [Var "y", Function "g" [Var "z"]])]

ex3 = [(Function "f" [Var "x", Function "g" [Var "a"]],

        Function "f" [Var "y", Var "y"])]


ex4 = [(Function "g" [Var "x"],

        Function "f" [Var "x"])]

ex5 = [(Function "f" [Function "g" [Var "x"], Var "x"],

        Function "f" [Var "x", Var "x"])]

ex6 = [(Function "g" [Var "x"],

        Function "g"[])]


exs = [ex0, ex1, ex2, ex3, ex4, ex5, ex6]
unifs = map unify exs
z = zip exs unifs

main = printPbs z
  where
    printPbs [] = return ()
    printPbs ((ex,unifier):z) = do
        putStrLn $ "Unify" ++ show ex
        putStrLn $ "\t" ++ show unifier ++ "\n"
        printPbs z
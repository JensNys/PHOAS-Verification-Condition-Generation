{- HLINT ignore "Use camelCase" -}
module Vcg.ProgrammingLanguage where
import Data.Map 
import Control.Monad.State
-- here we define the program syntax and its semantics. 
-- we also define the syntax and semantics for logic variables

--type Var = String
type Value = Int
type (Store v) = Map X v-- [(X,v)]
--program variables. They are immutable location
type X = String
--function names
type F = String


data Prog = Fun F [X] Stm

data Relop = Equal | LessThan | GreaterThan | LessThanEqual | GreaterThanEqual
  deriving (Eq)
instance Show Relop where
  show Equal = "=="
  show LessThan ="<"
  show GreaterThan=">"
  show LessThanEqual = "<="
  show GreaterThanEqual = ">="

data Bexp = Compare Relop Exp Exp
    deriving (Eq,Show)


data Exp = Lit Value
    | Var X
    | Add Exp Exp
    | Mul Exp Exp
    | Minus Exp Exp
  deriving (Eq,Show)
  
data Stm = Expr Exp
    | Assign X Exp -- x := Stm (update a variable)
    | Let X Exp Stm -- let X = Stm where Stm (make a new variable)
    | Seq Stm Stm --e1;e2
    | If Bexp Stm Stm -- if bexp then stm else stm
  deriving (Eq,Show)




-- this is the same type as Stm-> Valuation ->Maybe Value
-- interp ::Stm -> ReaderT Valuation Maybe Integer

deleteL ::Eq a => a-> [(a,b)]-> [(a,b)]
deleteL _ [] = []
deleteL a ((a',b):xs) = if a'==a then xs else (a',b):deleteL a xs

change :: Eq a => a->b-> [(a,b)]-> [(a,b)]
change _ _ [] = []
change a b ((a',b'):xs) = if a==a' then ((a',b):xs) else ((a',b'):(change a b xs))

pushL :: Eq a => a->b-> [(a,b)]-> [(a,b)]
pushL _ _ [] = []
pushL a b l = (a,b):l

popL :: Eq a => [(a,b)]-> [(a,b)]
popL [] = []
popL ((_,_):l) = l



-- the monadic computation fails if we try to lookup a variable that is not in the store.
lookupVarSfail:: X->StateT (Store Value) Maybe Value
lookupVarSfail var = do env <- get
                        case (Data.Map.lookup var env) of
                            Just a -> return a
                            Nothing -> lift Nothing
-- the computation doesn't fail if we try to lookup a variable that is not in the store, it just returns Nothing.
lookupVarSafe:: X->StateT (Store Value) Maybe (Maybe Value)
lookupVarSafe var = do env <- get
                       return (Data.Map.lookup var env) 
putS :: X->Value -> StateT (Store Value) Maybe Value
putS var c = do env <- get
                put (insert var c env)
                return c

restore :: X-> Maybe Value -> StateT (Store Value) Maybe ()
restore var Nothing = do env <- get
                         put (delete var env)
restore var (Just val) = do env <- get
                            put (insert var val env)






--assign :: X->Value -> StateT (Store Value) Maybe Value
--assign var c = state (\m -> (c,insert var c m))


--pop :: StateT (Store Value) Maybe Value
--pop = state (\m -> (snd (head m),tail m))

--remove :: X-> StateT (Store Value) Maybe ()
--remove x = state (\m -> ((),deleteL x m))


toFunc :: Relop -> (Int->Int->Bool)
toFunc Equal = (==)
toFunc LessThan = (<)
toFunc GreaterThan = (>)
toFunc LessThanEqual = (<=)
toFunc GreaterThanEqual = (>=)

interpb :: Bexp -> StateT (Store Value) Maybe Bool
interpb (Compare op s1 s2) = do x <- interp_exp s1
                                y <- interp_exp s2
                                return (toFunc op x y)
-- this is a naive version where i don't use monad functionality 
-- Stm -> Valuation -> Maybe (Value, Valuation)





interp_exp :: Exp->StateT (Store Value) Maybe Value
interp_exp (Lit c) = return c
interp_exp (Var a) = lookupVarSfail a
interp_exp (Add s1 s2) = do x <- interp_exp s1
                            y <- interp_exp s2
                            return (x+y)
interp_exp (Mul s1 s2) = do x <- interp_exp s1
                            y <- interp_exp s2
                            return (x*y)
interp_exp (Minus s1 s2) = do x <- interp_exp s1
                              y <- interp_exp s2
                              return (x-y)




interp :: Stm -> StateT (Store Value) Maybe Value
interp (Expr e) = interp_exp e
interp (Assign var s) = do x <- interp_exp s -- it changes the variable in the valuation and
                           putS var x --i don't use monad put here for now because it would return () instead of an integer. I could add in a later stage that it returns () but i have to take into account that computations "() + 4" would return a failed computation Nothing
interp (Let var s1 s2) = do x <- interp_exp s1 -- p -- in a later stage we could let this computation fail if x is already a variable.
                            previous <- lookupVarSafe var
                            putS var x
                            result <- interp s2
                            restore var previous
                            return result
interp (Seq s1 s2) =do _ <- interp s1
                       interp s2
interp (If bexp s1 s2) = do b <- interpb bexp
                            if b then (interp s1) else (interp s2)








-- examples
add_5_to_1_with_var :: Stm
add_5_to_1_with_var = Let "x" ((Lit 5)) (Expr (Add (Var "x") (Lit 1)))

testingScope :: Stm
testingScope = Let "x" ((Lit 5)) (Seq (Assign "x" ( (Lit 1))) (Expr (Var "x")))

testingScope2 :: Stm
testingScope2 = Seq (Let "x" ((Lit 5)) (Expr (Lit 5))) (Expr (Lit 7))

testingScope3 :: Stm
testingScope3 = Let "y" (Lit 2) (Let "x" (Lit 3) (Seq (Let "y" (Lit 4) (Assign "x" ((Lit 2)))) (Expr (Add (Var "x") (Var "y")))))

absoluteValueStm :: Stm
absoluteValueStm = Let "x" (Lit (-5)) (If (Compare LessThan (Var "x") (Lit 0)) (Expr (Minus (Lit 0) (Var "x"))) (Expr (Var "x")))


absoluteValue :: Prog
absoluteValue = Fun "abs" ["x"] (If (Compare LessThan (Var "x") (Lit 0)) (Expr (Minus (Lit 0) (Var "x"))) (Expr (Var "x")))


-- Program -> Parameters -> executed program.
execute :: Prog -> [Value]-> Maybe Value
execute (Fun _ l s) pars = fmap fst (runStateT (interp s) (fromList (zip l pars)))


runStatement :: Stm -> Maybe (Value,(Store Value))
runStatement s = (runStateT (interp s) empty)

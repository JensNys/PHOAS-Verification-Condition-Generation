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
  deriving (Eq,Show)

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
    | Let X Stm Stm -- let X = Stm where Stm (make a new variable)
    | Seq Stm Stm --e1;e2
    | If Bexp Stm Stm -- if bexp then stm else stm
    | Recurse [Stm]
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

{- getCurrentBindings :: [X] -> StateT (Store Value) Maybe ([Maybe Value])
getCurrentBindings l = getCurrentBindings' l []

getCurrentBindings' :: [X] -> [Value]-> StateT (Store Value) Maybe [Maybe Value]
getCurrentBindings' (x:l) acc = do v <- lookupVarSafe x 
                                   getCurrentBindings' l (v:acc)
getCurrentBindings' [] acc = return acc


restoreCurrentBindings :: [(X,Maybe Value)] -> StateT (Store Value) Maybe ()
restoreCurrentBindings l = getCurrentBindings' l [] -}



--getAllBindings :: StateT (Store Value) Maybe (Store Value)
--getAllBindings = get

--replaceAllBindings = (\store -> (,empty))

--restoreAllBindings :: (Store Value) -> StateT (Store Value) Maybe (Store Value)
--restoreAllBindings = put

--restoreCurrentBindings' :: [X] -> [Value]-> StateT (Store Value) Maybe [Maybe Value]
--restoreCurrentBindings' ((key,value):l) acc = do v <- restore
--                                       getCurrentBindings' l (v:acc)
--restoreCurrentBindings' [] acc = return acc




insertS :: X->Value -> StateT (Store Value) Maybe Value
insertS var c = do env <- get
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




interp_list' :: [Stm]->[Value]->Prog-> StateT (Store Value) Maybe [Value]
interp_list' (stm:rest) acc prog = do v <- (interp stm prog)
                                      interp_list' rest (v:acc) prog
interp_list' [] acc prog = return acc

interp_list :: [Stm]->Prog-> StateT (Store Value) Maybe [Value]
interp_list l prog = interp_list' l [] prog


interp :: Stm ->Prog-> StateT (Store Value) Maybe Value
interp (Expr e) p = interp_exp e
interp (Assign var s) p = do x <- interp_exp s -- it changes the variable in the valuation and
                             insertS var x --i don't use monad put here for now because it would return () instead of an integer. I could add in a later stage that it returns () but i have to take into account that computations "() + 4" would return a failed computation Nothing
interp (Let var s1 s2) p = do x <- interp s1 p
                              previous <- lookupVarSafe var
                              insertS var x
                              result <- interp s2 p
                              restore var previous
                              return result
interp (Seq s1 s2) p =do _ <- interp s1 p
                         interp s2 p
interp (If bexp s1 s2) p = do b <- interpb bexp
                              if b then (interp s1 p) else (interp s2 p)
interp (Recurse stmlist) (Fun n paramnames stm) = do 
                                state_before_call <- get --save the current state
                                valueList <- interp_list stmlist (Fun n paramnames stm) -- compute the values the function will be called with
                                put (fromList (zip paramnames valueList)) -- bind the parameters to the store and interpret with that
                                result <- interp stm (Fun n paramnames stm) -- execute the body
                                put state_before_call --restore the state
                                return result --return the result
                                
  
  









-- examples
add_5_to_1_with_var :: Stm
add_5_to_1_with_var = Let "x" (Expr (Lit 5)) (Expr (Add (Var "x") (Lit 1)))

testingScope :: Stm
testingScope = Let "x" (Expr (Lit 5)) (Seq (Assign "x" ( (Lit 1))) (Expr (Var "x")))

testingScope2 :: Stm
testingScope2 = Seq (Let "x" (Expr (Lit 5)) (Expr (Lit 5))) (Expr (Lit 7))

testingScope3 :: Stm
testingScope3 = Let "y" (Expr (Lit 2)) (Let "x" (Expr (Lit 3)) (Seq (Let "y" (Expr (Lit 4)) (Assign "x" ( (Lit 2)))) (Expr (Add (Var "x") (Var "y")))))

absoluteValueStm :: Stm
absoluteValueStm = Let "x" (Expr (Lit (-5))) (If (Compare LessThan (Var "x") ( (Lit 0))) (Expr (Minus ( (Lit 0)) (Var "x"))) (Expr (Var "x")))


absoluteValue :: Prog
absoluteValue = Fun "abs" ["x"] (If (Compare LessThan (Var "x") (Lit 0)) (Expr (Minus (Lit 0) (Var "x"))) (Expr (Var "x")))

mySum :: Prog
mySum  = Fun "sum" ["x"] (If (Compare Equal (Lit 0) (Var "x")) 
                                  (Expr (Lit 0))
                                  (Let "sum_until_x_min_1" (Recurse [Expr (Minus (Var "x") (Lit 1))]) 
                                    (Expr (Add (Var "x") (Var "sum_until_x_min_1")))))

runSum :: Int -> Maybe Int
runSum n = execute mySum [n]

-- Program -> Parameters -> executed program.

execute :: Prog -> [Value]-> Maybe Value
execute (Fun name l s) pars = fmap fst (runStateT (interp s (Fun name l s)) (fromList (zip l pars)))


runStatement :: Stm -> Maybe (Value,(Store Value))
runStatement s = (runStateT (interp s (Fun "" [] s)) empty)

{- HLINT ignore "Use camelCase" -}
module ProgrammingLanguage where
import Data.Map 
import Control.Monad.State
-- here we define the program syntax and its semantics. 
-- we also define the syntax and semantics for logic variables

--type Var = String
type Value = Int

type (Store v) = Map X v
--program variables. They are immutable location
type X = String
--function names
type F = String




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
    | Assign X Stm -- x := Stm (update a variable)
    | Let X Stm Stm -- let X = Stm where Stm (make a new variable)
    | Seq Stm Stm -- stm1; stm2 (execute statements after one another)
    | If Bexp Stm Stm -- if bexp then stm else stm
    | Recurse [Stm] -- call the current function again with these parameters.
  deriving (Eq,Show)

data Prog = Fun F [X] Stm
  deriving (Eq,Show)


-- semantics

type Eval a = StateT (Store Value) Maybe a


-- the monadic computation fails if we try to lookup a variable that is not in the store, returns the value otherwise.
lookupVarFail:: X->Eval Value
lookupVarFail var =  do env <- get
                        case (Data.Map.lookup var env) of
                            Just a -> return a
                            Nothing -> lift Nothing

-- the computation doesn't fail if we try to lookup a variable that is not in the store, it just returns Nothing.
lookupVarSafe:: X->Eval (Maybe Value)
lookupVarSafe var = do env <- get
                       return (Data.Map.lookup var env) 

insertInState :: X->Value ->Eval ()
insertInState var c = do env <- get
                         put (insert var c env)

deleteInState :: X -> Eval ()
deleteInState var = do env <- get
                       put (delete var env)

restore :: X-> Maybe Value -> Eval ()
restore var Nothing = deleteInState var
restore var (Just val) = insertInState var val


toFunc :: Relop -> (Int->Int->Bool)
toFunc Equal = (==)
toFunc LessThan = (<)
toFunc GreaterThan = (>)
toFunc LessThanEqual = (<=)
toFunc GreaterThanEqual = (>=)

interpb :: Bexp -> Eval Bool
interpb (Compare op s1 s2) = do x <- interp_exp s1
                                y <- interp_exp s2
                                return (toFunc op x y)


interp_exp :: Exp-> Eval Value
interp_exp (Lit c) = return c
interp_exp (Var a) = lookupVarFail a
interp_exp (Add s1 s2) = do x <- interp_exp s1
                            y <- interp_exp s2
                            return (x+y)
interp_exp (Mul s1 s2) = do x <- interp_exp s1
                            y <- interp_exp s2
                            return (x*y)
interp_exp (Minus s1 s2) = do x <- interp_exp s1
                              y <- interp_exp s2
                              return (x-y)




interp_list' :: [Stm]->[Value]->Prog-> Eval [Value]
interp_list' (stm:rest) acc prog = do v <- (interp stm prog)
                                      interp_list' rest (v:acc) prog
interp_list' [] acc prog = return acc

interp_list :: [Stm]->Prog-> Eval [Value]
interp_list l prog = interp_list' l [] prog


interp :: Stm ->Prog-> Eval Value
interp (Expr e) p = interp_exp e
interp (Assign var s) p = do x <- interp s p -- evaluate the value that will be given to the variable
                             insertInState var x -- bind this value to the variable name
                             return x -- we consider the evaluated value to be the result
interp (Let var s1 s2) p = do x <- interp s1 p -- evaluate the value that will be given to the variable
                              previous <- lookupVarSafe var -- save the previous binding to this variable name
                              insertInState var x -- bind the new value to the variable name
                              result <- interp s2 p -- evaluate the body of let under this new store
                              restore var previous -- restore the state to what it was before this binding
                              return result -- return the result
interp (Seq s1 s2) p =do _ <- interp s1 p -- evaluate the first statement
                         interp s2 p -- evaluate the second statement
interp (If bexp s1 s2) p = do b <- interpb bexp -- evaluate the expression
                              if b then (interp s1 p) else (interp s2 p) -- evaluate 1 subbranch based on the expression
interp (Recurse stmlist) (Fun n paramnames stm) = do 
                                state_before_call <- get --save the current state
                                valueList <- interp_list stmlist (Fun n paramnames stm) -- compute the values the function will be called with
                                put (fromList (zip paramnames valueList)) -- bind the parameters to the store and interpret with only these variables in scope
                                result <- interp stm (Fun n paramnames stm) -- execute the body
                                put state_before_call -- restore the state
                                return result -- return the result
                                
  
  











-- Program -> Parameters -> executed program.

execute :: Prog -> [Value]-> Maybe Value
execute (Fun name l s) pars = fmap fst (runStateT (interp s (Fun name l s)) (fromList (zip l pars)))





runStatement :: Stm -> Maybe (Value,(Store Value))
runStatement s = (runStateT (interp s (Fun "" [] s)) empty)

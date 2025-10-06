module ProgramAssertionSemantics where
import Data.Map as M
import Control.Monad.State
import Control.Monad.Trans.Maybe
import Control.Monad.Cont
-- here we define the program syntax and its semantics. 
-- we also define the syntax and semantics for logic variables

type Var = String
type Const = Int
type Valuation = Map Var Const

--program variables. They are immutable location
type X = String
--function names
type F = String


data Prog = Fun F [X] Stm

data Relop = Equal | LessThan | GreaterThan | NotEqual | LessThanEqual | GreaterThanEqual

data Bexp = Compare Relop Stm Stm

data Stm = Lit Const
    | Var X
    | Add Stm Stm
    | Mul Stm Stm
    | Min Stm Stm
    | Assign X Stm -- x := Stm (update a variable)
    | Let X Stm Stm -- let X = Stm where Stm (make a new variable)
    | Seq Stm Stm --e1;e2
    | If Bexp Stm Stm -- if bexp then stm else stm


-- this is the same type as Stm-> Valuation ->Maybe Const
-- interp ::Stm -> ReaderT Valuation Maybe Integer


lookupVar:: Var->StateT Valuation Maybe Const
lookupVar var = do env <- get
                   case (M.lookup var env) of
                        Just a -> return a
                        Nothing -> lift Nothing



putMap :: Var->Const -> StateT Valuation Maybe Const
putMap var c = state (\m -> (c,insert var c m))
                
toFunc :: Relop -> (Int->Int->Bool)
toFunc Equal = (==)
toFunc LessThan = (<)
toFunc GreaterThan = (>)
toFunc NotEqual = (/=)
toFunc LessThanEqual = (<=)
toFunc GreaterThanEqual = (>=)

interpb :: Bexp -> StateT Valuation Maybe Bool
interpb (Compare op s1 s2) = do x <- interp s1
                                y <- interp s2
                                return ((toFunc op) x y)
-- this is a naive version where i don't use monad functionality 
-- Stm -> Valuation -> Maybe (Const, Valuation)
interp :: Stm -> StateT Valuation Maybe Const
interp (Lit c) = return c
interp (Var a) = lookupVar a
interp (Add s1 s2) = do x <- interp s1
                        y <- interp s2
                        return (x+y)
interp (Mul s1 s2) = do x <- interp s1
                        y <- interp s2
                        return (x*y)
interp (Min s1 s2) = do x <- interp s1
                        y <- interp s2
                        return (x-y)

interp (Assign var s) = do x <- interp s -- it changes the variable in the valuation and
                           putMap var x --i don't use monad put here for now because it would return () instead of an integer. I could add in a later stage that it returns () but i have to take into account that computations "() + 4" would return a failed computation Nothing
interp (Let var s1 s2) = do x <- interp s1 -- p -- in a later stage we could let this computation fail if x is already a variable.
                            oldState <- get
                            _ <- putMap var x
                            result <- interp s2
                            put oldState
                            return result

interp (Seq s1 s2) =do _ <- interp s1
                       interp s2
interp (If bexp s1 s2) = do b <- interpb bexp
                            if b then (interp s1) else (interp s2)
    


add_5_to_1_with_var :: Stm
add_5_to_1_with_var = Let "x" (Lit 5) (Add (Var "x") (Lit 1))

testingScope :: Stm
testingScope = Let "x" (Lit 5) (Seq (Assign "x" (Lit 1)) (Var "x"))

testingScope2 :: Stm
testingScope2 = Seq (Let "x" (Lit 5) (Lit 5)) (Lit 7)


absoluteValueStm :: Stm 
absoluteValueStm = Let "x" (Lit (-5)) (If (Compare LessThan (Var "x") (Lit 0)) (Min (Lit 0) (Var "x")) (Var "x"))


absoluteValue :: Prog
absoluteValue = Fun "abs" ["x"] (If (Compare LessThan (Var "x") (Lit 0)) (Min (Lit 0) (Var "x")) (Var "x"))


-- Program -> Parameters -> executed program.
exec :: Prog -> [Const]-> Maybe Const
exec (Fun _ l s) pars = fmap fst (runStateT (interp s) (fromList (zip l pars)))


runStatement :: Stm -> Maybe (Const,Valuation)
runStatement s = (runStateT (interp s) empty) 


------------------------------------------------------------------------------------------------
-- we define the syntax for Assertions


data Prop = T 
    | F 
    | Cmp Relop Int Int 
    | And Prop Prop 
    | Or Prop Prop 
    | Implies Prop Prop
    | Exist (Const->Prop) 
    | Forall (Const->Prop)


type L = String -- logic variables

data Contract = MkContract [L] Prop Prog (Int->Prop) -- forAll logicVariables {Precondition} Program {Int->Postcondition}




absoluteValueContract :: Contract
--absoluteValueContract = MkContract ["x"] T absoluteValue (\x -> And (Cmp GreaterThan x 0) (Cmp GreaterThanEqual "x" x))
absoluteValueContract = MkContract ["x"] T absoluteValue (\x -> And (Cmp GreaterThan x 0) (T))


newtype Wpure a = Wpure {runWpure :: (a->Prop)->Prop} 
instance Functor Wpure where
  fmap = liftM

instance Applicative Wpure where
  pure a = Wpure $ (\post->post a)
  (<*>) = ap

instance Monad Wpure where
    return = pure
    c >>= k = Wpure $ (\post-> (runWpure c) (\a->runWpure (k a) post))


block :: Wpure a
block = Wpure $ (\post->T)

fail :: Wpure a
fail = Wpure $ (\post->F)

angelic :: Maybe String -> Wpure Const
angelic _ = Wpure $ (\post-> Exist (\v->post v))

demonic :: Maybe String -> Wpure Const
demonic _ = Wpure $ (\post-> Forall (\v->post v))

add :: Wpure a->Wpure a -> Wpure a
add m1 m2 = Wpure $ (\post -> Or ((runWpure m1) post) ((runWpure m2) post))

multiply :: Wpure a->Wpure a -> Wpure a
multiply m1 m2 = Wpure $ (\post -> And ((runWpure m1) post) ((runWpure m2) post))

assert :: Prop -> Wpure ()
assert p = Wpure $ (\post -> And p (post ()))

assume :: Prop -> Wpure ()
assume p = Wpure $ (\post -> Implies p (post ()))





newtype Wstore a =Wstore {runWstore :: (a->Valuation->Prop)->Valuation->Prop}
instance Functor Wstore where
  fmap = liftM
instance Applicative Wstore where
  pure a = Wstore $ (\post store->post a store)
  (<*>) = ap

instance Monad Wstore where
    return = pure
    c >>= k = Wstore $ (\post store1-> (runWstore c) (\a store2->runWstore (k a) post store2) store1)



{- 
-- TODO Add another Prop for failure?
-- TODO monad instance
type MWstore a = StateT Valuation (MaybeT (Cont Prop))
---
evalStore :: Wstore a -> Valuation -> Wpure a
evalStore m store = Wpure $ (\post-> m (\a store'->post a) store)

--evalStore' :: Wstore a -> Valuation -> Wpure a
--evalStore' m store = Wpure $ (\post-> (runStateT m) store (\a ->post (fst a)))


push :: X->Const->Wstore ()
push x v = (\post store-> post () (insert x v store))

pop :: Wstore ()
pop = (\post store -> post () store)




 -}
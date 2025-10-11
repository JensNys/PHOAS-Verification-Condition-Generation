module ProgramAssertionSemantics where
import Control.Monad.State
import Control.Monad.Trans.Maybe
--import Control.Monad.Cont
import Data.Map as M
-- here we define the program syntax and its semantics. 
-- we also define the syntax and semantics for logic variables

--type Var = String
type Value = Int
type Store = [(X,Value)]
--program variables. They are immutable location
type X = String
--function names
type F = String


data Prog = Fun F [X] Stm

data Relop = Equal | LessThan | GreaterThan | NotEqual | LessThanEqual | GreaterThanEqual

data Bexp = Compare Relop Stm Stm

data Stm = Lit Value
    | Var X
    | Add Stm Stm
    | Mul Stm Stm
    | Min Stm Stm
    | Assign X Stm -- x := Stm (update a variable)
    | Let X Stm Stm -- let X = Stm where Stm (make a new variable)
    | Seq Stm Stm --e1;e2
    | If Bexp Stm Stm -- if bexp then stm else stm


-- this is the same type as Stm-> Valuation ->Maybe Value
-- interp ::Stm -> ReaderT Valuation Maybe Integer

deleteL ::Eq a => a-> [(a,b)]-> [(a,b)]
deleteL _ [] = []
deleteL a ((a',b):xs) = if (a'==a) then xs else (a',b):(deleteL a xs)

change :: Eq a => a->b-> [(a,b)]-> [(a,b)]
change _ _ [] = []
change a b ((a',b'):xs) = if (a==a') then ((a',b):xs) else ((a',b'):(change a b xs))

pushL :: Eq a => a->b-> [(a,b)]-> [(a,b)]
pushL _ _ [] = []
pushL a b l = (a,b):l

popL :: Eq a => [(a,b)]-> [(a,b)]
popL [] = []
popL ((_,_):l) = l




lookupVarS:: X->StateT Store Maybe Value
lookupVarS var = do env <- get
                    case (Prelude.lookup var env) of
                         Just a -> return a
                         Nothing -> lift Nothing
putS :: X->Value -> StateT Store Maybe Value
putS var c = state (\m -> (c,(var,c):m))



assign :: X->Value -> StateT Store Maybe Value
assign var c = state (\m -> (c,change var c m))


pop :: StateT Store Maybe Value
pop = state (\m -> (snd (head m),tail m))

remove :: X-> StateT Store Maybe ()
remove x = state (\m -> ((),deleteL x m))

                
toFunc :: Relop -> (Int->Int->Bool)
toFunc Equal = (==)
toFunc LessThan = (<)
toFunc GreaterThan = (>)
toFunc NotEqual = (/=)
toFunc LessThanEqual = (<=)
toFunc GreaterThanEqual = (>=)

interpb :: Bexp -> StateT Store Maybe Bool
interpb (Compare op s1 s2) = do x <- interp s1
                                y <- interp s2
                                return ((toFunc op) x y)
-- this is a naive version where i don't use monad functionality 
-- Stm -> Valuation -> Maybe (Value, Valuation)

    
interp :: Stm -> StateT Store Maybe Value
interp (Lit c) = return c
interp (Var a) = lookupVarS a
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
                           assign var x --i don't use monad put here for now because it would return () instead of an integer. I could add in a later stage that it returns () but i have to take into account that computations "() + 4" would return a failed computation Nothing
interp (Let var s1 s2) = do x <- interp s1 -- p -- in a later stage we could let this computation fail if x is already a variable.
                            _ <- putS var x
                            result <- interp s2
                            remove var
                            return result
interp (Seq s1 s2) =do _ <- interp s1
                       interp s2
interp (If bexp s1 s2) = do b <- interpb bexp
                            if b then (interp s1) else (interp s2)








-- examples
add_5_to_1_with_var :: Stm
add_5_to_1_with_var = Let "x" (Lit 5) (Add (Var "x") (Lit 1))

testingScope :: Stm
testingScope = Let "x" (Lit 5) (Seq (Assign "x" (Lit 1)) (Var "x"))

testingScope2 :: Stm
testingScope2 = Seq (Let "x" (Lit 5) (Lit 5)) (Lit 7)

testingScope3 :: Stm
testingScope3 = Let "y" (Lit 2) (Let "x" (Lit 3) (Seq (Let "y" (Lit 4) (Assign "x" (Lit 2))) (Add (Var "x") (Var "y"))))

absoluteValueStm :: Stm 
absoluteValueStm = Let "x" (Lit (-5)) (If (Compare LessThan (Var "x") (Lit 0)) (Min (Lit 0) (Var "x")) (Var "x"))


absoluteValue :: Prog
absoluteValue = Fun "abs" ["x"] (If (Compare LessThan (Var "x") (Lit 0)) (Min (Lit 0) (Var "x")) (Var "x"))


-- Program -> Parameters -> executed program.
exec :: Prog -> [Value]-> Maybe Value
exec (Fun _ l s) pars = fmap fst (runStateT (interp s) ((zip l pars)))


runStatement :: Stm -> Maybe (Value,Store)
runStatement s = (runStateT (interp s) []) 


------------------------------------------------------------------------------------------------
-- we define the syntax for Assertions


data Prop = T 
    | F 
    | Cmp Relop Int Int 
    | And Prop Prop 
    | Or Prop Prop 
    | Implies Prop Prop
    | Exist (Value->Prop) 
    | Forall (Value->Prop)

type LVar = String -- logic variables
type Valuation = M.Map LVar Value



data Contract = ForallC (Value -> Contract) -- forAll logicVariables {Precondition} Program {Int->Postcondition}
    | HoareTriple Prop Prog [Value] (Value->Prop)



absoluteValueContract :: Contract
--absoluteValueContract = MkContract ["x"] T absoluteValue (\x -> )
--absoluteValueContract = MkContract ["x"] T absoluteValue (\x -> And (Cmp GreaterThan x 0) (T))
absoluteValueContract = ForallC (\x->HoareTriple T absoluteValue [x] (\result->And (Cmp GreaterThan result 0) (Cmp GreaterThanEqual result x)))

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
block = Wpure $ (\_->T)

fail :: Wpure a
fail = Wpure $ (\_->F)

angelic :: Maybe String -> Wpure Value
angelic _ = Wpure $ (\post-> Exist (\v->post v))

demonic :: Maybe String -> Wpure Value
demonic _ = Wpure $ (\post-> Forall (\v->post v))

-- unicode 2295
(⊕) :: Wpure a->Wpure a -> Wpure a
m1 ⊕ m2 = Wpure $ (\post -> Or ((runWpure m1) post) ((runWpure m2) post))

(⊗) :: Wpure a->Wpure a -> Wpure a
m1 ⊗ m2 = Wpure $ (\post -> And ((runWpure m1) post) ((runWpure m2) post))

assert :: Prop -> Wpure ()
assert p = Wpure $ (\post -> And p (post ()))

assume :: Prop -> Wpure ()
assume p = Wpure $ (\post -> Implies p (post ()))





newtype Wstore a =Wstore {runWstore :: (a->Store->Prop)->Store->Prop}
instance Functor Wstore where
  fmap = liftM
instance Applicative Wstore where
  pure a = Wstore $ (\post store->post a store)
  (<*>) = ap

instance Monad Wstore where
    return = pure
    c >>= k = Wstore $ (\post store1-> (runWstore c) (\a store2->runWstore (k a) post store2) store1)

evalStore :: Wstore a ->Store-> Wpure a 
evalStore m store = Wpure $ (\post-> (runWstore m) (\a _->post a) store)

pushStore :: X->Value -> Wstore ()
pushStore x v = Wstore $ (\post store->post () (pushL x v store))

popStore :: Wstore ()
popStore = Wstore $ (\post store -> post () (popL store))

{- 
-- TODO Add another Prop for failure?
-- TODO monad instance
type MWstore a = StateT Valuation (MaybeT (Cont Prop))
---
evalStore :: Wstore a -> Valuation -> Wpure a
evalStore m store = Wpure $ (\post-> m (\a store'->post a) store)

--evalStore' :: Wstore a -> Valuation -> Wpure a
--evalStore' m store = Wpure $ (\post-> (runStateT m) store (\a ->post (fst a)))


push :: X->Value->Wstore ()
push x v = (\post store-> post () (insert x v store))

pop :: Wstore ()
pop = (\post store -> post () store)




 -}
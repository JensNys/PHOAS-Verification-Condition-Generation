{-# LANGUAGE RankNTypes  #-}
module ProgramAssertionSemantics where


import Control.Monad.State
--import Control.Monad.Trans.Maybe
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
    | Minus Stm Stm
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
interp (Minus s1 s2) = do x <- interp s1
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
absoluteValueStm = Let "x" (Lit (-5)) (If (Compare LessThan (Var "x") (Lit 0)) (Minus (Lit 0) (Var "x")) (Var "x"))


absoluteValue :: Prog
absoluteValue = Fun "abs" ["x"] (If (Compare LessThan (Var "x") (Lit 0)) (Minus (Lit 0) (Var "x")) (Var "x"))


-- Program -> Parameters -> executed program.
execute :: Prog -> [Value]-> Maybe Value
execute (Fun _ l s) pars = fmap fst (runStateT (interp s) ((zip l pars)))


runStatement :: Stm -> Maybe (Value,Store)
runStatement s = (runStateT (interp s) []) 


------------------------------------------------------------------------------------------------
-- we define the syntax for Assertions


data Prop = T 
    | F 
    | Cmp Relop Value Value 
    | Not Prop
    | And Prop Prop 
    | Or Prop Prop 
    | Implies Prop Prop
    | Exist (Value->Prop) 
    | Forall (Value->Prop)

{- class Proposition a where
  true :: Proposition a
  false :: Proposition a
  cmp :: Relop->Value->Value->Proposition a
  and :: Bool->Bool->Prop
  or :: Proposition a->Proposition a->Proposition a
  implies ::  Proposition a->
  exist :: (Value->p)->p
  forAll :: (Value->p)->p

type PhoasProp = forall a. Proposition a => a -}


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




angelic :: Maybe String -> Wpure Value
angelic _ = Wpure $ (\post-> Exist (\v->post v))

demonic :: Maybe String -> Wpure Value
demonic _ = Wpure $ (\post-> Forall (\v->post v))

-- unicode 2295
{- 
block :: Wpure a
block = Wpure $ (\_->T)

fail :: Wpure a
fail = Wpure $ (\_->F)


(⊕) :: Wpure a->Wpure a -> Wpure a
m1 ⊕ m2 = Wpure $ (\post -> Or ((runWpure m1) post) ((runWpure m2) post))

(⊗) :: Wpure a->Wpure a -> Wpure a
m1 ⊗ m2 = Wpure $ (\post -> And ((runWpure m1) post) ((runWpure m2) post))


assert :: Prop -> Wpure ()
assert p = Wpure $ (\post store-> And p (post ()))

assume :: Prop -> Wpure ()
assume p = Wpure $ (\post -> Implies p (post ())) -}





newtype Wstore a = Wstore {runWstore :: (a->Store->Prop)->Store->Prop}
instance Functor Wstore where
  fmap = liftM
instance Applicative Wstore where
  pure a = Wstore $ (\post store->post a store)
  (<*>) = ap

instance Monad Wstore where
    return = pure
    c >>= k = Wstore $ (\post store1-> (runWstore c) (\a store2->runWstore (k a) post store2) store1)


block :: Wstore a
block = Wstore $ (\_ _->T)

fail :: Wstore a
fail = Wstore $ (\_ _->F)

-- unicode 2295
(⊕) :: Wstore a->Wstore a -> Wstore a
m1 ⊕ m2 = Wstore $ (\post store-> Or ((runWstore m1) post store) ((runWstore m2) post store))

(⊗) :: Wstore a->Wstore a -> Wstore a
m1 ⊗ m2 = Wstore $ (\post store -> And ((runWstore m1) post store) ((runWstore m2) post store))


assert :: Prop -> Wstore ()
assert p = Wstore $ (\post store-> And p (post () store))

assume :: Prop -> Wstore ()
assume p = Wstore $ (\post store-> Implies p (post () store))





evalStore :: Wstore a ->Store-> Wpure a 
evalStore m store = Wpure $ (\post-> (runWstore m) (\a _->post a) store)

pushStore :: X->Value -> Wstore ()
pushStore x v = Wstore $ (\post store->post () (pushL x v store))

popStore :: Wstore ()
popStore = Wstore $ (\post store -> post () (popL store))

-- the cond parameter should be 
matchBool_angelic :: Prop-> Wstore a-> Wstore a-> Wstore a
matchBool_angelic cond m1 m2= (do assume cond;m1) 
                              ⊗
                              (do assume (Not cond);m2)

matchBool_demonic :: Prop-> Wstore a-> Wstore a-> Wstore a
matchBool_demonic cond m1 m2= (do assert cond;m1) 
                              ⊕
                              (do assert (Not cond);m2)


assignWstore :: X->Value->Wstore ()
assignWstore x v = Wstore $ (\post store->post () (change x v store))

lookupWstore :: X->Wstore Value
lookupWstore a = Wstore $ (\post store->case (Prelude.lookup a store) of
                                                Nothing -> F
                                                Just value -> post value store)

-- turns a boolean expression into the proposition that is equivalent to the expression in the monadic Wstore environment
execb :: Bexp->Wstore Prop
execb (Compare op s1 s2) = do x <- exec s1
                              y <- exec s2
                              return (Cmp op x y)

exec :: Stm->Wstore Value
exec (Lit c) = return c
exec (Var a) = lookupWstore a
exec (Add s1 s2) = do x <- exec s1
                      y <- exec s2
                      return (x+y)
exec (Mul s1 s2) = do x <- exec s1
                      y <- exec s2
                      return (x*y)
exec (Minus s1 s2) = do x <- exec s1
                        y <- exec s2
                        return (x-y)
exec (Assign var s) = do v <-exec s 
                         assignWstore var v
                         return v
exec (Let var s1 s2) = do x <- exec s1 -- p -- in a later stage we could let this computation fail if x is already a variable.
                          pushStore var x
                          result <- exec s2
                          popStore
                          return result
exec (Seq s1 s2) = do _ <- exec s1
                      exec s2
exec (If bexp s1 s2) = do b <- execb bexp
                          matchBool_angelic b (exec s1) (exec s2)





-- with normal state: θ St(m) = λpost s0. post (m s0)
-- total correctness interpretation by doing F
observationTotal ::  StateT Store Maybe a->Wstore a 
observationTotal r = Wstore $ (\post s0-> case ((runStateT r) s0) of 
                                          Nothing -> F
                                          Just (a,store) -> post a store)

-- with normal state: θ St(m) = λpost s0. post (m s0)
-- partial correctness interpretation by doing T
observationPartial ::  StateT Store Maybe a->Wstore a 
observationPartial r = Wstore $ (\post s0-> case ((runStateT r) s0) of 
                                          Nothing -> T
                                          Just (a,store) -> post a store)
{-# LANGUAGE RankNTypes  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module ProgramAssertionSemantics where

import Control.Monad.Reader
import Control.Monad.State
--import Control.Monad.Trans.Maybe
--import Control.Monad.Cont
import Data.Map as M
-- here we define the program syntax and its semantics. 
-- we also define the syntax and semantics for logic variables

--type Var = String
type Value = Int
type (Store v) = [(X,v)]
--program variables. They are immutable location
type X = String
--function names
type F = String


data Prog = Fun F [X] Stm

data Relop = Equal | LessThan | GreaterThan | NotEqual | LessThanEqual | GreaterThanEqual
  deriving (Eq)
instance Show Relop where
  show Equal = "=="
  show LessThan ="<"
  show GreaterThan=">"
  show NotEqual = "!="
  show LessThanEqual = "<="
  show GreaterThanEqual = ">="

data Bexp = Compare Relop Stm Stm
    deriving (Eq,Show)
data Stm = Lit Value
    | Var X
    | Add Stm Stm
    | Mul Stm Stm
    | Minus Stm Stm
    | Assign X Stm -- x := Stm (update a variable)
    | Let X Stm Stm -- let X = Stm where Stm (make a new variable)
    | Seq Stm Stm --e1;e2
    | If Bexp Stm Stm -- if bexp then stm else stm
  deriving (Eq,Show)




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




lookupVarS:: X->StateT (Store Value) Maybe Value
lookupVarS var = do env <- get
                    case (Prelude.lookup var env) of
                         Just a -> return a
                         Nothing -> lift Nothing
putS :: X->Value -> StateT (Store Value) Maybe Value
putS var c = state (\m -> (c,(var,c):m))



assign :: X->Value -> StateT (Store Value) Maybe Value
assign var c = state (\m -> (c,change var c m))


pop :: StateT (Store Value) Maybe Value
pop = state (\m -> (snd (head m),tail m))

remove :: X-> StateT (Store Value) Maybe ()
remove x = state (\m -> ((),deleteL x m))

                
toFunc :: Relop -> (Int->Int->Bool)
toFunc Equal = (==)
toFunc LessThan = (<)
toFunc GreaterThan = (>)
toFunc NotEqual = (/=)
toFunc LessThanEqual = (<=)
toFunc GreaterThanEqual = (>=)

interpb :: Bexp -> StateT (Store Value) Maybe Bool
interpb (Compare op s1 s2) = do x <- interp s1
                                y <- interp s2
                                return ((toFunc op) x y)
-- this is a naive version where i don't use monad functionality 
-- Stm -> Valuation -> Maybe (Value, Valuation)

    
interp :: Stm -> StateT (Store Value) Maybe Value
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


runStatement :: Stm -> Maybe (Value,(Store Value))
runStatement s = (runStateT (interp s) []) 


------------------------------------------------------------------------------------------------
-- we define the syntax for Assertions
type LVar = String -- logic variables
type Valuation = M.Map LVar Value

data Prop = T 
    | F 
    | Cmp Relop Value Value 
    | Not Prop
    | And Prop Prop 
    | Or Prop Prop 
    | Implies Prop Prop
    | Exist (Value->Prop) 
    | Forall (Value->Prop)



{- data FoasValue =  FVal Value
                | FVar LVar
    deriving (Eq,Show) -}

data FoasProp = FoasT 
    | FoasF 
    | FoasCmp Relop Stm Stm -- these can be both LVars as values 
    | FoasNot FoasProp
    | FoasAnd FoasProp FoasProp 
    | FoasOr FoasProp FoasProp 
    | FoasImplies FoasProp FoasProp
    | FoasExist LVar FoasProp 
    | FoasForall LVar FoasProp
    deriving (Eq,Show)
{- 
data PhoasValue a =  PVal Value
                | PVar a -}
prettyPrint :: FoasProp->String
prettyPrint FoasT = "True"
prettyPrint FoasF = "False"
prettyPrint( FoasCmp relop s1 s2) =  "("++show s1 ++ " "++ show relop ++" "++ show s2++")" -- these can be both LVars as values 
prettyPrint (FoasNot p) = "-"++ prettyPrint p
prettyPrint( FoasAnd p1 p2) = "("++prettyPrint p1 ++ "/\\" ++ prettyPrint p2 ++")"
prettyPrint (FoasOr p1 p2) = "("++ prettyPrint p1 ++ "\\/" ++ prettyPrint p2++")"
prettyPrint (FoasImplies p1 p2) = "("++ prettyPrint p1 ++ "=>" ++ prettyPrint p2 ++ ")"
prettyPrint (FoasExist lvar p ) = "("++ "!"++ lvar ++ ":"++ prettyPrint p ++ ")"
prettyPrint (FoasForall lvar p) = "("++ "?"++ lvar ++":"++ prettyPrint p ++ ")"

--expression algebra
class ValueAlgebra v where
    lit :: Value->v
    add :: v -> v -> v
    minus :: v -> v -> v
    mul :: v -> v -> v

data PhoasProp v = PhoasT 
    | PhoasF 
    | PhoasCmp Relop v v  -- these can be both LVars as values 
    | PhoasNot (PhoasProp v)
    | PhoasAnd (PhoasProp v) (PhoasProp v) 
    | PhoasOr (PhoasProp v) (PhoasProp v) 
    | PhoasImplies (PhoasProp v) (PhoasProp v)
    | PhoasExist (Maybe String) (v->(PhoasProp v))
    | PhoasForall (Maybe String) (v->(PhoasProp v))
-- assumes the maybe string isn't of the form "x" ++ show i for an integer i.



-- typeclass for the operations on Values.
instance ValueAlgebra Stm where
  lit = Lit
  add = Add
  mul = Mul
  minus = Minus


instance ValueAlgebra Int where
  lit = id
  add = (+)
  mul = (*)
  minus = (-)



instance ValueAlgebra (Reader Int Stm) where
  lit i = return $ Lit i
  add x y = do v1 <- x
               v2 <- y
               return (Add v1 v2)
  mul x y=  do v1 <- x
               v2 <- y
               return (Mul v1 v2)
  minus x y=do v1 <- x
               v2 <- y
               return (Minus v1 v2)

-- the motivation between FoasValue is that in the Hoas prop, you can say Exists (\v-> Cmp Equal v 5) so in first order a comparison could be between variables and FoasValues (Exist "v" (Cmp Equal (Var "v") (Val 5)))


type ReaderInt v = Reader Int v



{- phoasValue_to_foasValueReader :: PhoasValue (ReaderInt Stm) -> ReaderInt FoasValue
phoasValue_to_foasValueReader (PVal v) = return $ FVal v
phoasValue_to_foasValueReader (PVar rfv) = rfv -}


phoas_to_foas :: PhoasProp (ReaderInt Stm) -> FoasProp
phoas_to_foas phoasProp = runReader (phoas_to_foas_reader phoasProp) 0




phoas_to_foas_reader :: PhoasProp (ReaderInt Stm) -> ReaderInt FoasProp
phoas_to_foas_reader PhoasT = return FoasT
phoas_to_foas_reader PhoasF = return FoasF
phoas_to_foas_reader (PhoasCmp op l r) = do v1 <- l
                                            v2 <- r
                                            return $ FoasCmp op v1 v2
phoas_to_foas_reader (PhoasNot p) = do r <- phoas_to_foas_reader p
                                       return $ FoasNot r
phoas_to_foas_reader (PhoasAnd p1 p2)    = binary_prop_to_foas_reader p1 p2 FoasAnd
phoas_to_foas_reader (PhoasOr p1 p2)     = binary_prop_to_foas_reader p1 p2 FoasOr
phoas_to_foas_reader (PhoasImplies p1 p2)= binary_prop_to_foas_reader p1 p2 FoasImplies 
phoas_to_foas_reader (PhoasExist m f)    = quantifiers_to_foas_reader m f FoasExist
phoas_to_foas_reader (PhoasForall m f)   = quantifiers_to_foas_reader m f FoasForall



-- interprets a quantifier
quantifiers_to_foas_reader :: Maybe String -> ((ReaderInt Stm)->PhoasProp (ReaderInt Stm))->(LVar->FoasProp->FoasProp)->ReaderInt FoasProp
quantifiers_to_foas_reader  m f quantifier=do i <- ask
                                              let arg = "x" ++ show i

                                              case m of 
                                                Nothing -> do
                                                   body <- (local (+1) $ phoas_to_foas_reader $ (f (return (Var arg))))
                                                   return $ quantifier arg body
                                                Just s -> do
                                                   body <-              (phoas_to_foas_reader $ (f (return (Var s))))
                                                   return $ quantifier s body
                                              


--interprets a binary propositional operator.
binary_prop_to_foas_reader :: (PhoasProp (ReaderInt Stm))->(PhoasProp (ReaderInt Stm))->(FoasProp->FoasProp->FoasProp)->ReaderInt FoasProp
binary_prop_to_foas_reader p1 p2 bin = do r1 <- phoas_to_foas_reader p1
                                          r2 <- phoas_to_foas_reader p2
                                          return $ bin r1 r2

-- forall x, there exist y: x<y /\ 0<y
phoas_example ::ValueAlgebra v => PhoasProp v
phoas_example= PhoasForall Nothing (\x->PhoasExist Nothing (\y->(PhoasAnd (PhoasCmp LessThanEqual x y) (PhoasCmp LessThanEqual (lit 0) y))))

foas_example :: FoasProp
foas_example = FoasForall "x0" (FoasExist "x1" (FoasAnd (FoasCmp LessThanEqual (Var "x0") (Var "x1")) (FoasCmp LessThanEqual (Lit 0) (Var "x1"))))



{- class Proposition p a where
  true :: p
  false :: p
  cmp :: Relop->a->a->p
  and :: p->p->p
  or :: p->p->p
  implies ::  p->p->p
  exist :: (a->p)->p
  forAll :: (a->p)->p

type PhoasProposition = forall a. forall p. Proposition p a => p -}


foas_to_phoas :: FoasProp->PhoasProp v
foas_to_phoas p = PhoasT



-- the result variable should be named "Result"
data FirstOrderContract = MkContract [LVar] (FoasProp) Prog [LVar] LVar FoasProp
--                universalQuantifications precondition Program Parameters Postcondition

firstOrderAbsContract :: FirstOrderContract
firstOrderAbsContract=  MkContract ["x"] (FoasT) absoluteValue ["x"] "result" $ FoasAnd (FoasCmp GreaterThanEqual (Var "result") (Lit 0)) (FoasCmp GreaterThanEqual (Var "result") (Var "x"))




data Contract v =  ForallC (Maybe String) (v -> Contract v) -- forAll logicVariables {Precondition} Program {Int->Postcondition}
    | HoareTriple (PhoasProp v) Prog [v] (v->(Store v)->PhoasProp v)



absoluteValueContract :: ValueAlgebra v => Contract v
--absoluteValueContract = MkContract ["x"] T absoluteValue (\x -> )
--absoluteValueContract = MkContract ["x"] T absoluteValue (\x -> And (Cmp GreaterThan x 0) (T))
absoluteValueContract = ForallC (Just "x") (\x->HoareTriple PhoasT absoluteValue [x] (\result _->PhoasAnd (PhoasCmp GreaterThanEqual result (lit 0)) (PhoasCmp GreaterThanEqual result x)))





newtype Wpure v a = Wpure {runWpure :: (a->PhoasProp v)->PhoasProp v}
instance Functor (Wpure v) where
  fmap = liftM

instance Applicative (Wpure v) where
  pure a = Wpure $ (\post->post a)
  (<*>) = ap

instance Monad (Wpure v) where
    return = pure
    c >>= k = Wpure $ (\post-> (runWpure c) (\a->runWpure (k a) post))




angelic :: ValueAlgebra v =>Maybe String -> Wpure v v
angelic m = Wpure $ (\post-> PhoasExist m (\v->post v))

demonic :: ValueAlgebra v => Maybe String -> Wpure v v
demonic m = Wpure $ (\post-> PhoasForall m (\v->post v))






newtype Wstore v a = Wstore {runWstore :: (a->(Store v)->PhoasProp v)->(Store v)->PhoasProp v}
instance Functor (Wstore v) where
  fmap = liftM
instance Applicative (Wstore v) where
  pure a = Wstore $ (\post store->post a store)
  (<*>) = ap

instance Monad (Wstore v) where
    return = pure
    c >>= k = Wstore $ (\post store1-> (runWstore c) (\a store2->runWstore (k a) post store2) store1)


block :: ValueAlgebra v =>Wstore v a
block = Wstore $ (\_ _->PhoasT)

fail :: ValueAlgebra v =>Wstore v a
fail = Wstore $ (\_ _->PhoasF)

-- unicode 2295
(⊕) ::ValueAlgebra v => Wstore v a->Wstore v a -> Wstore v a
m1 ⊕ m2 = Wstore $ (\post store-> PhoasOr ((runWstore m1) post store) ((runWstore m2) post store))

(⊗) :: ValueAlgebra v =>Wstore v a->Wstore v a -> Wstore v a
m1 ⊗ m2 = Wstore $ (\post store -> PhoasAnd ((runWstore m1) post store) ((runWstore m2) post store))


assert :: ValueAlgebra v =>PhoasProp v -> Wstore v ()
assert p = Wstore $ (\post store-> PhoasAnd p (post () store))

assume :: ValueAlgebra v =>PhoasProp v -> Wstore v ()
assume p = Wstore $ (\post store-> PhoasImplies p (post () store))





evalStore ::ValueAlgebra v => Wstore v a ->(Store v)-> Wpure v a 
evalStore m store = Wpure $ (\post-> (runWstore m) (\a _->post a) store)

pushStore ::ValueAlgebra v => X->v -> Wstore v ()
pushStore x v = Wstore $ (\post store->post () (pushL x v store))

popStore :: ValueAlgebra v =>Wstore v ()
popStore = Wstore $ (\post store -> post () (popL store))

-- the cond parameter should be 
matchBool_demonic :: ValueAlgebra v =>PhoasProp v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_demonic cond m1 m2= (do assume cond;m1) 
                              ⊗
                              (do assume (PhoasNot cond);m2)

matchBool_angelic :: ValueAlgebra v =>PhoasProp v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_angelic cond m1 m2= (do assert cond;m1) 
                              ⊕
                              (do assert (PhoasNot cond);m2)


assignWstore ::ValueAlgebra v => X->v->Wstore v ()
assignWstore x v = Wstore $ (\post store->post () (change x v store))

lookupWstore ::ValueAlgebra v => X->Wstore v v
lookupWstore a = Wstore $ (\post store->case (Prelude.lookup a store) of
                                                Nothing -> PhoasF
                                                Just value -> post value store)

-- turns a boolean expression into the proposition that is equivalent to the expression in the monadic Wstore environment
execb :: ValueAlgebra v=> Bexp->Wstore v (PhoasProp v)
execb (Compare op s1 s2) = do x <- exec s1
                              y <- exec s2
                              return (PhoasCmp op x y)

exec :: ValueAlgebra v=> Stm->Wstore v v
exec (Lit c) = return $ lit c
exec (Var a) = lookupWstore a
exec (Add s1 s2) = do x <- exec s1
                      y <- exec s2
                      return (add x y)
exec (Mul s1 s2) = do x <- exec s1
                      y <- exec s2
                      return (mul x y)
exec (Minus s1 s2) = do x <- exec s1
                        y <- exec s2
                        return (minus x y)
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
                          matchBool_demonic b (exec s1) (exec s2)





-- with normal state: θ St(m) = λpost s0. post (m s0)
-- total correctness interpretation by doing F
{- observationTotal :: ValueAlgebra v => StateT (Store v) Maybe a->Wstore v a 
observationTotal r = Wstore $ (\post s0-> case ((runStateT r) s0) of 
                                          Nothing -> PhoasF
                                          Just (a,store) -> post a store)

-- with normal state: θ St(m) = λpost s0. post (m s0)
-- partial correctness interpretation by doing T
observationPartial :: ValueAlgebra v => StateT (Store v) Maybe a->Wstore v a 
observationPartial r = Wstore $ (\post s0-> case ((runStateT r) s0) of 
                                          Nothing -> PhoasT
                                          Just (a,store) -> post a store) -}



-- Print Scope type_scope. Coq

wp :: ValueAlgebra v=>Stm -> (v->(Store v)->PhoasProp v)->(Store v)->PhoasProp v
wp stm post initStore = (runWstore (exec stm)) post initStore




vc :: ValueAlgebra v=>Contract v -> PhoasProp v
vc (ForallC mstring f) = PhoasForall mstring (\v -> vc (f v))
vc (HoareTriple pre prog args post) = case prog of 
  Fun _ params body -> PhoasImplies pre (wp body post (zip params args))

--zip params args should be a Store.
--it is only a Store if args is a list of Values

--locate coq

main ::IO ()
main =  putStrLn $ prettyPrint $ phoas_to_foas $ vc absoluteValueContract
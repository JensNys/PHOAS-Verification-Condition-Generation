{-# LANGUAGE RankNTypes  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Week1.LambdaCalculi where
--{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
--{-# HLINT ignore "Use camelCase" #-}

import Control.Monad.Reader
import Control.Monad.State
import Data.Char

data Foas_Exp = Var String
    | Lambda String Foas_Exp
    | App Foas_Exp Foas_Exp
    deriving (Eq,Show)

data Hoas_Exp = HLambda (Hoas_Exp -> Hoas_Exp)
    | HApp Hoas_Exp Hoas_Exp

data Phoas_Exp a = PVar a
    | PLambda (a -> Phoas_Exp a)
    | PApp (Phoas_Exp a) (Phoas_Exp a)


class UntypedLambda exp where
    lam :: (exp -> exp) -> exp
    app :: exp -> exp -> exp 

type Phoas = forall a. UntypedLambda a => a

data DBTerm = DBVar Int
    | DBLam DBTerm
    | DBApp DBTerm DBTerm
    deriving (Show,Eq)



prettify :: Foas_Exp->String
prettify (Var str) = str
prettify (Lambda str exp) = "(\\" ++ str ++ "." ++ (prettify exp) ++ ")"
prettify (App l r) = (prettify l) ++ " " ++ (prettify r)

prettyPrint = putStrLn . prettify





-- combinator I for the term (λx.x)
foasI :: Foas_Exp
foasI = Lambda "x" (Var "x")

hoasI :: Hoas_Exp
hoasI = HLambda (\x->x)

phoasI :: Phoas_Exp a
phoasI = PLambda (\x->PVar x)

typeclass_hoasI :: Phoas
typeclass_hoasI = lam (\x->x)

deBruinI :: DBTerm
deBruinI = DBLam (DBVar 0)


--combinator B (function composition) for the term 
foasB :: Foas_Exp
foasB = Lambda "x" (Lambda "y" (Lambda "z" (App (Var "x") (App (Var "y") (Var "z")))))

hoasB :: Hoas_Exp
hoasB = HLambda (\x->HLambda (\y->HLambda (\z->HApp x (HApp y z))))

phoasB :: Phoas_Exp a
phoasB = PLambda (\x->PLambda (\y->PLambda (\z->PApp (PVar x) (PApp (PVar y) (PVar z)))))

typeclass_hoasB :: Phoas
typeclass_hoasB = lam (\x->lam (\y->lam (\z->app x (app y z))))

deBruinB :: DBTerm
deBruinB = DBLam (DBLam (DBLam (DBApp (DBVar 2) (DBApp (DBVar 1) (DBVar 0)))))

-- Y combinator = λf. (λx. f (x x)) (λx. f (x x))
foasY :: Foas_Exp
foasY = (Lambda "f" (App (Lambda "x" (App (Var "f") (App (Var "x") (Var "x")))) (Lambda "x" (App (Var "f") (App (Var "x") (Var "x"))))))






--the examples represent the term (λx. (λy. x y)) (λz.z)
foas_example :: Foas_Exp
foas_example = App (Lambda "x" (Lambda "y" (App (Var "x") (Var "y")))) (Lambda "z" (Var "z"))

hoas_example :: Hoas_Exp
hoas_example = HApp (HLambda (\x-> HLambda (\y -> HApp x y))) (HLambda id)

phoas_example :: Phoas_Exp a
phoas_example = PApp (PLambda (\x-> PLambda (\y -> PApp (PVar x) (PVar y)))) (PLambda (\z -> PVar z))

typeclass_hoas_example :: Phoas
typeclass_hoas_example = app (lam (\x->lam (\y-> app x y))) (lam (\z->z))

deBruinExample :: DBTerm
deBruinExample = DBApp (DBLam (DBLam (DBApp (DBVar 1) (DBVar 0)))) (DBLam (DBVar 0))


--evaluation functions for foas representations

--searches for the first lambda abstraction and substitutes its string with
substitute :: Foas_Exp -> Foas_Exp -> Foas_Exp
substitute e (App e1 e2) = App (substitute e e1) (substitute e e2)
substitute e (Var x) = Var x
substitute e (Lambda s e2) = substitute_string s e e2

-- substitutes the variable s with the expression e everywhere it occurs in the 3rd parameter
substitute_string :: String->Foas_Exp->Foas_Exp->Foas_Exp
substitute_string s e (Var m) = if m==s then e else (Var m)
substitute_string s e (App e1 e2) = App (substitute_string s e e1) (substitute_string s e e2)
substitute_string s e (Lambda m e2) = if m==s then (Lambda m e2) else Lambda m (substitute_string s e e2)




{- alphaReduce :: String-> String->Foas_Exp -> Foas_Exp
alphaReduce s1 s2 (Var s) =
alphaReduce s1 s2 (App e1 e2) = 
alphaReduce s1 s2 (Lambda s e) = 
 -}
betaReduce :: Foas_Exp -> Foas_Exp
betaReduce (Var s) = (Var s)
betaReduce (Lambda s exp) = Lambda s (betaReduce exp)
betaReduce (App e1 e2) = substitute e2 e1



run :: Foas_Exp -> Foas_Exp
run a = if betaReduce a == a then a else run $ betaReduce a




-----------------------------
-- conversions from phoas to foas in different ways
{- newtype First = First {unFirst :: Int->Foas_Exp}

phoas_to_first :: Phoas_Exp a->First
phoas_to_first (PVar v)    = First $( \i->Var "x")
phoas_to_first (PLambda f) =First $(\i->Var "x")
phoas_to_first (PApp l r)  = First $(\i->Var "x") -}


newtype First = First {unFirst :: Int->Foas_Exp}

{- phoas_to_first :: Phoas_Exp a->First
phoas_to_first (PVar v)    = First $( \i->Var "x")
phoas_to_first (PLambda f) =First $(\i->Var "x")
phoas_to_first (PApp l r)  = First $(\i->Var "x") -}

instance UntypedLambda First where
    --lam :: (First->First)->First
    lam f = First $ (\i-> Lambda ( "x" ++ show i) (unFirst (f (First $ (\j->Var ("x" ++ show i)))) (i+1)))
    --app :: First->First->First
    app left right= First $ (\i->App (unFirst left i) (unFirst right i))



typeclass_phoas_to_first :: Phoas-> First
typeclass_phoas_to_first hoas = hoas

typeclass_phoas_to_foas :: First -> Foas_Exp
typeclass_phoas_to_foas  hoas = unFirst hoas 0


type ReaderFirst = Reader Int Foas_Exp

{- phoas_to_first :: Phoas_Exp a->First
phoas_to_first (PVar v)    = First $( \i->Var "x")
phoas_to_first (PLambda f) =First $(\i->Var "x")
phoas_to_first (PApp l r)  = First $(\i->Var "x") -}

instance UntypedLambda ReaderFirst where
    --lam :: (First->First)->First
    lam f = do i <- ask
               let arg = "x" ++ show i
               body <- local (+1) (f (return (Var arg)))
               return $ Lambda arg body

    --app :: First->First->First
    app left right = do l <- left
                        r <- right
                        return $ App l r

typeclass_phoas_to_readerfirst :: Phoas-> ReaderFirst
typeclass_phoas_to_readerfirst phoas = phoas

typeclass_phoas_to_readerfoas :: Phoas -> Foas_Exp
typeclass_phoas_to_readerfoas phoas = runReader (typeclass_phoas_to_readerfirst phoas) 0

type StateFirst = State Int Foas_Exp


instance UntypedLambda StateFirst where
    --lam :: (First->First)->First
    lam f = do i <- get
               let arg = "x" ++ show i
               put (i+1)
               body <- f (return (Var arg))
               return $ Lambda arg body

    --app :: First->First->First
    app left right = do l <- left
                        r <- right
                        return $ App l r

typeclass_phoas_to_statefirst :: Phoas-> StateFirst
typeclass_phoas_to_statefirst phoas = phoas

typeclass_phoas_to_statefoas :: Phoas -> Foas_Exp
typeclass_phoas_to_statefoas phoas = fst $ runState (typeclass_phoas_to_statefirst phoas) 0

{- data Foas_Exp = Var String
    | Lambda String Foas_Exp
    | App Foas_Exp Foas_Exp
    deriving (Eq,Show)

data Hoas_Exp = HLambda (Hoas_Exp -> Hoas_Exp)
    | HApp Hoas_Exp Hoas_Exp

data Phoas_Exp a = PVar a
    | PLambda (a -> Phoas_Exp a)
    | PApp (Phoas_Exp a) (Phoas_Exp a) -}


--type FirstOrderReader = Reader (Int,String) Foas_Exp
-- Int is the state of new variables. If the String is non-empty, it is the one that should be put in

    
-- conversion from phoas to first order representation
-- algebraic datatype version
phoas_to_foas :: Phoas_Exp String  -> Foas_Exp
phoas_to_foas a = runReader (go a) 0
    
go :: Phoas_Exp String -> ReaderFirst
go (PApp left right) = do l <- go left
                          r <- go right
                          return $ App l r
go (PLambda f)  = do i <- ask
                     let arg = "x" ++ show i
                     body <- local (+1) $ go $ (f arg)
                     return $ Lambda arg body
go (PVar a) = return $ Var a

-- problem: i have to instantiate the polymorphic parameter to String







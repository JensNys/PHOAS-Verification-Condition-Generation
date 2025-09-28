{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use camelCase" #-}
import Test.HUnit
import Test.QuickCheck

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

type Hoas = forall a. UntypedLambda a => a
















-- combinator I for the term (λx.x)
foasI :: Foas_Exp
foasI = Lambda "x" (Var "x")

hoasI :: Hoas_Exp
hoasI = HLambda (\x->x)

phoasI :: Phoas_Exp a
phoasI = PLambda (\x->PVar x)

typeclass_hoasI :: Hoas
typeclass_hoasI = lam (\x->x)


--combinator B (function composition) for the term 
foasB :: Foas_Exp
foasB = Lambda "x" (Lambda "y" (Lambda "z" (App (Var "x") (App (Var "y") (Var "z")))))

hoasB :: Hoas_Exp
hoasB = HLambda (\x->HLambda (\y->HLambda (\z->HApp x (HApp y z))))

phoasB :: Phoas_Exp a
phoasB = PLambda (\x->PLambda (\y->PLambda (\z->PApp (PVar x) (PApp (PVar y) (PVar z)))))

typeclass_hoasB :: Hoas
typeclass_hoasB = lam (\x->lam (\y->lam (\z->app x (app y z))))



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

typeclass_hoas_example :: Hoas
typeclass_hoas_example = app (lam (\x->lam (\y-> app x y))) (lam (\z->z))





-- conversion from phoas to first order representation
-- algebraic datatype version
phoas_to_foas :: Phoas_Exp String -> Foas_Exp
phoas_to_foas a = go (map (\i-> "x" ++ show i) [1..]) a
    where 
    go :: [String] -> Phoas_Exp String -> Foas_Exp
    go l (PApp e1 e2) = App (go l e1) (go l e2)
    go (x:xs) (PLambda f) = Lambda x (go xs (f x))
    go l (PVar a) = Var a

-- problem: i have to instantiate the polymorphic parameter to String


-- typeclass version
instance UntypedLambda Foas_Exp where
    lam :: (Foas_Exp->Foas_Exp)->Foas_Exp
    lam f = Lambda "x" (f (Var "x"))
    app :: Foas_Exp->Foas_Exp->Foas_Exp
    app = App

typeclass_hoas_to_foas :: Hoas-> Foas_Exp
typeclass_hoas_to_foas hoas = hoas


-- problem: all of the variables are named "x"









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

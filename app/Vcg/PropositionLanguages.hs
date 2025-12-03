{-# LANGUAGE FlexibleInstances #-}
{- HLINT ignore "Use camelCase" -}
module Vcg.PropositionLanguages where
import Vcg.ProgrammingLanguage

import Control.Monad.Reader
import Data.Map as M




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



data FoasProp = FoasT
    | FoasF
    | FoasCmp Relop Exp Exp -- these can be both LVars as values 
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


data PhoasProp v = PhoasT
    | PhoasF
    | PhoasCmp Relop v v  -- these can be both LVars as values 
    | PhoasNot (PhoasProp v)
    | PhoasAnd (PhoasProp v) (PhoasProp v)
    | PhoasOr (PhoasProp v) (PhoasProp v)
    | PhoasImplies (PhoasProp v) (PhoasProp v)
    | PhoasExist (Maybe String) (v->PhoasProp v)
    | PhoasForall (Maybe String) (v->PhoasProp v)
-- assumes the maybe string isn't of the form "x" ++ show i for an integer i.



--expression algebra
class ValueAlgebra v where
    lit :: Value->v
    add :: v -> v -> v
    minus :: v -> v -> v
    mul :: v -> v -> v

-- typeclass for the operations on Values.
instance ValueAlgebra Exp where
  lit = Lit
  add = Add
  mul = Mul
  minus = Minus


instance ValueAlgebra Int where
  lit = id
  add = (+)
  mul = (*)
  minus = (-)



instance ValueAlgebra (Reader Int Exp) where
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


phoas_to_foas :: PhoasProp (ReaderInt Exp) -> FoasProp
phoas_to_foas phoasProp = runReader (phoas_to_foas_reader phoasProp) 0




phoas_to_foas_reader :: PhoasProp (ReaderInt Exp) -> ReaderInt FoasProp
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

phoas_to_hoas ::  PhoasProp Value-> Prop
phoas_to_hoas PhoasT = T
phoas_to_hoas PhoasF = F
phoas_to_hoas (PhoasCmp op l r) = Cmp op l r
phoas_to_hoas (PhoasNot p) = Not  (phoas_to_hoas p)
phoas_to_hoas (PhoasAnd p1 p2)    = And (phoas_to_hoas p1) (phoas_to_hoas p2)
phoas_to_hoas (PhoasOr p1 p2)     = Or (phoas_to_hoas p1) (phoas_to_hoas p2)
phoas_to_hoas (PhoasImplies p1 p2)= Implies (phoas_to_hoas p1) (phoas_to_hoas p2)
phoas_to_hoas (PhoasExist _ f)    = Exist (phoas_to_hoas . f)
phoas_to_hoas (PhoasForall _ f)   = Forall (phoas_to_hoas . f)


-- interprets a quantifier
quantifiers_to_foas_reader :: Maybe String -> ((ReaderInt Exp)->PhoasProp (ReaderInt Exp))->(LVar->FoasProp->FoasProp)->ReaderInt FoasProp
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
binary_prop_to_foas_reader :: (PhoasProp (ReaderInt Exp))->(PhoasProp (ReaderInt Exp))->(FoasProp->FoasProp->FoasProp)->ReaderInt FoasProp
binary_prop_to_foas_reader p1 p2 bin = do r1 <- phoas_to_foas_reader p1
                                          r2 <- phoas_to_foas_reader p2
                                          return $ bin r1 r2

-- forall x, there exist y: x<y /\ 0<y
phoas_example ::ValueAlgebra v => PhoasProp v
phoas_example= PhoasForall Nothing (\x->PhoasExist Nothing (\y->(PhoasAnd (PhoasCmp LessThanEqual x y) (PhoasCmp LessThanEqual (lit 0) y))))

foas_example :: FoasProp
foas_example = FoasForall "x0" (FoasExist "x1" (FoasAnd (FoasCmp LessThanEqual (Var "x0") (Var "x1")) (FoasCmp LessThanEqual (Lit 0) (Var "x1"))))

--
---- foas to phoas
foas_to_phoas :: ValueAlgebra a => FoasProp -> PhoasProp a
foas_to_phoas f = foas_to_phoas' f empty

foas_to_phoas' :: ValueAlgebra a => FoasProp -> Map LVar a -> PhoasProp a
foas_to_phoas' FoasT _ = PhoasT
foas_to_phoas' FoasF _ = PhoasF
foas_to_phoas' (FoasCmp relop s1 s2) env = PhoasCmp relop (expression_to_algebra s1 env) (expression_to_algebra s2 env)
foas_to_phoas' (FoasNot p) env =  PhoasNot  (foas_to_phoas' p env)
foas_to_phoas' (FoasAnd p1 p2) env = PhoasAnd (foas_to_phoas' p1 env) (foas_to_phoas' p2 env)
foas_to_phoas' (FoasOr p1 p2) env = PhoasOr (foas_to_phoas' p1 env) (foas_to_phoas' p2 env)
foas_to_phoas' (FoasImplies p1 p2) env = PhoasImplies (foas_to_phoas' p1 env) (foas_to_phoas' p2 env)
foas_to_phoas' (FoasExist lvar p ) env = PhoasExist (Just lvar) (\v -> foas_to_phoas' p (insert lvar v env))
foas_to_phoas' (FoasForall lvar p) env = PhoasForall (Just lvar) (\v -> foas_to_phoas' p (insert lvar v env))


expression_to_algebra :: ValueAlgebra a => Exp -> Map LVar a -> a
expression_to_algebra (Lit v) _ = lit v
expression_to_algebra (Var x) env = case (M.lookup x env) of
                                Nothing -> error $ "foas formula is not well formed. "++ x ++" is not in scope"
                                Just v -> v
expression_to_algebra (Add s1 s2)   env = add (expression_to_algebra s1 env) (expression_to_algebra s2 env)
expression_to_algebra (Mul s1 s2)   env = mul (expression_to_algebra s1 env) (expression_to_algebra s2 env)
expression_to_algebra (Minus s1 s2) env = minus (expression_to_algebra s1 env) (expression_to_algebra s2 env)








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

{- stm_to_parametric :: ValueAlgebra v => Stm -> v
stm_to_parametric (Lit v) = lit v
    | Var X
    | Add Stm Stm
    | Mul Stm Stm
    | Minus Stm Stm
    | Assign X Stm -- x := Stm (update a variable)
    | Let X Stm Stm -- let X = Stm where Stm (make a new variable)
    | Seq Stm Stm --e1;e2
    | If Bexp Stm Stm -- if bexp then stm else stm -}



{- foas_to_phoas :: ValueAlgebra v => FoasProp->PhoasProp v
foas_to_phoas FoasT = PhoasT 
foas_to_phoas FoasF    | PhoasF 
foas_to_phoas FoasCmp   | PhoasCmp Relop v v  -- these can be both LVars as values 
foas_to_phoas FoasNot p   | PhoasNot (foas_to_phoas p)
foas_to_phoas FoasAnd p1 p2   | PhoasAnd (foas_to_phoas p1) (foas_to_phoas p2)
foas_to_phoas FoasOr    | PhoasOr (foas_to_phoas p1) (foas_to_phoas p2)
foas_to_phoas    | PhoasImplies (foas_to_phoas p) (foas_to_phoas p)
foas_to_phoas    | PhoasExist (Maybe String) (v->(PhoasProp v))
foas_to_phoas    | PhoasForall (Maybe String) (v->(PhoasProp v)) -}



-- the result variable should be named "Result"
data FirstOrderContract = MkContract [LVar] (FoasProp) Prog [LVar] LVar FoasProp
--                universalQuantifications precondition Program Parameters ResultName storeNames Postcondition

data Contract v =  ForallC (Maybe String) (v -> Contract v) -- forAll logicVariables {Precondition} Program {Int->Postcondition}
    | HoareTriple (PhoasProp v) Prog [v] (v->PhoasProp v)


firstOrderAbsContract :: FirstOrderContract
firstOrderAbsContract=  MkContract ["x"] FoasT absoluteValue ["x"] "result" $ FoasAnd (FoasCmp GreaterThanEqual (Var "result") (Lit 0)) (FoasCmp GreaterThanEqual (Var "result") (Var "x"))

absoluteValueContract :: ValueAlgebra v => Contract v
absoluteValueContract = ForallC (Just "x") (\x->HoareTriple PhoasT absoluteValue [x] (\result->PhoasAnd (PhoasCmp GreaterThanEqual result (lit 0)) (PhoasCmp GreaterThanEqual result x)))




foas_to_phoas_contract :: ValueAlgebra v => FirstOrderContract -> Contract v
foas_to_phoas_contract contract = foas_to_phoas_contract_env contract empty

foas_to_phoas_contract_env :: ValueAlgebra v => FirstOrderContract ->M.Map LVar v -> Contract v
foas_to_phoas_contract_env (MkContract (x:xs) precondition program variables result postcondition) env = ForallC (Just x) (\a -> foas_to_phoas_contract_env (MkContract xs precondition program variables result postcondition) (insert x a env))
foas_to_phoas_contract_env (MkContract [] precondition program variables result postcondition) env =
   HoareTriple (foas_to_phoas' precondition env) program (fmap (env !) variables) (\r-> foas_to_phoas' postcondition (insert result r env))




--(?x:(True=>(((Var "x" < Lit 0)=>((Minus (Lit 0) (Var "x") >= Lit 0)/\(Minus (Lit 0) (Var "x") >= Var "x")))/\(-(Var "x" < Lit 0)=>((Var "x" >= Lit 0)/\(Var "x" >= Var "x"))))))
foas_to_coq_formula :: FoasProp -> String
foas_to_coq_formula FoasT = "True"
foas_to_coq_formula FoasF = "False"
foas_to_coq_formula( FoasCmp relop s1 s2) =  "("++  showCoq relop ++" "++showCoqExp s1 ++" "++ showCoqExp s2++")" -- these can be both LVars as values 
foas_to_coq_formula (FoasNot p) = "(not "++ foas_to_coq_formula p++")"
foas_to_coq_formula( FoasAnd p1 p2) = "(and "++foas_to_coq_formula p1 ++ foas_to_coq_formula p2 ++")"
foas_to_coq_formula (FoasOr p1 p2) = "(or "++ foas_to_coq_formula p1 ++ foas_to_coq_formula p2++")"
foas_to_coq_formula (FoasImplies p1 p2) = "(forall _ :"++ foas_to_coq_formula p1 ++ ", " ++ foas_to_coq_formula p2 ++ ")"
foas_to_coq_formula (FoasExist lvar p ) = "("++ "exists "++ lvar ++ " : Z, "++ foas_to_coq_formula p ++ ")"
foas_to_coq_formula (FoasForall lvar p) = "("++ "forall "++ lvar ++ " : Z, "++ foas_to_coq_formula p ++ ")"

showCoq :: Relop->String
showCoq Equal = "eq"
showCoq LessThan ="Z.lt"
showCoq GreaterThan="Z.gt"
showCoq LessThanEqual = "Z.le"
showCoq GreaterThanEqual = "Z.ge"

showCoqExp :: Exp->String
showCoqExp (Lit value) = show value
showCoqExp (Var x) = x
showCoqExp (Add s1 s2) = "(Z.add "++ showCoqExp s1 ++ " " ++ showCoqExp s2 ++ ")"
showCoqExp (Mul s1 s2) = "(Z.mul "++ showCoqExp s1 ++ " " ++ showCoqExp s2 ++ ")"
showCoqExp (Minus s1 s2) = "(Z.sub "++ showCoqExp s1 ++ " " ++ showCoqExp s2 ++ ")"

makeCoqTheorem :: String -> FoasProp->String
makeCoqTheorem name formula = "Theorem "++name++" :\n" ++ foas_to_coq_formula formula ++".\nProof.\nlia.\nQed."


makeCoqFileContent :: String -> FoasProp->String
makeCoqFileContent name formula = "Require Import ZArith.\nRequire Import Lia.\nOpen Scope Z_scope.\n\n" ++ makeCoqTheorem name formula



makeCoqFile :: String -> FoasProp->IO ()
makeCoqFile name formula = writeFile (name ++ ".v") (makeCoqFileContent name formula)

prettyPrint :: FoasProp->String
prettyPrint FoasT = "True"
prettyPrint FoasF = "False"
prettyPrint( FoasCmp relop s1 s2) =  "("++ show s1 ++ " "++ show relop ++" "++ show s2++")" -- these can be both LVars as values 
prettyPrint (FoasNot p) = "~"++ "(" ++ prettyPrint p ++")"
prettyPrint( FoasAnd p1 p2) = "("++prettyPrint p1 ++ "/\\" ++ prettyPrint p2 ++")"
prettyPrint (FoasOr p1 p2) = "("++ prettyPrint p1 ++ "\\/" ++ prettyPrint p2++")"
prettyPrint (FoasImplies p1 p2) = "("++ prettyPrint p1 ++ "->" ++ prettyPrint p2 ++ ")"
prettyPrint (FoasExist lvar p ) = "("++ "?"++ lvar ++ ":"++ prettyPrint p ++ ")"
prettyPrint (FoasForall lvar p) = "("++ "!"++ lvar ++":"++ prettyPrint p ++ ")"


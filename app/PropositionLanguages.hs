{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{- HLINT ignore "Use camelCase" -}
module PropositionLanguages where
import ProgrammingLanguage
import Foas
import Phoas
import Hoas


import Control.Monad.Reader
import Data.Map as M
import Control.Monad.State
import Documentation.SBV.Examples.Transformers.SymbolicEval (Env(result))




-- we define the syntax for Assertions

-- assumes the maybe string isn't of the form "x" ++ show i for an integer i.





-- typeclass for the operations on Values.
instance ValueAlgebra Exp where
  lit = Lit
  add = Add
  mul = Mul
  minus = Minus


instance ValueAlgebra DBExp where
  lit = DBLit
  add = DBAdd
  mul = DBMul
  minus :: DBExp -> DBExp -> DBExp
  minus = DBMinus

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

instance ValueAlgebra (Reader Int DBExp) where
  lit i = return $ DBLit i
  add :: Reader Int DBExp -> Reader Int DBExp -> Reader Int DBExp
  add x y = do v1 <- x
               v2 <- y
               return (DBAdd v1 v2)
  mul x y=  do v1 <- x
               v2 <- y
               return (DBMul v1 v2)
  minus :: Reader Int DBExp -> Reader Int DBExp -> Reader Int DBExp
  minus x y=do v1 <- x
               v2 <- y
               return (DBMinus v1 v2)


instance ValueAlgebra (State Int Exp) where
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

-- the motivation between Foas.Value is that in the Hoas prop, you can say Exists (\v-> Cmp Equal v 5) so in first order a comparison could be between variables and Foas.Values (Exist "v" (Cmp Equal (Var "v") (Val 5)))


type IntReader v = Reader Int v



{- phoasValue_to_foasValueReader :: PhoasValue (IntReader Stm) -> IntReader FoasValue
phoasValue_to_foasValueReader (PVal v) = return $ FVal v
phoasValue_to_foasValueReader (PVar rfv) = rfv -}

example_2_scopes ::  Phoas.Prop a
example_2_scopes = Phoas.And (Phoas.Forall  (\a -> Phoas.Cmp Equal a a)) (Phoas.Exist (\a-> Phoas.Cmp Equal a a ))

example_db ::  Phoas.Prop a
example_db = Phoas.Forall  (\b -> Phoas.And (Phoas.Forall  (\a -> Phoas.Cmp Equal a b)) (Phoas.Cmp Equal b b)) 




-------------------


phoas_to_foas :: Phoas.Prop (IntReader Exp) -> Foas.Prop
phoas_to_foas phoasProp = runReader (phoas_to_foas_reader phoasProp) 0

phoas_to_foas_reader :: Phoas.Prop (IntReader Exp) -> IntReader Foas.Prop
phoas_to_foas_reader Phoas.T = return Foas.T
phoas_to_foas_reader Phoas.F = return Foas.F
phoas_to_foas_reader (Phoas.Cmp op l r) = do v1 <- l
                                             v2 <- r
                                             return $ Foas.Cmp op v1 v2
phoas_to_foas_reader (Phoas.Not p) = do r <- phoas_to_foas_reader p
                                        return $ Foas.Not r
phoas_to_foas_reader (Phoas.And p1 p2)    = binary_prop_to_foas_reader p1 p2 Foas.And
phoas_to_foas_reader (Phoas.Or p1 p2)     = binary_prop_to_foas_reader p1 p2 Foas.Or
phoas_to_foas_reader (Phoas.Implies p1 p2)= binary_prop_to_foas_reader p1 p2 Foas.Implies
phoas_to_foas_reader (Phoas.Exist f)    = quantifiers_to_foas_reader f Foas.Exist
phoas_to_foas_reader (Phoas.Forall f)   = quantifiers_to_foas_reader f Foas.Forall

-- interprets a quantifier
quantifiers_to_foas_reader :: ((IntReader Exp)->Phoas.Prop (IntReader Exp))->(LVar->Foas.Prop->Foas.Prop)->IntReader Foas.Prop
quantifiers_to_foas_reader f quantifier=do i <- ask
                                           let arg = "x" ++ show i 
                                           body <- (local (+1) $ phoas_to_foas_reader $ (f (return (Var arg))))
                                           return $ quantifier arg body




--interprets a binary propositional operator.
binary_prop_to_foas_reader :: (Phoas.Prop (IntReader Exp))->(Phoas.Prop (IntReader Exp))->(Foas.Prop->Foas.Prop->Foas.Prop)->IntReader Foas.Prop
binary_prop_to_foas_reader p1 p2 bin = do r1 <- phoas_to_foas_reader p1
                                          r2 <- phoas_to_foas_reader p2
                                          return $ bin r1 r2
---------------------------------
type IntState v = State Int v

phoas_to_foas_global :: Phoas.Prop (IntState Exp) -> Foas.Prop
phoas_to_foas_global phoasProp = evalState (phoas_to_foas_state phoasProp) 0




phoas_to_foas_state :: Phoas.Prop (IntState Exp) -> IntState Foas.Prop
phoas_to_foas_state Phoas.T = return Foas.T
phoas_to_foas_state Phoas.F = return Foas.F
phoas_to_foas_state (Phoas.Cmp op l r) = do v1 <- l
                                            v2 <- r
                                            return $ Foas.Cmp op v1 v2
phoas_to_foas_state (Phoas.Not p) = do r <- phoas_to_foas_state p
                                       return $ Foas.Not r
phoas_to_foas_state (Phoas.And p1 p2)    = binary_prop_to_foas_state p1 p2 Foas.And
phoas_to_foas_state (Phoas.Or p1 p2)     = binary_prop_to_foas_state p1 p2 Foas.Or
phoas_to_foas_state (Phoas.Implies p1 p2)= binary_prop_to_foas_state p1 p2 Foas.Implies
phoas_to_foas_state (Phoas.Exist f)    = quantifiers_to_foas_state f Foas.Exist
phoas_to_foas_state (Phoas.Forall f)   = quantifiers_to_foas_state f Foas.Forall




-- interprets a quantifier
quantifiers_to_foas_state ::  ((IntState Exp)->Phoas.Prop (IntState Exp))->(LVar->Foas.Prop->Foas.Prop)->IntState Foas.Prop
quantifiers_to_foas_state f quantifier=do i <- get
                                          let arg = "x" ++ show i 
                                          modify (+1)
                                          body <- (phoas_to_foas_state $ (f (return (Var arg))))
                                          return $ quantifier arg body
                                            



--interprets a binary propositional operator.
binary_prop_to_foas_state :: (Phoas.Prop (IntState Exp))->(Phoas.Prop (IntState Exp))->(Foas.Prop->Foas.Prop->Foas.Prop)->IntState Foas.Prop
binary_prop_to_foas_state p1 p2 bin = do r1 <- phoas_to_foas_state p1
                                         r2 <- phoas_to_foas_state p2
                                         return $ bin r1 r2
---------------------------

phoas_to_foas_state_exp :: Phoas.Prop Exp -> Foas.Prop
phoas_to_foas_state_exp phoasProp = evalState (phoas_to_foas_state' phoasProp) 0




phoas_to_foas_state' :: Phoas.Prop Exp -> IntState Foas.Prop
phoas_to_foas_state' Phoas.T = return Foas.T
phoas_to_foas_state' Phoas.F = return Foas.F
phoas_to_foas_state' (Phoas.Cmp op l r) = return $ Foas.Cmp op l r
phoas_to_foas_state' (Phoas.Not p) = do r <- phoas_to_foas_state' p
                                        return $ Foas.Not r
phoas_to_foas_state' (Phoas.And p1 p2)    = binary_prop_to_foas_state' p1 p2 Foas.And
phoas_to_foas_state' (Phoas.Or p1 p2)     = binary_prop_to_foas_state' p1 p2 Foas.Or
phoas_to_foas_state' (Phoas.Implies p1 p2)= binary_prop_to_foas_state' p1 p2 Foas.Implies
phoas_to_foas_state' (Phoas.Exist f)    = quantifiers_to_foas_state' f Foas.Exist
phoas_to_foas_state' (Phoas.Forall f)   = quantifiers_to_foas_state' f Foas.Forall

-- interprets a quantifier
quantifiers_to_foas_state' ::  (( Exp)->Phoas.Prop ( Exp))->(LVar->Foas.Prop->Foas.Prop)->IntState Foas.Prop
quantifiers_to_foas_state' f quantifier=do i <- get
                                           let arg = "x" ++ show i 
                                           modify (+1)
                                           body <- (phoas_to_foas_state' $ (f (Var arg)))
                                           return $ quantifier arg body
--interprets a binary propositional operator.
binary_prop_to_foas_state' :: (Phoas.Prop ( Exp))->(Phoas.Prop ( Exp))->(Foas.Prop->Foas.Prop->Foas.Prop)->IntState Foas.Prop
binary_prop_to_foas_state' p1 p2 bin = do r1 <- phoas_to_foas_state' p1
                                          r2 <- phoas_to_foas_state' p2
                                          return $ bin r1 r2








-----------------------------
phoas_to_foas_unfolded :: Phoas.Prop (Exp) -> Foas.Prop
phoas_to_foas_unfolded phoasProp = runReader (phoas_to_foas_reader' phoasProp) 0

-----------------------------------

phoas_to_foas_reader' :: Phoas.Prop (Exp) -> IntReader Foas.Prop
phoas_to_foas_reader' Phoas.T = return Foas.T
phoas_to_foas_reader' Phoas.F = return Foas.F
phoas_to_foas_reader' (Phoas.Cmp op l r) = return $ Foas.Cmp op l r
phoas_to_foas_reader' (Phoas.Not p) = do r <- phoas_to_foas_reader' p
                                         return $ Foas.Not r
phoas_to_foas_reader' (Phoas.And p1 p2)    = binary_prop_to_foas_reader' p1 p2 Foas.And
phoas_to_foas_reader' (Phoas.Or p1 p2)     = binary_prop_to_foas_reader' p1 p2 Foas.Or
phoas_to_foas_reader' (Phoas.Implies p1 p2)= binary_prop_to_foas_reader' p1 p2 Foas.Implies
phoas_to_foas_reader' (Phoas.Exist f)    = quantifiers_to_foas_reader' f Foas.Exist
phoas_to_foas_reader' (Phoas.Forall f)   = quantifiers_to_foas_reader' f Foas.Forall

binary_prop_to_foas_reader' :: (Phoas.Prop ( Exp))->(Phoas.Prop (Exp))->(Foas.Prop->Foas.Prop->Foas.Prop)->IntReader Foas.Prop
binary_prop_to_foas_reader' p1 p2 bin = do r1 <- phoas_to_foas_reader' p1
                                           r2 <- phoas_to_foas_reader' p2
                                           return $ bin r1 r2


quantifiers_to_foas_reader' ::  (Exp->Phoas.Prop ( Exp))->(LVar->Foas.Prop->Foas.Prop)->IntReader Foas.Prop
quantifiers_to_foas_reader' f quantifier=do i <- ask
                                            let arg = "x" ++ show i
                                            --no suggestion provided, we pick arg as our fresh variable and increment i with 1.
                                            body <- (local (+1) $ phoas_to_foas_reader' $ (f (Var arg)))
                                            return $ quantifier arg body
---------------------------------- de bruijn
data DBExp = DBLit Value
    | DBVar Int
    | DBAdd DBExp DBExp
    | DBMul DBExp DBExp
    | DBMinus DBExp DBExp
  deriving (Eq,Show)

data DBProp = DBT
    | DBF
    | DBCmp Relop DBExp DBExp -- these can be both LVars as values 
    | DBNot DBProp
    | DBAnd DBProp DBProp
    | DBOr DBProp DBProp
    | DBImplies DBProp DBProp
    | DBExist DBProp
    | DBForall DBProp
    deriving (Eq,Show)



phoas_to_db :: Phoas.Prop (IntReader DBExp) -> DBProp
phoas_to_db phoasProp = runReader (phoas_to_db_reader phoasProp) 0

phoas_to_db_reader :: Phoas.Prop (IntReader DBExp) -> IntReader DBProp
phoas_to_db_reader Phoas.T = return DBT
phoas_to_db_reader Phoas.F = return DBF
phoas_to_db_reader (Phoas.Cmp op l r) = do v1 <- l
                                           v2 <- r
                                           return $ DBCmp op v1 v2
phoas_to_db_reader (Phoas.Not p) = do r <- phoas_to_db_reader p
                                      return $ DBNot r
phoas_to_db_reader (Phoas.And p1 p2)    = binary_prop_to_db_reader p1 p2 DBAnd
phoas_to_db_reader (Phoas.Or p1 p2)     = binary_prop_to_db_reader p1 p2 DBOr
phoas_to_db_reader (Phoas.Implies p1 p2)= binary_prop_to_db_reader p1 p2 DBImplies
phoas_to_db_reader (Phoas.Exist f)    = quantifiers_to_db_reader f DBExist
phoas_to_db_reader (Phoas.Forall f)   = quantifiers_to_db_reader f DBForall

-- interprets a quantifier
quantifiers_to_db_reader :: ((IntReader DBExp)->Phoas.Prop (IntReader DBExp))->(DBProp->DBProp)->IntReader DBProp
quantifiers_to_db_reader  f quantifier=do i <- ask
                                          body <- (local (+1) $ phoas_to_db_reader $ (f (reader (\j -> DBVar (j-(i+1))))))
                                          return $ quantifier body


--interprets a binary propositional operator.
binary_prop_to_db_reader :: (Phoas.Prop (IntReader DBExp))->(Phoas.Prop (IntReader DBExp))->(DBProp->DBProp->DBProp)->IntReader DBProp
binary_prop_to_db_reader p1 p2 bin = do r1 <- phoas_to_db_reader p1
                                        r2 <- phoas_to_db_reader p2
                                        return $ bin r1 r2













------------------------------------



phoas_to_hoas ::  Phoas.Prop Value-> Hoas.Prop
phoas_to_hoas Phoas.T = Hoas.T
phoas_to_hoas Phoas.F = Hoas.F
phoas_to_hoas (Phoas.Cmp op l r) = Hoas.Cmp op l r
phoas_to_hoas (Phoas.Not p) = Hoas.Not  (phoas_to_hoas p)
phoas_to_hoas (Phoas.And p1 p2)    = Hoas.And (phoas_to_hoas p1) (phoas_to_hoas p2)
phoas_to_hoas (Phoas.Or p1 p2)     = Hoas.Or (phoas_to_hoas p1) (phoas_to_hoas p2)
phoas_to_hoas (Phoas.Implies p1 p2)= Hoas.Implies (phoas_to_hoas p1) (phoas_to_hoas p2)
phoas_to_hoas (Phoas.Exist f)    = Hoas.Exist (phoas_to_hoas . f)
phoas_to_hoas (Phoas.Forall f)   = Hoas.Forall (phoas_to_hoas . f)


-- forall x, there exist y: x<y /\ 0<y
phoas_example ::ValueAlgebra v => Phoas.Prop v
phoas_example= Phoas.Forall (\x->Phoas.Exist (\y->(Phoas.And (Phoas.Cmp LessThanEqual x y) (Phoas.Cmp LessThanEqual (lit 0) y))))

foas_example :: Foas.Prop
foas_example = Foas.Forall "x0" (Foas.Exist "x1" (Foas.And (Foas.Cmp LessThanEqual (Var "x0") (Var "x1")) (Foas.Cmp LessThanEqual (Lit 0) (Var "x1"))))

--
---- foas to phoas
foas_to_phoas :: ValueAlgebra a => Foas.Prop -> Phoas.Prop a
foas_to_phoas f = foas_to_phoas' f empty

foas_to_phoas' :: ValueAlgebra a => Foas.Prop -> Map String a -> Phoas.Prop a
foas_to_phoas' Foas.T _ = Phoas.T
foas_to_phoas' Foas.F _ = Phoas.F
foas_to_phoas' (Foas.Not p) env =  Phoas.Not  (foas_to_phoas' p env)
foas_to_phoas' (Foas.And p1 p2) env = Phoas.And (foas_to_phoas' p1 env) (foas_to_phoas' p2 env)
foas_to_phoas' (Foas.Or p1 p2) env = Phoas.Or (foas_to_phoas' p1 env) (foas_to_phoas' p2 env)
foas_to_phoas' (Foas.Implies p1 p2) env = Phoas.Implies (foas_to_phoas' p1 env) (foas_to_phoas' p2 env)
foas_to_phoas' (Foas.Exist lvar p ) env = Phoas.Exist  (\v -> foas_to_phoas' p (insert lvar v env))
foas_to_phoas' (Foas.Forall lvar p) env = Phoas.Forall  (\v -> foas_to_phoas' p (insert lvar v env))
foas_to_phoas' (Foas.Cmp relop s1 s2) env = Phoas.Cmp relop (expression_to_algebra s1 env) (expression_to_algebra s2 env)

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

type Phoas.Proposition = forall a. forall p. Proposition p a => p -}

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



{- foas_to_phoas :: ValueAlgebra v => Foas.Prop->Phoas.Prop v
foas_to_phoas Foas.T = Phoas.T 
foas_to_phoas Foas.F    | Phoas.F 
foas_to_phoas Foas.Cmp   | Phoas.Cmp Relop v v  -- these can be both LVars as values 
foas_to_phoas Foas.Not p   | Phoas.Not (foas_to_phoas p)
foas_to_phoas Foas.And p1 p2   | Phoas.And (foas_to_phoas p1) (foas_to_phoas p2)
foas_to_phoas Foas.Or    | Phoas.Or (foas_to_phoas p1) (foas_to_phoas p2)
foas_to_phoas    | Phoas.Implies (foas_to_phoas p) (foas_to_phoas p)
foas_to_phoas    | Phoas.Exist (Maybe String) (v->(Phoas.Prop v))
foas_to_phoas    | Phoas.Forall (Maybe String) (v->(Phoas.Prop v)) -}




data FirstOrderContract = MkContract [LVar] (Foas.Prop) Prog [Exp] LVar Foas.Prop
  deriving (Eq,Show)
--                universalQuantifications precondition Program Parameters ResultName storeNames Postcondition

data Contract v =  ForallC (v -> Contract v) -- forAll logicVariables {Precondition} Program {Int->Postcondition}
    | HoareTriple (Phoas.Prop v) Prog [v] (v->Phoas.Prop v)



foas_to_phoas_contract :: ValueAlgebra v => FirstOrderContract -> Contract v
foas_to_phoas_contract contract = foas_to_phoas_contract_env contract empty

foas_to_phoas_contract_env :: ValueAlgebra v => FirstOrderContract ->M.Map LVar v -> Contract v
foas_to_phoas_contract_env (MkContract (x:xs) precondition program variables result postcondition) env = ForallC (\a -> foas_to_phoas_contract_env (MkContract xs precondition program variables result postcondition) (insert x a env))
foas_to_phoas_contract_env (MkContract [] precondition program variables result postcondition) env =
   HoareTriple (foas_to_phoas' precondition env) program (Prelude.map (`expression_to_algebra` env) (variables)) (\r-> foas_to_phoas' postcondition (insert result r env))




--(?x:(True=>(((Var "x" < Lit 0)=>((Minus (Lit 0) (Var "x") >= Lit 0)/\(Minus (Lit 0) (Var "x") >= Var "x")))/\(-(Var "x" < Lit 0)=>((Var "x" >= Lit 0)/\(Var "x" >= Var "x"))))))
foas_to_coq_formula :: Foas.Prop -> String
foas_to_coq_formula Foas.T = "True"
foas_to_coq_formula Foas.F = "False"
foas_to_coq_formula( Foas.Cmp relop s1 s2) =  "("++  showCoq relop ++" "++showCoqExp s1 ++" "++ showCoqExp s2++")" -- these can be both LVars as values 
foas_to_coq_formula (Foas.Not p) = "(not "++ foas_to_coq_formula p++")"
foas_to_coq_formula( Foas.And p1 p2) = "(and "++foas_to_coq_formula p1 ++ foas_to_coq_formula p2 ++")"
foas_to_coq_formula (Foas.Or p1 p2) = "(or "++ foas_to_coq_formula p1 ++ foas_to_coq_formula p2++")"
foas_to_coq_formula (Foas.Implies p1 p2) = "(forall _ :"++ foas_to_coq_formula p1 ++ ", " ++ foas_to_coq_formula p2 ++ ")"
foas_to_coq_formula (Foas.Exist lvar p ) = "("++ "exists "++ lvar ++ " : Z, "++ foas_to_coq_formula p ++ ")"
foas_to_coq_formula (Foas.Forall lvar p) = "("++ "forall "++ lvar ++ " : Z, "++ foas_to_coq_formula p ++ ")"

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

makeCoqTheorem :: String -> Foas.Prop->String
makeCoqTheorem name formula = "Theorem "++name++" :\n" ++ foas_to_coq_formula formula ++".\nProof.\neauto 10 with arith_hints.\nQed."


makeCoqFileContent :: String -> Foas.Prop->String
makeCoqFileContent name formula = "Require Import ZArith Psatz.\nOpen Scope Z_scope.\n#[local] Hint Extern 1 => nia : arith_hints.\n\n" ++ makeCoqTheorem name formula



makeCoqFile :: String -> Foas.Prop->IO ()
makeCoqFile name formula = writeFile (name ++ ".v") (makeCoqFileContent name formula)

prettyPrint :: Foas.Prop->String
prettyPrint Foas.T = "True"
prettyPrint Foas.F = "False"
prettyPrint( Foas.Cmp relop s1 s2) =  "("++ show s1 ++ " "++ show relop ++" "++ show s2++")" -- these can be both LVars as values 
prettyPrint (Foas.Not p) = "~"++ "(" ++ prettyPrint p ++")"
prettyPrint( Foas.And p1 p2) = "("++prettyPrint p1 ++ "/\\" ++ prettyPrint p2 ++")"
prettyPrint (Foas.Or p1 p2) = "("++ prettyPrint p1 ++ "\\/" ++ prettyPrint p2++")"
prettyPrint (Foas.Implies p1 p2) = "("++ prettyPrint p1 ++ "->" ++ prettyPrint p2 ++ ")"
prettyPrint (Foas.Exist lvar p ) = "("++ "?"++ lvar ++ ":"++ prettyPrint p ++ ")"
prettyPrint (Foas.Forall lvar p) = "("++ "!"++ lvar ++":"++ prettyPrint p ++ ")"


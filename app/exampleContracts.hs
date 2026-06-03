module ExampleContracts where

import ProgrammingLanguage
import PropositionLanguages
import Foas
import Phoas
import Hoas



{- assign_and_return :: Prog
assign_and_return = Fun "f" ["y"] (Let "x" (Add (Lit 7) (Var "y")) (Expr $ Lit 5))

assign_return_hoas_contract :: ValueAlgebra v => Contract v
assign_return_hoas_contract = ForallC (Just "y") (\y-> HoareTriple (Phoas.Cmp GreaterThanEqual y (lit 0)) assign_and_return [y] (\result->Phoas.Cmp GreaterThanEqual (fromJust $ Prelude.lookup "x" store ) (lit 0)))


successor :: Prog
successor = Fun "add1" ["y"] succStm
succStm :: Stm
succStm = (Expr (Add (Lit 1) (Var "y")))

succContract ::ValueAlgebra v => Contract v
succContract = ForallC (Just "i") (\i->HoareTriple (Phoas.T) successor [i] (\iPlus1 _ -> Phoas.Cmp Equal iPlus1 (add (i) (lit 1))))
-- wp succStm (\result _->Phoas.Cmp GreaterThanEqual result 0) ["y"]
test :: IO ()
test = putStrLn $ prettyPrint $ phoas_to_foas $ vc succContract -}








absoluteValue :: Prog
absoluteValue = Fun "abs" ["x"] 
                (If (Compare LessThan (Var "x") (Lit 0)) 
                    (Expr (Minus (Lit 0) (Var "x"))) 
                    (Expr (Var "x")))

mySum :: Prog
mySum  = Fun "sum" ["x"] (If (Compare Equal (Lit 0) (Var "x")) 
                                  (Expr (Lit 0))
                                  (Let "recursive_result" (Recurse [Expr (Minus (Var "x") (Lit 1))]) 
                                    (Expr (Add (Var "x") (Var "recursive_result")))))


infiniteProg :: Prog
infiniteProg = Fun "infinite" ["x"] (Recurse [Expr (Var "x")])



runSum :: Int -> Maybe Int
runSum n = execute mySum [n]

distributive :: Prog 
distributive = Fun "distributive" ["x0","x1","x2"] (Expr (Mul (Var "x0") (Add (Var "x1") (Var "x2"))))

modulo :: Prog
modulo = Fun "mod" ["a", "b"]
  (If (Compare LessThan (Var "a") (Var "b"))
      (Expr (Var "a"))
      (Recurse [Expr (Minus (Var "a") (Var "b")), Expr (Var "b")]))

exp :: Prog
exp = Fun "mod" ["a", "b"]
  (If (Compare LessThan (Var "a") (Var "b"))
      (Expr (Var "a"))
      (Recurse [Expr (Minus (Var "a") (Var "b")), Expr (Var "b")]))

max :: Prog
max = Fun "maximum" ["a", "b"]
                (If (Compare GreaterThanEqual (Var "a") (Var "b")) 
                    (Expr (Var "a")) 
                    (Expr (Var "b")))

maxAdditionContract :: FirstOrderContract
maxAdditionContract = MkContract ["x","y"] -- quantifiers
                                ( (Foas.Cmp LessThanEqual (Lit 0) (Var "x"))
                                         ) -- precondition

                                ExampleContracts.max [(Add (Var "x") (Var "y")) , Var "y"] --program and its parameters
                                
                                "result" --name of the result in the postcondition                      
                                ( (Foas.Cmp Equal (Var "result") (Add (Var "x") (Var "y")))) --postcondition


maxAdditionContractPhoas :: ValueAlgebra v => Contract v
maxAdditionContractPhoas  = ForallC (\x -> ForallC (\y -> 
                                  HoareTriple (Phoas.Cmp LessThanEqual (lit 0) x) 
                                              ExampleContracts.max [add x y, y]
                                              (\result -> Phoas.Cmp Equal result (add x y))))




firstOrderAbsContract :: FirstOrderContract
firstOrderAbsContract=  MkContract ["x"] 
                                    Foas.T 
                                    absoluteValue [Var "x"]
                                     "result" $ 
                                     Foas.And (Foas.Cmp GreaterThanEqual (Var "result") (Lit 0))
                                             (Foas.Cmp GreaterThanEqual (Var "result") (Var "x"))

absoluteValueContract :: ValueAlgebra v => Contract v
absoluteValueContract = ForallC (\x->
                              HoareTriple 
                              Phoas.T 
                              absoluteValue [x] 
                              (\result-> Phoas.And (Phoas.Cmp GreaterThanEqual result (lit 0)) 
                                                  (Phoas.Cmp GreaterThanEqual result x)))

mySumFoasContract :: FirstOrderContract
mySumFoasContract = MkContract ["in"] (Foas.Cmp GreaterThanEqual (Var "in") (Lit 0)) mySum [Var "in"] "result" (Foas.Cmp Equal (Mul (Lit 2) (Var "result")) (Mul (Var "in") (Add (Var "in") (Lit 1))))

mySumContract :: ValueAlgebra v => Contract v
mySumContract = ForallC (\inp -> HoareTriple (Phoas.Cmp GreaterThanEqual inp (lit 0)) mySum [inp] (\result  -> Phoas.Cmp Equal (mul (lit 2) result) (mul inp (add inp (lit 1)))))
  
distributiveContract :: FirstOrderContract
distributiveContract = MkContract ["a","b","c"] Foas.T distributive [Var "a",Var "b",Var "c"] "result" (Foas.Cmp Equal (Add (Mul (Var "a") (Var "b")) (Mul (Var "a") (Var "c"))) (Var "result"))

moduloContractSmaller :: FirstOrderContract
moduloContractSmaller = MkContract ["a","b"] Foas.T modulo [Var "a",Var "b"] "result" (Foas.Cmp LessThan (Var "result") (Var "b"))
moduloContractSmallernormal :: FirstOrderContract
moduloContractSmallernormal = MkContract ["b","a"] Foas.T modulo [Var "a",Var "b"] "result" (Foas.Cmp LessThan (Var "result") (Var "b"))


infiniteContract1 :: FirstOrderContract
infiniteContract1 =MkContract ["x"] Foas.T infiniteProg [Var "x"] "result" (Foas.Cmp Equal (Var "result") (Lit 1))

infiniteContract2 =MkContract ["x"] Foas.T infiniteProg [Var "x"] "result" Foas.F


 

-- examples
add_5_to_1_with_var :: Stm
add_5_to_1_with_var = Let "x" (Expr (Lit 5)) (Expr (Add (Var "x") (Lit 1)))

testingScope :: Stm
testingScope = Let "x" (Expr (Lit 5)) (Seq (Assign "x" (Expr (Lit 1))) (Expr (Var "x")))

testingScope2 :: Stm
testingScope2 = Seq (Let "x" (Expr (Lit 5)) (Expr (Lit 5))) (Expr (Lit 7))

testingScope3 :: Stm
testingScope3 = Let "y" (Expr (Lit 2)) (Let "x" (Expr (Lit 3)) (Seq (Let "y" (Expr (Lit 4)) (Assign "x" (Expr (Lit 2)))) (Expr (Add (Var "x") (Var "y")))))

absoluteValueStm :: Stm
absoluteValueStm = Let "x" (Expr (Lit (-5))) (If (Compare LessThan (Var "x") ( (Lit 0))) (Expr (Minus ( (Lit 0)) (Var "x"))) (Expr (Var "x")))



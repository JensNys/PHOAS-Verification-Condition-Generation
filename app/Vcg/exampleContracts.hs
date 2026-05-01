module Vcg.ExampleContracts where

import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration

import Data.Maybe



{- assign_and_return :: Prog
assign_and_return = Fun "f" ["y"] (Let "x" (Add (Lit 7) (Var "y")) (Expr $ Lit 5))

assign_return_hoas_contract :: ValueAlgebra v => Contract v
assign_return_hoas_contract = ForallC (Just "y") (\y-> HoareTriple (PhoasCmp GreaterThanEqual y (lit 0)) assign_and_return [y] (\result->PhoasCmp GreaterThanEqual (fromJust $ Prelude.lookup "x" store ) (lit 0)))


successor :: Prog
successor = Fun "add1" ["y"] succStm
succStm :: Stm
succStm = (Expr (Add (Lit 1) (Var "y")))

succContract ::ValueAlgebra v => Contract v
succContract = ForallC (Just "i") (\i->HoareTriple (PhoasT) successor [i] (\iPlus1 _ -> PhoasCmp Equal iPlus1 (add (i) (lit 1))))
-- wp succStm (\result _->PhoasCmp GreaterThanEqual result 0) ["y"]
test :: IO ()
test = putStrLn $ prettyPrint $ phoas_to_foas $ vc succContract -}








absoluteValue :: Prog
absoluteValue = Fun "abs" ["x"] (If (Compare LessThan (Var "x") (Lit 0)) (Expr (Minus (Lit 0) (Var "x"))) (Expr (Var "x")))

mySum :: Prog
mySum  = Fun "sum" ["x"] (If (Compare Equal (Lit 0) (Var "x")) 
                                  (Expr (Lit 0))
                                  (Let "sum_until_x_min_1" (Recurse [Expr (Minus (Var "x") (Lit 1))]) 
                                    (Expr (Add (Var "x") (Var "sum_until_x_min_1")))))

runSum :: Int -> Maybe Int
runSum n = execute mySum [n]

distributive :: Prog 
distributive = Fun "distributive" ["x0","x1","x2"] (Expr (Mul (Var "x0") (Add (Var "x1") (Var "x2"))))

modulo :: Prog
modulo = Fun "mod" ["a", "b"]
  (If (Compare LessThan (Var "a") (Var "b"))
      (Expr (Var "a"))
      (Recurse [Expr (Minus (Var "a") (Var "b")), Expr (Var "b")]))


      

firstOrderAbsContract :: FirstOrderContract
firstOrderAbsContract=  MkContract ["x"] FoasT absoluteValue ["x"] "result" $ FoasAnd (FoasCmp GreaterThanEqual (Var "result") (Lit 0)) (FoasCmp GreaterThanEqual (Var "result") (Var "x"))

absoluteValueContract :: ValueAlgebra v => Contract v
absoluteValueContract = ForallC (\x->HoareTriple PhoasT absoluteValue [x] (\result->PhoasAnd (PhoasCmp GreaterThanEqual result (lit 0)) (PhoasCmp GreaterThanEqual result x)))

mySumFoasContract :: FirstOrderContract
mySumFoasContract = MkContract ["in"] (FoasCmp GreaterThanEqual (Var "in") (Lit 0)) mySum ["in"] "result" (FoasCmp Equal (Mul (Lit 2) (Var "result")) (Mul (Var "in") (Add (Var "in") (Lit 1))))

mySumContract :: ValueAlgebra v => Contract v
mySumContract = ForallC (\inp -> HoareTriple (PhoasCmp GreaterThanEqual inp (lit 0)) mySum [inp] (\result  -> PhoasCmp Equal (mul (lit 2) result) (mul inp (add inp (lit 1)))))
  
distributiveContract :: FirstOrderContract
distributiveContract = MkContract ["a","b","c"] FoasT distributive ["a","b","c"] "result" (FoasCmp Equal (Add (Mul (Var "a") (Var "b")) (Mul (Var "a") (Var "c"))) (Var "result"))

moduloContractSmaller :: FirstOrderContract
moduloContractSmaller = MkContract ["a","b"] FoasT modulo ["a","b"] "result" (FoasCmp LessThan (Var "result") (Var "b"))
moduloContractSmallernormal :: FirstOrderContract
moduloContractSmallernormal = MkContract ["b","a"] FoasT modulo ["a","b"] "result" (FoasCmp LessThan (Var "result") (Var "b"))








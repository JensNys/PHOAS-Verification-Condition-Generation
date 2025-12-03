import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration

import Data.Maybe



assign_and_return :: Prog
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
test = putStrLn $ prettyPrint $ phoas_to_foas $ vc succContract
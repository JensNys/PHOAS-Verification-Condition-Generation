{-# HLINT ignore "Use camelCase" #-}
module Vcg.Benchmark where
import Criterion.Main
import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration


----------------------- benchmarking foas_to_phoas------------------------



-- benchmark_prop n has n variable introductions and 2n variable occurences
benchmark_foas_prop :: Int -> FoasProp
benchmark_foas_prop 0 = FoasT
benchmark_foas_prop i = FoasExist (show i) (FoasAnd (FoasCmp Equal (Var (show i)) (Var (show i))) (benchmark_foas_prop (i-1)))

benchmark_foas_to_phoas ::ValueAlgebra v => Int -> PhoasProp v
benchmark_foas_to_phoas n = foas_to_phoas (benchmark_foas_prop n)







-----------------------benchmarking phoas_to_foas------------------------

benchmark_phoas_prop ::  Int -> PhoasProp v
benchmark_phoas_prop 0 = PhoasT
benchmark_phoas_prop i = PhoasExist (\var -> PhoasAnd (PhoasCmp Equal var var) (benchmark_phoas_prop (i-1)))




-----------------------benchmarking "middle" part of vcgen------------------------

-- benchmark_stm n assumes there are already n variables named ("i" ++ show k) with k<=n in scope, has n Let introductions, n assignments, and 2n variable lookups
benchmark_stm :: Int -> Stm
benchmark_stm 0 = Expr (Lit 0)
benchmark_stm n = Let ("l" ++ show n) (Expr (Var ("i" ++ show n))) (Seq (Assign ("l" ++ show n) (Add (Var ("l" ++ show n)) (Lit 1)) ) (benchmark_stm (n-1)))

benchmark_program :: Int -> Prog
benchmark_program n =Fun "f" (map (\i -> "i" ++ show i) [1 .. n]) (benchmark_stm n)

benchmark_phoas_contract :: Int -> Contract v
benchmark_phoas_contract n = benchmark_phoas_contract_variables n [] 

benchmark_phoas_contract_variables :: Int ->[v]-> Contract v
benchmark_phoas_contract_variables 0 params = HoareTriple (benchmark_phoas_prop (length params)) (benchmark_program 0) params (\result -> benchmark_phoas_prop (length params))
benchmark_phoas_contract_variables n params = ForallC  (\var -> benchmark_phoas_contract_variables (n-1) (var:params))








-----------------------benchmarking end-to-end------------------------
benchmark_foas_contract :: Int ->  FirstOrderContract
benchmark_foas_contract n = MkContract (map (\i -> "i" ++ show i) [1 .. n]) (benchmark_foas_prop n) (benchmark_program n) (map (\i -> "i" ++ show i) [1 .. n]) "result" (benchmark_foas_prop n) 


benchmark_reader_reader :: Int -> FoasProp
benchmark_reader_reader  = vcFoas_reader_reader . benchmark_foas_contract

benchmark_reader_exp :: Int -> FoasProp
benchmark_reader_exp  = vcFoas_reader_exp . benchmark_foas_contract

benchmark_state_state :: Int -> FoasProp
benchmark_state_state  = vcFoas_state_state . benchmark_foas_contract

--benchmark_state_exp :: Int -> FoasProp
--benchmark_state_exp  = vcFoas_state_exp . benchmark_foas_contract


benchmark_db :: Int -> DBProp
benchmark_db  = vcFoas_db . benchmark_foas_contract




runBenchmark  :: IO ()
runBenchmark  = defaultMain
  [ bgroup "benchmark_reader_reader"
      [ bench (show n) $ whnf benchmark_reader_reader n
      | n <- [1..50]
      ]
  ]

--MkContract [LVar] (FoasProp) Prog [LVar] LVar FoasProp
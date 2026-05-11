{-# HLINT ignore "Use camelCase" #-}
module Vcg.Benchmark where
import Criterion.Main
import Criterion.Main.Options (defaultConfig)
import Criterion.Types (csvFile)
import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration


----------------------- benchmarking foas_to_phoas------------------------



-- benchmark_prop n has n variable introductions and 2n variable occurences. Occurence and introduction is close to each other.
benchmark_foas_prop_close :: Int -> FoasProp
benchmark_foas_prop_close 0 = FoasT
benchmark_foas_prop_close i = FoasExist (show i) (FoasAnd (FoasCmp Equal (Var (show i)) (Var (show i))) (benchmark_foas_prop_close (i-1)))



-- benchmark_prop n has n variable introductions and 2n variable occurences. Occurence and introduction is close to each other.


benchmark_intro :: Int -> Int-> FoasProp
benchmark_intro 0 n = benchmark_usage n
benchmark_intro i n = FoasExist (show i)  (benchmark_foas_prop_close (i-1))

benchmark_usage ::  Int -> FoasProp
benchmark_usage 0 = FoasT
benchmark_usage i = FoasAnd (FoasCmp Equal (Var (show i)) (Var (show i))) (benchmark_usage (i-1))

benchmark_foas_prop_far :: Int -> FoasProp
benchmark_foas_prop_far n = benchmark_intro n n

benchmark_f2p2f_close :: Int -> Int
benchmark_f2p2f_close = sizeFoasProp . phoas_to_foas_unfolded . foas_to_phoas . benchmark_foas_prop_close


benchmark_f2p2f_far :: Int -> Int
benchmark_f2p2f_far = sizeFoasProp .  phoas_to_foas_unfolded . foas_to_phoas . benchmark_foas_prop_close








-----------------------benchmarking phoas_to_foas------------------------

benchmark_phoas_prop ::  Int -> PhoasProp v
benchmark_phoas_prop 0 = PhoasT
benchmark_phoas_prop i = PhoasExist (\var -> PhoasAnd (PhoasCmp Equal var var) (benchmark_phoas_prop (i-1)))




-----------------------benchmarking "middle" part of vcgen------------------------

-- benchmark_stm n assumes there are already n variables named ("i" ++ show k) with k<=n in scope, has n Let introductions, n assignments, and 2n variable lookups
benchmark_stm :: Int -> Stm
benchmark_stm 0 = Expr (Lit 0)
benchmark_stm n = Let ("l" ++ show n) (Expr (Var ("i" ++ show n))) (Seq (Assign ("l" ++ show n) (Expr (Add (Var ("l" ++ show n)) (Lit 1))) ) (benchmark_stm (n-1)))

-- benchmark_stm n assumes there are already n variables named ("i" ++ show k) with k<=n in scope, has n Let introductions, n assignments, and 2n variable lookups
benchmark_stm_far :: Int->Int -> Stm
benchmark_stm_far 0 i= Recurse (map (\i -> Expr (Var ("l" ++ show i))) [1..i])
benchmark_stm_far n i= Let ("l" ++ show n) (Expr (Var ("i" ++ show n))) (benchmark_stm_far (n-1) i)



benchmark_program :: Int -> Prog
benchmark_program n =Fun "f" (map (\i -> "i" ++ show i) [1 .. n]) (benchmark_stm n)

benchmark_program_far :: Int -> Prog
benchmark_program_far n = Fun "f" (map (\i -> "i" ++ show i) [1 .. n]) (benchmark_stm_far n n)



benchmark_phoas_contract :: Int -> Contract v
benchmark_phoas_contract n = benchmark_phoas_contract_variables n [] 

benchmark_phoas_contract_variables :: Int ->[v]-> Contract v
benchmark_phoas_contract_variables 0 params = HoareTriple (benchmark_phoas_prop (length params)) (benchmark_program 0) params (\result -> benchmark_phoas_prop (length params))
benchmark_phoas_contract_variables n params = ForallC  (\var -> benchmark_phoas_contract_variables (n-1) (var:params))


sizeFoasProp :: FoasProp -> Int
sizeFoasProp FoasT                  = 1
sizeFoasProp FoasF                  = 1
sizeFoasProp (FoasCmp _ _ _)        = 1
sizeFoasProp (FoasNot p)            = 1 + sizeFoasProp p
sizeFoasProp (FoasAnd p q)          = 1 + sizeFoasProp p + sizeFoasProp q
sizeFoasProp (FoasOr p q)           = 1 + sizeFoasProp p + sizeFoasProp q
sizeFoasProp (FoasImplies p q)      = 1 + sizeFoasProp p + sizeFoasProp q
sizeFoasProp (FoasExist _ p)        = 1 + sizeFoasProp p
sizeFoasProp (FoasForall _ p)       = 1 + sizeFoasProp p


sizeDBProp :: DBProp -> Int
sizeDBProp DBT                  = 1
sizeDBProp DBF                  = 1
sizeDBProp (DBCmp _ _ _)        = 1
sizeDBProp (DBNot p)            = 1 + sizeDBProp p
sizeDBProp (DBAnd p q)          = 1 + sizeDBProp p + sizeDBProp q
sizeDBProp (DBOr p q)           = 1 + sizeDBProp p + sizeDBProp q
sizeDBProp (DBImplies p q)      = 1 + sizeDBProp p + sizeDBProp q
sizeDBProp (DBExist p)          = 1 + sizeDBProp p
sizeDBProp (DBForall p)         = 1 + sizeDBProp p

-----------------------benchmarking end-to-end------------------------
benchmark_foas_contract :: Int ->  FirstOrderContract
benchmark_foas_contract n = MkContract (map (\i -> "i" ++ show i) [1 .. n]) (benchmark_foas_prop_close n) (benchmark_program n) (map (\i -> Var ("i" ++ show i)) [1 .. n]) "result" (benchmark_foas_prop_close n) 

benchmark_foas_contract_far :: Int ->  FirstOrderContract
benchmark_foas_contract_far n = MkContract (map (\i -> "i" ++ show i) [1 .. n]) (benchmark_foas_prop_far n) (benchmark_program_far n) (map (\i -> Var ("i" ++ show i)) [1 .. n]) "result" (benchmark_foas_prop_far n) 




benchmark_reader_reader :: Int -> Int
benchmark_reader_reader  = sizeFoasProp . vcFoas_reader_reader . benchmark_foas_contract

benchmark_reader_exp :: Int -> Int
benchmark_reader_exp  = sizeFoasProp .vcFoas_reader_exp . benchmark_foas_contract

benchmark_state_state :: Int -> Int
benchmark_state_state  = sizeFoasProp . vcFoas_state_state . benchmark_foas_contract

benchmark_state_exp :: Int -> Int
benchmark_state_exp  = sizeFoasProp . vcFoas_state_exp . benchmark_foas_contract


benchmark_db :: Int -> Int
benchmark_db  = sizeDBProp . vcFoas_db . benchmark_foas_contract

benchmark_values :: Int-> [Int]
benchmark_values 0 = []
benchmark_values n = benchmark_values (n-1) ++ [(100 * (2 ^ n)) ]

-----------------geen vcgen, close-------------
f2p2f_close_reader_reader :: Int->Int
f2p2f_close_reader_reader = sizeFoasProp . phoas_to_foas . foas_to_phoas . benchmark_foas_prop_close

f2p2f_close_reader_exp :: Int->Int
f2p2f_close_reader_exp = sizeFoasProp . phoas_to_foas_unfolded . foas_to_phoas . benchmark_foas_prop_close

f2p2f_close_state_state :: Int->Int
f2p2f_close_state_state =sizeFoasProp . phoas_to_foas_unfolded . foas_to_phoas . benchmark_foas_prop_close

f2p2f_close_state_exp :: Int->Int
f2p2f_close_state_exp =sizeFoasProp . phoas_to_foas_state_exp . foas_to_phoas . benchmark_foas_prop_close

f2p2f_close_db :: Int->Int
f2p2f_close_db =sizeDBProp . phoas_to_db . foas_to_phoas . benchmark_foas_prop_close

-- geen vcgen, far---

f2p2f_far_reader_reader :: Int->Int
f2p2f_far_reader_reader = sizeFoasProp . phoas_to_foas . foas_to_phoas . benchmark_foas_prop_far

f2p2f_far_reader_exp :: Int->Int
f2p2f_far_reader_exp = sizeFoasProp . phoas_to_foas_unfolded . foas_to_phoas . benchmark_foas_prop_far

f2p2f_far_state_state :: Int->Int
f2p2f_far_state_state = sizeFoasProp . phoas_to_foas_unfolded . foas_to_phoas . benchmark_foas_prop_far

f2p2f_far_state_exp :: Int->Int
f2p2f_far_state_exp = sizeFoasProp . phoas_to_foas_state_exp . foas_to_phoas . benchmark_foas_prop_far

f2p2f_far_db :: Int->Int
f2p2f_far_db = sizeDBProp . phoas_to_db . foas_to_phoas . benchmark_foas_prop_far

---------- with vcgen--- close


benchmark_reader_reader_close :: Int -> Int
benchmark_reader_reader_close  = sizeFoasProp . vcFoas_reader_reader . benchmark_foas_contract

benchmark_reader_exp_close :: Int -> Int
benchmark_reader_exp_close  = sizeFoasProp .vcFoas_reader_exp . benchmark_foas_contract

benchmark_state_state_close :: Int -> Int
benchmark_state_state_close  = sizeFoasProp . vcFoas_state_state . benchmark_foas_contract

benchmark_state_exp_close :: Int -> Int
benchmark_state_exp_close  = sizeFoasProp . vcFoas_state_exp . benchmark_foas_contract


benchmark_db_close :: Int -> Int
benchmark_db_close  = sizeDBProp . vcFoas_db . benchmark_foas_contract


--- with vcgen far (does recursion but no assignments)


benchmark_reader_reader_far :: Int -> Int
benchmark_reader_reader_far  = sizeFoasProp . vcFoas_reader_reader . benchmark_foas_contract_far

benchmark_reader_exp_far :: Int -> FoasProp
benchmark_reader_exp_far  = vcFoas_reader_exp . benchmark_foas_contract_far

benchmark_state_state_far :: Int -> Int
benchmark_state_state_far  = sizeFoasProp . vcFoas_state_state . benchmark_foas_contract_far

benchmark_state_exp_far :: Int -> Int
benchmark_state_exp_far  = sizeFoasProp . vcFoas_state_exp . benchmark_foas_contract_far


benchmark_db_far :: Int -> Int
benchmark_db_far  = sizeDBProp . vcFoas_db . benchmark_foas_contract_far





runBenchmark :: IO ()
runBenchmark = defaultMainWith (defaultConfig { csvFile = Just "results.csv" })
  [ bgroup "f2p2f_close"
      [ bgroup "reader_reader" [ bench (show n) $ whnf f2p2f_close_reader_reader n | n <- benchmark_values 10 ]
      , bgroup "reader_exp"    [ bench (show n) $ whnf f2p2f_close_reader_exp n    | n <- benchmark_values 10 ]
      , bgroup "state_state"   [ bench (show n) $ whnf f2p2f_close_state_state n   | n <- benchmark_values 10 ]
      , bgroup "state_exp"     [ bench (show n) $ whnf f2p2f_close_state_exp n     | n <- benchmark_values 10 ]
      , bgroup "db"            [ bench (show n) $ whnf f2p2f_close_db n            | n <- benchmark_values 10 ]
      ]
  , bgroup "f2p2f_far"
      [ bgroup "reader_reader" [ bench (show n) $ whnf f2p2f_far_reader_reader n | n <- benchmark_values 10 ]
      , bgroup "reader_exp"    [ bench (show n) $ whnf f2p2f_far_reader_exp n    | n <- benchmark_values 10 ]
      , bgroup "state_state"   [ bench (show n) $ whnf f2p2f_far_state_state n   | n <- benchmark_values 10 ]
      , bgroup "state_exp"     [ bench (show n) $ whnf f2p2f_far_state_exp n     | n <- benchmark_values 10 ]
      , bgroup "db"            [ bench (show n) $ whnf f2p2f_far_db n            | n <- benchmark_values 10 ]
      ]
  , bgroup "vcgen_close"
      [ bgroup "reader_reader" [ bench (show n) $ whnf benchmark_reader_reader_close n | n <- benchmark_values 10 ]
      , bgroup "reader_exp"    [ bench (show n) $ whnf benchmark_reader_exp_close n    | n <- benchmark_values 10 ]
      , bgroup "state_state"   [ bench (show n) $ whnf benchmark_state_state_close n   | n <- benchmark_values 10 ]
      , bgroup "state_exp"     [ bench (show n) $ whnf benchmark_state_exp_close n     | n <- benchmark_values 10 ]
      , bgroup "db"            [ bench (show n) $ whnf benchmark_db_close n            | n <- benchmark_values 10 ]
      ]
  , bgroup "vcgen_far"
      [ bgroup "reader_reader" [ bench (show n) $ whnf benchmark_reader_reader_far n | n <- benchmark_values 8 ]
      , bgroup "reader_exp"    [ bench (show n) $ whnf benchmark_reader_exp_far n    | n <- benchmark_values 8 ]
      , bgroup "state_state"   [ bench (show n) $ whnf benchmark_state_state_far n   | n <- benchmark_values 8 ]
      , bgroup "state_exp"     [ bench (show n) $ whnf benchmark_state_exp_far n     | n <- benchmark_values 8 ]
      , bgroup "db"            [ bench (show n) $ whnf benchmark_db_far n            | n <- benchmark_values 8 ]
      ]
  ]
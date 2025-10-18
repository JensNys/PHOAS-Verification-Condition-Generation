--import Test.QuickCheck
import Test.HUnit
import Data.Map
import Week1.LambdaCalculi
--import SimpleLanguage



main :: IO ()
main = runTestTT tests >> return ()


tests = TestList [test6,test7]
-- run 1 test with runTestTT test1
-- run all tests by runTestTT tests


--test1 = TestCase (assertEqual "typeclass_hoasI is converted correctly for I combinator" foasI (typeclass_hoas_to_foas typeclass_hoasI))

-- the following tests will work if Eq considers alpha equivalence.
--test2 = TestCase (assertEqual "phoasI is converted correctly for I combinator" foasI (typeclass_hoas_to_foas typeclass_hoasI))
--test2 = TestCase (assertEqual "phoasI is converted correctly for I combinator" foasI (run foas_example))

--test4 = TestCase (assertEqual "interp" (interp (singleton "x" 1) (Add (EVar "x") (EConst 2))) 3)
--test5 = TestCase (assertEqual "exec" (Data.Map.lookup "i" (exec empty countUntil10)) (Just 10))

test6 = TestCase (assertEqual "exec" (typeclass_phoas_to_foas typeclass_hoas_example) (typeclass_phoas_to_readerfoas typeclass_hoas_example))
test7 = TestCase (assertEqual "exec" (typeclass_phoas_to_foas typeclass_hoas_example) (phoas_to_foas phoas_example))




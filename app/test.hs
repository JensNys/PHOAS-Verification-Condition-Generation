import Test.QuickCheck
import Test.HUnit
import LambdaCalculi




main :: IO ()
main = runTestTT tests >> return ()


tests = TestList [test1]
-- run 1 test with runTestTT test1
-- run all tests by runTestTT tests


test1 = TestCase (assertEqual "typeclass_hoasI is converted correctly for I combinator" foasI (typeclass_hoas_to_foas typeclass_hoasI))

-- the following tests will work if Eq considers alpha equivalence.
--test2 = TestCase (assertEqual "phoasI is converted correctly for I combinator" foasI (typeclass_hoas_to_foas typeclass_hoasI))
--test2 = TestCase (assertEqual "phoasI is converted correctly for I combinator" foasI (run foas_example))






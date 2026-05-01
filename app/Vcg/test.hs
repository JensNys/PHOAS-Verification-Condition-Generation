--import Test.Quickcheck
module Vcg.Test where
import Test.HUnit

import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration
import Data.Map

runTests :: IO ()
runTests = runTestTT tests >> return ()

tests :: Test
tests = TestList [test1,test2,test3,test4,test5,test6,test7]
-- run 1 test with runTestTT test1
-- run all tests by runTestTT tests

test1 :: Test
test1 = TestCase (assertEqual "absoluteValue" (runStatement absoluteValueStm) (Just (5,empty))) 
test2 :: Test
test2 = TestCase (assertEqual "testScope1" (runStatement testingScope) (Just (1,empty))) 
test3 :: Test
test3 = TestCase (assertEqual "testScope2" (runStatement testingScope2) (Just (7, empty))) 
test4 :: Test
test4 = TestCase (assertEqual "testScope3" (runStatement testingScope3) (Just (4, empty))) 
test5 :: Test 
test5 = TestCase (assertEqual "test phoas_to_foas" (phoas_to_foas phoas_example) (foas_example))
test6 :: Test 
test6 = TestCase (assertEqual "test foas_to_phoas" (phoas_to_foas (foas_to_phoas foas_example)) (foas_example))
test7 :: Test
test7 = TestCase (assertEqual "test Contract conversion" (vcFoas_reader_reader firstOrderAbsContract) (phoas_to_foas $ vc absoluteValueContract))




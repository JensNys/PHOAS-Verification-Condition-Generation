--import Test.Quickcheck
module Vcg.Test where
import Test.HUnit

import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration
import Vcg.ExampleContracts
import Data.Map
import System.Process (readProcessWithExitCode)
import System.Exit (ExitCode(..))
import Vcg.ExampleContracts (infiniteContract1)

runTests :: IO ()
runTests = runTestTT tests >> return ()

tests :: Test
tests = TestList [test1,test2,test3,test4,test5,test6,test7,test8,test9,test10,test11,test12,test13,test14,test15]
-- run 1 test with runTestTT test1
-- run all tests by runTestTT tests



propVerifier :: String -> FoasProp-> Test
propVerifier name prop = 
    TestCase $ do
                    
                    makeCoqFile name prop
                    (exitCode, _, stderr) <- readProcessWithExitCode "coqc" [name ++ ".v"] ""
                    assertEqual ("Coq verification failed:\n" ++ stderr) ExitSuccess exitCode




contractVerifier :: String -> FirstOrderContract-> Test
contractVerifier name contract = propVerifier name (vcFoas_reader_reader contract)
    



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


test8 :: Test 
test8 = contractVerifier "test_file"  firstOrderAbsContract


test9 :: Test 
test9 = contractVerifier "test_file"  mySumFoasContract

test10 :: Test 
test10 = contractVerifier "test_file"  distributiveContract

test11 :: Test 
test11 = contractVerifier "test_file"  moduloContractSmaller

test12 :: Test 
test12 = contractVerifier "test_file"  moduloContractSmallernormal

test13 :: Test
test13 = contractVerifier "test_file" maxAdditionContract


test14 :: Test
test14 = contractVerifier "test_file" infiniteContract1
test15 :: Test
test15 = contractVerifier "test_file" infiniteContract2
 






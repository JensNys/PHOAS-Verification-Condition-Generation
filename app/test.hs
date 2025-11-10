--import Test.Quickcheck
import ProgramAssertionSemantics
import Test.HUnit


runTests :: IO ()
runTests = runTestTT tests >> return ()

tests :: Test
tests = TestList [test1,test2,test3,test4,test5,test6]
-- run 1 test with runTestTT test1
-- run all tests by runTestTT tests

test1 :: Test
test1 = TestCase (assertEqual "absoluteValue" (runStatement absoluteValueStm) (Just (5,[]))) 
test2 :: Test
test2 = TestCase (assertEqual "testScope1" (runStatement testingScope) (Just (1,[]))) 
test3 :: Test
test3 = TestCase (assertEqual "testScope2" (runStatement testingScope2) (Just (7, []))) 
test4 :: Test
test4 = TestCase (assertEqual "testScope3" (runStatement testingScope3) (Just (4, []))) 
test5 :: Test 
test5 = TestCase (assertEqual "test phoas_to_foas" (phoas_to_foas phoas_example) (foas_example))


test6 :: Test 
test6 = TestCase (assertEqual "test foas_to_phoas" (phoas_to_foas (foas_to_phoas foas_example)) (foas_example))


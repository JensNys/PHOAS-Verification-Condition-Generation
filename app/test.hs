import Test.HUnit
import ProgramAssertionSemantics



main :: IO ()
main = runTestTT tests >> return ()

tests :: Test
tests = TestList [test1,test2,test3]
-- run 1 test with runTestTT test1
-- run all tests by runTestTT tests

test1 :: Test
test1 = TestCase (assertEqual "absoluteValue" (runStatement absoluteValueStm) (Just (5,[]))) 
test2 :: Test
test2 = TestCase (assertEqual "testScope1" (runStatement testingScope) (Just (1,[]))) 
test3 :: Test
test3 = TestCase (assertEqual "testScope2" (runStatement testingScope2) (Just (7, []))) 

import Test.HUnit
import ProgramAssertions




main :: IO ()
main = runTestTT tests >> return ()


tests = TestList [test1,test2,test3]
-- run 1 test with runTestTT test1
-- run all tests by runTestTT tests


test1 = TestCase (assertEqual "" (runStatement absoluteValueStm) (Just (5,fromList []))) 
test2 = TestCase (assertEqual "" (runStatement testingScope) (Just (1,fromList []))) 
test3 = TestCase (assertEqual "" (runStatement testingScope2) (Just (7,fromList []))) 

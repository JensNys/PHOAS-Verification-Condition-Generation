module Main where
    
--import Vcg.ProgrammingLanguage
import PropositionLanguages
import ConstraintGeneration
import Test

import Benchmark (runBenchmark)

main :: IO ()
main = runBenchmark--runTests
--main =  makeCoqFile "absoluteValueContractFirstOrderInput" $ vcFoas_reader_exp firstOrderAbsContract



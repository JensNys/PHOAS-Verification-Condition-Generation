module Main where
    
--import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration
import Vcg.Test

import Vcg.Benchmark (runBenchmark)

main :: IO ()
main = runTests
--main =  makeCoqFile "absoluteValueContractFirstOrderInput" $ vcFoas_reader_exp firstOrderAbsContract



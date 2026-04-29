module Main where
    
--import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration


import Vcg.Benchmark (runBenchmark)

main :: IO ()
main = runBenchmark
--main =  makeCoqFile "absoluteValueContractFirstOrderInput" $ vcFoas_reader_exp firstOrderAbsContract



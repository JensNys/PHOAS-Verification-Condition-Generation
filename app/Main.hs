module Main where
    
--import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration


main ::IO ()
main =  makeCoqFile "absoluteValueContractFirstOrderInput" $ vcFoas firstOrderAbsContract



module Main where
    
import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
import Vcg.ConstraintGeneration


main ::IO ()
main =  makeCoqFile "absoluteValueContract2" $ phoas_to_foas $ vc absoluteValueContract



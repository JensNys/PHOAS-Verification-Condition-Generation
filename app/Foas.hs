module Foas where 
    import ProgrammingLanguage
    type LVar = String
    data Prop = T
        | F
        | Cmp Relop Exp Exp -- these can be both LVars as values 
        | Not Prop
        | And Prop Prop
        | Or Prop Prop
        | Implies Prop Prop
        | Exist LVar Prop
        | Forall LVar Prop
        deriving (Eq,Show)
    

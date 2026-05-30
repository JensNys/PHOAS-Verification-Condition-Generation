module Hoas where
    import ProgrammingLanguage
    
    data Prop = T
        | F
        | Cmp Relop Value Value
        | Not Prop
        | And Prop Prop
        | Or Prop Prop
        | Implies Prop Prop
        | Exist (Value->Prop)
        | Forall (Value->Prop)

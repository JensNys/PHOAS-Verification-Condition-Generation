module Phoas where
    import ProgrammingLanguage
    
    data Prop v = T
        | F
        | Cmp Relop v v  -- these can be both LVars as values 
        | Not (Prop v)
        | And (Prop v) (Prop v)
        | Or (Prop v) (Prop v)
        | Implies (Prop v) (Prop v)
        | Exist (v->Prop v)
        | Forall (v->Prop v)
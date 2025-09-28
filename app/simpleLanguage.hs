

import Data.Map
type Var = String

type Const = Int

data Exp = EConst Const
    | EVar Var
    | Add Exp Exp
    | Mul Exp Exp
        
type Valuation = Map Var Const

interp :: Valuation -> Exp -> Const
interp v (EConst c)=c
interp v (Evar var) = findWithDefault 0 var v
interp v ()
{- data Command = Skip
    | -}
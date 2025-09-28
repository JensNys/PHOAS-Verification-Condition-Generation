

module SimpleLanguage where
import Data.Map
type Var = String

type Const = Int

data Exp = EConst Const
    | EVar Var
    | Add Exp Exp
    | Mul Exp Exp
    deriving (Show)
type Valuation = Map Var Const

data Command = Skip | Assign Var Exp | Seq Command Command |Repeat Exp Command
    deriving (Show)
{- 
i <- 0;
Repeat 10:
    i <- (i+1)
 -}


interp :: Valuation -> Exp -> Const
interp v (EConst c)=c
interp v (EVar var) = findWithDefault 0 var v
interp v (Add e1 e2) = (interp v e1) + (interp v e2)
interp v (Mul e1 e2) = (interp v e1) * (interp v e2)
{- data Command = Skip
    | -}
n_times :: Int->Command->Command
n_times 0 c = Skip
n_times n c = Seq c (n_times (n-1) c)

exec :: Valuation -> Command -> Valuation
exec v Skip = v
exec v (Assign var e) = insert var (interp v e) v
exec v (Seq c1 c2) = exec (exec v c1) c2
exec v (Repeat e c) = exec v (n_times (interp v e) c)

countUntil10 :: Command
countUntil10 = Seq (Assign "i" (EConst 0)) (Repeat (EConst 10) (Assign "i" (Add (EVar "i") (EConst 1))))


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


plus2 :: Command
plus2 = Seq (Assign "i" (EConst 0)) (Assign "j" (Add (EVar "i") (EConst 2)))


data LExpr a = LConst Const
    | LEVar Var
    | LVar a
    | LAdd (LExpr a) (LExpr a)
    | LMul (LExpr a) (LExpr a)
    deriving (Show)

data Formula a = Equal (LExpr a) (LExpr a)
                | LessThan (LExpr a) (LExpr a)
                | GreaterThan (LExpr a) (LExpr a)

data Assertion a = T | F | Form (Formula a) | And (Assertion a) (Assertion a) | Or (Assertion a) (Assertion a) | Exist (a->Assertion a)

-- ∃n: (i<n ∧ n<j)
isBetween :: Assertion a
isBetween = Exist (\n-> And (Form (LessThan (LEVar "i") (LVar n))) (Form ((LessThan (LVar n) (LEVar "j") ))))


lInterp :: Valuation -> LExpr a -> Const
lInterp v (LConst c)=c
lInterp v (LEVar var) = findWithDefault 0 var v
lInterp v (LAdd e1 e2) = (lInterp v e1) + (lInterp v e2)
lInterp v (LMul e1 e2) = (lInterp v e1) * (lInterp v e2)
-- Lvar case should throw an error because you don't know its value.



lInterpFormula:: Valuation -> Formula a -> Bool
lInterpFormula v (Equal e1 e2) = (lInterp v e1) ==( lInterp v e2)
lInterpFormula v (LessThan e1 e2) = (lInterp v e1) < (lInterp v e2)
lInterpFormula v (GreaterThan e1 e2) = (lInterp v e1) > (lInterp v e2)


-- infinite list of all integers.
ints :: [Int]
ints = concatMap (\n -> [n, -n]) [0..]


--T | F | Formula a | And (Assertion a) (Assertion a) | Or (Assertion a) (Assertion a) | Exist (a->Assertion a)
-- problem: iterates over all integers for an exists statement, so isn't 
semant :: Valuation -> Assertion a -> Bool
semant v T = True
semant v F = False
semant v (Form f) = lInterpFormula v f
semant v (And a1 a2) = (semant v a1) && (semant v a2)
semant v (Or a1 a2) = (semant v a1) || (semant v a2)

-- this doens't typecheck because i give [Int] instead of [a]. If it would typecheck it still wouldn't work because I can't interpret ex. (LVar 10) to 10, I can only interpret LVar a if a is an integer but i can't enforce that in lInterp. Even if that worked, it wouldn't terminate if there is no integer that satisfies the statement.
--semant v (Exist f) = any ((semant v) . f) ints







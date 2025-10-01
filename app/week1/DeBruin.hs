

data DBTerm = DBVar Int
    | DBLam DBTerm
    | DBApp DBTerm DBTerm
    deriving (Show,Eq)








class UntypedLambda exp where
    lam :: (exp -> exp) -> exp
    app :: exp -> exp -> exp 

type Hoas = forall a. UntypedLambda a => a

example1 :: Hoas
example1 = lam (\x -> lam (\y -> x `app` y))


newtype Size = Size { size :: Integer }

instance UntypedLambda Size where
    lam f = Size $ 1 + size (f (Size 1))
    x `app` y = Size $ 1 + size x + size y


getSize :: Hoas -> Integer
getSize term = size term

newtype DB = DB { unDB :: Int -> DBTerm }

instance UntypedLambda DB where
    lam f = DB $ \i -> let v = \j -> DBVar (j-(i+1)) in
        DBLam (unDB (f (DB v)) (i+1))
    app x y = DB $ \i -> DBApp (unDB x i) (unDB y i)

toTerm :: Hoas -> DBTerm
toTerm v = unDB v 0


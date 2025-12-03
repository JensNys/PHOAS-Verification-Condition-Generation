{-# LANGUAGE RankNTypes  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{- HLINT ignore "Use camelCase" -}
module Vcg.ConstraintGeneration where
import Vcg.ProgrammingLanguage
import Vcg.PropositionLanguages
--import Control.Monad.State
import Control.Monad (liftM, ap)



newtype Wpure v a = Wpure {runWpure :: (a->PhoasProp v)->PhoasProp v}
instance Functor (Wpure v) where
  fmap = liftM

instance Applicative (Wpure v) where
  pure a = Wpure $ (\post->post a)
  (<*>) = ap

instance Monad (Wpure v) where
    return = pure
    c >>= k = Wpure $ (\post-> (runWpure c) (\a->runWpure (k a) post))




angelic :: ValueAlgebra v =>Maybe String -> Wpure v v
angelic m = Wpure $ (\post-> PhoasExist m (\v->post v))

demonic :: ValueAlgebra v => Maybe String -> Wpure v v
demonic m = Wpure $ (\post-> PhoasForall m (\v->post v))






newtype Wstore v a = Wstore {runWstore :: (a->(Store v)->PhoasProp v)->(Store v)->PhoasProp v}
instance Functor (Wstore v) where
  fmap = liftM
instance Applicative (Wstore v) where
  pure a = Wstore $ (\post store->post a store)
  (<*>) = ap

instance Monad (Wstore v) where
    return = pure
    c >>= k = Wstore $ (\post store1-> (runWstore c) (\a store2->runWstore (k a) post store2) store1)


block :: ValueAlgebra v =>Wstore v a
block = Wstore $ (\_ _->PhoasT)

fail :: ValueAlgebra v =>Wstore v a
fail = Wstore $ (\_ _->PhoasF)

-- unicode 2295
(⊕) ::ValueAlgebra v => Wstore v a->Wstore v a -> Wstore v a
m1 ⊕ m2 = Wstore $ (\post store-> PhoasOr ((runWstore m1) post store) ((runWstore m2) post store))

(⊗) :: ValueAlgebra v =>Wstore v a->Wstore v a -> Wstore v a
m1 ⊗ m2 = Wstore $ (\post store -> PhoasAnd ((runWstore m1) post store) ((runWstore m2) post store))


assert :: ValueAlgebra v =>PhoasProp v -> Wstore v ()
assert p = Wstore $ (\post store-> PhoasAnd p (post () store))

assume :: ValueAlgebra v =>PhoasProp v -> Wstore v ()
assume p = Wstore $ (\post store-> PhoasImplies p (post () store))





evalStore ::ValueAlgebra v => Wstore v a ->(Store v)-> Wpure v a
evalStore m store = Wpure $ (\post-> (runWstore m) (\a _->post a) store)

pushStore ::ValueAlgebra v => X->v -> Wstore v ()
pushStore x v = Wstore $ (\post store->post () (pushL x v store))

popStore :: ValueAlgebra v =>Wstore v ()
popStore = Wstore $ (\post store -> post () (popL store))

-- the cond parameter should be 
matchBool_demonic :: ValueAlgebra v =>PhoasProp v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_demonic cond m1 m2= (do assume cond;m1)
                              ⊗
                              (do assume (PhoasNot cond);m2)

matchBool_angelic :: ValueAlgebra v =>PhoasProp v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_angelic cond m1 m2= (do assert cond;m1)
                              ⊕
                              (do assert (PhoasNot cond);m2)


assignWstore ::ValueAlgebra v => X->v->Wstore v ()
assignWstore x v = Wstore $ (\post store->post () (change x v store))

lookupWstore ::ValueAlgebra v => X->Wstore v v
lookupWstore a = Wstore $ (\post store->case (Prelude.lookup a store) of
                                                Nothing -> PhoasF
                                                Just value -> post value store)

-- turns a boolean expression into the proposition that is equivalent to the expression in the monadic Wstore environment
execb :: ValueAlgebra v=> Bexp->Wstore v (PhoasProp v)
execb (Compare op s1 s2) = do x <- exec_exp s1
                              y <- exec_exp s2
                              return (PhoasCmp op x y)




exec_exp :: ValueAlgebra v=> Exp->Wstore v v
exec_exp (Lit c) = return $ lit c
exec_exp (Var a) = lookupWstore a
exec_exp (Add s1 s2) = do x <- exec_exp s1
                          y <- exec_exp s2
                          return (add x y)
exec_exp (Mul s1 s2) = do x <- exec_exp s1
                          y <- exec_exp s2
                          return (mul x y)
exec_exp (Minus s1 s2) = do x <- exec_exp s1
                            y <- exec_exp s2
                            return (minus x y)

exec :: ValueAlgebra v=> Stm->Wstore v v
exec (Expr expr) = exec_exp expr
exec (Assign var s) = do v <-exec_exp s
                         assignWstore var v
                         return v
exec (Let var s1 s2) = do x <- exec_exp s1 -- p -- in a later stage we could let this computation fail if x is already a variable.
                          pushStore var x
                          result <- exec s2
                          popStore
                          return result
exec (Seq s1 s2) = do _ <- exec s1
                      exec s2
exec (If bexp s1 s2) = do b <- execb bexp
                          matchBool_demonic b (exec s1) (exec s2)





-- with normal state: θ St(m) = λpost s0. post (m s0)
-- total correctness interpretation by doing F
{- observationTotal :: ValueAlgebra v => StateT (Store v) Maybe a->Wstore v a 
observationTotal r = Wstore $ (\post s0-> case ((runStateT r) s0) of 
                                          Nothing -> PhoasF
                                          Just (a,store) -> post a store)

-- with normal state: θ St(m) = λpost s0. post (m s0)
-- partial correctness interpretation by doing T
observationPartial :: ValueAlgebra v => StateT (Store v) Maybe a->Wstore v a 
observationPartial r = Wstore $ (\post s0-> case ((runStateT r) s0) of 
                                          Nothing -> PhoasT
                                          Just (a,store) -> post a store) -}



-- Print Scope type_scope. Coq

wp :: ValueAlgebra v=>Stm -> (v->Store v->PhoasProp v)->Store v->PhoasProp v
wp stm post initStore = (runWstore (exec stm)) post initStore




vc :: ValueAlgebra v=>Contract v -> PhoasProp v
vc (ForallC mstring f) = PhoasForall mstring (\v -> vc (f v))
vc (HoareTriple pre prog args post) = case prog of
  Fun _ params body -> PhoasImplies pre (wp body (\result _-> post result) (zip params args))


vcFoas :: FirstOrderContract -> FoasProp
vcFoas  = phoas_to_foas . vc . foas_to_phoas_contract 



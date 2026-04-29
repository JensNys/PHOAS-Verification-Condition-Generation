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
import Data.Map


newtype Wpure v a = Wpure {runWpure :: (a->PhoasProp v)->PhoasProp v}
instance Functor (Wpure v) where
  fmap = liftM

instance Applicative (Wpure v) where
  pure a = Wpure $ (\post->post a)
  (<*>) = ap

instance Monad (Wpure v) where
    return = pure
    c >>= k = Wpure $ (\post-> (runWpure c) (\a->runWpure (k a) post))




angelic :: ValueAlgebra v =>Wpure v v
angelic = Wpure $ (\post-> PhoasExist (\v->post v))

demonic :: ValueAlgebra v =>Wpure v v
demonic = Wpure $ (\post-> PhoasForall (\v->post v))






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





insertStore ::ValueAlgebra v => X->v -> Wstore v ()
insertStore x v = Wstore $ (\post store->post () (insert x v store))

deleteStore ::ValueAlgebra v => X-> Wstore v ()
deleteStore x = Wstore $ (\post store-> post () (delete x store))



lookupWstore_fail ::ValueAlgebra v => X->Wstore v v
lookupWstore_fail k = Wstore $ (\post store->case (Data.Map.lookup k store) of
                                                Nothing -> PhoasF
                                                Just value -> post value store)

lookupWstore_safe ::ValueAlgebra v => X->Wstore v (Maybe v)
lookupWstore_safe k = Wstore $ (\post store-> post (Data.Map.lookup k store) store)

restoreWstore ::ValueAlgebra v => X-> Maybe v ->Wstore v ()
restoreWstore var Nothing = deleteStore var
restoreWstore var (Just val) = insertStore var val




-- the cond parameter should be 
matchBool_demonic :: ValueAlgebra v =>PhoasProp v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_demonic cond m1 m2= (do assume cond;m1)
                              ⊗
                              (do assume (PhoasNot cond);m2)

matchBool_angelic :: ValueAlgebra v =>PhoasProp v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_angelic cond m1 m2= (do assert cond;m1)
                              ⊕
                              (do assert (PhoasNot cond);m2)






-- turns a boolean expression into the proposition that is equivalent to the expression in the monadic Wstore environment
execb :: ValueAlgebra v=> Bexp->Wstore v (PhoasProp v)
execb (Compare op s1 s2) = do x <- exec_exp s1
                              y <- exec_exp s2
                              return (PhoasCmp op x y)




exec_exp :: ValueAlgebra v=> Exp->Wstore v v
exec_exp (Lit c) = return $ lit c
exec_exp (Var a) = lookupWstore_fail a
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
exec (Assign var s) = do v <- exec_exp s
                         insertStore var v
                         return v
exec (Let var s1 s2) = do x <- exec s1 -- p -- 
                          previous <- lookupWstore_safe var
                          insertStore var x
                          result <- exec s2
                          restoreWstore var previous
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
vc (ForallC f) = PhoasForall (\v -> vc (f v))
vc (HoareTriple pre prog args post) = case prog of
  Fun _ params body -> PhoasImplies pre (wp body (\result _-> post result) (fromList (zip params args)))


vcFoas_reader_reader :: FirstOrderContract -> FoasProp
vcFoas_reader_reader  = phoas_to_foas . vc . foas_to_phoas_contract 

vcFoas_reader_exp :: FirstOrderContract -> FoasProp
vcFoas_reader_exp  = phoas_to_foas_unfolded . vc . foas_to_phoas_contract

vcFoas_state_state :: FirstOrderContract -> FoasProp
vcFoas_state_state  = phoas_to_foas_global . vc . foas_to_phoas_contract

--vcFoas_state_exp :: FirstOrderContract -> FoasProp
--vcFoas_state_exp  = phoas_to_foas . vc . foas_to_phoas_contract


vcFoas_db :: FirstOrderContract -> DBProp
vcFoas_db  = phoas_to_db . vc . foas_to_phoas_contract
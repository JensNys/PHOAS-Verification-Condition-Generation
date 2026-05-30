{-# LANGUAGE RankNTypes  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{- HLINT ignore "Use camelCase" -}
module ConstraintGeneration where
import Foas
import Phoas
import Hoas
import ProgrammingLanguage
import PropositionLanguages
--import Control.Monad.State
import Control.Monad (liftM, ap)
import Data.Map
import Phoas
import Foas
import qualified Data.Maybe
import qualified Data.Map as Map



newtype Wstore v a = Wstore {runWstore :: (a->(Store v)->Phoas.Prop v)->(Store v)->Phoas.Prop v}
instance Functor (Wstore v) where
  fmap :: (a -> b) -> Wstore v a -> Wstore v b
  fmap = liftM
instance Applicative (Wstore v) where
  pure a = Wstore $ (\post store->post a store)
  (<*>) = ap

instance Monad (Wstore v) where
    return = pure
    c >>= k = Wstore $ (\post store1-> (runWstore c) (\a store2->runWstore (k a) post store2) store1)





block :: ValueAlgebra v =>Wstore v a
block = Wstore $ (\_ _->Phoas.T)

fail :: ValueAlgebra v =>Wstore v a
fail = Wstore $ (\_ _->Phoas.F)


(⊕) ::ValueAlgebra v => Wstore v a->Wstore v a -> Wstore v a
m1 ⊕ m2 = Wstore $ (\post store-> Phoas.Or ((runWstore m1) post store) ((runWstore m2) post store))

(⊗) :: ValueAlgebra v =>Wstore v a->Wstore v a -> Wstore v a
m1 ⊗ m2 = Wstore $ (\post store -> Phoas.And ((runWstore m1) post store) ((runWstore m2) post store))

-- The given proposition must hold together with our postcondition.
assert :: ValueAlgebra v =>Phoas.Prop v -> Wstore v ()
assert p = Wstore $ (\post store-> Phoas.And p (post () store))

-- If this proposition holds, the postcondition should hold.
assume :: ValueAlgebra v =>Phoas.Prop v -> Wstore v ()
assume p = Wstore $ (\post store-> Phoas.Implies p (post () store))

-- A value is given such that our postcondition holds for it.
angelic :: ValueAlgebra v => Wstore v v
angelic = Wstore $ (\post store-> Phoas.Exist (\v->post v store))

--
demonic :: ValueAlgebra v =>Wstore v v
demonic = Wstore $ (\post store-> Phoas.Forall (\v->post v store))





lookupWstore_fail ::ValueAlgebra v => X->Wstore v v
lookupWstore_fail k = Wstore $ (\post store->case (Data.Map.lookup k store) of
                                                Nothing -> Phoas.F
                                                Just value -> post value store)

lookupWstore_safe ::ValueAlgebra v => X->Wstore v (Maybe v)
lookupWstore_safe k = Wstore $ (\post store-> post (Data.Map.lookup k store) store)

insertStore ::ValueAlgebra v => X->v -> Wstore v ()
insertStore x v = Wstore $ (\post store->post () (insert x v store))

deleteStore ::ValueAlgebra v => X-> Wstore v ()
deleteStore x = Wstore $ (\post store-> post () (delete x store))

restoreWstore ::ValueAlgebra v => X-> Maybe v ->Wstore v ()
restoreWstore var Nothing = deleteStore var
restoreWstore var (Just val) = insertStore var val




-- the cond parameter should be 
matchBool_demonic :: ValueAlgebra v =>Phoas.Prop v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_demonic cond m1 m2= (do assume cond;m1)
                              ⊗
                              (do assume (Phoas.Not cond);m2)

matchBool_angelic :: ValueAlgebra v =>Phoas.Prop v-> Wstore v a-> Wstore v a-> Wstore v a
matchBool_angelic cond m1 m2= (do assert cond;m1)
                              ⊕
                              (do assert (Phoas.Not cond);m2)






-- turns a boolean expression into the proposition that is equivalent to the expression in the monadic Wstore environment
execb :: ValueAlgebra v=> Bexp->Wstore v (Phoas.Prop v)
execb (Compare op s1 s2) = do x <- exec_exp s1
                              y <- exec_exp s2
                              return (Phoas.Cmp op x y)




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

exec_list :: ValueAlgebra v=> [Stm]->Contract v->Wstore v [v]
exec_list l c = exec_list' l [] c

exec_list' :: ValueAlgebra v=> [Stm]->[v]->Contract v->Wstore v [v]
exec_list' (stm:rest) acc c = do v <- (exec stm c)
                                 exec_list' rest (acc ++ [v]) c
exec_list' [] acc _ = return acc


exec :: ValueAlgebra v=> Stm->Contract v->Wstore v v
exec (Expr expr) _= exec_exp expr
exec (Assign var s) c = do v <- exec s c -- evaluate the value that will be given to the variable
                           insertStore var v -- bind this value to the variable name
                           return v
exec (Let var s1 s2) c = do x <- exec s1 c -- evaluate the value that will be given to the variable
                            previous <- lookupWstore_safe var -- save the previous binding to this variable name
                            insertStore var x -- bind the new value to the variable name
                            result <- exec s2 c -- evaluate the body of let under this new store
                            restoreWstore var previous -- restore the state to what it was before this binding
                            return result -- return the result
exec (Seq s1 s2) c = do _ <- exec s1 c -- evaluate the first statement
                        exec s2 c -- evaluate the second statement
exec (If bexp s1 s2) c = do b <- execb bexp
                            matchBool_demonic b (exec s1 c) (exec s2 c)
exec (Recurse stmList) c = 
          do exec_recursion (Recurse stmList) c c

exec (If bexp s1 s2) c = do b <- execb bexp
                            matchBool_demonic b (exec s1 c) (exec s2 c)

                      
allEqual :: [v]->[v]-> Phoas.Prop v
allEqual l1 l2 = Prelude.foldr Phoas.And Phoas.T (zipWith (Phoas.Cmp Equal) l1 l2)



exec_recursion ::ValueAlgebra v=> Stm->Contract v->Contract v -> Wstore v v
exec_recursion (Recurse stmList) (ForallC f) c =
          do v <- angelic --angelically chose a variable to instantiate with
             exec_recursion (Recurse stmList) (f v) c
exec_recursion (Recurse stmList) (HoareTriple pre _ inputs post) c =
          do value_list <- exec_list stmList c -- evaluate the arguments we will call the program with
             assert (allEqual inputs value_list) -- assert that these values are equal to the values in the contract
             assert pre --assert that the precondition holds
             v_result <- demonic -- get a result
             assume (post v_result) -- We assume that the postcondition holds for the result
             return v_result
exec_recursion _ _ _  = do ConstraintGeneration.fail -- this function should only be called when there is recursion





-- Print Scope type_scope. Coq

wp :: ValueAlgebra v=>Stm -> (v->Store v->Phoas.Prop v)->Store v->Contract v->Phoas.Prop v
wp stm post initStore c = (runWstore (exec stm c)) post initStore




vc' :: ValueAlgebra v=>Contract v ->Contract v -> Phoas.Prop v
vc' (ForallC f) c = Phoas.Forall (\v -> vc' (f v) c)
vc' (HoareTriple pre prog args post) c= case prog of
  Fun _ params body -> Phoas.Implies pre (wp body (\result _-> post result) (fromList (zip params args)) c )

vc:: ValueAlgebra v=>Contract v -> Phoas.Prop v
vc c = vc' c c


vcFoas_reader_reader :: FirstOrderContract -> Foas.Prop
vcFoas_reader_reader  = phoas_to_foas . vc . foas_to_phoas_contract 

vcFoas_reader_exp :: FirstOrderContract -> Foas.Prop
vcFoas_reader_exp = phoas_to_foas_unfolded . vc . foas_to_phoas_contract
vcFoas_state_state :: FirstOrderContract -> Foas.Prop
vcFoas_state_state = phoas_to_foas_global . vc . foas_to_phoas_contract 

vcFoas_state_exp :: FirstOrderContract -> Foas.Prop
vcFoas_state_exp  = phoas_to_foas_state_exp . vc . foas_to_phoas_contract 


vcFoas_db :: FirstOrderContract -> DBProp
vcFoas_db   = phoas_to_db . vc . foas_to_phoas_contract 
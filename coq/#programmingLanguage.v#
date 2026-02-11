From Coq Require Import
  Classes.Morphisms
  NArith.BinNat
  Relations.Relation_Definitions
  ZArith.BinInt.


Require Import Strings.String.
Require Import stdpp.gmap.
From stdpp Require Import options.

From Coq Require Import Program.Basics.
Local Open Scope program_scope.

Set Implicit Arguments.



Inductive Exp : Set :=
  | Lit (n : nat)
  | Var (x : string)
  | Add (e1 e2 : Exp).
  
  
Inductive Stm : Set :=
  | Expr (e : Exp)
  | Let (x : string) (e : Exp) (body:Stm).
  
  
  

Module listmap.

Definition abstract_map (A : Set)  := list (string*A).
Fixpoint lookup (A : Set) (k : string) (store : abstract_map A) : option A :=
  match store with
        | nil => None
        | (k',v) :: rest => if ( String.eqb k k') then Some v else lookup k rest
  end.

Fixpoint insert (A : Set) (k : string) (v : A) (store : abstract_map A) : abstract_map A :=
  (k,v) :: store.
  
Fixpoint delete (A : Set) (k : string)  (store : abstract_map A) : abstract_map A :=
  match store with
        | nil => nil
        | (k',v) :: rest => if ( String.eqb k k') then rest else (k',v) :: (delete k rest)
  end.

End listmap.
  
  
(*important! gmap should be replaced with List (K * V) with lookup, add and remove in their interface for the semantics to remain right.*)


  
Definition value := nat.
Definition eval_store := listmap.abstract_map value.
 
  
  
  
  
  
  
(* I use big step semantics because it is closer to the interpreter i already have. 
The disadvantage of big step semantics is that it doesn't give a semantics to non-terminating programs. 
Since a contract and it postcondition makes a statement about terminating programs (If a program terminates with result r, {P} program {r.Q} holds). angelic/demonic choice determines whether a contract holds for non-terminating programs by either making the weakest precondition true or false.
therefore in our case i don't think we have a need for a small-step semantics. *)


Search gmap.

(* big step semantics for expressions*)
Inductive evalExp :  Exp -> eval_store -> option value->Prop :=
  | EvalLit : forall n store, evalExp (Lit n) store (Some n)
  | EvalVar : forall x store, evalExp (Var x) store (listmap.lookup x store)
  | EvalAddLeftFail : forall store a b, evalExp a store None -> evalExp (Add a b) store None
  | EvalAddRightFail : forall store a b, evalExp b store None -> evalExp (Add a b) store None
  | EvalAdd : forall store a b, evalExp b store None -> evalExp (Add a b) store None.
  
(*big step semantics for statements*)
Inductive evalStm :  Stm -> eval_store -> (option value * eval_store)->Prop :=
  | EvalExpr : forall mv e store, evalExp e store mv -> evalStm (Expr e) store (mv,store)
  | EvalLetSucces  : forall x e body store store' result v, evalExp e store (Some v) -> evalStm body (listmap.insert x v store) (result,store')-> evalStm (Let x e body) store (result, listmap.delete x store') .
  
  
  
  
  
































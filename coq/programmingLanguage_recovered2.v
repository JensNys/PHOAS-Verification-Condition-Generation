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

  
  

Module listmap.

Definition abstract_map (A : Set)  := list (string*A).
Fixpoint lookup (A : Set) (k : string) (store : abstract_map A) : option A :=
  match store with
        | nil => None
        | (k',v) :: rest => if ( String.eqb k k') then Some v else lookup k rest
  end.

Definition insert (A : Set) (k : string) (v : A) (store : abstract_map A) : abstract_map A :=
  (k,v) :: store.
  
Fixpoint delete (A : Set) (k : string)  (store : abstract_map A) : abstract_map A :=
  match store with
        | nil => nil
        | (k',v) :: rest => if ( String.eqb k k') then rest else (k',v) :: (delete k rest)
  end.
  


End listmap.
  
  
(*important! gmap should be replaced with List (K * V) with lookup, add and remove in their interface for the semantics to remain right.*)

Module PL.



Definition value := Z.
Definition eval_store := listmap.abstract_map value.
Inductive Exp : Set :=
  | Lit (n : value)
  | Var (x : string)
  | Add (e1 e2 : Exp).
  
  
Inductive Stm : Set :=
  | Expr (e : Exp)
  | Let (x : string) (e : Exp) (body:Stm).
Inductive Prog : Set :=
  | Fun (functionName : string) (param : string) (body : Stm).
  
(* I use big step semantics because it is closer to the interpreter i already have. 
The disadvantage of big step semantics is that it doesn't give a semantics to non-terminating programs. 
Since a contract and it postcondition makes a statement about terminating programs (If a program terminates with result r, {P} program {r.Q} holds). angelic/demonic choice determines whether a contract holds for non-terminating programs by either making the weakest precondition true or false.
therefore in our case i don't think we have a need for a small-step semantics. *)



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
  
  
End PL.
  
  





(*------------------------------------------------------*)


Module Phoas.
Require Export ExtLib.Structures.Monads.

Inductive Relop : Set :=
  | Equal
  | GreaterThan
  | SmallerThan
  | GreaterThanEqual
  | SmallerThanEqual.
  

Inductive prop (A : Set) : Set :=
  | T
  | F
  | Cmp (r:Relop) (a : A) (b:A)
  | Implies (l : prop A) (r : prop A)
  | And (l : prop A) (r : prop A)
  | Or (l : prop A) (r : prop A)
  | Forall (f : A ->  prop A).
  
  
  
  
  
  Class ValueAlgebra (V: Set) :=
  {
  lit : PL.value -> V;
  add : V -> V -> V
  }.
  
  
  Instance value_valueAlgebra : ValueAlgebra Z :=
  {
  lit := id;
  add := Z.add
  
  }.
  
  Instance expression_valueAlgebra : ValueAlgebra PL.Exp :=
  {
  lit := PL.Lit;
  add := PL.Add
  
  }.
  
  Definition Reader (R A : Set) : Set := R->A.
  Definition IntReader (A : Set) : Set := Reader Z A.
  
  (*Class Monad (M : Set->Set) : Set:=
  {
  ret  : forall {A : Set}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
  }.*)
  
  Definition ret (A:Set) (a:A) : IntReader A := fun i => a.
  Definition bind (A B:Set) (m : IntReader A) (k : A->IntReader B) : IntReader B :=
  fun r => k (m r) r.
  
  
  
  

  Instance reader_valueAlgebra : ValueAlgebra (Z -> PL.Exp) :=
  {
  lit i:= ret (PL.Lit i);
  add x y := bind x (fun v1 => 
             bind y (fun v2 =>
             ret (PL.Add v1 v2)))
  }.
  
  Inductive Contract (V:Set) := 
     | ForallC (f: V -> Contract V)
     | HoareTriple (pre : prop V) (program : PL.Prog) (post : PL.value -> prop V).
End Phoas.


Section constraintGeneration.

  Definition Wstore (V A:Set) := (A -> listmap.abstract_map V -> Phoas.prop V) -> listmap.abstract_map V -> Phoas.prop V.
  Definition ret (V A:Set) (a:A) : Wstore V A := fun post store => post a store.
  Definition bind (V A B:Set) (c : Wstore V A) (k : A->Wstore V B) : Wstore V B :=
  fun post store1 => c (fun a store2 => (k a) post store2) store1.
  
  Definition lookupWstore (V : Set)  (varname : string) : Wstore V V :=
  fun post store => match (listmap.lookup varname store) with 
                        | None => Phoas.F V
                        | Some value => post value store
                    end.
  Definition insertWstore (V : Set)  (varname : string) (v:V) : Wstore V unit  :=
  fun post store => post tt (listmap.insert varname v store).
  Definition deleteWstore (V : Set)  (varname : string) : Wstore V unit  :=
  fun post store => post tt (listmap.delete varname store).
  
  
  Fixpoint exec_exp (V:Set) (VA : Phoas.ValueAlgebra V) (e : PL.Exp) : (Wstore V V):= 
  match e with
  | PL.Lit n => ret (VA.(Phoas.lit) n)
  | PL.Var x => lookupWstore x
  | PL.Add e1 e2 => bind (exec_exp VA e1)  (fun x =>
                    bind (exec_exp VA e2)  (fun y =>
                    ret (VA.(Phoas.add) x y)
  
  ))
  end.
  
  
  Fixpoint exec_stm (V:Set) (VA : Phoas.ValueAlgebra V) (stm : PL.Stm) : (Wstore V V):= 
  match stm with
  | PL.Expr e => exec_exp VA e
  | PL.Let var e body => bind (exec_exp VA e)      (fun  x =>
                         bind (insertWstore var x) (fun _ =>
                         bind (exec_stm VA body)      (fun result =>
                         bind (deleteWstore var)   (fun _ =>
                         ret result
                         
                         ))))
  end.
  
  Definition wp (V:Set) (VA : Phoas.ValueAlgebra V) (stm : PL.Stm) (post : V -> listmap.abstract_map V -> Phoas.prop V)  (initStore : listmap.abstract_map V) : Phoas.prop V :=
  (exec_stm VA stm) post initStore.
  
  Fixpoint vc (V:Set) (VA : Phoas.ValueAlgebra V) (contract : Phoas.Contract V) : Phoas.prop V :=
  match contract with
    | CForall f => (fun v => vc (f v))
    | HoareTriple pre prog arg post = 
      match prog with 
        | 
  
  

  
  Inductive Contract (V:Set) := 
     | CForall (f: V -> Contract V)
     | HoareTriple (pre : prop V) (program : PL.Prog) (post : PL.value -> prop V).




End constraintGeneration.




















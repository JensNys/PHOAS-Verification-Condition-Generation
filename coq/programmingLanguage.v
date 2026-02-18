From Coq Require Import
  Classes.Morphisms
  NArith.BinNat
  Relations.Relation_Definitions
  ZArith.BinInt.

Require Import Coq.Strings.HexString.
Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Numbers.DecimalZ.
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
  Definition singleton (A : Set) (k : string) (v : A)  : abstract_map A :=
  (k,v) :: nil.
  
Fixpoint delete (A : Set) (k : string)  (store : abstract_map A) : abstract_map A :=
  match store with
        | nil => nil
        | (k',v) :: rest => if ( String.eqb k k') then rest else (k',v) :: (delete k rest)
  end.
  


End listmap.
  
  
(*important! gmap should be replaced with List (K * V) with lookup, add and remove in their interface for the semantics to remain right.*)

Module PL.
Definition value := Z.
(*Definition eval_store := listmap.abstract_map value.*)
Inductive Exp  : Set :=
  | Lit (n : value)
  | Var (x : string)
  | Add (e1 e2 : Exp).
  
  
Inductive Stm : Set :=
  | Expr (e : Exp)
  | Let (x : string) (e : Exp) (body:Stm).
Inductive Prog : Set :=
  | Fun (functionName : string) (param : string) (body : Stm).
  
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
  
(* I use big step semantics because it is closer to the interpreter i already have. 
The disadvantage of big step semantics is that it doesn't give a semantics to non-terminating programs. 
Since a contract and it postcondition makes a statement about terminating programs (If a program terminates with result r, {P} program {r.Q} holds). angelic/demonic choice determines whether a contract holds for non-terminating programs by either making the weakest precondition true or false.
therefore in our case i don't think we have a need for a small-step semantics. *)

(* big step semantics for expressions*)
Inductive evalExp (V : Set) (VA: ValueAlgebra V) :  Exp -> listmap.abstract_map V -> option V->Prop :=
  | EvalLit : forall n store, evalExp VA (Lit n) store (Some (lit n))
  | EvalVar : forall x store, evalExp VA (Var x) store (listmap.lookup x store)
  | EvalAddLeftFail : forall store a b, evalExp VA a store None -> evalExp VA (Add a b) store None
  | EvalAddRightFail : forall store a b, evalExp VA b store None -> evalExp VA (Add a b) store None
  | EvalAdd : forall store a b, evalExp VA b store None -> evalExp VA (Add a b) store None.
  
(*big step semantics for statements*)
Inductive evalStm (V:Set) (VA:ValueAlgebra V) :  Stm -> listmap.abstract_map V -> (option V * listmap.abstract_map V)->Prop :=
  | EvalExpr : forall mv e store, evalExp VA e store mv -> evalStm VA (Expr e) store (mv,store)
  | EvalLetSucces  : forall x e body store store' result v, evalExp VA e store (Some v) -> evalStm VA  body (listmap.insert x v store) (result,store')-> evalStm VA (Let x e body) store (result, listmap.delete x store') .
  
  
End PL.
  
  





(*------------------------------------------------------*)

Inductive Relop : Set :=
  | Equal
  | GreaterThan
  | SmallerThan
  | GreaterThanEqual
  | SmallerThanEqual.



Module Foas.

Inductive prop : Set :=
  | T
  | F
  | Cmp (r:Relop) (a : PL.Exp) (b:PL.Exp)
  | Implies (l : prop) (r : prop)
  | And (l : prop) (r : prop)
  | Or (l : prop) (r : prop)
  | Forall (var:string ) (p :  prop).
  
  
  Inductive Contract := 
     | MkContract (forallVar : string) (pre : prop) (prog : PL.Prog) (arg : string) (result: string) (post : prop).
     
     
(*
Fixpoint string_to_Prop (var :string) : Prop :=
  forall var, (Z.add var 1 = Z.of_nat 3).

Inductive mini : Set :=
  | miniCmp (a : string) 
  | miniForall (var:string ) (p :  mini).
  Fixpoint mini_to_Prop (m:mini) : Prop:=
  match m with
    |miniCmp a => (Z.add a 1 =  Z.of_nat 3)
    |miniForall var p => forall var, mini_to_Prop p
  end.
Check string_to_prop "x".
  Lemma naam:string_to_prop "x".


  Fixpoint propToProp (p : prop) : Prop :=
  match prop with
    | T => True
    | F => False
    | Cmp r l r => 
    | Implies l r => 
    | And l r =>
    | Or l r =>
    | Forall (var:string ) (p :  prop).
    *)
  
  
End Foas.

Module Phoas.


Inductive prop (A : Set) : Set :=
  | T
  | F
  | Cmp (r:Relop) (a : A) (b:A)
  | Implies (l : prop A) (r : prop A)
  | And (l : prop A) (r : prop A)
  | Or (l : prop A) (r : prop A)
  | Forall (f : A ->  prop A).
  
  
  
  
  
  
  
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
  Definition ask :(IntReader Z) := fun i => i.
  
  Definition local (A B :Set) (g: B->B) (f : Reader B A): (Reader B A) := fun i => f (g i).
  
  
  

  Instance reader_valueAlgebra : PL.ValueAlgebra (Z -> PL.Exp) :=
  {
  lit i:= ret (PL.Lit i);
  add x y := bind x (fun v1 => 
             bind y (fun v2 =>
             ret (PL.Add v1 v2)))
  }.
  
  Inductive Contract (V:Set) := 
     | ForallC (f: V -> Contract V)
     | HoareTriple (pre : prop V) (program : PL.Prog) (arg:V) (post :V -> prop V).
     
     Search (Z->string).
     
     
     Check local.
     
   Fixpoint phoas_to_foas_reader (r : Phoas.prop (IntReader PL.Exp)) : IntReader Foas.prop :=
   match r with
    | T _ => ret Foas.T
    | F _=> ret Foas.F
    | Cmp op l r => bind l (fun v1  => 
                    bind r (fun v2 =>
                    ret (Foas.Cmp op v1 v2)))
    | Implies p1 p2 =>bind (phoas_to_foas_reader p1) (fun r1 =>
                      bind (phoas_to_foas_reader p2) (fun r2 =>
                      ret (Foas.Implies r1 r2)))
    
    
    | And l r =>bind (phoas_to_foas_reader l) (fun r1 =>
                      bind (phoas_to_foas_reader r) (fun r2 =>
                      ret (Foas.And r1 r2)))
    | Or l r =>bind (phoas_to_foas_reader l) (fun r1 =>
                      bind (phoas_to_foas_reader r) (fun r2 =>
                      ret (Foas.Or r1 r2)))
    | Forall f => bind ask (fun i => 
                  bind (local (fun i=>Z.add i 1) (phoas_to_foas_reader (f (ret (PL.Var ("x" ++ (of_Z i))))) ) ) (fun body =>
                  
                  
                  
                  (ret (Foas.Forall ("x" ++ (of_Z i)) body))))
    
   
   end.
   Search (nat->Z).
   Fixpoint phoas_to_foas (phoasProp : Phoas.prop (IntReader PL.Exp)) : Foas.prop :=
   (phoas_to_foas_reader phoasProp) (Z.of_nat 0).
   
   
   
   
   
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
  
  
  Fixpoint exec_exp (V:Set) (VA : PL.ValueAlgebra V) (e : PL.Exp) : (Wstore V V):= 
  match e with
  | PL.Lit n => ret (VA.(PL.lit) n)
  | PL.Var x => lookupWstore x
  | PL.Add e1 e2 => bind (exec_exp VA e1)  (fun x =>
                    bind (exec_exp VA e2)  (fun y =>
                    ret (VA.(PL.add) x y)
  
  ))
  end.
  
  
  Fixpoint exec_stm (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) : (Wstore V V):= 
  match stm with
  | PL.Expr e => exec_exp VA e
  | PL.Let var e body => bind (exec_exp VA e)      (fun  x =>
                         bind (insertWstore var x) (fun _ =>
                         bind (exec_stm VA body)      (fun result =>
                         bind (deleteWstore var)   (fun _ =>
                         ret result
                         
                         ))))
  end.
  
  Definition wp (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) (post : V -> listmap.abstract_map V -> Phoas.prop V)  (initStore : listmap.abstract_map V) : Phoas.prop V :=
  (exec_stm VA stm) post initStore.
  
  
  Definition weaken (V:Set) (post : V->Phoas.prop V) : V->listmap.abstract_map V->Phoas.prop V :=
  fun result _ => post result.
  
  Fixpoint vc (V:Set) (VA : PL.ValueAlgebra V) (contract : Phoas.Contract V) : Phoas.prop V :=
  match contract with
    | Phoas.ForallC f => Phoas.Forall (fun v => vc VA (f v))
    | Phoas.HoareTriple pre prog arg post =>
      match prog with 
        | PL.Fun functionName param body => (Phoas.Implies (pre) (wp VA body (weaken post) (listmap.singleton param arg)))
      end
  end.
  
  
  Lemma semantp (V:Set) (p : Phoas.prop V) : Prop.
  Admitted.
  
  Lemma semantImplies : forall (V:Set) (p q : Phoas.prop V), semantp (Phoas.Implies p q) -> semantp p -> semantp q. Admitted. 
  
  
  
  (*this definition throws away the v, while p can depend on v.*)
  Lemma semantForall : forall (V:Set) (p : Phoas.prop V) (f: V-> Phoas.prop V), f =(fun v=>p) -> semantp (Phoas.Forall f) -> forall v', semantp (f v'). Admitted. 
  
  Definition satisfies_post_angelic (V:Set) (post: V->listmap.abstract_map V->Phoas.prop V)(o : (option V * listmap.abstract_map V)) : Phoas.prop V :=
  match o with
    |(opt,m) => (match opt with 
                    |None => Phoas.T _
                    |Some v => post v m
                end)
  end.

  (*(*wp generates a precondition*)
  Lemma wpPrecondition : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.abstract_map V->Phoas.prop V) (stm : PL.Stm) (initStore :  listmap.abstract_map V) r, 
  
  semantp (wp VA stm post initStore) -> PL.evalStm VA stm initStore r -> semantp (satisfies_post_angelic post r). Admitted.
  *)
  
  
  (*wp generates the weakest precondition*)
  Lemma wpWeakest : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.abstract_map V->Phoas.prop V) (stm : PL.Stm) (pre : Phoas.prop V) (initStore :  listmap.abstract_map V) r,       
  
  ((semantp pre) -> PL.evalStm VA stm initStore r-> semantp (satisfies_post_angelic post r)) (*if pre is a precondition*)
  ->
  (semantp pre -> semantp (wp VA stm post initStore) ). Admitted. (*pre implies the weakest precondition *)
  
  Lemma wpPrecondition : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.abstract_map V->Phoas.prop V) (stm : PL.Stm) (pre : Phoas.prop V) (initStore :  listmap.abstract_map V) result,       
  
  (semantp pre -> semantp (wp VA stm post initStore) )
  ->
  ((semantp pre) -> PL.evalStm VA stm initStore result-> semantp (satisfies_post_angelic post result)).  Admitted.
  
  Lemma wpCorrect  : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.abstract_map V->Phoas.prop V) (stm : PL.Stm) (pre : Phoas.prop V) (initStore :  listmap.abstract_map V) result,       
  
  (semantp pre -> semantp (wp VA stm post initStore) )
  <->
  ((semantp pre) -> PL.evalStm VA stm initStore result-> semantp (satisfies_post_angelic post result)).  
  Proof.
  intros. split.
  - eapply wpPrecondition.
  - eapply wpWeakest.
  Qed.
  

   
   
   
   Lemma vcGenSound : forall (V:Set) (VA:PL.ValueAlgebra V) (pre : V->Phoas.prop V) (post : V->V->Phoas.prop V) (stm : PL.Stm) (contract : Phoas.Contract V) (v:V) funcName var result, contract = Phoas.ForallC (fun v' =>Phoas.HoareTriple (pre v') (PL.Fun funcName var stm) v' (post v')) -> 
  semantp (vc VA contract) -> semantp (pre v) ->PL.evalStm VA stm (listmap.singleton var v) result-> semantp (satisfies_post_angelic (weaken (post v)) result).
  
  Proof.
  intros.
  unfold vc in H0.
  rewrite H in  H0.
  eapply semantForall in H0.
  - eapply semantImplies  in H0.
   +  Check wpWeakest.
      Check wpPrecondition.
   eapply wpPrecondition.
    *  intros. eapply wpWeakest; eauto.
    * eapply wpPrecondition;eauto.
    * apply H2.
   
   + admit.
   - admit.
   Admitted. 
   
   
   
   
   
   
   
   
   
     
    (*
  admit.
  - 
  
  apply (semantForall (Phoas.Implies pre
            (wp VA stm (weaken post)
               (listmap.singleton var v))) ((fun v => V,
          Phoas.Implies pre
            (wp VA stm (weaken post)
               (listmap.singleton var v))))) in H0. 
               
               
               
  eapply (semantImplies pre (wp VA stm (weaken post) (listmap.singleton var v0))) in H0.
  
  
  
  simplify.
  
  eauto.  
  
  
  
  
  
  (post : PL.value -> Phoas.prop PL.value) (stm : PL.Stm) (initStore : list_map.abstract_map PL.value) ()






*)



End constraintGeneration.




























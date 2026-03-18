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
From stdpp Require Import
  gmap mapset option stringmap.

Import EqNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.

  

Module debruijnmap.

Definition debruijnmap (A : Set)  := list A.

Definition lookup (A : Set) (k : nat) (store : debruijnmap A) : option A :=
  nth_error store k.
  Search "length".
  Search (Z->nat).
  
  
  Definition contains (A : Set)  (store : debruijnmap A) (k : nat) :Prop :=
   k < length store.
  
  

Definition insert (A : Set)  (v : A) (store : debruijnmap A) : debruijnmap A :=
   v::store.
  
  
  Definition singleton (A : Set) (k : nat) (v : A)  : debruijnmap A :=
  v :: nil.
  Definition double (A : Set) (v1 : A)  (v2 : A)  : debruijnmap A :=
  v1:: v2 :: nil.
  
Fixpoint delete (A : Set)  (store : debruijnmap A) : debruijnmap A :=
  match store with
        | nil => nil
        | v :: rest =>   rest
  end.
  
  
  Search "nth_error".
  Search "nth_In".
  Definition contains_implies_lookup_some: forall (A:Set) (store : debruijnmap A) k, contains store k -> {v | lookup k store = Some v}.
  Proof.
  intros A store k H.
  unfold contains in H.
  apply nth_error_Some in H.
  fold lookup.
   destruct (nth_error store k) as [v|] eqn:Heq.
   - unfold lookup.
   exists v.
   simpl.
   rewrite Heq.
   reflexivity.
   - contradiction.
   Defined.
     
  
  
  Definition insert_implies_contains : forall (A:Set) (store : debruijnmap A) key, contains (insert key store) 0.
  Proof.
    intros A store key.
  (* 1. Reveal the underlying list operations *)
  unfold contains, insert.
  (* 2. In your module, debruijnmap is a list, so length is standard list length *)
  simpl. 
  (* 3. You are now left with: 0 < S (length store) *)
  (* In Coq's Peano arithmetic, 0 is always less than a Successor *)
  auto with arith.

  Admitted. 
  
  (*
  store' = insert value store-> contains store' key.
  Proof.
 intros A store store' key value H.
  (* 1. Replace store' with its definition using the hypothesis H *)
  subst store'.
  (* 2. Unfold 'insert' and 'contains' to see the underlying logic *)
  unfold insert, contains, length.
  (* 3. You are left with: (if key =? key then true else contains store key) *)
  (* The term (key =? key) simplifies to true. *)
  rewrite String.eqb_refl.
  (* 4. Now the goal is simply 'true', which in a Prop context means 'Is_true true' *)
  simpl. 
  exact I. (* 'I' is the constructor for 'True' *)*)
  
  
  
End debruijnmap.


Module listmap.

Definition string_map (A : Set)  := list (string*A).
Fixpoint lookup (A : Set) (k : string) (store : string_map A) : option A :=
  match store with
        | nil => None
        | (k',v) :: rest => if ( String.eqb k k') then Some v else lookup k rest
  end.
  
  Fixpoint contains (A : Set)  (store : string_map A) (k : string) :Prop :=
  match store with
        | nil => false
        | (k',v) :: rest => if ( String.eqb k k') then true else contains rest k
  end.

Definition insert (A : Set) (k : string) (v : A) (store : string_map A) : string_map A :=
  (k,v) :: store.
  Definition singleton (A : Set) (k : string) (v : A)  : string_map A :=
  (k,v) :: nil.
  Definition double (A : Set) (k1 : string) (v1 : A) (k2 : string) (v2 : A)  : string_map A :=
  (k2,v2) :: (k1,v1) :: nil.
  
Fixpoint delete (A : Set) (k : string)  (store : string_map A) : string_map A :=
  match store with
        | nil => nil
        | (k',v) :: rest => if ( String.eqb k k') then rest else (k',v) :: (delete k rest)
  end.
  
  
  Search "?=".
  Lemma contains_implies_lookup_some: forall (A:Set) (store : string_map A) k, contains store k -> {v | lookup k store = Some v}.
  Proof.
  intros.
  induction store.
  - contradiction.
  - unfold lookup.
    destruct a.
    destruct (k =? s)%string eqn:Heq.
    (*destruct (string_dec k s) as [Heq | Hneq].*)
   (*Search "forall s, (s ?= s)%string=true".*)
 
    + exists a. reflexivity. (* subst. simpl. apply Z.compare_refl s.*) 
    + apply IHstore . 
    
      unfold contains in H. rewrite Heq in H. simpl in H.  apply H.
      Qed.
    (*Lemma insert_implies_contains : forall (A:Set) (store : string_map A) store' key value, store' = insert key value store-> contains store' key.
  Proof.
    
    intros A store store' key value H.
  (* 1. Replace store' with its definition using the hypothesis H *)
  subst store'.
  (* 2. Unfold 'insert' and 'contains' to see the underlying logic *)
  unfold insert, contains.
  (* 3. You are left with: (if key =? key then true else contains store key) *)
  (* The term (key =? key) simplifies to true. *)
  rewrite String.eqb_refl.
  (* 4. Now the goal is simply 'true', which in a Prop context means 'Is_true true' *)
  simpl. 
  exact I. (* 'I' is the constructor for 'True' *)
  Qed.
  
  *)  
  
 


End listmap.
  
  
(*important! gmap should be replaced with List (K * V) with lookup, add and remove in their interface for the semantics to remain right.*)

Module PL.
Definition Value := Z.
(*Definition eval_store := listmap.string_map value.*)
Inductive Exp : Set :=
| Lit (n : Z)
| Var (x : string)
| Add (e1 e2 : Exp).
  
  
Inductive Stm : Set :=
  | Expr (e : Exp)
  | Let (var:string) (e : Exp) (body:Stm).
Inductive Prog : Set :=
  | Fun (functionName : string) (param : string) (body : Stm).
  
  Class ValueAlgebra (V: Set) :=
  {
  lit : PL.Value -> V;
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
Inductive evalExp (store : stringmap Value) :  Exp -> Value ->Prop :=
  | EvalLit : forall n , evalExp store (Lit n) n  
  | EvalVar : forall x  v,  lookup x store = Some v -> evalExp store (Var x)  v
  | EvalAdd : forall a b v1 v2, evalExp store a v1 -> evalExp store b  v2 -> evalExp store (Add a b)  (Z.add v1 v2).
  
(*big step semantics for statements*)
Inductive evalStm (store : stringmap Value) :  Stm  -> (Value * stringmap Value)->Prop :=
  | EvalExpr : forall mv e, evalExp store e  mv -> evalStm store (Expr e)  (mv,store)
  | EvalLetSucces  : forall x e body store' result v, evalExp store e (v) -> evalStm (insert x v store)  body (result,store')-> evalStm store (Let x e body)  (result, delete x store') .
  
Inductive evalProg : Prog->Value-> Value->Prop :=
  | EvalFunc: forall (functionName : string) (param : string) (body : Stm) input result o,  evalStm ({[ param := input ]}) body (result,o) -> evalProg (Fun functionName param body) input result.

Inductive wfexp (Γ : stringset) : Exp -> Type :=
| WfLit n :
  wfexp Γ (Lit n)
| WfVar x :
  x ∈ Γ ->
  wfexp Γ (Var x)
| WfAdd e1 e2 :
  wfexp Γ e1 ->
  wfexp Γ e2 ->
  wfexp Γ (Add e1 e2).



  
  (*
  Fixpoint interp  (s: debruijnmap.debruijnmap value) (e : Exp) (proof : WellScopedExp s e) : value :=
    match proof with
      |LitScoped _ n => n
      
      |VarScoped contains_proof => match (debruijnmap.contains_implies_lookup_some contains_proof) with
                                          | exist _ v H => v
                                       end
      | AddScoped  H1 H2=> Z.add (interp H1) (interp H2)
    end.

    
    
  *)
  Search stringmap.
  Search stringset.
  Check elem_of_dom.

  (*als ik een store heb en x \in (dom store) -> exists y: some y = lookup x store*)
  Definition contains_implies_lookup (V : Set) (store : stringmap V)  : forall x, x ∈ (dom store) -> {y | lookup x store = Some y}.
  Proof.
intros x H.
  apply elem_of_dom in H.
  (* H : is_Some (store !! x) *)
  unfold is_Some in H.
  (* Now case split on the actual map lookup *)
  destruct (lookup x store) as [y|] eqn:Heq.
  - exists y. reflexivity.
  - exfalso. destruct H as [y Hy]. congruence.
  
  Defined.




  Fixpoint interp_to_va (V : Set) (VA: ValueAlgebra V) (store:stringmap V) (e : Exp) (proof : wfexp (dom store) e) : V :=
    match proof with
      |WfLit _ n => lit n
      
      |WfVar contains_proof => match (contains_implies_lookup store contains_proof) with
                                          | exist _ v H => v
                                       end
      | WfAdd H1 H2=> add (interp_to_va VA store H1) (interp_to_va VA store H2)
    end.

    
  
  
                                           
    
    
      
  
  
  (*match (lookup x s) with
                  |Some v => v
                  |None => match proof with 
                                | VarScoped _ _ contains_proof => 
                                    (* Use contains_proof to derive a contradiction *)
                                    False_rect value (contains_implies_lookup_some x s contains_proof)
                            end
                  end*)
End PL.
  
  





(*------------------------------------------------------*)

Inductive Relop : Set :=
  | Equal
  | GreaterThan
  | SmallerThan
  | GreaterThanEqual
  | SmallerThanEqual.

Fixpoint semant_Relop (r:Relop) : PL.Value->PL.Value->Prop :=
    match r with
      |Equal => eq
      |SmallerThan => Z.lt
      |GreaterThan => Z.gt
      |GreaterThanEqual => Z.ge
      |SmallerThanEqual => Z.le
    
    end.

Module Foas.

 Inductive prop : Set :=
  | T
  | F
  | Cmp (r:Relop) (a b : PL.Exp)
  | Implies (l : prop) (r : prop)
  | And (l : prop) (r : prop)
  | Or (l : prop) (r : prop)
  | Forall (x : string) (p :  prop).

  Inductive wfprop (Γ : stringset) : prop -> Type :=
    | WfT : wfprop Γ T
    | WfF: wfprop Γ F
    | WfCmp c l r :
      PL.wfexp Γ l ->
      PL.wfexp Γ r ->
      wfprop Γ (Cmp c l r)
    | WfImplies l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Implies l r)
    | WfAnd l r : wfprop Γ l->wfprop Γ r->wfprop Γ (And l r)
    | WfOr l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Or l r)
    | WfForall (x : string) (body : prop) :
    wfprop (union Γ (singleton x)) body ->
    wfprop Γ (Foas.Forall x body).
    
    
    (*
    | WfForall  : forall (body : prop), (forall (x : string),
      wfprop (union Γ (singleton x)) body ->
      wfprop Γ (Foas.Forall x body)).
    *)
    
  
  
  
  Inductive Contract := 
     | MkContract (forallVar : string) (pre : prop) (prog : PL.Prog) (arg : string) (result: string) (post : prop).
     Locate "->".
     
     
    (*Fixpoint (r:Relop)*)
    Check Z.lt.
    
    
    Lemma variable_introduction_domain :forall (V:Set) (store : stringmap V) x arg, (dom store ∪ {[x]}) = (dom (<[x:=arg]> store)) .
    Proof.
    intros.
    rewrite dom_insert_L. 
    set_solver.
    Defined.

    Fixpoint semant (store : stringmap PL.Value) (foasprop : Foas.prop) (proof : Foas.wfprop (dom store) foasprop ) : Prop:=
    match proof with
    |Foas.WfT _ => True
    |Foas.WfF _ => False
    |Foas.WfImplies H1 H2 => forall _ :  (semant store H1), (semant store H2)
    |Foas.WfAnd H1 H2=> and (semant store H1) (semant store H2)
    |Foas.WfOr H1 H2=> or (semant store H1) (semant store H2)
    |@Foas.WfForall _ x body H => 
    forall arg,  @semant  (insert x arg store) body (rew [fun x => Foas.wfprop x body] variable_introduction_domain store x arg  in H)  
   |Foas.WfCmp cmp H1 H2 =>  (semant_Relop cmp) (PL.interp_to_va PL.value_valueAlgebra store H1) (PL.interp_to_va PL.value_valueAlgebra store H2)
    end.
   
    
    (*this states falsely that everything is well_scoped*)
    
     (*
     Fixpoint semant (s:debruijnmap.debruijnmap PL.Value) (p : Foas.prop) (proof : WellScopedProp s p)  : Prop :=
    match proof with
      | TrueScoped _ => True
      | FalseScoped _ => False
      | ImpliesScoped l r  =>forall _ : (semant l), (semant r)
      | AndScoped l r => and  (semant l) (semant r)
      | OrScoped l r => or (semant l) (semant r)
      |@Foas.ForallScoped _ _ _ H => forall arg, semant (H arg)
      | CmpScoped comparison l r => (semant_Relop comparison) (PL.interp l) (PL.interp r) 
    end.
     *)
    


    

     Set Printing Implicit.
    (*
    Lemma ForallSemant : forall s body H, @semant s (Foas.Forall body) (@ForallScoped _ _ _ H) -> forall arg, semant (H arg).
    Proof.
      intros.
      apply H0. 
    Qed.


    Lemma ImpliesSemant : forall  s l r Hl Hr, @semant s (Foas.Implies l r) (ImpliesScoped Hl Hr) -> @semant s l Hl -> @semant s r Hr.
    Proof.
      intros.
      exact (H H0).
    Qed.
    
    
    *)
    
      
     
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
  | Implies (l : prop A) (r : prop A)
  | And (l : prop A) (r : prop A)
  | Or (l : prop A) (r : prop A)
  | Forall (f : A ->  prop A)
  | Cmp (r:Relop) (a : A) (b:A).
  
  
  Section WithA.

    Variable (A : Set).
    Variable (WA : stringset -> A -> Type).

    Inductive wfprop (Γ : stringset) : prop A -> Type :=
    | WfT : wfprop Γ (T A)
    | WfF : wfprop Γ (F A)
    | WfImplies {l r} : wfprop Γ l -> wfprop Γ r -> wfprop Γ (Implies l r)
    | WfAnd {l r} : wfprop Γ l -> wfprop Γ r -> wfprop Γ (And l r)
    | WfOr {l r} : wfprop Γ l -> wfprop Γ r -> wfprop Γ (Or l r)
    | WfForall {f : A -> prop A} :
        (forall (a : A) Γ', subseteq Γ Γ' -> WA Γ' a -> wfprop Γ' (f a)) ->
        wfprop Γ (Forall f)
    | WfCmp {r : Relop} {a b : A} : WA Γ a -> WA Γ b -> wfprop Γ (Cmp r a b).

  End WithA.
  
  Fixpoint semant  (p : Phoas.prop (PL.Value)) : Prop :=
    match p with
    | Phoas.T _ => True
    | Phoas.F _ => False
    | Phoas.Implies l r => forall _: (semant l), (semant r)
    | Phoas.And l r => and (semant l) (semant r)
    | Phoas.Or l r => or (semant l) (semant r)
    | Phoas.Forall f =>   forall x, (semant (f x))
    | Phoas.Cmp r a b => (semant_Relop r) (a ) (b )
    end.
  
  
  (*
  Definition Reader (R A : Set) : Set := R->A.
  Definition NatReader (A : Set) : Set := Reader nat A.
  
  (*Class Monad (M : Set->Set) : Set:=
  {
  ret  : forall {A : Set}, A -> M A;
  bind : forall {A B}, M A -> (A -> M B) -> M B
  }.*)
  
  Definition ret (A:Set) (a:A) : NatReader A := fun i => a.
  Definition bind (A B:Set) (m : NatReader A) (k : A->NatReader B) : NatReader B :=
  fun r => k (m r) r.
  Definition ask :(NatReader nat) := fun i => i.
  
  Definition local (A B :Set) (g: B->B) (f : Reader B A): (Reader B A) := fun i => f (g i).
  
  *)
  
  
  
  (*
  
  *)
  
  
  Inductive Contract (V:Set) := 
     | ForallC (f: V -> Contract V)
     | HoareTriple (pre : prop V) (program : PL.Prog) (arg:V) (post :V -> prop V).
     
     
     
     
     
     (*
     |TrueScoped : forall store, WellScopedProp store T
     |FalseScoped: forall store, WellScopedProp store F
     |ImpliesScoped: forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (Implies l r)
     |AndScoped :  forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (And l r)
     |OrScoped :  forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (Or l r)
     |ForallScoped: forall store name value body, WellScopedProp (listmap.insert name value store) body -> WellScopedProp store (Forall name body)
     |CmpScoped: forall c l r store, PL.WellScopedExp store l-> PL.WellScopedExp store r-> WellScopedProp store (Cmp c l r).*)
     (*
     
     
     *)
     Check Foas.WfForall.
     

     Search dom.


    

    (*Fixpoint convert_eq (V:Set) (store : stringmap V) (x:string) (arg:V) (a : (dom store ∪ {[x]})) : (dom (<[x:=arg]> store)).
    *)
    Lemma variable_introduction_domain :forall (V:Set) (store : stringmap V) x arg, (dom store ∪ {[x]}) = (dom (<[x:=arg]> store)) .
    Proof.
    intros.
    rewrite dom_insert_L. 
    set_solver.
    Defined.
  

    Fixpoint foas_to_phoas (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V) (foasprop : Foas.prop) (proof : Foas.wfprop (dom store) foasprop ) : prop V :=
    match proof with
    |Foas.WfT _ => T V
    |Foas.WfF _ => F V
    |Foas.WfImplies H1 H2 => Implies (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.WfAnd H1 H2=> And (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.WfOr H1 H2=> Or (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |@Foas.WfForall _ x body H => 
  Forall (fun arg => @foas_to_phoas V VA (insert x arg store) body (rew [fun x => Foas.wfprop x body] variable_introduction_domain store x arg  in H)  )
   |Foas.WfCmp cmp H1 H2 => Cmp cmp (PL.interp_to_va VA store H1) (PL.interp_to_va VA store H2)
    end. 
     
     Check foas_to_phoas.



     Check Phoas.wfprop.
    
    
    
    
    
  Definition R (A : Set) : Set := stringset -> A.
  Definition ret (A:Set) (a:A) : R A := fun i => a.
  Definition bind (A B:Set) (m : R A) (k : A->R B) : R B :=
     fun r => k (m r) r.
  
  Instance R_valueAlgebra : PL.ValueAlgebra (stringset -> PL.Exp) :=
    {
    lit i:= ret (PL.Lit i);
    add x y := bind x (fun v1 => 
              bind y (fun v2 =>
              ret (PL.Add v1 v2)))
    }.


  Fixpoint phoas_to_foas (Γ : stringset) (p : Phoas.prop (R PL.Exp)) : Foas.prop :=
    match p with
    | Phoas.T _ => Foas.T
    | Phoas.F _ => Foas.F
    | Phoas.Implies l r => Foas.Implies (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.And l r => Foas.And (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.Or l r => Foas.Or (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.Forall f =>
        let x := fresh_string_of_set "" Γ in
        Foas.Forall x
          (phoas_to_foas (union Γ (singleton x))
             (f (fun _ => PL.Var x)))
    | Phoas.Cmp r a b => Foas.Cmp r (a Γ) (b Γ)
    end.

  Definition wfr (Γ : stringset) (m : R PL.Exp) : Type :=
    PL.wfexp Γ (m Γ).

  Lemma wfphoas_to_foas (Γ : stringset) (p : Phoas.prop (R PL.Exp)) (wfp : Phoas.wfprop wfr Γ p) :
    Foas.wfprop Γ (phoas_to_foas Γ p).
  Proof.
    induction wfp; cbn.
    - constructor.
    - constructor.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
    - constructor.
      apply X.
      + set_solver.
      + 
      constructor.
      set_solver.
    - constructor; auto.
  Qed.


    (*if I make a decision procedure with Ltac that decides whether a Foas formula is well formed, can I use it to*)

  Fixpoint foas_to_phoas_admitted (V:Set) (env : stringmap V) (foasprop : Foas.prop) : prop V. Admitted.



  Definition foas_contract_to_phoas_contract (V : Set) (env : stringmap V) (foas_contract : Foas.Contract) : Contract V :=
     match foas_contract with
      | Foas.MkContract forallVar pre prog  arg result post => ForallC (fun v => HoareTriple (foas_to_phoas_admitted {[ forallVar := v ]} pre) prog v (fun r => foas_to_phoas_admitted ({[ forallVar := v ]} ∪ {[ result := r ]} ) post))
     end .


  (*
  
  *)

  


  (*
  Lemma wf_foas_to_phoas (A:Set) (VA:PL.ValueAlgebra A) (R : stringset → A → Type ) (store : stringmap A) (Γ : stringset) (fprop : Foas.prop) (wfp : Foas.wfprop Γ fprop) :
     (Γ = dom store) -> Phoas.wfprop R (dom store) (foas_to_phoas VA store wfp).
  Proof.
  intros.
    induction wfp. cbn.
    - constructor.
    - constructor.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
    - constructor.
      apply X.
      + set_solver.
      + 
      constructor.
      set_solver.
    - constructor; auto.
  Qed.

  *)
    
    

 
  (*
  
*)
     
     
   
   
   (* tbcCheck phoas_to_foas (Foas.foas_to_phoas simplePropScoped). *)
   
  
   Definition simpleProp : Foas.prop  := Foas.Forall "x" (Foas.Implies (Foas.Cmp SmallerThan (PL.Lit 1%Z) (PL.Var "x"))(Foas.Cmp SmallerThan (PL.Lit 0%Z) (PL.Var "x"))).
     
     
     
  Lemma simplePropScoped (V:Set): Foas.wfprop ∅ simpleProp.
     Proof.
     unfold simpleProp.
     constructor.
     intros.
     constructor.
     + constructor.
      - constructor.
      - constructor. set_solver.
     + constructor.
      - constructor.
      - constructor. set_solver.
     Defined.
     Check phoas_to_foas.
     Check wfphoas_to_foas.


     (*if we have a wellscopedness proof of phoas_to_foas*)
    
      Check phoas_to_foas.
      Check foas_to_phoas.

      
    (*
    Compute phoas_to_foas ∅ (@foas_to_phoas (R PL.Exp) R_valueAlgebra (empty : stringmap (R PL.Exp)) simpleProp (simplePropScoped (R PL.Exp))).
     it takes too long
    
    *)
     
     
     (*
     Definition simplePropTrue : @Foas.semant nil simpleProp (simplePropScoped PL.Value).
     Proof.
      simpl. 
      (*now we see the verification condition as it should be.*)
      lia.
     Qed.



    Definition simplePropTrue : @Foas.semant (∅:stringmap PL.Value) simpleProp (simplePropScoped PL.Value).
     Proof.
      simpl. 
      (*now we see the verification condition as it should be.*)
      lia.
     Qed.


     *)
     
     
     
     (*
     
     *)
     Definition simplePropInverse : phoas_to_foas ∅ (@foas_to_phoas (R PL.Exp) R_valueAlgebra (empty : stringmap (R PL.Exp)) simpleProp (simplePropScoped (R PL.Exp))) = simpleProp.
     Proof.
     simpl.
     
     Admitted.


     
     Set Printing Implicit.

     

   
End Phoas.

Module Hoas.


Inductive prop : Set :=
  | T
  | F
  | Implies (l : prop) (r : prop)
  | And (l : prop ) (r : prop)
  | Or (l : prop ) (r : prop)
  | Forall (f : PL.Value ->  prop)
  | Cmp (r:Relop) (a : PL.Value) (b:PL.Value).

  Fixpoint phoas_to_hoas (phoasProp : Phoas.prop PL.Value ) : prop :=
    match phoasProp with
      | Phoas.T _ => T
      | Phoas.F _=> F
      | Phoas.Implies l r => Implies (phoas_to_hoas l) (phoas_to_hoas r)
      | Phoas.And l r => And (phoas_to_hoas l) (phoas_to_hoas r)
      | Phoas.Or l r => Or (phoas_to_hoas l) (phoas_to_hoas r)
      | Phoas.Forall f => Forall (phoas_to_hoas ∘ f)
      | Phoas.Cmp c l r => Cmp c l r 
      end.
  Fixpoint hoas_to_phoas (phoasProp : prop) : Phoas.prop PL.Value  :=
    match phoasProp with
      | Forall f => Phoas.Forall (hoas_to_phoas ∘ f)
      | Cmp c l r => Phoas.Cmp c l r 
      | T => Phoas.T _
      | F => Phoas.F _
      | Implies l r => Phoas.Implies (hoas_to_phoas l) (hoas_to_phoas r)
      | And l r => Phoas.And (hoas_to_phoas l) (hoas_to_phoas r)
      | Or l r => Phoas.Or (hoas_to_phoas l) (hoas_to_phoas r)
      
      end.
  
  Inductive Contract  := 
     | ForallC (f: PL.Value -> Contract)
     | HoareTriple (pre : prop) (program : PL.Prog) (arg:PL.Value) (post :PL.Value -> prop).

  Fixpoint phoas_to_hoas_contract (c : Phoas.Contract PL.Value ) : Contract :=
    match c with
      | Phoas.ForallC f => ForallC (fun v => phoas_to_hoas_contract (f v))
      | Phoas.HoareTriple pre prog arg post => HoareTriple (phoas_to_hoas pre) prog arg (fun v => phoas_to_hoas (post v))
      end.

  Fixpoint hoas_to_phoas_contract (c : Contract) : Phoas.Contract PL.Value  :=
    match c with
      | ForallC f => Phoas.ForallC (fun v => hoas_to_phoas_contract (f v))
      | HoareTriple pre prog arg post => Phoas.HoareTriple (hoas_to_phoas pre) prog arg (fun v => hoas_to_phoas (post v))
      end.


  Lemma inverse_formula (p: Phoas.prop PL.Value) : hoas_to_phoas (phoas_to_hoas p) = p.
  induction p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl. f_equal. unfold "∘".  extensionality v. apply H.
  - simpl. reflexivity.
  Qed.
  Lemma inverse_formula2 (p: prop) : phoas_to_hoas (hoas_to_phoas p) = p.
  induction p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl; f_equal;try(apply IHp1);try(apply IHp2).
  - simpl. f_equal. unfold "∘".  extensionality v. apply H.
  - simpl. reflexivity.
  Qed.



  Lemma inverse_contract (c: Phoas.Contract PL.Value): hoas_to_phoas_contract (phoas_to_hoas_contract c) = c.
  induction c.
  -  simpl. f_equal.  extensionality v. apply H.
  - simpl. f_equal. 
    + apply (inverse_formula ).
    + extensionality v. apply inverse_formula.
  Qed.
  
  
  
  Fixpoint semant  (p : prop ) : Prop :=
    match p with
    | T => True
    | F => False
    | Implies l r => forall _: (semant l), (semant r)
    | And l r => and (semant l) (semant r)
    | Or l r => or (semant l) (semant r)
    | Forall f =>   forall x, (semant (f x))
    | Cmp r a b => (semant_Relop r) (a ) (b )
    end.
  
  Definition contract_semant (contract:Hoas.Contract ) :Prop := forall  pre prog (post : PL.Value->PL.Value->prop), 
       contract= (ForallC (fun v => HoareTriple (pre v) prog v (post v) )) -> 
       forall inp result, semant (pre inp) ->
               PL.evalProg prog inp result ->
               semant (post inp result).



  Lemma preserves_semantics (p:Phoas.prop PL.Value): Hoas.semant (Hoas.phoas_to_hoas p) <-> Phoas.semant p.
  Proof.
  induction p.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl; try(rewrite IHp1; rewrite IHp2); reflexivity.
  - simpl; try(rewrite IHp1; rewrite IHp2); reflexivity.
  - simpl; try(rewrite IHp1; rewrite IHp2); reflexivity.
  - simpl. split. + intros. eapply H. eapply H0.
                  + intros. eapply H. eapply H0. 
  - simpl. reflexivity.
  Qed.  



End Hoas.








Section constraintGeneration.
Definition Wstore (V A:Set) := (A -> stringmap V -> Phoas.prop V) -> stringmap V -> Phoas.prop V.
  Definition ret (V A:Set) (a:A) : Wstore V A := fun post store => post a store.
  Definition bind (V A B:Set) (c : Wstore V A) (k : A->Wstore V B) : Wstore V B :=
  fun post store1 => c (fun a store2 => (k a) post store2) store1.
  
  Definition lookupWstore (V : Set)  (varname : string) : Wstore V V :=
  fun post store => match (lookup varname store) with 
                        | None => Phoas.F V
                        | Some value => post value store
                    end.
  Definition insertWstore (V : Set)  (varname : string) (v:V) : Wstore V unit  :=
  fun post store => post tt (insert varname v store).
  Definition deleteWstore (V : Set)  (varname : string) : Wstore V unit  :=
  fun post store => post tt (delete varname store).
  
  
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
  
  Definition wp (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) (post : V -> stringmap V -> Phoas.prop V)  (initStore : stringmap V) : Phoas.prop V :=
  (exec_stm VA stm) post initStore.
  
  
  Definition weaken (V:Set) (post : V->Phoas.prop V) : V->stringmap V->Phoas.prop V :=
  fun result _ => post result.
  
  Fixpoint vc (V:Set) (VA : PL.ValueAlgebra V) (contract : Phoas.Contract V) : Phoas.prop V :=
  match contract with
    | Phoas.ForallC f => Phoas.Forall (fun v => vc VA (f v))
    | Phoas.HoareTriple pre prog arg post =>
      match prog with 
        | PL.Fun functionName param body => (Phoas.Implies (pre) (wp VA body (weaken post) ({[ param := arg ]})))
      end
  end.
  
  Definition vc_hoas  (c : Phoas.Contract PL.Value) : Hoas.prop :=
  Hoas.phoas_to_hoas (vc (PL.value_valueAlgebra) c).
  
  Definition vc_foas (c : Foas.Contract) : Foas.prop :=
  
  Phoas.phoas_to_foas ∅ (vc (Phoas.R_valueAlgebra) (Phoas.foas_contract_to_phoas_contract ∅ c)).



  End constraintGeneration.






  Section hoasProof.


  


Lemma wpWeakest : forall  (post : PL.Value->stringmap PL.Value->Phoas.prop PL.Value) (stm : PL.Stm) (pre : Phoas.prop PL.Value) (initStore :  stringmap PL.Value) result endmap,       
  
  (Phoas.semant pre -> PL.evalStm initStore stm (result,endmap)-> Phoas.semant (post result endmap)) (*if pre is a precondition*)
  ->
  (Phoas.semant pre -> Phoas.semant (wp PL.value_valueAlgebra stm post initStore) ). Admitted.

  Check wp.
  Check Hoas.hoas_to_phoas.

  


  Lemma wpPreconditionHoas : forall  (post : PL.Value->Hoas.prop) (stm : PL.Stm) (pre : Hoas.prop)  (inp : PL.Value) (arg : string) result fname,       
  (Hoas.semant pre -> Phoas.semant (wp PL.value_valueAlgebra stm (weaken (Hoas.hoas_to_phoas ∘  post)) {[arg := inp]})) 
  ->
  (Hoas.semant pre -> PL.evalProg (PL.Fun fname arg stm ) inp result)-> Hoas.semant (post result ). Admitted. (*if pre is a precondition*)
  
  (*Lemma wpPrecondition : forall  (post : PL.Value->stringmap PL.Value->Phoas.prop PL.Value) (stm : PL.Stm) (pre : Phoas.prop PL.Value) (inp : PL.Value) (arg : string) result fname,       
  (Hoas.semant pre -> Hoas.semant  )  
  ->
  (Hoas.semant pre -> PL.evalProg (PL.Fun fname arg stm ) inp result)-> Phoas.semant (post result ∅  ). Admitted.
  
  
  *)
  
  
(*

*)


  (*
 
  
  *)

   Lemma translation_irrelevance : forall c pre prog post,
    Hoas.phoas_to_hoas_contract c =  Hoas.ForallC  (λ v : PL.Value,
                                                    Hoas.HoareTriple (pre v) prog v (post v))
  -> 
       c = Phoas.ForallC (λ v : PL.Value,
       Phoas.HoareTriple (Hoas.hoas_to_phoas (pre v)) prog v (fun result => Hoas.hoas_to_phoas (post v result))).
       intros.
    Proof.
    pose proof (f_equal Hoas.hoas_to_phoas_contract H) as H'.
    pose proof (Hoas.inverse_contract c) as H''.
    rewrite H'' in H'.
    simpl in H'.
    apply H'.
  Qed.



  Definition adequate (c : Phoas.Contract PL.Value) : Hoas.semant (vc_hoas c)->  Hoas.contract_semant (Hoas.phoas_to_hoas_contract c).
  Proof.
  
  unfold Hoas.contract_semant.
  intro.
  intro.
  intro.
  intro.
  intro.
  intro.
  (*intros.*)
  unfold vc_hoas in H.
  
  simpl in H.
  apply translation_irrelevance in H0.
  rewrite H0 in H.
  destruct prog.
  simpl in H.
  pose proof (Hoas.inverse_formula2 (pre inp)).
  specialize (H inp).
  rewrite H1 in H.
  
  Check (weaken
               (λ result : PL.Value,
                  Hoas.hoas_to_phoas
                    (post inp result))).
  Check (λ result : PL.Value,
                  Hoas.hoas_to_phoas
                    (post inp result)).
  Check wpPreconditionHoas.
  intro result.
  pose proof (@wpPreconditionHoas (post inp) body (pre inp) inp param result functionName) as Hwp.
  intros.
  apply Hwp.
  - intros. apply H in H4.
    unfold "∘".
    pose proof (Hoas.preserves_semantics (wp PL.value_valueAlgebra body
              (weaken
                (λ result : PL.Value,
                    Hoas.hoas_to_phoas (post inp result)))
              {[param := inp]})).

    
    rewrite H5 in H4.
    exact H4.        
            
    (*I would think i could finish with rewrite H5 in H4 (simplifiying H4) and then exact H4.*)
    
    (*rewrite H5 in H4. apply H4.*)
    
    - intros. exact H3.

  Qed.
  
  




    
  End hoasProof.
  


  
  (*this definition throws away the v, while p can depend on v.*)
  Lemma semantForall : forall (V:Set) (p : Phoas.prop V) (f: V-> Phoas.prop V), f =(fun v=>p) -> semantp (Phoas.Forall f) -> forall v', semantp (f v'). Admitted. 
  
  Definition satisfies_post_angelic (V:Set) (post: V->stringmap V->Phoas.prop V)(t : (V * stringmap V)) : Phoas.prop V :=
  match t with 
  | (v,s) => post v s
  end.
  
  
  
  (*when extending to dealing with lists, the argument given to prog refers to the value associated with the values in forallVar. Right now, we ignore arg because we know it must be the string mentioned in forallVar.*)
  Definition contract_semant (contract:Foas.Contract) : Prop := forall  forallVar pre stm arg resultName post result endStore fName,  contract=Foas.MkContract forallVar pre (PL.Fun fName arg stm ) forallVar resultName post -> forall inp, (Foas.semant (singleton forallVar inp) pre) -> PL.evalStm stm (listmap.singleton arg inp) (result,endStore) -> Foas.semant (listmap.double forallVar inp resultName result) post. 
  
  
  Lemma adequacy (contract:Foas.Contract) : 
  Foas.semant nil (vc_foas contract) -> adequate contract. 
   
  


  


























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
  
Fixpoint delete (A : Set) (k : nat)  (store : debruijnmap A) : debruijnmap A :=
  match store with
        | nil => nil
        | v :: rest => if ( Nat.eqb k 0) then rest else (v) :: (delete (k-1) rest)
  end.
  
  
  Search "nth_error".
  Search "nth_In".
  Lemma contains_implies_lookup_some: forall (A:Set) (store : debruijnmap A) k, contains store k -> {v | lookup k store = Some v}.
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
   Qed.
     
  
  (*
  Lemma insert_implies_contains : forall (A:Set) (store : debruijnmap A) store' key value, store' = insert key value store-> contains store' key.
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
      
  Lemma insert_implies_contains : forall (A:Set) (store : string_map A) store' key value, store' = insert key value store-> contains store' key.
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
  
  


End listmap.
  
  
(*important! gmap should be replaced with List (K * V) with lookup, add and remove in their interface for the semantics to remain right.*)

Module PL.
Definition value := Z.
(*Definition eval_store := listmap.string_map value.*)
Inductive Exp  : Set :=
  | Lit (n : value)
  | Var (x : nat)
  | Add (e1 e2 : Exp).
  
  
Inductive Stm : Set :=
  | Expr (e : Exp)
  | Let (e : Exp) (body:Stm).
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
Inductive evalExp  :  Exp -> debruijnmap.debruijnmap value -> value ->Prop :=
  | EvalLit : forall n store, evalExp (Lit n) store (  n)
  | EvalVar : forall x store v,  debruijnmap.lookup x store = Some v -> evalExp (Var x) store v
  | EvalAdd : forall store a b v1 v2, evalExp a store v1 -> evalExp b store v2 -> evalExp (Add a b) store (Z.add v1 v2).
  
(*big step semantics for statements*)
Inductive evalStm :  Stm -> debruijnmap.debruijnmap value -> (value * debruijnmap.debruijnmap value)->Prop :=
  | EvalExpr : forall mv e store, evalExp e store mv -> evalStm  (Expr e) store (mv,store)
  | EvalLetSucces  : forall e body store store' result v, evalExp  e store (v) -> evalStm   body (debruijnmap.insert v store) (result,store')-> evalStm  (Let e body) store (result,store') .
  
  
  Inductive WellScopedExp (V:Set) : debruijnmap.debruijnmap V->Exp->Type :=
  | LitScoped :  forall store n, WellScopedExp store (Lit n)
  | VarScoped : forall store x, debruijnmap.contains store x-> WellScopedExp store (Var x)
  |AddScoped : forall store e1 e2, WellScopedExp store e1->WellScopedExp store e2 -> WellScopedExp store (Add e1 e2).
  
  
  
  Check listmap.contains_implies_lookup_some.
  Fixpoint interp  (s:listmap.string_map value) (e : Exp) (proof : WellScopedExp s e) : value :=
    match proof with
      |LitScoped _ n => n
      
      |VarScoped s x contains_proof => match (listmap.contains_implies_lookup_some s x contains_proof) with
                                          | exist _ v H => v
                                       end
      | AddScoped  H1 H2=> Z.add (interp H1) (interp H2)
    end.
    Fixpoint interp_to_va (V : Set) (VA: ValueAlgebra V) (s:listmap.string_map V) (e : Exp) (proof : WellScopedExp s e) : V :=
    match proof with
      |LitScoped _ n => lit n
      
      |VarScoped s x contains_proof => match (listmap.contains_implies_lookup_some s x contains_proof) with
                                          | exist _ v H => v
                                       end
      | AddScoped H1 H2=> add (interp_to_va VA H1) (interp_to_va VA H2)
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
     Locate "->".
     
     
    (*Fixpoint (r:Relop)*)
    Check Z.lt.
    Fixpoint semant_Relop (r:Relop) : PL.value->PL.value->Prop :=
    match r with
      |Equal => eq
      |SmallerThan => Z.lt
      |GreaterThan => Z.gt
      |GreaterThanEqual => Z.ge
      |SmallerThanEqual => Z.le
    
    end.
    
    Inductive WellScopedProp (V : Set) : listmap.string_map V->Foas.prop->Type :=
     |TrueScoped : forall store, WellScopedProp store T
     |FalseScoped: forall store, WellScopedProp store F
     |ImpliesScoped: forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (Implies l r)
     |AndScoped :  forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (And l r)
     |OrScoped :  forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (Or l r)
     |ForallScoped: forall store value name body, WellScopedProp (listmap.insert name value store) body -> WellScopedProp store (Forall name body)
     |CmpScoped: forall c l r store, PL.WellScopedExp store l-> PL.WellScopedExp store r-> WellScopedProp store (Cmp c l r).
    
    
    (*this states falsely that everything is well_scoped*)
    Lemma everything_well_scoped : forall (s:listmap.string_map PL.value) e, PL.WellScopedExp s e.
    Admitted.
     
    Fixpoint semant (s:listmap.string_map PL.value) (p : prop)  : Prop :=
    match p with
      | T => True
      | F => False
      | Implies l r  =>forall _ : (semant s l), (semant s r)
      | And l r => and  (semant s l) (semant s r)
      | Or l r => or (semant s l) (semant s r)
      | Forall var p => forall (v : PL.value), semant (listmap.insert var v s) p
      | Cmp r a b => (semant_Relop r) (PL.interp (everything_well_scoped s a)) (PL.interp (everything_well_scoped s b)) 
    end.
     
     
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
     
     
     (*
     |TrueScoped : forall store, WellScopedProp store T
     |FalseScoped: forall store, WellScopedProp store F
     |ImpliesScoped: forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (Implies l r)
     |AndScoped :  forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (And l r)
     |OrScoped :  forall store l r, WellScopedProp store l->WellScopedProp store r->WellScopedProp store (Or l r)
     |ForallScoped: forall store name value body, WellScopedProp (listmap.insert name value store) body -> WellScopedProp store (Forall name body)
     |CmpScoped: forall c l r store, PL.WellScopedExp store l-> PL.WellScopedExp store r-> WellScopedProp store (Cmp c l r).*)
     Fixpoint foas_to_phoas (V:Set) (VA: PL.ValueAlgebra V) (env : listmap.string_map V) (foasprop : Foas.prop) (proof : Foas.WellScopedProp env foasprop ) : prop V :=
     match proof with
     |Foas.TrueScoped _ => T V
     |Foas.FalseScoped _ => F V
     |Foas.ImpliesScoped H1 H2 => Implies (foas_to_phoas VA H1) (foas_to_phoas VA H2)
     |Foas.AndScoped H1 H2=> And (foas_to_phoas VA H1) (foas_to_phoas VA H2)
     |Foas.OrScoped H1 H2=> Or (foas_to_phoas VA H1) (foas_to_phoas VA H2)
     |Foas.ForallScoped H => Forall (fun arg => foas_to_phoas VA H)
     |Foas.CmpScoped cmp H1 H2 => Cmp cmp (PL.interp_to_va VA H1) (PL.interp_to_va VA H2)
     end. (*there is something fishy about the Forall case. I should pass the arg into the recursive call, but i don't know if this is done implicitely by H or not. I don't know which values for name and value are picked in H*)
     
     
     
     
     
     
      
     
     
     
     
     
     Fixpoint foas_to_phoas_admitted (V:Set) (env : listmap.string_map V) (foasprop : Foas.prop) : prop V. Admitted.
     
     
     Definition foas_contract_to_phoas_contract (V : Set) (env : listmap.string_map V) (foas_contract : Foas.Contract) : Contract V :=
     match foas_contract with
      | Foas.MkContract forallVar pre prog  arg result post => ForallC (fun v => HoareTriple (foas_to_phoas_admitted (listmap.singleton forallVar v) pre) prog v (fun r => foas_to_phoas_admitted (listmap.double forallVar v result r) post) )
     end .
     
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
   
   
   
   
   (* tbcCheck phoas_to_foas (Foas.foas_to_phoas simplePropScoped). *)
   
   Definition WellScopedProp2 : list string->Foas.prop -> Prop. Admitted.
  
   Definition simpleProp : Foas.prop  := Foas.Forall "x" (Foas.Implies (Foas.Cmp SmallerThan (PL.Lit 1%Z) (PL.Var "x"))(Foas.Cmp SmallerThan (PL.Lit 0%Z) (PL.Var "x"))).
     
     
     
     Lemma simplePropScoped : WellScopedProp2 nil simpleProp.
     Proof.
     unfold simpleProp.
     eapply Foas.ForallScoped.
     eapply Foas.ImpliesScoped.
     + eapply Foas.CmpScoped .
      - eapply PL.LitScoped.
      - eapply PL.VarScoped.
        eapply listmap.insert_implies_contains. eauto.
     + eapply Foas.CmpScoped. 
       - eapply PL.LitScoped.
       - eapply PL.VarScoped.
        eapply listmap.insert_implies_contains. eauto.
     Unshelve.
     auto.
     Qed.
     
     Compute phoas_to_foas (foas_to_phoas reader_valueAlgebra simplePropScoped).
   
   
End Phoas.








Section constraintGeneration.

  Definition Wstore (V A:Set) := (A -> listmap.string_map V -> Phoas.prop V) -> listmap.string_map V -> Phoas.prop V.
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
  
  Definition wp (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) (post : V -> listmap.string_map V -> Phoas.prop V)  (initStore : listmap.string_map V) : Phoas.prop V :=
  (exec_stm VA stm) post initStore.
  
  
  Definition weaken (V:Set) (post : V->Phoas.prop V) : V->listmap.string_map V->Phoas.prop V :=
  fun result _ => post result.
  
  Fixpoint vc (V:Set) (VA : PL.ValueAlgebra V) (contract : Phoas.Contract V) : Phoas.prop V :=
  match contract with
    | Phoas.ForallC f => Phoas.Forall (fun v => vc VA (f v))
    | Phoas.HoareTriple pre prog arg post =>
      match prog with 
        | PL.Fun functionName param body => (Phoas.Implies (pre) (wp VA body (weaken post) (listmap.singleton param arg)))
      end
  end.
  
  Fixpoint vc_foas (c : Foas.Contract) : Foas.prop :=
  
  
  Phoas.phoas_to_foas (vc (Phoas.reader_valueAlgebra) (Phoas.foas_contract_to_phoas_contract nil c)).
  
  Lemma semantp (V:Set) (p : Phoas.prop V) : Prop.
  Admitted.
  
  Lemma semantImplies : forall (V:Set) (p q : Phoas.prop V), semantp (Phoas.Implies p q) -> semantp p -> semantp q. Admitted. 
  
  
  
  (*this definition throws away the v, while p can depend on v.*)
  Lemma semantForall : forall (V:Set) (p : Phoas.prop V) (f: V-> Phoas.prop V), f =(fun v=>p) -> semantp (Phoas.Forall f) -> forall v', semantp (f v'). Admitted. 
  
  Definition satisfies_post_angelic (V:Set) (post: V->listmap.string_map V->Phoas.prop V)(t : (V * listmap.string_map V)) : Phoas.prop V :=
  match t with 
  | (v,s) => post v s
  end.
  
  
  
  (*when extending to dealing with lists, the argument given to prog refers to the value associated with the values in forallVar. Right now, we ignore arg because we know it must be the string mentioned in forallVar.*)
  Definition contract_semant (contract:Foas.Contract) :Prop := forall  forallVar pre stm arg resultName post result endStore fName,  contract=Foas.MkContract forallVar pre (PL.Fun fName arg stm ) forallVar resultName post -> forall inp, (Foas.semant (listmap.singleton forallVar inp) pre) -> PL.evalStm stm (listmap.singleton arg inp) (result,endStore) -> Foas.semant (listmap.double forallVar inp resultName result) post. 
  
  
  Lemma adequacy (contract:Foas.Contract) : 
  Foas.semant nil (vc_foas contract) -> adequate contract. 
   
  
  (*
  
  
 
  

  (*(*wp generates a precondition*)
  Lemma wpPrecondition : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.string_map V->Phoas.prop V) (stm : PL.Stm) (initStore :  listmap.string_map V) r, 
  
  semantp (wp VA stm post initStore) -> PL.evalStm VA stm initStore r -> semantp (satisfies_post_angelic post r). Admitted.
  *)
  
  
  (*wp generates the weakest precondition*)
  Lemma wpWeakest : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.string_map V->Phoas.prop V) (stm : PL.Stm) (pre : Phoas.prop V) (initStore :  listmap.string_map V) r,       
  
  ((semantp pre) -> PL.evalStm VA stm initStore r-> semantp (satisfies_post_angelic post r)) (*if pre is a precondition*)
  ->
  (semantp pre -> semantp (wp VA stm post initStore) ). Admitted. (*pre implies the weakest precondition *)
  
  Lemma wpPrecondition : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.string_map V->Phoas.prop V) (stm : PL.Stm) (pre : Phoas.prop V) (initStore :  listmap.string_map V) result,       
  
  (semantp pre -> semantp (wp VA stm post initStore) )
  ->
  ((semantp pre) -> PL.evalStm VA stm initStore result-> semantp (satisfies_post_angelic post result)).  Admitted.
  
  Lemma wpCorrect  : forall (V:Set) (VA:PL.ValueAlgebra V) (post : V->listmap.string_map V->Phoas.prop V) (stm : PL.Stm) (pre : Phoas.prop V) (initStore :  listmap.string_map V) result,       
  
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
  
  
  
  
  
  (post : PL.value -> Phoas.prop PL.value) (stm : PL.Stm) (initStore : list_map.string_map PL.value) ()






*)*)



End constraintGeneration.

























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
Require Import Coq.Program.Equality.

From stdpp Require Import options.
From Coq Require Import Program.Basics.
Local Open Scope program_scope.
From stdpp Require Import
  gmap mapset option stringmap.

Import EqNotations.
Set Implicit Arguments.
Require Import Coq.Logic.FunctionalExtensionality.

  


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



Inductive wfStm (Γ : stringset)  : Stm -> Prop :=
  | WfExpr (e : Exp) :  wfexp Γ e -> wfStm Γ (Expr e)
  | WfLet (var:string) (e : Exp) (body:Stm) : wfexp Γ e -> wfStm (union Γ (singleton var)) body-> wfStm Γ (Let var e body) .


Inductive wfProg : Prog -> Prop :=
  | WfFun name param body: wfStm  (singleton param) body -> wfProg (Fun name param  body ).
  


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

  Fixpoint interp_to_va_default (V : Set) (VA: ValueAlgebra V) (store:stringmap V) (e : Exp)  : V :=
    match e with
      |Lit n => lit n
      
      |Var x => match (lookup x store) with
                                          | None => lit 0%Z
                                          | Some v => v
                                       end

      | Add l r=> add (interp_to_va_default VA store l) (interp_to_va_default VA store r)
    end.

    
  
  
                                           
    
    
      

End PL.
  
  



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

Definition WF (World : Type) (X : Set) := World-> X -> Type.
 
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
    | WfImplies l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Implies l r)
    | WfAnd l r : wfprop Γ l->wfprop Γ r->wfprop Γ (And l r)
    | WfOr l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Or l r)
    | WfCmp c l r :PL.wfexp Γ l -> PL.wfexp Γ r -> wfprop Γ (Cmp c l r)
    | WfForall (x : string) (body : prop) :
    wfprop (union Γ (singleton x)) body ->
    wfprop Γ (Foas.Forall x body).
    
  
  
  
  Inductive Contract := 
     | MkContract (forallVar : string) (pre : prop) (prog : PL.Prog) (arg : string) (result: string) (post : prop).

  
Check Foas.wfprop. 
  Definition wfContract (c : Contract) : Type :=
  match c with
  | MkContract forallVar pre prog arg result post =>
      (Foas.wfprop (singleton forallVar) pre )*
      (forallVar = arg) *
      (forallVar <> result) *
     ( Foas.wfprop (union (singleton forallVar) (singleton result)) post)
  end.



  
    
    
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
   
    

    

     Set Printing Implicit.
    
  
  
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
  
   Class Weakening (V:Set)  (World: Type) (Acc: relation World) (WA: WF World V) := {
    weaken : forall (Γ Γ' : World) (v:V), Acc Γ Γ' -> WA Γ v -> WA Γ' v
}.
  Section WithA.

    Context {World : Type} (Acc : relation World) {pre : PreOrder Acc}.

    Variable (A : Set).
    Variable (WA :WF World A).
    Variable (weaken : Weakening Acc WA).
    Inductive wfprop (w : World) : prop A -> Type :=
    | WfT : wfprop w (T A)
    | WfF : wfprop w (F A)
    | WfImplies {l r} : wfprop w l -> wfprop w r -> wfprop w (Implies l r)
    | WfAnd {l r} : wfprop w l -> wfprop w r -> wfprop w (And l r)
    | WfOr {l r} : wfprop w l -> wfprop w r -> wfprop w (Or l r)
    | WfForall {f : A -> prop A} :
        (forall (a : A) w', Acc w w' -> WA w' a -> wfprop w' (f a)) ->
        wfprop w (Forall f)
    | WfCmp {r : Relop} {a b : A} : WA w a -> WA w b -> wfprop w (Cmp r a b).

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
  
  

  
  Inductive Contract (V:Set) := 
     | ForallC (f: V -> Contract V)
     | HoareTriple (pre : prop V) (program : PL.Prog) (arg:V) (post :V -> prop V).
  
  Inductive wfContract (World : Type) (V:Set) {acc : relation World} (wfV : WF World V) (w:World) :  Contract V -> Prop :=
  | WfForallC {f : V -> Contract V} :
        (forall (v : V) w', acc w w' -> wfV w' v -> wfContract  wfV w' (f v)) ->
        wfContract  wfV w (ForallC f)
  | WfHoareTriple (pre : prop V) (program : PL.Prog) (arg:V) (post :V -> prop V):
        wfprop acc wfV w pre ->
        wfV w arg ->
        (forall (result : V) w', acc w w' -> wfV w' result ->
          wfprop acc wfV w' (post result)) -> 
          wfContract wfV w (HoareTriple pre program arg post)
          .
    
     

    
    Lemma variable_introduction_domain :forall (V:Set) (store : stringmap V) x arg, (dom store ∪ {[x]}) = (dom (<[x:=arg]> store)) .
    Proof.
    intros.
    rewrite dom_insert_L. 
    set_solver.
    Defined.



    Fixpoint foas_to_phoas (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V) (foasprop : Foas.prop)  : prop V :=
    match foasprop with
    |Foas.T => T V
    |Foas.F => F V
    |Foas.Implies H1 H2 => Implies (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.And H1 H2=> And (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |Foas.Or H1 H2=> Or (foas_to_phoas VA store H1) (foas_to_phoas VA store H2)
    |@Foas.Forall x body  => 
        Forall (fun arg => @foas_to_phoas V VA (insert x arg store) body)
    |Foas.Cmp cmp l r => Cmp cmp (PL.interp_to_va_default VA store l) (PL.interp_to_va_default VA store r)
    end. 
     
     Check foas_to_phoas.


Class WF_VA (World : Type) (V:Set) (VA: PL.ValueAlgebra V) 
(WA: WF World V)  := {
    wf_lit : forall Γ n, WA Γ (PL.lit n);
    wf_add : forall Γ v1 v2, WA Γ v1 -> WA Γ v2 -> WA Γ (PL.add v1 v2);
}.





Definition WfStore (World : Type) (V : Set)  (WA :WF World V) : WF World (stringmap V) :=
    fun (w : World) (store : stringmap V)
     =>
    forall s v, (store !! s = Some v) -> (WA w v ).
 
 







Lemma wf_foas_to_phoas (World : Type) (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V)  (foasprop : Foas.prop) (wfFoas : Foas.wfprop (dom store) foasprop ) 
      (acc: relation World) (context : World) WA  
       (wfStore : WfStore WA context store ) (X : WF_VA VA WA) (Hweaken : Weakening  acc WA)
       : 
              @wfprop World acc V WA context (@foas_to_phoas V VA store foasprop).
Proof.
intros.
dependent induction wfFoas. 
- constructor.
- constructor.
-  simpl. constructor.
 + eapply IHwfFoas1; auto .
 + eapply IHwfFoas2; auto .
-  simpl. constructor.
 + eapply IHwfFoas1; auto.
 + eapply IHwfFoas2; auto .
-  simpl. constructor.
 + eapply IHwfFoas1; auto .
 + eapply IHwfFoas2; auto .
 -  simpl. constructor.
 + induction w.
  * simpl. apply wf_lit.
  * simpl. 
  
  eapply (wfStore x). Check   PL.contains_implies_lookup.
  destruct (PL.contains_implies_lookup store e) as [v Hv]. rewrite Hv. reflexivity. 
  
  
  * simpl. apply wf_add; auto.
 + induction w0.
  * simpl. apply wf_lit.
  * simpl.  eapply (wfStore x). destruct (PL.contains_implies_lookup store e) as [v Hv]. rewrite Hv. reflexivity.
  
  * simpl. apply wf_add; auto.
 - simpl. constructor. intros. eapply  IHwfFoas;eauto.
  + apply variable_introduction_domain.
  + simpl. 
  
  generalize (variable_introduction_domain store x a). 
  unfold WfStore.
  intros H0 s v Hlookup.
  
 

  destruct (decide (s = x)) as [-> | Hne].
* (* s = x, so lookup returns a *)
  Check lookup_insert.
  rewrite lookup_insert in Hlookup.
  injection Hlookup as <-.
  apply X0.
* rewrite lookup_insert_ne in Hlookup.
** unfold WfStore in wfStore.
  specialize (wfStore s v).
  apply wfStore in Hlookup.
  apply (weaken context w');auto.



** symmetry. exact Hne.
Qed.



Lemma wf_foas_to_phoas2 (World : Type) (V:Set) (VA: PL.ValueAlgebra V) (store : stringmap V)  (foasprop : Foas.prop) (wfFoas : Foas.wfprop (dom store) foasprop ) :
      forall  (acc: relation World) (context : World) (WA : WF World V)
       (wfStore : WfStore ( WA) context store  ) (X : WF_VA VA WA ) 
       ( HaccElem: Weakening acc ( WA)), 
              @wfprop World acc V WA  context (@foas_to_phoas V VA store foasprop).
Proof.
  intros.
  apply wf_foas_to_phoas; auto.
Qed.

    
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


  Fixpoint phoas_to_foas (Γ : stringset) (p : Phoas.prop (PL.Exp)) : Foas.prop :=
    match p with
    | Phoas.T _ => Foas.T
    | Phoas.F _ => Foas.F
    | Phoas.Implies l r => Foas.Implies (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.And l r => Foas.And (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.Or l r => Foas.Or (phoas_to_foas Γ l) (phoas_to_foas Γ r)
    | Phoas.Forall f =>
        let x := fresh_string_of_set "x" Γ in
        Foas.Forall x
          (phoas_to_foas (union Γ (singleton x))
             (f (PL.Var x)))
    | Phoas.Cmp r a b => Foas.Cmp r (a ) (b)
    end.

  Definition wfr : WF stringset (R PL.Exp) : Type :=
    fun (Γ : stringset) (m : R PL.Exp)  => PL.wfexp Γ (m Γ).

  Definition wfe  : WF stringset (PL.Exp) :=
    fun (Γ : stringset) (m : PL.Exp) =>
        PL.wfexp Γ m.

  

  




  
  Lemma wf_phoas_to_foas (World : Type) (Γ : stringset) (p : Phoas.prop (PL.Exp)) 
  (wfp : @Phoas.wfprop stringset subseteq (PL.Exp) wfe Γ p) :
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
      + constructor.
      set_solver.
    - constructor; auto.
  Qed.


  Check foas_to_phoas.
  Definition foas_contract_to_phoas_contract (V : Set) (VA : PL.ValueAlgebra V) (env : stringmap V) (foas_contract : Foas.Contract) : Contract V :=
     match foas_contract with
      | Foas.MkContract forallVar pre prog  arg result post => ForallC (fun v => HoareTriple (foas_to_phoas VA {[ forallVar := v ]} pre) prog v (fun r => foas_to_phoas VA ({[ forallVar := v ]} ∪ {[ result := r ]} ) post))
     end .
Lemma lookup_union_case
  (V : Set)
  (v result_v : V)
  (env : stringmap V)
  (forallVar result : string) :
  forall s v',  result <> forallVar ->
    (env = ({[forallVar := v]}
   ∪ {[result := result_v]})) /\ env  !! s = Some v' ->
    (s = forallVar -> v' = v) /\
    (s = result -> v' = result_v) /\
    (s <> forallVar /\ s <> result -> False).
    Proof.

intros. split.
   * destruct H0 as [Henv Hlookup].
subst env. intros. rewrite H0 in *. 

subst s.
rewrite lookup_union_Some in Hlookup. 
**
  destruct Hlookup as [H1 | H2]. 
      ***
        rewrite lookup_singleton_Some in *. eauto.
        destruct H1. 
        rewrite H1. reflexivity.
      *** 
        rewrite lookup_singleton_Some in *. 
        destruct H2. contradiction.
** apply map_disjoint_singleton_l_2 .
rewrite lookup_singleton_ne; done.
* 
 Admitted. 


Theorem wf_foas_to_phoas_contract (World : Type) (V : Set) (acc : relation World)
    (VA: PL.ValueAlgebra V)
     (wfV : WF World V)
    (w : World)
    (env : stringmap V)
    (c : Foas.Contract) 
    (wfE' : WF_VA VA wfV)
    (weaken : Weakening acc wfV)
    :
    Foas.wfContract c ->
    @wfContract World V acc wfV w
      (foas_contract_to_phoas_contract VA env c).
Proof.
  intros Hwf.
  destruct c as [forallVar pre prog arg result post].
  (* unfold the FOAS well-formedness *)
  destruct Hwf as [[[Hwfpre  Harg] Hresultname] Hwfpost].
  (* the translation wraps in ForallC *)
  simpl. apply WfForallC.
  intros v w' Hacc Hwfv.
  (* now prove WfHoareTriple *)
  apply WfHoareTriple.
  - (* pre well-formed: use foas_to_phoas_wfprop *)
    eapply Phoas.wf_foas_to_phoas  ;eauto.
    + rewrite dom_singleton_L. exact Hwfpre.
    + rewrite Harg.
     
     intros s v' Hlookup.
      rewrite lookup_singleton_Some in Hlookup.
      destruct Hlookup as [_ ->].
      exact Hwfv.

  - 
    exact Hwfv.
  - (* post well-formed: similar to pre, larger domain *)
    intros result_v w'' Hacc' Hwfresult.
    eapply Phoas.wf_foas_to_phoas  ;eauto.
    + rewrite dom_union_L, !dom_singleton_L.
    exact Hwfpost.
    + 
      intros s v' Hlookup.

destruct (String.eq_dec s forallVar) as [Hs | Hs].
-- subst s.
rewrite lookup_union_Some in Hlookup. **

  admit. 
  **


 apply map_disjoint_singleton_l_2.
rewrite lookup_singleton_ne; done. 

--

Admitted.
  



  


     
  
   Definition simpleProp : Foas.prop  := Foas.Forall "x" 
                                                
                                                 (Foas.Cmp SmallerThan (PL.Lit 0%Z) (PL.Var "x")).
     

  
  
  Lemma wf_lit_expR: forall Γ n, wfr Γ (PL.lit n).
  Proof.
  intros.
  unfold wfr. constructor.
  Qed.

  

  Lemma wf_add_expR : forall Γ v1 v2, wfr Γ v1 -> wfr Γ v2 -> wfr Γ (PL.add v1 v2).
  intros.
  constructor.
  - eapply X.
  - eapply X0.
  Qed. 

  Lemma wf_lit_exp: forall Γ n, wfe Γ (PL.Lit n).
  Proof.
  intros.
  unfold wfe. constructor.
  Qed.

  

  Lemma wf_add_exp : forall Γ v1 v2, wfe Γ v1 -> wfe Γ v2 -> wfe Γ (PL.Add v1 v2).
  intros.
  constructor.
  - eapply X.
  - eapply X0.
  Qed. 
 
  
  Instance WF_VA_R: WF_VA  R_valueAlgebra  wfr  := {
    wf_lit := wf_lit_expR;
    wf_add := wf_add_expR
  }.

  Instance WF_VA_exp: WF_VA  PL.expression_valueAlgebra  wfe  := {
    wf_lit := wf_lit_exp;
    wf_add := wf_add_exp
  }.
  
  

  Instance weakening_wfe : Weakening subseteq wfe.
  Proof.
  constructor.
  intros.
  unfold wfe in *.
  induction v.
  - constructor.
  - constructor. apply H.  inversion X. apply H1.
  - constructor; inversion X;auto. 

  
  Qed.

  
     Definition simplePropInverse : phoas_to_foas ∅ (@foas_to_phoas ( PL.Exp) PL.expression_valueAlgebra (empty : stringmap (PL.Exp)) simpleProp ) = simpleProp.
     Proof.
     vm_compute. reflexivity.  (* simpl. this causes stack overflow*)
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





Module constraintGeneration.
Definition Wstore (V A:Set) := (A -> stringmap V -> Phoas.prop V) -> stringmap V -> Phoas.prop V.



  Definition ret (V A:Set) (a:A) : Wstore V A := fun post store => post a store.
  Definition bind (V A B:Set) (c : Wstore V A) (k : A->Wstore V B) : Wstore V B :=
  fun post store1 => c (fun a store2 => (k a) post store2) store1.

  Check WF.


  Section WFs.
  Variable (World : Type).
  Variable (acc : relation World).
  Variable  (pre : PreOrder acc).
  Variable ( V A: Set) (wfA :WF World A) (wfV :WF World V).
  Variable (VA : PL.ValueAlgebra V).
  Variable (weaken : Phoas.Weakening acc wfV).

Definition WfFunc {World: Type} {A B : Set} (wfA :WF World A) (wfB : WF World B) : WF World (A -> B) :=
fun w f => forall (a:A), wfA w a -> wfB w (f a).

  Definition Box {A : Set} (WA : WF World A)  : WF World A :=
    fun w a => forall w' , acc w w' -> WA w' a .

Declare Scope rel_scope.
Delimit Scope rel_scope with R.
 Open Scope rel_scope.
  Notation "A ↣ B" :=
      (WfFunc A%R B%R)
        (at level 99, B at level 200, right associativity)
        : rel_scope.

  Notation "□ A"    := (Box A%R) (at level 50, A at level 9): rel_scope.
        

Lemma refl : forall w, acc w w.
  reflexivity.
  Qed.
  Hint Resolve refl : core.

  Lemma trans : forall w w' w'', acc w w' -> acc w' w'' -> acc w w''.

  etransitivity ;eauto.
  Qed.
  Hint Resolve trans : core.



    
  Definition Wfprop  (A: Set) (wfA : WF World A): WF World (Phoas.prop A) :=
    fun w p =>   (Phoas.wfprop acc wfA) w p.




  Definition WfPost ( V A: Set) (wfA :WF World A) (wfV :WF World V): WF World (A->stringmap V → Phoas.prop V) :=
   wfA  ↣ Phoas.WfStore wfV ↣ Wfprop wfV.


Definition Wf_Wstore (V A:Set)  (wfV :WF World V) (wfA : WF World A) : WF World (Wstore V A):=
   (□ (WfPost wfA wfV)) ↣ (Phoas.WfStore wfV) ↣ (Wfprop wfV).



  Definition Wf_lift (V A B: Set) (wfV :WF World V) (wfA :WF World A) (wfB :WF World B) : (WF World (A -> Wstore V B)) :=
      wfA ↣ (Wf_Wstore wfV wfB).


  


  Lemma wfRet  (C : Set) (w:World) (c : C) (wfC : WF World C) (wf_c : wfC w c) : Wf_Wstore wfV wfC w (ret c).
  repeat unfold Wf_Wstore,WfFunc,WfPost, Wfprop, Box.
  intros.
  eapply X;eauto.
  Qed.



  Lemma S   : forall (p : WF World V) (w : World) (v : V), Box wfV w v -> wfV w v.
  Proof using pre.
  intros.
  apply X.
  reflexivity.
  Qed.

  Lemma positive_introspection  : forall (p : WF World V) (w : World) (v : V), Box wfV w v -> Box (Box wfV) w v.
  Proof using pre.
  unfold Box in *.
  
  intros.
  apply X.
  etransitivity ;eauto.
  Qed.

  
  

  Lemma wfBind  (C B: Set) (wfC : WF World C)  (wfB :WF World B) 
  (w:World) (c : Wstore V C) (k : C->Wstore V B) 
  (wf_c : Wf_Wstore wfV wfC w c) (wf_k : Box ( Wf_lift wfV wfC wfB ) w k) : Wf_Wstore wfV wfB w (bind c k).
  unfold bind.
  unfold Wf_Wstore.
  unfold WfFunc.
  
  repeat unfold Wf_Wstore,WfFunc,WfPost, Wfprop, Box, Wf_lift in *.
  intros  post H store wfStore .

   eauto. 


 
   Qed.
 

  
  Definition lookupWstore (V : Set)  (varname : string) : Wstore V V :=
  fun post store => match (lookup varname store) with 
                        | None => Phoas.F V
                        | Some value => post value store
                    end.

   Lemma wflookupWstore  (w:World) (s : string)  : Wf_Wstore wfV wfV w (lookupWstore s).
  unfold lookupWstore.
  unfold Wf_Wstore.
  unfold WfFunc.
  repeat unfold Wf_Wstore,WfFunc,WfPost, Wfprop', Box, Wf_lift in *.
  intros post H store wfStore .
  
  destruct (store !! s) eqn:Heq .
  - 
 
   eapply H;eauto. 
  - constructor.
  Qed.


  Definition insertWstore (V : Set)  (varname : string) (v:V) : Wstore V unit  :=
  fun post store => post tt (insert varname v store).

  Definition wf_unit : WF World unit :=
  fun w u => True.

  Lemma wfinsertWstore  (w:World) (varname : string) (v:V) (wf_v : wfV w v) : Wf_Wstore wfV wf_unit w (insertWstore varname v).
  unfold insertWstore.
  unfold Wf_Wstore.
  unfold WfFunc.
  repeat unfold Wf_Wstore,WfFunc,WfPost, Wfprop', Box, Wf_lift in *.
  intros post H store wfStore .
  eapply H;eauto.
  - unfold wf_unit. reflexivity.
  - admit.
   (*specialize (H () I store wfStore).*)


  Admitted.
 

  Definition deleteWstore (V : Set)  (varname : string) : Wstore V unit  :=
  fun post store => post tt (delete varname store).
  


  Fixpoint WfExpfp (wfString : WF World string) (w : World) (e : PL.Exp) : Type :=
  match e with
  | PL.Lit n     => True
  | PL.Var x     => wfString w x
  | PL.Add e1 e2 => prod (WfExpfp wfString w e1) (WfExpfp wfString w e2)
  end.

  Definition WfExp (wfString : WF World string) : WF World PL.Exp :=
    fun w e => WfExpfp wfString w e.

    
  
  Fixpoint exec_exp (V:Set) (VA : PL.ValueAlgebra V) (e : PL.Exp) : (Wstore V V):= 
  match e with
  | PL.Lit n => ret (VA.(PL.lit) n)
  | PL.Var x => lookupWstore x
  | PL.Add e1 e2 => bind (exec_exp VA e1)  (fun x =>
                    bind (exec_exp VA e2)  (fun y =>
                    ret (VA.(PL.add) x y)
  
  ))
  end.


  Definition wf_string_store  {V:Set} (store: stringmap V) (wfV : WF World V) : WF World string :=
  fun w s => forall v,  store !! s = Some v -> wfV w v.

  Fixpoint WfStmfp (wfString : WF World string) (w : World) (p : PL.Stm) : Type :=
  match p with
  | PL.Expr e => WfExpfp wfString w e
  | PL.Let var e body => forall w', acc w w' -> wfString w' var -> WfStmfp wfString w' body 
  end.



 Lemma WfStore_weaken  :
    forall w w' (s : stringmap V), 
    acc w w' -> Phoas.WfStore wfV w s -> Phoas.WfStore wfV w' s.
Proof using weaken.
  intros w w' s Hw Hs.
  unfold Phoas.WfStore.
  intros k v Hlookup.
  eapply Phoas.weaken.
  - exact Hw.
  - eapply Hs. exact Hlookup.
Qed.

  Lemma wf_exec_exp  
  (like_wfV : Phoas.WF_VA VA wfV) (e : PL.Exp)  
    (w:World)   (varname : string)
      : Wf_Wstore wfV wfV w (exec_exp VA e).
  Proof.
  
   repeat unfold Wf_Wstore,WfFunc,WfPost, Wfprop, Box, Wf_lift in *.

      induction e;
   intros post H store wfStore .

    (*Lit*)
   - simpl. eapply H;eauto.  
    apply Phoas.wf_lit.
    (*Var*)
   - simpl. eapply wflookupWstore;eauto.
   (*Add*)
   - simpl.  eapply wfBind ; eauto.
   
   repeat unfold WfFunc,WfPost, Wfprop, Box, Wf_lift .
     intros. 
     eapply wfBind;eauto.
     ++ simpl in *. 
     
     
     
     repeat unfold Wf_Wstore,WfFunc,WfPost, Wfprop, Box, Wf_lift in *.
     intros.
     simpl.
     eauto.

     (*
     
     apply IHe2; eauto.
     unfold WfExp in wfe.
     simpl in wfe. apply wfe.
     *)
     
     admit.
     
     
     ++ repeat unfold Wf_Wstore,WfFunc,WfPost, Wfprop, Box, Wf_lift in *.
        intros.
        eapply wfRet;eauto.
        apply Phoas.wf_add;eauto.
        eapply weaken;eauto.
  Admitted.


  

  
  
  Fixpoint exec_stm (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) : (Wstore V V):= 
  match stm with
  | PL.Expr e => exec_exp VA e
  | PL.Let var e body => bind (exec_exp VA e)      (fun  x =>
                         bind (insertWstore var x) (fun _ =>
                         bind (exec_stm VA body)   (fun result =>
                         bind (deleteWstore var)   (fun _ =>
                         ret result
                         
                         ))))
  end.




  
  Definition wp (V:Set) (VA : PL.ValueAlgebra V) (stm : PL.Stm) (post : V -> stringmap V -> Phoas.prop V)  (initStore : stringmap V) : Phoas.prop V :=
  (exec_stm VA stm) post initStore.
  
  
  Definition weaken' (V:Set) (post : V->Phoas.prop V) : V->stringmap V->Phoas.prop V :=
  fun result _ => post result.
  
  Fixpoint vc (V:Set) (VA : PL.ValueAlgebra V) (contract : Phoas.Contract V) : Phoas.prop V :=
  match contract with
    | Phoas.ForallC f => Phoas.Forall (fun v => vc VA (f v))
    | Phoas.HoareTriple pre prog arg post =>
      match prog with 
        | PL.Fun functionName param body => (Phoas.Implies (pre) (wp VA body (weaken' post) ({[ param := arg ]})))
      end
  end.

  Lemma wf_vc
    (c : Phoas.Contract V) (w : World): 
    @Phoas.wfContract World V acc wfV  w c ->
    Phoas.wfprop acc wfV w (vc VA c).
    
    Admitted.


  Definition vc_hoas  (c : Phoas.Contract PL.Value) : Hoas.prop :=
  Hoas.phoas_to_hoas (vc (PL.value_valueAlgebra) c).
  
  Definition vc_foas (c : Foas.Contract) : Foas.prop :=
  
  Phoas.phoas_to_foas ∅ (vc (PL.expression_valueAlgebra) (Phoas.foas_contract_to_phoas_contract PL.expression_valueAlgebra  ∅ c)).


Lemma wf_exec_exp' 
  (like_wfV : Phoas.WF_VA VA wfV) (e : PL.Exp)  
    (w:World)   (varname : string)
      : Wf_Wstore wfV wfV w (exec_exp VA e). Admitted.





End WFs.
  End constraintGeneration.

Section well_formed_generation.
Check Phoas.wfprop.
Check Phoas.R.

Search subseteq.
Print Instances PreOrder.



Theorem wf_vc_foas : forall (c : Foas.Contract), Foas.wfContract c -> Foas.wfprop empty (constraintGeneration.vc_foas c).
  intros.
  destruct c.
  destruct X as [[[Hwfpre Hwfprog] Harg] Hwfpost].
  unfold constraintGeneration.vc_foas.
  eapply Phoas.wf_phoas_to_foas. (*phoas to foas*)
  - apply stringset.
  - eapply constraintGeneration.wf_vc . (*vc*)
      * apply set_subseteq_preorder. 
      * apply Phoas.wfe.
      * apply Phoas.weakening_wfe.
    * eapply Phoas.wf_foas_to_phoas_contract. (*foas to phoas contract*)
        + apply Phoas.WF_VA_exp.
        + apply Phoas.weakening_wfe.
        + constructor; eauto.
Qed.


Lemma weakening : forall (V:Set) (Γ:stringset) Γ' (p:Phoas.prop V) (wfV : stringset->V->Type) acc,  Phoas.wfprop acc wfV Γ p ->  Γ ⊆ Γ' -> Phoas.wfprop acc wfV Γ' p.
Proof.

Admitted.




Lemma vc_well_formed: forall (V:Set) (VA : PL.ValueAlgebra V) (World:Type) (Γ:World) wfV c acc , Phoas.wfprop acc  wfV Γ (constraintGeneration.vc VA c).
Proof.
intros.
induction c.
- simpl. constructor. intros. pose proof (X a).
admit.
-   admit.
Admitted.


End well_formed_generation.




  Section hoasProof.


  


Lemma wpWeakest : forall  (post : PL.Value->stringmap PL.Value->Phoas.prop PL.Value) (stm : PL.Stm) (pre : Phoas.prop PL.Value) (initStore :  stringmap PL.Value) result endmap,       
  
  (Phoas.semant pre -> PL.evalStm initStore stm (result,endmap)-> Phoas.semant (post result endmap)) (*if pre is a precondition*)
  ->
  (Phoas.semant pre -> Phoas.semant (constraintGeneration.wp PL.value_valueAlgebra stm post initStore) ). Admitted.



  


  Lemma wpPreconditionHoas : forall  (post : PL.Value->Hoas.prop) (stm : PL.Stm)  (inp : PL.Value) (arg : string) result fname,       
  (Phoas.semant (constraintGeneration.wp PL.value_valueAlgebra stm (constraintGeneration.weaken' (Hoas.hoas_to_phoas ∘  post)) {[arg := inp]})) 
  ->
  (PL.evalProg (PL.Fun fname arg stm ) inp result)-> Hoas.semant (post result ). Admitted. (*if pre is a precondition*)
  










  

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



  Definition adequate (c : Phoas.Contract PL.Value) : Hoas.semant (constraintGeneration.vc_hoas c)->  Hoas.contract_semant (Hoas.phoas_to_hoas_contract c).
  Proof.
  
  unfold Hoas.contract_semant.
  intros.
  (*intros.*)
  unfold constraintGeneration.vc_hoas in H.
  
  simpl in H.
  apply translation_irrelevance in H0.
  rewrite H0 in H.
  destruct prog.
  simpl in H.
  pose proof (Hoas.inverse_formula2 (pre inp)).
  specialize (H inp).
  rewrite H3 in H.
  
  
  Check (λ result : PL.Value,
                  Hoas.hoas_to_phoas
                    (post inp result)).
  Check wpPreconditionHoas.

  pose proof (@wpPreconditionHoas (post inp) body inp param result functionName) as Hwp.
  intros.
  apply Hwp.
  - intros. apply H in H1.
    unfold "∘".
    pose proof (Hoas.preserves_semantics (constraintGeneration.wp PL.value_valueAlgebra body
              (constraintGeneration.weaken'
                (λ result : PL.Value,
                    Hoas.hoas_to_phoas (post inp result)))
              {[param := inp]})).

    
    rewrite H4 in H1.
    exact H1.        
    - intros. exact H2.

  Qed.
  
  




    
  End hoasProof.
  




From Coq Require Import
  ZArith.ZArith.
From stdpp Require Import
  gmap mapset option stringmap.

Set Implicit Arguments.

Definition value := Z.

Inductive Exp : Set :=
| Lit (n : Z)
| Var (x : string)
| Add (e1 e2 : Exp).

Inductive wfexp (Γ : stringset) : Exp -> Prop :=
| WfLit n :
  wfexp Γ (Lit n)
| WfVar x :
  x ∈ Γ ->
  wfexp Γ (Var x)
| WfAdd e1 e2 :
  wfexp Γ e1 ->
  wfexp Γ e2 ->
  wfexp Γ (Add e1 e2).

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
  | Cmp (r:Relop) (a b : Exp)
  | Implies (l : prop) (r : prop)
  | And (l : prop) (r : prop)
  | Or (l : prop) (r : prop)
  | Forall (x : string) (p :  prop).

  Inductive wfprop (Γ : stringset) : prop -> Prop :=
  | WfT : wfprop Γ T
  | WfF: wfprop Γ F
  | WfCmp c l r :
    wfexp Γ l ->
    wfexp Γ r ->
    wfprop Γ (Cmp c l r)
  | WfImplies l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Implies l r)
  | WfAnd l r : wfprop Γ l->wfprop Γ r->wfprop Γ (And l r)
  | WfOr l r : wfprop Γ l->wfprop Γ r->wfprop Γ (Or l r)
  | WfForall (x : string) (body : prop) :
    wfprop (union Γ (singleton x)) body ->
    wfprop Γ (Foas.Forall x body).

End Foas.

Module Phoas.

  Inductive prop (A : Set) : Set :=
  | T
  | F
  | Implies (l : prop A) (r : prop A)
  | And (l : prop A) (r : prop A)
  | Or (l : prop A) (r : prop A)
  | Forall (f : A -> prop A)
  | Cmp (r:Relop) (a : A) (b:A).

  Section WithA.

    Variable (A : Set).
    Variable (WA : stringset -> A -> Prop).

    Inductive wfprop (Γ : stringset) : prop A -> Prop :=
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

End Phoas.

Module Conversion.

  Definition R (A : Set) : Set := stringset -> A.

  Fixpoint p2f (Γ : stringset) (p : Phoas.prop (R Exp)) : Foas.prop :=
    match p with
    | Phoas.T _ => Foas.T
    | Phoas.F _ => Foas.F
    | Phoas.Implies l r => Foas.Implies (p2f Γ l) (p2f Γ r)
    | Phoas.And l r => Foas.And (p2f Γ l) (p2f Γ r)
    | Phoas.Or l r => Foas.Or (p2f Γ l) (p2f Γ r)
    | Phoas.Forall f =>
        let x := fresh_string_of_set "" Γ in
        Foas.Forall x
          (p2f (union Γ (singleton x))
             (f (fun _ => Var x)))
    | Phoas.Cmp r a b => Foas.Cmp r (a Γ) (b Γ)
    end.

  Definition wfr (Γ : stringset) (m : R Exp) : Prop :=
    wfexp Γ (m Γ).

  Lemma wfp2f (Γ : stringset) (p : Phoas.prop (R Exp)) (wfp : Phoas.wfprop wfr Γ p) :
    Foas.wfprop Γ (p2f Γ p).
  Proof.
    induction wfp; cbn.
    - constructor.
    - constructor.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
    - constructor.
      apply H0.
      set_solver.
      constructor.
      set_solver.
    - constructor; auto.
  Qed.

End Conversion.

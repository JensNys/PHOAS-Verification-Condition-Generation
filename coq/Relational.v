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

Module Order.
(*relate 2 computations that are higher order*)
  
  Definition MonotoneNatFunc' (f : nat -> nat) : Prop :=
    forall (x y : nat), x <= y -> f x <= f y.
  (* in result 2 functions f v and f w. These functions are "respectful"*)
  Definition MonotoneNatFunc2' (f : nat -> nat -> nat) : Prop :=
    forall (v w : nat), v <= w -> forall x y, x <= y -> f v x <= f w y.
Print relation.
  Definition Monotone {A B} (RA : relation A) (RB : relation B) (f : A -> B) : Prop :=
    forall (x y : A), RA x y -> RB (f x) (f y).

  Definition Monotone2 {C A B} (RC : relation C) (RA : relation A) (RB : relation B) (f : C -> A -> B) : Prop :=
    forall (v w : C), RC v w -> forall (x y : A), RA x y -> RB (f v x) (f w y).

  (*forall g h, (forall x y, x<=y -> g x <= h y) -> f g <= f h.
    forall g h, (respectful f g) -> f g <= f h.*)


  Definition MonotoneNatFix' (f : (nat -> nat) -> nat) : Prop.
  Proof.
    refine (Monotone _ le f).
    intros g h.
    refine (forall x y, x <= y -> g x <= h y).
  Defined.

  
  
  Open Scope signature_scope.
  Locate "le ==> le".
  Print respectful.

  Definition MonotoneNatFun (f : nat -> nat) : Prop :=
    (le ==> le) f f.
  

  Definition MonotoneNatFunc2 (f : nat -> nat -> nat) : Prop :=
    (le ==> le ==> le) f f.

  Definition MonotoneNatFix (f : (nat -> nat) -> nat) : Prop :=
    ((le ==> le) ==> le) f f.

End Order.

Module LR.
  (* different relation for every type in the language*)
  (*similar: indexed family of  things  in proof assistants, first family of types (here Codes) then function that interprets code at some type.
    we work with STLC with base type Nat but don't define it here and use rocq types*)
  
  
  Inductive Code : Set :=
  | cnat
  | cfunc (c1 c2 : Code).

  Fixpoint semNat (c : Code) : Set :=
    match c with
    | cnat => nat
    | cfunc c1 c2 => semNat c1 -> semNat c2
    end.
  Print respectful.

  Fixpoint related (c : Code) : relation (semNat c) :=
    match c return relation (semNat c) with
    | cnat        => le
    | cfunc c1 c2 => respectful (related c1) (related c2)
    end%signature.

  Definition Monotone (c : Code) (f : semNat c) : Prop :=
    related c f f.

  Eval cbv in (Monotone (cfunc cnat cnat)).
  Eval cbv in (Monotone (cfunc cnat (cfunc cnat cnat))).
  Eval cbv in (Monotone (cfunc (cfunc cnat cnat) cnat)).
  
  
  (*slogan of logical relations: related functions take related inputs to related outputs*)
  

  Fixpoint semBinNat (c : Code) : Set :=
    match c with
    | cnat        => N(*binary naturals*)
    | cfunc c1 c2 => semBinNat c1 -> semBinNat c2
    end.

  Fixpoint semBinInt (c : Code) : Set :=
    match c with
    | cnat        => Z
    | cfunc c1 c2 => semBinInt c1 -> semBinInt c2
    end.

  Definition natintrelation (c : Code) : Type :=
    semBinNat c -> semBinInt c -> Prop.

  Definition rnat : natintrelation cnat :=
    fun n z => Z.of_N n = z. (*typecasts n to z and checks if it is equal to the given z. could also be done with <=*)

  Definition rfunc (ca cb : Code) (RA : natintrelation ca) (RB : natintrelation cb) :
    natintrelation (cfunc ca cb) :=
    fun f1 f2 => forall a1 a2 (ra : RA a1 a2), RB (f1 a1) (f2 a2).

  Fixpoint natintrelated (c : Code) : natintrelation c :=
    match c with
    | cnat        => rnat
    | cfunc c1 c2 => rfunc (natintrelated c1) (natintrelated c2)
    end.

(*Problem:
  - Closed for extensions, what if we want to add booleans, finite maps, state, pairs. We always need to add them everywhere
  - inconvenient for programming:
      inferring
        cfunc (cfunc ncnat cnat) cnat
      from
        (nat->nat)->nat
      is hard for rocq.
      
      higher order unification, but is undecidable in general. Rocq can do it with hints, but programmer can't give the hints.
  
  to extend we make other machinery where we make natintrelation part of a typeclass. To extend we just need to add an instance
  
  *)
End LR.

Module OpenLR.

  Class Related (A B : Type) : Type :=
    rel : A -> B -> Prop.

  Instance RNat : Related N Z :=
    fun n z => Z.of_N n = z.

  Instance RFunc {A1 A2 B1 B2: Set} (R1 : Related A1 B1) (R2 : Related A2 B2) :
    Related (A1 -> A2) (B1 -> B2) :=
    fun f g => forall a1 a2, R1 a1 a2 -> R2 (f a1) (g a2).

End OpenLR.

Module Exps.

  Import OpenLR.

  Inductive Exp : Set :=
  | lit (n : nat)
  | var (x : string)
  | plus (e1 e2 : Exp).

   (*Fixpoint interpInt (e:Exp):Z :=
    match e with
    | lit n => Z.of_nat n
    | plus e1 e2 Z.add (interpInt e1) (interpInt Z)
    end.*)


  (*interpreter to A, for example Z or binary naturals*) (*class is like a record*)
  Class ExpAlg (A : Set) : Set :=
    { alit : nat -> A;
      aplus : A -> A -> A;
    }.
  Definition abstract_map (A : Set)  := gmap string A.
  Print lookup.
    
    (*all interpreters can be written with the ExpAlg. initial algerba semantics*)

  Definition bind {A B} (o : option A) (f : A -> option B) :=
  match o with
  | Some x => f x
  | None   => None
  end.

  Notation "m >>= f" := (bind m f) (at level 50, left associativity).





  Fixpoint foldExp (e : Exp) {A : Set} (m : abstract_map A) {a : ExpAlg A}  : option A :=
    match e with
    | lit n      => Some (alit n)
    | var x      => m !! x
    | plus e1 e2 => 
              foldExp e1 m >>= (fun x1 =>
              foldExp e2 m >>= (fun x2 =>
              Some (aplus x1 x2)))
    end.

  Instance NatExpAlg : ExpAlg N :=
    {| alit := N.of_nat;
       aplus := N.add;
    |}.

  Instance IntExpAlg : ExpAlg Z :=
    {| alit := Z.of_nat;
       aplus := Z.add;
    |}.

  Arguments alit : clear implicits.
  Arguments aplus : clear implicits.

  Infix "==>" := RFunc.
  
  (*Goal forall (e:Exp), Z.of_N (@foldExp e N NatExpAlg) = (@foldExp e Z IntExpAlg).
  Proof. Abort.*)
  
  (*try to make 2 algebras related such that interpreting with both gives a related result*)
  Definition liftRelationOption (A B : Set) (R: Related A B) : Related (option A) (option B) :=
  fun maybeA maybeB => match (maybeA) with
                                 |Some vA   => match (maybeB) with
                                                  |Some vB => R vA vB
                                                  |None    => False
                                               end
                                 |None      => match (maybeB) with
                                                  |Some vB => False
                                                  |None    => True
                                               end
                               end.

  Instance RExpAlg (A B : Set) (R : Related A B) : Related (ExpAlg A) (ExpAlg B) :=
    fun algA algB =>
      (eq ==> R) (alit A algA) (alit B algB) /\ (*forall n, R @alit A algA x) #lit B algB x))*)
      (R ==> R ==> R) (aplus A algA) (aplus B algB). (*forall a1 a2 b1 b2, R a1 b1 -> R a2 b2 -> R  (aplus A algA a1 a2) (aplus B algB b1 b2) *)
  Instance RalgMap (A B: Set) (R : Related A B) : Related (abstract_map A) (abstract_map B) :=
    fun mapA mapB => forall s, (liftRelationOption R) (mapA !! s) (mapB !! s).
  
  (*  Instance RFunc {A1 A2 B1 B2: Set} (R1 : Related A1 B1) (R2 : Related A2 B2) :
    Related (A1 -> A2) (B1 -> B2) :=
    fun f g => forall a1 a2, R1 a1 a2 -> R2 (f a1) (g a2).*)
  Definition Rbind (A1 B1 A2 B2: Set) (Rarg : Related A1 A2) (Rresult : Related B1 B2) : Related (A1 -> option B1) (A2 -> option B2):=
    RFunc Rarg (liftRelationOption Rresult).
    

    
    
    
  
  
  
  
  Print RFunc.
  
  Print Related.
  Lemma rMonad: forall (A1 B1 A2 B2: Set) (Ra : Related A1 A2) (Rb : Related B1 B2) (a1 : option A1) (a2 :option  A2) (lam1: (A1->option B1) ) (lam2:(A2->option B2)), liftRelationOption Ra a1 a2 -> Rbind Ra Rb lam1 lam2 -> liftRelationOption Rb (bind a1 lam1) (bind a2 lam2).
  Proof.
  intros.
  destruct a1;destruct a2; unfold bind;try(unfold liftRelationOption in H; contradiction). 
  -
  
  
  unfold Rbind in H0.
  unfold "==>" in H0.
  
  specialize (H0 a a0).
  apply H0 in H.
  apply H.
  - unfold liftRelationOption. reflexivity.
  
  Qed.
  
  

  
  Lemma rfoldExp (e : Exp) : (*this is a free theorem*) 
  (*because of parametricity, it coundn't look at A and B types, so it had to apply lit and plus in the same order*)
  (*it is true, but we can't proof it in coq because of metatheory*)
    forall (A B : Set) (R : A -> B -> Prop) (mA : abstract_map A) (mB : abstract_map B),
    RalgMap R mA mB-> ( (RExpAlg R ==> liftRelationOption R)) (@foldExp e A mA) (@foldExp e B mB). (* given related algebras, folding gives related results*)
  Proof.
    intros A B R mA mB HrelatedMaps algA algB [rlit rplus].
    induction e; cbn.
    - apply rlit. reflexivity.
    - apply HrelatedMaps. 
(* Lemma rMonad: forall (A1 B1 A2 B2: Set) (Ra : Related A1 A2) (Rb : Related B1 B2) (a1 : option A1) (a2 :option  A2) (lam1: (A1->option B1) ) (lam2:(A2->option B2)), liftRelationOption Ra a1 a2 -> Rbind Ra Rb lam1 lam2 -> liftRelationOption Rb (bind a1 lam1) (bind a2 lam2).*)
    - eapply rMonad; try(apply IHe1).
      intros.
      
      eapply rMonad;try(apply IHe2).
      unfold Rbind.
      unfold "==>".
      intros.
      
      apply rplus; auto.
      
      Qed.

  (* Even more generic. *)

  Instance RForall (F G : Set -> Set)
    (R : forall (A B : Set) (R : Related A B),
       Related (F A) (G B)) : Related (forall A, F A) (forall B, G B) :=
    fun f g => forall (A B : Set) (RAB : Related A B), R A B RAB (f A) (g B).

  (* Lemma rfoldExp' (e : Exp) : (*Steven would not do this*)
    RForall _ _ (fun A B R => RExpAlg R ==> R) (@foldExp e) (@foldExp e).
  Proof.
    intros ? ? ?. apply rfoldExp.
  Qed.*)


(*homework: 
 - Extend Exp with variables (use gmap for stdpp). because no modules
 - Introduce Reader Monad to foldExp
 - RelReader RE RAB() (Reader E1 A1) (Reader E2 B).
 
 Work forward until rfoldExp
  - start porting code from rocq to 
  
  
  fold would be vcgen.
 RFiniteMap
 
 
 you can then write gmap string nat

fig. 30. w are kripke indexes that we can ignore for now.

correctness of first vcgen to second vcgen.

second case is parameters. After instantiating all varian





End Exps.

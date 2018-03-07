Section Ej1.

Variables Leal Ordenes Inteligente Comprendio : Prop.

Hypothesis H1 : Leal -> Ordenes.
Hypothesis H2 : Inteligente -> Comprendio.
Hypothesis H3 : ~Ordenes \/ ~Comprendio.

Theorem ej1 : ~Leal \/ ~Inteligente.
Proof.
  unfold not in H3.
  unfold not.
  elim H3.
    intros.
    left.
    intros.
    apply H.
    apply H1.
    assumption.

    intros.
    right.
    intros.
    apply H.
    apply H2.
    assumption.
Qed.

End Ej1.

Section Ej2.

Require Import Classical.

Variable C : Set.
Variable P : C -> C -> Prop.

Lemma lema2 : (exists x : C, exists y : C, P x y) \/ ~(exists x : C, P x x).
Proof.
  unfold not.
  elim (classic (exists x : C, P x x)).
    intros.
    left.
    elim H.
    intros.
    exists x.
    exists x.
    assumption.

    unfold not.
    intros.
    right.
    assumption.
Qed.

End Ej2.

Section Ej3.

Variable U : Set.
Variable a : U.
Variables P Q R T : U -> Prop.

Lemma Ej3_1 : (forall x : U, P x -> Q x) -> P a -> Q a.
Proof.
  exact (fun f x => f a x).
Qed.

Lemma Ej3_2 : (forall x : U, P x -> Q x) -> (forall x : U, Q x -> R x) -> forall x : U, P x -> R x.
Proof.
  intros.
  exact ((H0 x) (H x H1)).
Qed.

Lemma L3_3: (forall x:U, Q x) \/ (forall y:U, T y) -> forall z:U, Q z \/ T z.
Proof.
  intros A; elim A; intros B; [left | right]; apply B.
Qed.

End Ej3.

Section Ej4.

Parameter ABnat : forall n : nat, Set.

(* Ej4 a *)
Parameter null : ABnat 0.
Check null.

(* Ej4 b *)
Parameter add : forall n m : nat, ABnat n -> nat -> ABnat m -> ABnat (n + m + 1).
Check add.

(* Ej4 c *)
Definition nodos3altura3 : ABnat 3
  := add 0 2 null 7 (add 0 1 null 8 (add 0 0 null 9 null)).
Check nodos3altura3.

(* Ej4 d *)
Parameter ABGen : forall (X : Set) (n : nat), Set.

Parameter nullGen : forall X : Set, ABGen X 0.
Check nullGen.

Parameter addGen : forall (X : Set) (n m : nat), ABGen X n -> X -> ABGen X m -> ABGen X (n + m + 1).
Check addGen.

End Ej4.

Section Ej5.

Variable Bool: Set.
Variable TRUE : Bool.
Variable FALSE : Bool.
Variable Not : Bool -> Bool.
Variable Imp : Bool -> Bool -> Bool.
Variable Xor : Bool -> Bool -> Bool.
Axiom Disc : ~ (FALSE = TRUE).
Axiom BoolVal : forall b : Bool, b = TRUE \/ b = FALSE.
Axiom NotTrue : Not TRUE = FALSE.
Axiom NotFalse : Not FALSE = TRUE.
Axiom ImpFalse : forall b : Bool, Imp FALSE b = TRUE.
Axiom ImpTrue : forall b : Bool, Imp TRUE b = b.
Axiom XorTrue : forall b : Bool, Xor TRUE b = Not b.
Axiom XorFalse : forall b : Bool, Xor FALSE b = b.

Lemma L51 : forall b: Bool, Xor b b = FALSE.
Proof.
  intros.
  elim (BoolVal b).
    intros.
    rewrite H.
    rewrite XorTrue.
    rewrite NotTrue.
    reflexivity.

    intros.
    rewrite H.
    rewrite XorFalse.
    reflexivity.
Qed.

Lemma L52: forall b1 b2: Bool, Imp b1 b2 = FALSE -> b1 = TRUE /\ b2 = FALSE.
Proof.
  intros.
  elim (BoolVal b1).
  intros.
    rewrite H0 in H.
    rewrite ImpTrue in H.
    split.
      assumption.
      
      assumption.

    intros.
    rewrite H0 in H.
    rewrite ImpFalse in H.
    assert False.
    absurd (FALSE = TRUE).
    apply Disc.
    symmetry.
    assumption. 
    contradiction.
Qed.

End Ej5.
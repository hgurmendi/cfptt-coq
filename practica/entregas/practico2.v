Section Ejercicio3.

Variable U   : Set.
Variable A B : U -> Prop.
Variable P Q : Prop.
Variable R S : U -> U -> Prop.

Definition H1 := forall x:U, (R x x).
Definition H2 := forall x y z:U, (R x y) /\ (R x z) -> (R y z).

Definition Reflexiva := forall x:U, (R x x).
Definition Transitiva := forall x y z:U, (R x y) /\ (R y z) -> (R x z).
Definition Simetrica := forall x y:U, (R x y) -> (R y x).

Theorem e231: H1 /\ H2 -> Reflexiva /\ Transitiva /\ Simetrica.
Proof.
  unfold H1, H2, Reflexiva, Transitiva, Simetrica in *.
  intros.
  elim H.
  intros.
  split.
    apply H0.

    split.
      intros.
      elim H4.
      intros.
      apply (H3 y x z).
      split.
        apply (H3 x y x).
        split.
          assumption.

          apply H0.

          assumption.

    intros.
    apply (H3 x y x).
    split.
      assumption.

      apply H0.
Qed.

Definition Irreflexiva := forall x:U, ~(R x x).
Definition Asimetrica := forall x y:U, (R x y) -> ~(R y x).


Lemma e232 : Asimetrica -> Irreflexiva.
Proof.
  unfold Irreflexiva, Asimetrica in *.
  unfold not.
  intros.
  apply (H x x).
    assumption.

    assumption.
Qed.

End Ejercicio3.

Section Ejercicio7.

Variable U   : Set.
Variable A B : U -> Prop.

Theorem e71: (forall x:U, ((A x) /\ (B x)))
                       -> (forall x:U, (A x)) /\ (forall x:U, (B x)).
Proof.
  intros; split; intros; apply H.
Qed.

Theorem e72: (exists x:U, (A x \/ B x))->(exists x:U, A x )\/(exists x:U, B x).
Proof.
  intros; elim H; intros; elim H0; intros; [left | right]; exists x; assumption.
Qed.

Theorem e73: (forall x:U, A x) \/ (forall x:U, B x) -> forall x:U, A x \/ B x.
Proof.
  intros; elim H; intros; [left | right]; apply H0.
Qed.

End Ejercicio7.

Section Ejercicio9.

Require Import Classical.
Variables U : Set.
Variables A : U -> Prop.

Lemma not_ex_not_forall: (~exists x :U, ~A x) -> (forall x:U, A x).
Proof.
  intros.
  elim (classic (A x)).
    intros.
    assumption.

    intros.
    elim H.
    exists x.
    assumption.
Qed.

Lemma not_forall_ex_not: (~forall x :U, A x) -> (exists x:U,  ~A x).
Proof.
  intros.
  elim (classic (exists x : U, ~A x)).
    intros.
    assumption.

    intros.
    unfold not.
    elim H.
    apply not_ex_not_forall.
    assumption.
Qed.

End Ejercicio9.

Section Ejercicio10.

Variable nat : Set.
Variable  O  : nat.
Variable  S  : nat -> nat.

Axiom disc   : forall n:nat, ~O=(S n).
Axiom inj    : forall n m:nat, (S n)=(S m) -> n=m.
Axiom allNat : forall n: nat, n = O \/ exists m: nat, S m = n.

Variable sum prod : nat->nat->nat.

Axiom sum0   : forall n :nat, (sum n O)=n.
Axiom sumS   : forall n m :nat, (sum n (S m))=(S (sum n m)).
Axiom prod0  : forall n :nat, (prod n O)=O.
Axiom prodS  : forall n m :nat, (prod n (S m))=(sum n (prod n m)).

Lemma L10_1: (sum (S O) (S O)) = (S (S O)).
Proof.
  rewrite sumS.
  rewrite sum0.
  reflexivity.
Qed.

Lemma L10_2: forall n :nat, ~(O=n /\ (exists m :nat, n = (S m))).
Proof.
  unfold not.
  intros.
  elim H.
  intros.
  elim H3.
  intros.
  apply (disc x).
  transitivity n.
    assumption.
    
    assumption.
Qed.

Lemma prod_neutro: forall n :nat, (prod n (S O)) = n.
Proof.
  intros.
  rewrite prodS.
  rewrite prod0.
  apply sum0.
Qed.

Lemma diff: forall n:nat, ~(S (S n))=(S O).
Proof.
  intros.
  unfold not.
  intros.
  assert (S n = O).
    apply inj.
    assumption.
    
    apply (disc n).
    symmetry.
    assumption.
Qed.

Lemma L10_3: forall n: nat, exists m: nat, prod n (S m) = sum n n. 
Proof.
  intros.
  exists (S O).
  rewrite prodS.
  assert (prod n (S O) = n).
    rewrite prodS.
    rewrite prod0.
    rewrite sum0.
    reflexivity.

    rewrite H.
    reflexivity.
Qed.

Lemma L10_4: forall m n : nat, n <> O -> sum m n <> O.
Proof.
  unfold not.
  intros.
  elim (allNat n).
    assumption.

    intros.
    elim H3.
    intros.
    rewrite <- H4 in H0.
    rewrite sumS in H0.
    apply (disc (sum m x)).
    symmetry.
    assumption.
Qed.

Lemma L10_5: forall m n : nat, sum m n = O -> m = O /\ n = O.
Proof.
  intros.
  elim (allNat n).
    intros.
    rewrite H0 in H.
    rewrite sum0 in H.
    split.
      assumption.

      assumption.

    intros.
    elim H0.
    intros.
    rewrite <- H3 in H.
    rewrite sumS in H.
    elim (disc (sum m x)).
    symmetry.
    assumption.
Qed.

End Ejercicio10.


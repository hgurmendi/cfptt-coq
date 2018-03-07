(*
NOMBRE COMPLETO: Hernán Gurmendi
NRO. DE DOCUMENTO: 36765446
*)

Section Problema1.

Require Export List.
Require Export Arith.
Print beq_nat.

Set Implicit Arguments.

Fixpoint eliminar (z : nat) (l : list nat) : list nat :=
  match l with
  | nil       => nil
  | cons x xs => if beq_nat x z then xs else cons x (eliminar z xs)
  end.

Fixpoint pertenece (z : nat) (l : list nat) : bool :=
  match l with
  | nil       => false
  | cons x xs => if beq_nat x z then true else pertenece z xs
  end.

Fixpoint concatenar (A : Set) (l1 l2 : list A) : list A :=
  match l1 with
  | nil       => l2
  | cons x xs => cons x (concatenar xs l2)
  end.

Lemma L1_1 : forall (A : Set) (l : list A) (x : A), l <> x::l.
Proof.
  unfold not.
  induction l; intros.
  - discriminate.
  - apply IHl with (x := a).
    injection H.
    intros.
    assumption.
Qed.

Lemma L1_2 : forall (l1 l2 : list nat) (x : nat),
  pertenece x (concatenar l1 l2) = true -> 
  pertenece x l1 = true \/ pertenece x l2 = true.
Proof.
  induction l1; intros.
  - simpl in H.
    right.
    assumption.
  - simpl in H.
    case_eq (a =? x); intros.
    + left.
      simpl.
      rewrite H0.
      reflexivity.
    + rewrite H0 in H.
      simpl.
      rewrite H0.
      apply IHl1.
      assumption.
Qed.

Lemma L1_3 : forall (l : list nat) (x : nat), 
  pertenece x l = true -> eliminar x l <> l.
Proof.
  unfold not.
  induction l; intros.
  - inversion H.
  - simpl in H0.
    case_eq (a =? x); intros.
    + rewrite H1 in H0.
      apply IHl with (x := a).
      * rewrite <- H0 in H.
        assert (a = x). apply beq_nat_true. assumption.
        rewrite <- H2 in H.
        assumption.
      * rewrite H0.
        simpl.
        rewrite <- beq_nat_refl.
        assumption.
    + rewrite H1 in H0.
      injection H0.
      intro.
      simpl in H.
      rewrite H1 in H.
      apply IHl with (x := x); assumption.
Qed.

End Problema1.


Section Problema2.

Inductive distintas (A:Set) : list A -> list A -> Prop :=
  | distintasBase :
    distintas nil nil
  | distintasInd  : forall (x y : A) (l1 l2 : list A),
    x <> y -> distintas l1 l2 -> distintas (cons x l1) (cons y l2).

Hint Constructors distintas.

Lemma L2 : forall (l1 : list bool), { l2 : list bool | distintas l1 l2 }.
Proof.
  intros.
  induction l1.
  - exists nil.
    auto.
  - elim IHl1.
    intros ll H.
    case_eq a; intros.
    + exists (false :: ll).
      constructor.
      * unfold not.
        intros.
        discriminate.
      * assumption.
    + exists (true :: ll).
      constructor.
      * unfold not.
        intros.
        discriminate.
      * assumption.
Qed.

End Problema2.

Require Extraction.
Extraction Language Haskell.
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extraction "Parcial2_Problema2.hs" L2.


Section Problema3.

Definition Var := nat.
Definition Valor := nat.

Definition Memoria := Var -> Valor.

Definition lookup (m : Memoria) (v : Var) : Valor :=
  m v.

Definition update (m : Memoria) (v : Var) (w : Valor) : Memoria :=
  fun (v' : Var) => if v =? v' then w else lookup m v'.

Inductive Instr : Set :=
  | IAss : Var -> Valor -> Instr
  | ISeq : Instr -> Instr -> Instr
  | IIf  : Var -> Valor -> Instr -> Instr -> Instr.

Inductive Execute : Memoria -> Instr -> Memoria -> Prop :=
  | xAss : forall (m : Memoria) (v : Var) (w : Valor),
    Execute m (IAss v w) (update m v w)
  | xSeq : forall (m1 m2 m3 : Memoria) (i1 i2 : Instr),
    Execute m1 i1 m2 -> Execute m2 i2 m3 -> Execute m1 (ISeq i1 i2) m3
  | xIfT : forall (m1 m2 : Memoria) (v : Var) (w : Valor) (i1 i2 : Instr),
    lookup m1 v = w -> Execute m1 i1 m2 -> Execute m1 (IIf v w i1 i2) m2
  | xIfF : forall (m1 m2 : Memoria) (v : Var) (w : Valor) (i1 i2 : Instr),
    lookup m1 v <> w -> Execute m1 i2 m2 -> Execute m1 (IIf v w i1 i2) m2.

Lemma L3_1 : forall (m1 m2 : Memoria) (var : Var) (val : Valor),
  Execute m1 (IAss var val) m2 -> lookup m2 var = val.
Proof.
  intros.
  inversion H.
  unfold lookup, update.
  rewrite <- (beq_nat_refl var).
  reflexivity.
Qed.

Lemma L3_2 : forall (m1 m2 : Memoria) (v : Var) (val : Valor) (i1 i2 : Instr),
  lookup m1 v <> val -> Execute m1 (IIf v val i1 i2) m2 -> Execute m1 i2 m2.
Proof.
  intros.
  inversion H0.
  - contradiction.
  - assumption.
Qed.

Require Import Omega.

Lemma L3_3: forall (m1 m2 m3 : Memoria) (v1 v2 : Var) (val : Valor) (i1 i2 : Instr),
  v1 <> v2 -> Execute m1 (ISeq (IAss v1 val) (IAss v2 (S val))) m2 -> Execute m2 i2 m3 ->
  Execute m2 (IIf v2 (lookup m2 v1) i1 i2) m3.
Proof.
  intros.
  unfold not in H.
  apply xIfF.
  - unfold lookup.
    inversion H0.
    inversion H5.
    inversion H7.
    unfold update.
    rewrite <- (beq_nat_refl v2).
    assert (v2 =? v1 = false). apply beq_nat_false_iff. auto.
    rewrite H16.
    rewrite <- H9.
    unfold lookup, update.
    rewrite <- (beq_nat_refl v1).
    omega.
  - assumption.
Qed.
 
End Problema3.

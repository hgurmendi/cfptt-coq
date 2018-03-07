Set Asymmetric Patterns.

Require Extraction.

(* 6.3 *)
Section Ejercicio3.

Definition Value := bool.

Inductive BoolExpr : Set :=
  | bbool : bool -> BoolExpr
  | band : BoolExpr -> BoolExpr -> BoolExpr
  | bnot : BoolExpr -> BoolExpr.

Inductive BEval : BoolExpr -> Value -> Prop :=
  | ebool : forall b : bool, BEval (bbool b) (b:Value)
  | eandl : forall e1 e2 : BoolExpr, BEval e1 false -> BEval (band e1 e2) false
  | eandr : forall e1 e2 : BoolExpr, BEval e2 false -> BEval (band e1 e2) false
  | eandrl : forall e1 e2 : BoolExpr,
    BEval e1 true -> BEval e2 true -> BEval (band e1 e2) true
  | enott : forall e : BoolExpr, BEval e true -> BEval (bnot e) false
  | enotf : forall e : BoolExpr, BEval e false -> BEval (bnot e) true.

Fixpoint beval1 (e : BoolExpr) : Value :=
  match e with
  | bbool b    => b
  | band e1 e2 =>
    match beval1 e1, beval1 e2 with
    | true, true => true
    | _, _       => false
    end
  | bnot e1    => if beval1 e1 then false else true
  end.

Fixpoint beval2 (e : BoolExpr) : Value :=
  match e with
  | bbool b    => b
  | band e1 e2 =>
    match beval2 e1 with
    | false => false
    | _     => beval2 e2
    end
  | bnot e1    => if beval2 e1 then false else true
  end.

(* 6.3.1 *)
Lemma beval1C : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
  intros.
  exists (beval1 e).
  induction e; simpl.
  - apply ebool.
  - destruct (beval1 e1).
    + destruct (beval1 e2).
      * apply eandrl; assumption.
      * apply eandr.
        assumption.
    + apply eandl.
      assumption.
  - destruct (beval1 e); [apply enott | apply enotf]; assumption.
Qed.

Lemma beval2C : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
  intros.
  exists (beval2 e).
  induction e; simpl.
  - apply ebool.
  - destruct (beval2 e1).
    + destruct (beval2 e2).
      * apply eandrl; assumption.
      * apply eandr.
        assumption.
    + apply eandl.
      assumption.
  - destruct (beval2 e); [apply enott | apply enotf]; assumption.
Qed.

(* 6.3.2 *)
Hint Constructors BEval.

Lemma beval1C' : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
  intros.
  exists (beval1 e).
  induction e; simpl.
  - auto.
  - destruct (beval1 e1).
    + destruct (beval1 e2); auto.
    + auto.
  - destruct (beval1 e); auto.
Qed.

Lemma beval2C' : forall e : BoolExpr, {b : Value | BEval e b}.
Proof.
  intros.
  exists (beval2 e).
  induction e; simpl.
  - auto.
  - destruct (beval2 e1).
    + destruct (beval2 e2); auto.
    + auto.
  - destruct (beval2 e); auto.
Qed.

End Ejercicio3.

(* 6.3.3 *)
Extraction Language Haskell.
Extraction "beval1.hs" beval1C'.
Extraction "beval2.hs" beval2C'.

(* 6.3.4 *)
Extract Inductive bool => "Prelude.Bool" [ "Prelude.True" "Prelude.False" ].
Extraction "beval1_bool.hs" beval1C'.
Extraction "beval2_bool.hs" beval2C'.

(* 6.4 *)
Section Ejercicio4.

Variable A : Set.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.

Fixpoint append (l1 l2 : list) {struct l1} : list :=
  match l1 with
  | nil      => l2
  | cons a l => cons a (append l l2)
  end.

Inductive perm :  list -> list -> Prop :=
  | perm_refl : forall l, perm l l
  | perm_cons : forall a l0 l1, perm l0 l1 -> perm (cons a l0) (cons a l1)
  | perm_app : forall a l, perm (cons a l) (append l (cons a nil))
  | perm_trans : forall l1 l2 l3, perm l1 l2 -> perm l2 l3 -> perm l1 l3.

Hint Constructors perm.

(* 6.4.1 *)
Fixpoint reverse (l1 : list) : list :=
  match l1 with
  | nil      => nil
  | cons a l => append (reverse l) (cons a nil)
  end.

(* 6.4.2 *)
Lemma Ej6_4 : forall (l1 : list), {l2 : list | perm l1 l2}.
Proof.
  intros.
  exists (reverse l1).
  induction l1; simpl.
  - auto.
  - assert (perm (cons a l1) (cons a (reverse l1))).
    apply perm_cons.
    assumption.

    assert (perm (cons a (reverse l1)) (append (reverse l1) (cons a nil))).
    apply perm_app.

    apply perm_trans with (l2 := cons a (reverse l1)); auto.
Qed.

(* 6.4.2 versión alternativa *)
Lemma Ej6_4' : forall (l1 : list), {l2 : list | perm l1 l2}.
Proof.
  intros.
  exists (reverse l1).
  induction l1; simpl.
  - auto.
  - apply perm_trans with (l2 := cons a (reverse l1)); auto.
Qed.

End Ejercicio4.

(* 6.5 *)
Require Import FunInd.
Require Import Omega.

Section Ejercicio5.

(* 6.5.1 *)
Inductive Le : nat -> nat -> Prop :=
  | LeBase : forall (n1 : nat), Le 0 n1
  | LeInd : forall (n1 n2 : nat), Le n1 n2 -> Le (S n1) (S n2).

Inductive Gt : nat -> nat -> Prop  :=
  | GtBase : forall (n1 : nat), Gt (S n1) 0
  | GtInd : forall (n1 n2 : nat), Gt n1 n2 -> Gt (S n1) (S n2).

Fixpoint leBool (n1 n2 : nat) : bool :=
  match n1 with
  | 0     => true
  | (S n) =>
    match n2 with
    | 0     => false
    | (S m) => leBool n m
    end
  end.

Hint Constructors Le.
Hint Constructors Gt.

(* 6.5.2 *)
Functional Scheme leBool_ind := Induction for leBool Sort Set.

Lemma Le_Gt_dec : forall (n m : nat), {Le n m} + {Gt n m}.
Proof.
  intros.
  functional induction (leBool n m) using leBool_ind; simpl; auto.
  elim IHb; intros; auto.
Qed.

(* 6.5.3 *)
Lemma le_gt_dec : forall (n m : nat), {le n m} + {gt n m}.
Proof.
  intros.
  functional induction (leBool n m) using leBool_ind; simpl; auto.
  - left.
    omega.
  - right.
    omega.
  - elim IHb; intros.
    + left.
      omega.
    + right.
      omega.
Qed.

End Ejercicio5.

(* 6.6 *)
Require Import DecBool.
Require Import Compare_dec.
Require Import Plus.
Require Import Mult.

Section Ejercicio6.

Definition spec_res_nat_div_mod (a b : nat) (qr : nat * nat) :=
  match qr with
  | (q, r) => (a = b * q + r) /\ r < b
  end.

Definition nat_div_mod : forall a b : nat, not (b = 0) ->
  {qr : nat * nat | spec_res_nat_div_mod a b qr}.
Proof.
  intros.
  induction a.
  - exists (0, 0).
    unfold spec_res_nat_div_mod.
    omega.
  - elim IHa.
    intros.
    destruct x as (q, r).
    elim (lt_dec r (b - 1)); intros.
    + exists (q, S r).
      simpl in *.
      elim p.
      intros.
      omega.
    + exists (S q, 0).
      simpl in *.
      elim p.
      intros.
      split.
      * assert (S r = b).
        omega.
        rewrite <- H2.
        rewrite mult_succ_r.
        rewrite H2 at 1.
        omega.
      * omega.
Qed.

End Ejercicio6.

(* 6.7 *)
Section Ejercicio7.

Inductive tree (A : Set) : Set :=
  | leaf : tree A
  | node : A -> tree A -> tree A -> tree A.

Inductive tree_sub (A : Set) (t : tree A) : tree A -> Prop :=
  | tree_sub1 : forall (t' : tree A) (x : A), tree_sub A t (node A x t t')
  | tree_sub2 : forall (t' : tree A) (x : A), tree_sub A t (node A x t' t).

Theorem well_founded_tree_sub : forall A:Set, well_founded (tree_sub A).
Proof.
  unfold well_founded.
  intros.
  induction a.
  - apply Acc_intro.
    intros.
    inversion H.
  - apply Acc_intro.
    intros.
    inversion H; assumption.
Qed.

End Ejercicio7.

(* 6.8 *)
Section Ejercicio8.

(* 6.8.1 *)
Fixpoint size (be : BoolExpr) : nat :=
  match be with
  | bbool _  => 0
  | band l r => S (size l + size r)
  | bnot b   => S (size b)
  end.

Definition elt (e1 e2 : BoolExpr) := size e1 < size e2.

(* 6.8.2 *)
Require Import Wf_nat.
Require Import Inverse_Image.

Theorem well_founded_elt : well_founded elt.
Proof.
  apply (wf_inverse_image BoolExpr nat lt size).
  apply lt_wf.
Qed.

End Ejercicio8.


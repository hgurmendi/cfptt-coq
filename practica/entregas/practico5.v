Set Asymmetric Patterns.

Section Ejercicio5.

(* 5.5.1 *)
Definition Var : Set := nat.

Inductive BoolExpr : Set :=
  | VAR : Var -> BoolExpr
  | BOOL : bool -> BoolExpr
  | AND : BoolExpr -> BoolExpr -> BoolExpr
  | NOT : BoolExpr -> BoolExpr.

(* 5.5.2 *)

Definition Value : Set := bool.

Definition Memory : Set := Var -> Value.

Definition lookup (m : Memory) (v : Var) : Value := m v.

Inductive BEeval : BoolExpr -> Memory -> Value -> Prop :=
  | evar : forall (v : Var) (m : Memory), BEeval (VAR v) m (lookup m v)
  | eboolt : forall (m : Memory), BEeval (BOOL true) m true
  | eboolf : forall (m : Memory), BEeval (BOOL false) m false
  | eandl : forall (e1 e2 : BoolExpr) (m : Memory), BEeval e1 m false -> BEeval (AND e1 e2) m false
  | eandr : forall (e1 e2 : BoolExpr) (m : Memory), BEeval e2 m false -> BEeval (AND e1 e2) m false
  | eandrl : forall (e1 e2 : BoolExpr) (m : Memory), BEeval e1 m true -> BEeval e2 m true -> BEeval (AND e1 e2) m true
  | enott : forall (e : BoolExpr) (m : Memory), BEeval e m true -> BEeval (NOT e) m false
  | enotf : forall (e : BoolExpr) (m : Memory), BEeval e m false -> BEeval (NOT e) m true.


(* 5.5.3 *)
Lemma Ej5_5_3_a : forall (m : Memory), ~ (BEeval (BOOL true) m false).
Proof.
  unfold not.
  intros.
  inversion H.
Qed.

Lemma Ej5_5_3_b : forall (e1 e2 : BoolExpr) (m : Memory) (w : Value), BEeval e1 m true -> BEeval e2 m w -> BEeval (AND e1 e2) m w.
Proof.
  intros.
  destruct w.
  + apply eandrl; assumption.
  + apply eandr.
    assumption.
Qed.

Lemma Ej5_5_3_c : forall (m : Memory) (e : BoolExpr) (w1 w2 : Value), BEeval e m w1 -> BEeval e m w2 -> w1 = w2.
Proof.
  induction e; intros; auto.
  - inversion H.
    inversion H0.
    reflexivity.
  - inversion H; rewrite <- H2 in H0; inversion H0; reflexivity.
  - inversion H; inversion H0; auto.
  - inversion H; inversion H0; auto.
Qed.

(* El enunciado es incorrecto, demuestro lo contrario de lo que pide *)
Lemma Ej5_5_3_d : forall (e1 e2 : BoolExpr) (m : Memory), BEeval e1 m false -> BEeval (NOT (AND e1 e2)) m true.
Proof.
  unfold not.
  intros.
  apply enotf.
  apply eandl.
  assumption.
Qed.

(* 5.5.4 *)
Fixpoint beval (m : Memory) (e : BoolExpr) : Value :=
  match e with
  | VAR v   => lookup m v
  | BOOL b  => b
  | AND l r => if beval m l then beval m r else false
  | NOT be  => if beval m be then false else true
  end.

(* 5.5.5 *)
Lemma Ej5_5_5 : forall (e : BoolExpr) (m : Memory), BEeval e m (beval m e).
Proof.
  intros.
  induction e; simpl.
  - apply evar.
  - case_eq b; intros; [apply eboolt | apply eboolf].
  - case_eq (beval m e1); intros.
    + case_eq (beval m e2); intros.
      * apply eandrl. rewrite H in IHe1.
          assumption.
          
          rewrite H0 in IHe2.
          assumption.
      * apply eandr.
        rewrite H0 in IHe2.
        assumption.
    + apply eandl.
      rewrite H in IHe1.
      assumption.
  - case_eq (beval m e); intros.
    + apply enott.
      rewrite H in IHe.
      assumption.
    + apply enotf.
      rewrite H in IHe.
      assumption.
Qed.

End Ejercicio5.

Section Ejercicio6.

(* 5.6.1 *)
Inductive Instr : Set :=
  | ISkip : Instr
  | IVar : Var -> BoolExpr -> Instr
  | IIf : BoolExpr -> Instr -> Instr -> Instr
  | IWhile : BoolExpr -> Instr -> Instr
  | IRepeat : nat -> Instr -> Instr
  | IBlock : LInstr -> Instr
  with LInstr : Set :=
    | LIEmpty : LInstr
    | LISeq : Instr -> LInstr -> LInstr.

(* 5.6.2 *)
Notation "i ; li" := (LISeq i li) (at level 100, right associativity).
Notation "i ;" := (LISeq i LIEmpty) (at level 100, right associativity).

Definition PP_no_notation (v1 v2 : Var) : Instr :=
  IBlock
    (LISeq (IVar v1 (BOOL true))
    (LISeq (IVar v2 (NOT (VAR v1)))
    LIEmpty)).

Definition PP (v1 v2 : Var) : Instr :=
  IBlock (
    (IVar v1 (BOOL true));
    (IVar v2 (NOT (VAR v1)));
  ).

Compute (PP = PP_no_notation).

Definition swap_no_notation (v1 v2 aux : Var) : Instr :=
  IBlock
    (LISeq (IVar aux (VAR v1))
    (LISeq (IVar v1 (VAR v2))
    (LISeq (IVar v2  (VAR aux))
    LIEmpty))).

Definition swap (v1 v2 aux : Var) : Instr :=
  IBlock (
    (IVar aux (VAR v1));
    (IVar v1 (VAR v2));
    (IVar v2 (VAR aux));
  ).

Compute (swap = swap_no_notation).

(* 5.6.3 *)
Require Import Coq.Arith.EqNat.

(* Recordar que Definition Memory : Set := Var -> Value *)
Definition update (m : Memory) (var : Var) (val : Value) : Memory :=
  fun (var' : Var) => if beq_nat var var'
                      (* Actualizo el valor de la memoria *)
                      then val
                      (* Devuelvo el valor anterior de la memoria *)
                      else lookup m var'.

(* 5.6.4 *)
Lemma Ej5_6_4 : forall (m : Memory) (var : Var) (val : Value),
lookup (update m var val) var = val.
Proof.
  intros.
  unfold lookup, update.
  case_eq (beq_nat var var).
  - intros.
    reflexivity.
  - intros.
    rewrite <- beq_nat_refl in H.
    discriminate.
Qed.

(* 5.6.5 *)
Lemma Ej5_6_5 : forall (m : Memory) (var var' : Var) (val : Value),
var <> var' -> lookup (update m var val) var' = lookup m var'.
Proof.
  unfold not.
  intros.
  unfold lookup, update.
  case_eq (beq_nat var var'); intros.
  (* Claramente hay una contradicción entre H y H0 *)
  - apply beq_nat_true in H0.
    contradiction.
  - unfold lookup.
    reflexivity.
Qed.

End Ejercicio6.

Section Ejercicio7.

(* 5.7.1 *)
Inductive Execute : Instr -> Memory -> Memory -> Prop :=
  | xSkip : forall (m : Memory),
      Execute ISkip m m
  | xAss : forall (e : BoolExpr) (m : Memory) (w : Value) (v : Var),
      BEeval e m w -> Execute (IVar v e) m (update m v w)
  | xIFthen : forall (c : BoolExpr) (m m1 : Memory) (p1 p2 : Instr),
      BEeval c m true -> Execute p1 m m1 -> Execute (IIf c p1 p2) m m1
  | xIFelse : forall (c : BoolExpr) (m m2 : Memory) (p1 p2 : Instr),
      BEeval c m false -> Execute p2 m m2 -> Execute (IIf c p1 p2) m m2
  | xWhileTrue : forall (c : BoolExpr) (m m1 m2 : Memory) (p : Instr),
      BEeval c m true -> Execute p m m1 -> Execute (IWhile c p) m1 m2 -> Execute (IWhile c p) m m2
  | xWhileFalse : forall (c : BoolExpr) (m : Memory) (p : Instr),
      BEeval c m false -> Execute (IWhile c p) m m
  | xRepeat0 : forall (m : Memory) (i : Instr),
      Execute (IRepeat 0 i) m m
  | xRepeatS : forall (n : nat) (m1 m2 m3 : Memory) (i : Instr),
      Execute i m1 m2 -> Execute (IRepeat n i) m2 m3 -> Execute (IRepeat (S n) i) m1 m3
  | xBeginEnd : forall (m m1 : Memory) (p : LInstr),
      ExecuteL p m m1 -> Execute (IBlock p) m m1
  with ExecuteL : LInstr -> Memory -> Memory -> Prop :=
    | xEmptyBlock : forall (m : Memory),
        ExecuteL LIEmpty m m
    | xNext : forall (m m1 m2 : Memory) (i : Instr) (li : LInstr),
        Execute i m m1 -> ExecuteL li m1 m2 -> ExecuteL (LISeq i li) m m2.  

(* 5.7.2 *)
Lemma Ej5_7_2 : forall (m m' : Memory) (e1 e2 : Instr),
Execute (IIf (NOT (BOOL false)) e1 e2) m m' -> Execute (IIf (BOOL false) e2 e1) m m'.
Proof.
  intros.
  inversion H; inversion H5; constructor; assumption.
Qed.

(* 5.7.3 *)
Lemma Ej5_7_3 : forall (c : BoolExpr) (m m' : Memory) (e1 e2 : Instr),
Execute (IIf (NOT c) e1 e2) m m' -> Execute (IIf c e2 e1) m m'.
Proof.
  intro.
  case_eq c; intros; inversion H0; inversion H6; constructor; assumption.
Qed.

(* 5.7.4 *)
Lemma Ej5_7_4 : forall (m m' : Memory) (p : Instr),
Execute (IWhile (BOOL false) p) m m' -> m = m'.
Proof.
  intros.
  inversion H.
  - inversion H2.
  - reflexivity.
Qed.

(* 5.7.5 *)
Lemma Ej5_7_5 : forall (c : BoolExpr) (m m' : Memory) (p : Instr),
Execute (IBlock (LISeq (IIf c p ISkip) (LISeq (IWhile c p) LIEmpty))) m m' ->
Execute (IWhile c p) m m'.
Proof.
  intros.
  inversion_clear H.
  inversion H0.
  inversion H2.
  - inversion H5.
    inversion H18.
    rewrite -> H21 in H15.
    apply xWhileTrue with (m1 := m1); assumption.
  - inversion H5.
    inversion H12.
    inversion H18.
    rewrite H23 in H15.
    assumption.
Qed.

(* 5.7.6 *)
Lemma Ej5_7_6 : forall (n : nat) (m1 m2 : Memory) (i : Instr),
Execute (IBlock (LISeq i (LISeq (IRepeat n i) LIEmpty))) m1 m2 ->
Execute (IRepeat (S n) i) m1 m2.
Proof.
  intros.
  inversion H.
  inversion H1.
  inversion H9.
  apply xRepeatS with (m2 := m4).
  - assumption.
  - inversion H15.
    rewrite H18 in H12.
    assumption.
Qed.

(* 5.7.7 *)
Lemma Ej5_7_7 : forall (n1 n2 : nat) (m1 m2 m3 : Memory) (i : Instr),
Execute (IRepeat n1 i) m1 m2 -> Execute (IRepeat n2 i) m2 m3 -> Execute (IRepeat (n1 + n2) i) m1 m3.
Proof.
  induction n1; intros.
  - simpl.
    inversion H.
    assumption.
  - inversion H.
    simpl.
    apply xRepeatS with (m2 := m4).
    + assumption.
    + apply IHn1 with (m2 := m2); assumption.
Qed.

(* 5.7.8 *)
Lemma Ej5_7_8 : forall (m m' : Memory) (v1 v2 : Var),
Execute (PP v1 v2) m m' -> v1 <> v2 -> lookup m' v1 = true /\ lookup m' v2 = false.
Proof.
  intros.
  unfold lookup.
  unfold not in *.
  inversion_clear H.
  inversion_clear H1.
  inversion_clear H2.
  inversion H3.
  inversion H.
  inversion H1.
  inversion H9.
  split.
  - inversion H14.
    + rewrite <- H8 in H13.
      rewrite H5 in H13.
      rewrite <- H13.
      rewrite <- H20.
      unfold update.
      case_eq (beq_nat v2 v1); intros.
      * absurd (v1 = v2).
          assumption.

          symmetry.
          apply beq_nat_true.
          assumption.
      * unfold lookup.
        rewrite <- (beq_nat_refl v1).
        symmetry.
        assumption.
    + rewrite <- H5.
      rewrite <- H13.
      rewrite <- H20.
      rewrite <- H8.
      unfold update.
      case (beq_nat v2 v1); intros.
      * reflexivity.
      * unfold lookup.
        rewrite <- (beq_nat_refl v1).
        symmetry.
        assumption.
  - inversion H14.
    + rewrite <- H8 in H13.
      rewrite H5 in H13.
      rewrite <- H13.
      rewrite <- H20.
      unfold update.
      rewrite <- (beq_nat_refl v2).
      reflexivity.
    + inversion H18.
      rewrite <- H8 in H24.
      unfold lookup, update in H24.
      rewrite <- (beq_nat_refl v1) in H24.
      rewrite H24 in H17.
      discriminate.
Qed.

End Ejercicio7.


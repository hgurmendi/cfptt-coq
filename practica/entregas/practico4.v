(* Hernán Gurmendi *)

Set Asymmetric Patterns.

Section Ejercicio1.

Inductive list (A : Set) : Set :=
  | emptyL : list A
  | cons : A -> list A -> list A.

Inductive bintree (A : Set) : Set :=
  | emptyBT : bintree A
  | merge : bintree A -> A -> bintree A -> bintree A.


Inductive array (A : Set) : nat -> Set :=
  | emptyA : array A 0
  | add : forall (n : nat), A -> array A n -> array A (S n).

Inductive matrix (A : Set) : nat -> nat -> Set :=
  | oneCol : forall n : nat, array A n -> matrix A n 1
  | addCol : forall n m : nat, array A n -> matrix A n m -> matrix A n (S m).

Inductive leq : nat -> nat -> Prop :=
  | leq0 : forall m : nat, leq 0 m
  | leqS : forall n m : nat, leq n m -> leq (S n) (S m).

Inductive eq_list (A : Set) : list A -> list A -> Prop :=
  | eqlistE : eq_list A (emptyL A) (emptyL A)
  | eqlistC : forall (l r : list A) (x : A), eq_list A l r -> eq_list A (cons A x l) (cons A x r).

Inductive eq_list' (A : Set) (R : A -> A -> Prop) : list A -> list A -> Prop :=
  | eqlistE' : eq_list' A R (emptyL A) (emptyL A)
  | eqlistC' : forall (l r : list A) (x y : A), eq_list' A R l r -> R x y -> eq_list' A R (cons A x l) (cons A y r).

Inductive sorted (A : Set) (R : A -> A -> Prop) : list A -> Prop :=
  | sortedE : sorted A R (emptyL A)
  | sortedS : forall x : A, sorted A R (cons A x (emptyL A)) (* Singleton *)
  | sortedC : forall (x y : A) (l : list A), R x y -> sorted A R (cons A x (cons A y l)).

Inductive mirror (A : Set) : bintree A -> bintree A -> Prop :=
  | mirrorE : mirror A (emptyBT A) (emptyBT A)
  | mirrorM : forall (x : A) (ll lr rl rr : bintree A), mirror A ll rr -> mirror A lr rl -> mirror A (merge A ll x lr) (merge A rl x rr).

Inductive isomorfo (A : Set) : bintree A -> bintree A -> Prop :=
  | isomorfoE : isomorfo A (emptyBT A) (emptyBT A)
  | isomorfoM : forall (ll lr rl rr : bintree A) (x y : A), isomorfo A ll rl -> isomorfo A lr rr -> isomorfo A (merge A ll x lr) (merge A rl y rr).

End Ejercicio1.

Section Ejercicio3.

Fixpoint sum (n m : nat) : nat :=
    match n, m with
    | 0, m     => m
    | (S n), m => S (sum n m)
    end.

Fixpoint prod (n m : nat) : nat :=
    match n, m with
    | 0, m     => 0
    | (S n), m => sum m (prod n m)
    end.

Fixpoint pot (n m : nat) : nat :=
    match m with
    | 0     => 1
    | (S m) => prod n (pot n m)
    end.

End Ejercicio3.

Section Ejercicio4.

Fixpoint length (A : Set) (l : list A) : nat :=
    match l with
    | emptyL    => 0
    | cons x xs => 1 + length A xs
    end.

Fixpoint length' (A : Set) (l : list A) :=
    match l with
    | emptyL    => 0
    | cons _ xs => S (length' A xs)
    end.

Fixpoint append (A : Set) (l r : list A) : list A :=
    match l with
    | emptyL    => r
    | cons x xs => cons A x (append A xs r)
    end.

Fixpoint reverse (A : Set) (l : list A) : list A :=
    match l with
    | emptyL    => emptyL A
    | cons x xs => append A (reverse A xs) (cons A x (emptyL A))
    end.

Fixpoint filter (A : Set) (p : A -> bool) (l : list A) : list A :=
    match l with
    | emptyL    => emptyL A
    | cons x xs =>
        match (p x) with
        | true  => cons A x (filter A p xs)
        | false => filter A p xs
        end
    end.

Fixpoint map (A B : Set) (f : A -> B) (l : list A) : list B :=
    match l with
    | emptyL    => emptyL B
    | cons x xs => cons B (f x) (map A B f xs)
    end.

Fixpoint exists_ (A : Set) (p : A -> bool) (l : list A) : bool :=
    match l with
    | emptyL    => false
    | cons x xs =>
        match (p x) with
        | false => exists_ A p xs
        | true  => true
        end
    end.

End Ejercicio4.

Section Ejercicio5.

Fixpoint inverse (A : Set) (t : bintree A) : bintree A :=
  match t with
  | emptyBT     => emptyBT A
  | merge l x r => merge A (inverse A r) x (inverse A l)
  end.

End Ejercicio5.

Section Ejercicio9.

Lemma SumO : forall n : nat, sum n 0 = n /\ sum 0 n = n.
Proof.
  intros.
  induction n; split; simpl.
  - reflexivity.
  - reflexivity.
  - elim IHn. intros. rewrite H. reflexivity.
  - reflexivity.
Qed.

Lemma SumS : forall n m : nat, sum n (S m) = sum (S n) m.
Proof.
  intros.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma SumAsoc : forall n m p : nat, sum n (sum m p) = sum (sum n m) p.
Proof.
  intros.
  induction n; simpl.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed.

Lemma SumConm : forall n m : nat, sum n m = sum m n.
Proof.
  intros.
  induction n; simpl.
  - induction m; simpl.
    + reflexivity.
    + rewrite <- IHm. reflexivity.
  - rewrite IHn. rewrite SumS. simpl. reflexivity.
Qed.

End Ejercicio9.

Section Ejercicio12.

Lemma L7 : forall (A B : Set) (l m : list A) (f : A -> B),
  map A B f (append A l m) = append B (map A B f l) (map A B f m).
Proof.
  intros.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

Lemma L8 : forall (A : Set) (l m : list A) (P : A -> bool),
  filter A P (append A l m) = append A (filter A P l) (filter A P m).
Proof.
  intros.
  induction l; simpl.
  - reflexivity.
  - case (P a); simpl; rewrite IHl; reflexivity.
Qed.

Lemma L9 : forall (A : Set) (l : list A) (P : A -> bool),
  filter A P (filter A P l) = filter A P l.
Proof.
  intros.
  induction l; simpl.
  - reflexivity.
  - assert (P a = true \/ P a =  false). case (P a); [left | right]; reflexivity.
    elim H; intros Assumption; rewrite Assumption; simpl.
    + rewrite Assumption. rewrite IHl. reflexivity.
    + rewrite IHl. reflexivity.
Qed.

Lemma L10 : forall (A : Set) (l m n : list A),
  append A l (append A m n) = append A (append A l m) n.
Proof.
  intros.
  induction l; simpl.
  - reflexivity.
  - rewrite IHl. reflexivity.
Qed.

End Ejercicio12.

Section Ejercicio14.

Lemma Ej14 : forall (A : Set) (t : bintree A), mirror A (inverse A t) t.
Proof.
  intros.
  induction t; simpl.
  - apply mirrorE.
  - apply mirrorM; assumption.
Qed.

End Ejercicio14.

Section Ejercicio17.

Inductive posfijo (A : Set) : list A -> list A -> Prop :=
  | posfE : forall l : list A, posfijo A l l
  | posfC : forall (l1 l2 : list A) (x : A), posfijo A l1 l2 -> posfijo A l1 (cons A x l2).

Lemma Ej17_2_1 : forall (A : Set) (l1 l2 l3 : list A), l2 = append A l3 l1 -> posfijo A l1 l2.
Proof.
  intros.
  rewrite H.
  clear H.
  induction l3; simpl.
  - apply posfE.
  - apply posfC. apply IHl3.
Qed.

Lemma Ej17_2_2 : forall (A : Set) (l1 l2 : list A), posfijo A l1 l2 -> exists l3 : list A, l2 = append A l3 l1.
Proof.
  intros.
  induction H.
  - exists (emptyL A). simpl. reflexivity.
  - elim IHposfijo. intros. rewrite H0. exists (cons A x x0). simpl. reflexivity.
Qed.

Lemma Ej17_3_1 : forall (A : Set) (l1 l2 l3 : list A),
posfijo A l2 (append A l1 l2).
Proof.
  intros.
  induction l1; simpl.
  - apply posfE.
  - apply posfC. assumption.
Qed.

Lemma EmptyAppends : forall (A : Set) (l1 l2 : list A),
append A l1 l2 = emptyL A -> l1 = emptyL A /\ l2 = emptyL A.
Proof.
  intros.
  split; rewrite <- H; induction l1.
  - symmetry. assumption.
  - simpl in H. discriminate.
  - simpl. reflexivity.
  - simpl in H. discriminate.
Qed.

Axiom AppendEmptyLeft : forall (A : Set) (l1 l2 : list A), append A l1 l2 = l2 -> l1 = emptyL A.

Lemma Ej17_3_2 : forall (A : Set) (l1 l2 : list A),
posfijo A l1 l2 -> posfijo A l2 l1 -> l1 = l2.
Proof.
  intros.
  assert (exists l3 : list A, l2 = append A l3 l1). apply Ej17_2_2. assumption.
  assert (exists l3 : list A, l1 = append A l3 l2). apply Ej17_2_2. assumption.
  elim H1. intros.
  elim H2. intros.
  rewrite H4 in H3.
  rewrite L10 in H3.
  assert (append A x x0 = emptyL A).
  - apply (AppendEmptyLeft A (append A x x0) l2). symmetry. assumption.
  - assert (x0 = emptyL A).
    + elim (EmptyAppends A x x0).
      * intros. assumption.
      * assumption.
    + rewrite H6 in H4. simpl in H4. assumption.
Qed.

Lemma Ej17_3_3 : forall (A : Set) (l1 l2 l3 : list A),
posfijo A l1 l2 -> posfijo A l2 l3 -> posfijo A l1 l3.
Proof.
  intros.
  induction H0.
  - induction l; assumption.
  - induction H0; apply posfC.
    + assumption.
    + apply IHposfijo. assumption.
Qed.

Fixpoint ultimo (A : Set) (l : list A) : list A :=
  match l with
  | emptyL    => emptyL A
  | cons x xs =>
  match xs with
    | emptyL => cons A x (emptyL A)
    | _      => ultimo A xs
    end
  end.

Lemma Ej17_5 : forall (A : Set) (l : list A), posfijo A (ultimo A l) l.
Proof.
  intros.
  induction l; simpl.
  - apply posfE.
  - destruct l.
    + apply posfE.
    + apply posfC. assumption.
Qed.

End Ejercicio17.

Section Ejercicio20.

Inductive ACom (A : Set) : nat -> Set :=
  | single : A -> ACom A O
  | combine : forall n : nat, ACom A n -> A -> ACom A n -> ACom A (S n).

Fixpoint h (A : Set) (n : nat) (t : ACom A n) : nat :=
  match t with
  | single x => 1
  | combine _ t1 x t2 => sum (h A _ t1) (h A _ t2)
  end.

(* Parameter pot: nat -> nat -> nat. *) 
Axiom potO : forall n : nat, pot (S n) 0 = 1.  
Axiom potS : forall m: nat, pot 2 (S m) = sum (pot 2 m) (pot 2 m).

Lemma Ej20_3 : forall (A : Set) (n : nat) (t : ACom A n),
(h A n t) = (pot 2 n).
Proof.
  intros.
  induction t; simpl.
  - reflexivity.
  - rewrite IHt1. rewrite IHt2. elim (SumO (pot 2 n)). intros. rewrite H. reflexivity.
Qed.

End Ejercicio20.


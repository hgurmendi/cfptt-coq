(* Hernán Gurmendi *)

Section Ejercicio3.
Variable A B C: Set.

Definition apply : (A -> B) -> A -> B
  := fun f x => (f x).

Definition o : (B -> C) -> (A -> B) -> (A -> C)
  := fun f g x => (f (g x)).

Definition twice : (A -> A) -> A -> A
  := fun f x => (f (f x)). 

Definition apply' : forall X Y : Set, (X -> Y) -> X -> Y
  := fun (X Y : Set) (f : X -> Y) (x : X) => (f x).

Definition o' : forall X Y Z : Set, (Y -> Z) -> (X -> Y) -> (X -> Z)
  := fun (X Y Z : Set) (f : Y -> Z) (g : X -> Y) (x : X) => (f (g x)).

Definition twice' : forall X : Set, (X -> X) -> X -> X
  := fun (X : Set) (f : X -> X) (x : X) => (f (f x)). 

End Ejercicio3.


Section Ejercicio4.
Variable A: Set.

Definition id : A -> A
  := fun (x : A) => x.

Theorem e4 : forall x : A, (o A A A id id) x = id x.
Proof.
  reflexivity.
Qed.

End Ejercicio4.


Section Ejercicio5.


Definition opI : forall A : Set, A -> A
  := id.

Definition opK : forall A B : Set, A -> B -> A
  := fun (A B : Set) (a : A) (b : B) => a.

Definition opS : forall A B C : Set, (A -> B -> C) -> (A -> B) -> A -> C
  := fun (A B C : Set) (f : A -> B -> C) (g : A -> B) (x : A) => ((f x) (g x)).

Lemma e52 : forall A B : Set, opS A (B -> A) A (opK A (B -> A)) (opK A B) = opI A.
Proof.
  reflexivity.
Qed.

End Ejercicio5.


Section Ejercicio10.

Parameter Array : Set -> nat -> Set.
Parameter emptyA : forall X : Set, Array X 0.
Parameter addA : forall (X : Set) (n : nat), X -> Array X n -> Array X (S n).

Parameter Matrix : Set -> nat -> Set.
Parameter emptyM : forall X : Set, Matrix X 0.
Parameter addM : forall (X : Set) (n : nat), Matrix X n -> Array X (n + 1) -> Matrix X (n + 1).

Definition M1 := addM nat 0 (emptyM nat) (addA nat 0 3 (emptyA nat)).
Definition M2 := addM nat 1 M1 (addA nat 1 2 (addA nat 0 3 (emptyA nat))).
Definition M3 := addM nat 2 M2 (addA nat 2 1 (addA nat 1 2 (addA nat 0 3 (emptyA nat)))).

Check M3.

End Ejercicio10.


Section Ejercicio11.

Parameter ABNat : forall n : nat, Set.

Parameter emptyAB : ABNat 0.

Parameter addAB_eq : forall n, ABNat n -> nat -> ABNat n -> ABNat (n + 1).
Parameter addAB_lt : forall n, ABNat n -> nat -> ABNat (n + 1) -> ABNat (n + 1).
Parameter addAB_gt : forall n, ABNat (n + 1) -> nat -> ABNat n -> ABNat (n + 1).

Definition e11_3 : ABNat 2 
  := addAB_eq 1 (addAB_eq 0 emptyAB 2 emptyAB) 1 (addAB_eq 0 emptyAB 3 emptyAB).

Parameter ABGen : forall (T : Type) (n : nat), Set.
Parameter emptyABGen : forall (T : Type), ABGen T 0.
Parameter addABGen_eq' : forall T n, ABGen T n -> T -> ABGen T n -> ABGen T (n + 1). 
Parameter addABGen_lt' : forall T n, ABGen T n -> T -> ABGen T (n + 1) -> ABGen T (n + 1). 
Parameter addABGen_gt' : forall T n, ABGen T (n + 1) -> T -> ABGen T n -> ABGen T (n + 1). 

End Ejercicio11.


Section Ejercicio15.

Variable U : Set.
Variable e : U.
Variable A B : U -> Prop.
Variable P : Prop.
Variable R : U -> U -> Prop.

Lemma Ej315_1 : (forall x : U, A x -> B x) -> (forall x : U, A x) -> forall x : U, B x.
Proof.
  intros.
  exact (H x (H0 x)).
Qed.

Lemma Ej315_2 : forall x : U, A x -> ~(forall x : U, ~ A x).
Proof.
  unfold not.
  intros.
  exact (H0 x H).
Qed.

Lemma Ej315_3 : (forall x : U, P -> A x) -> P -> forall x : U, A x.
Proof.
  intros.
  exact (H x H0).
Qed.

Lemma Ej315_4 : (forall x y : U, R x y) -> forall x : U, R x x.
Proof.
  intros.
  exact (H x x).
Qed.

Lemma Ej315_5 : (forall x y: U, R x y -> R y x) -> forall z : U, R e z -> R z e.
Proof.
  intros.
  exact (H e z H0).
Qed.

End Ejercicio15.


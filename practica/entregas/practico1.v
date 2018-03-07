(* Practica 1 *)

Section P1.
Variables A B C:Prop.

(* Ej 1.1 *)
Theorem e11: A->A.
Proof.
  intros.
  assumption.
Qed.

(* Ej 1.2 *)
Theorem e12: A->B->A.
Proof.
  intros.
  assumption.
Qed.

(* Ej 1.3 *)
Theorem e13: (A->(B->C))->(A->B)->(A->C).
Proof.
  intros.
  apply H.
    assumption.

    apply H0.
    assumption.
Qed.

(*Ej 2.1 *)
Theorem e21: (A->B)->(B->C)->A->C.
Proof.
  intros.
  apply H0.
  apply H.
  assumption.
Qed.

(*Ej 2.2 *)
Theorem e22: (A->B->C)->B->A->C.
Proof.
  intros.
  apply H.
    assumption.

    assumption.
Qed.

(*Ej 3.1 *)
Theorem e31_1: A->A->A.
Proof.
  intros.
  assumption.
Qed.

Theorem e31_2: A->A->A.
Proof.
  intros.
  exact H.
Qed.

(* Ej 3.2 *)
Theorem e32_1: (A->B->C)->A->(A->C)->B->C.
Proof.
  intros.
  apply H1.
  assumption.
Qed.

Theorem e32_2: (A->B->C)->A->(A->C)->B->C.
Proof.
  intros.
  apply H.
    assumption.

    assumption.
Qed.

(* Ej 4.1 *)
Theorem e41: A -> ~~A.
Proof.
  intros.
  unfold not.
  intros.
  absurd A.
    assumption.

    assumption.
Qed.

(* Ej 4.2 *)
Theorem e42: A -> B -> (A /\ B).
Proof.
  intros.
  split.
    assumption.

    assumption.
Qed.

(* Ej 4.3 *)
Theorem e43: (A->B->C) -> (A/\B->C).
Proof.
  intros.
  apply H.
    elim H0.
    intros.
    assumption.

    elim H0.
    intros.
    assumption.
Qed.

(* Ej 4.4 *)
Theorem e44: A->(A\/B).
Proof.
  intros.
  left.
  assumption.
Qed.

(* Ej 4.5 *)
Theorem e45: B->(A\/B).
Proof.
  intros.
  right.
  assumption.
Qed.

(* Ej 4.6 *)
Theorem e46: (A \/ B) -> (B \/ A).
Proof.
  intros.
  elim H.
    intros.
    right.
    assumption.

    intros.
    left.
    assumption.
Qed.

(* Ej 4.7 *)
Theorem e47: (A->C)->(B->C)->A\/B->C.
Proof.
  intros.
  elim H1.
    intros.
    apply H.
    assumption.

    intros.
    apply H0.
    assumption.
Qed.

(* Ej 4.8 *)
Theorem e48: False->A.
Proof.
  intros.
  elim H.
Qed.

(* Ej 5.1 *)
Theorem e51: (A->B)-> ~B-> ~A.
Proof.
  intros.
  unfold not.
  intros.
  absurd B.
    assumption.

    apply H.
    assumption.
Qed.

(* Ej 5.2 *)
Theorem e52: ~(A/\~A).
Proof.
  unfold not.
  intros.
  elim H.
  intros.
  absurd A.
    assumption.

    assumption.
Qed.

(* Ej 5.3 *)
Theorem e53: (A->B)-> ~(A/\~B).
Proof.
  intros.
  unfold not.
  intros.
  elim H0.
  intros.
  absurd B.
    assumption.
    
    apply H.
    assumption.
Qed.

(* Ej 5.4 *)
Theorem e54: (A/\B)->~(A->~B).
Proof.
  intros.
  unfold not.
  intros.
  elim H.
  intros.
  apply H0.
    assumption.

    assumption.
Qed.

(* Ej 5.5 *)
Theorem e55: (~A /\ ~~A) -> False.
Proof.
  intros.
  elim H.
  intros.
  absurd (~A).
    assumption.

    assumption.
Qed.

(* Ej 6.1 *)
Theorem e61: (A\/B) -> ~(~A/\~B).
Proof.
  intros.
  unfold not.
  intros.
  elim H0.
  intros.
  elim H.
    intros.
    absurd A.
      assumption.

      assumption.

    intros.
    absurd B.
      assumption.

      assumption.
Qed.

(* Ej 6.2 *)
Theorem e62: A\/B <-> B\/A.
Proof.
  unfold iff.
  split.
    intros.
    elim H.
      intros.
      right.
      assumption.

      intros.
      left.
      assumption.

    intros.
    elim H.
      intros.
      right.
      assumption.

      intros.
      left.
      assumption.
Qed.

(* Ej 6.3 *)
Theorem e63: A\/B -> ((A->B)->B).
Proof.
  intros.
  elim H.
    intros.
    apply H0.
    assumption.

    intros.
    assumption.
Qed.

End P1.


Section Logica_Clasica.
Variables A B C: Prop.

(* Ej 7.1 *)
Theorem e71: A \/ ~A -> ~~A->A.
Proof.
  intros.
  elim H.
    intros.
    assumption.

    intros.
    absurd (~A).
    assumption.
    assumption.
Qed.

(* Ej 7.2 *)
Theorem e72: A\/~A -> ((A->B) \/ (B->A)).
Proof.
  intros.
  elim H.
    intros.
    right.
    intros.
    assumption.

    intros.
    left.
    unfold not in H0.
    intros.
    assert False.
      absurd A.
        assumption.
        
        assumption.
        elim H2.
Qed.

(* Ej 7.3 *)
Theorem e73: (A \/ ~A) -> ~(A /\ B) -> ~A \/ ~B.
Proof.
  intros.
  elim H.
    intros.
    unfold not in H0.
    right.
    unfold not.
    intros.
    apply H0.
    split.
      assumption.
      
      assumption.
    
    unfold not.
    intros.
    left.
    assumption.
Qed.


Require Import Classical.
Check classic.

(* Ej 8.1 *)
Theorem e81: forall A:Prop, ~~A->A.
Proof.
  intros.
  pose classic.
  elim o with (P := A0).
    intros.
    assumption.
    
    intros.
    absurd (~A0).
      assumption.
      
      assumption.
Qed.

(* Ej 8.2 *)
Theorem e82: forall A B:Prop, (A->B)\/(B ->A).
Proof.
  intros.
  pose classic.
  elim o with (P := A0).
    intros.
    right.
    intros.
    assumption.
    
    intros.
    left.
    intros.
    absurd A0.
      assumption.
      
      assumption.
Qed.

(* Ej 8.3 *)
Theorem e83: forall A B:Prop, ~(A/\B)-> ~A \/ ~B.
Proof.
  intros.
  pose classic.
  elim o with (P := A0).
    intros.
    unfold not in H.
    right.
    unfold not.
    intros.
    apply H.
    split.
      assumption.
      
      assumption.
    
    intros.
    left.
    assumption.
Qed.

End Logica_Clasica.


Section Traducciones.

(* Ej 9 *)
(* Definiciones *)
Variable NM RED CONS UTIL : Prop.

Hypothesis H1 : ~NM \/ ~RED.
Hypothesis H2 : CONS \/ ~UTIL.

Theorem ej9 : NM /\ UTIL -> CONS /\ ~RED.
Proof.
  intros.
  split.
  elim H2.
    intros.
    assumption.
    
    intros.
    elim H.
    intros.
    absurd UTIL.
      assumption.
      
      assumption.
      
    elim H1.
      intros.
      unfold not.
      intros.
      elim H.
      intros.
      absurd NM.
        assumption.
        
        assumption.
    
    intros.
    assumption.
Qed.

End Traducciones.

Section Traducciones2.
(* Ej 10 y 11 *)
(* Formalizaciones a cargo del estudiante *)


(* Ej 12 *)
(* Definiciones *)
Variable PF:Prop. (* el paciente tiene fiebre *)
Variable PA:Prop. (* el paciente tiene piel amarillenta *)
Variable PH:Prop. (* el paciente tiene hepatitis *)
Variable PR:Prop. (* el paciente tiene rubeola *)

Hypothesis Regla1: PF \/ PA -> PH \/ PR.
Hypothesis Regla2: ~PR \/ PF.
Hypothesis Regla3: PH /\ ~PR -> PA.


Theorem ej12: (~PA /\ PF) -> PR.
Proof.
  intro.
  elim H.
  intros.
  assert (~ (PH /\ ~PR)).
    intro.
    elim H2.
    intros.
    apply H0.
    apply Regla3.
    assumption.
  
    apply e83 in H2.
    elim H2.
      intros.
      elim Regla1.
        intro.
        contradiction.
        
        intro.
        assumption.
  
      left.
      assumption.

    intro.
    apply e81 in H3.
    assumption.
Qed.

End Traducciones2.


(*******************************************************************
 * Construcción Formal de Programas en Teoría de Tipos
 * Trabajo práctico final
 * Hernán Gurmendi
 ******************************************************************)

(*******************************************************************
 * Este archivo especifica las acciones
 * (Como transformadores de estado)
 ******************************************************************)

Load State.

Section Actions.

(* Tácticas obtenidas en http://adam.chlipala.net/cpdt/html/Match.html *)
Ltac notHyp P :=
  match goal with
    | [ _ : P |- _ ] => fail 1
    | _ =>
      match P with
        | ?P1 /\ ?P2 => first [ notHyp P1 | notHyp P2 | fail 2 ]
        | _ => idtac
      end
  end.

Ltac extend pf :=
  let t := type of pf in
    notHyp t; generalize pf; intro.

Ltac completer :=
  repeat match goal with
           | [ |- _ /\ _ ] => constructor
           | [ H : _ /\ _ |- _ ] => destruct H
           | [ H : ?P -> ?Q, H' : ?P |- _ ] => specialize (H H')
           | [ |- forall x, _ ] => intro

           | [ H : forall x, ?P x -> _, H' : ?P ?X |- _ ] => extend (H X H')
         end.


Parameter ctxt : context.


(* Ejercicio 7.2 *)

Inductive action : Set :=
  | read (va : vadd)
  | write (va : vadd) (val : value)
  | chmod.


(* Ejercicio 7.3 *)

(* in state _s_, is virtual address _va_ mapped to machine address _ma_? *)
Definition va_mapped_to_ma (s: state) (va: vadd) (ma: madd) : Prop :=
  exists (o: os) (pm: padd -> option madd) (ma': madd) (pg: page) (vm: vadd -> option madd),
    oss s (active_os s) = Some o
    /\ hypervisor s (active_os s) = Some pm
    /\ pm (curr_page o) = Some ma'
    /\ memory s ma' = Some pg
    /\ page_content pg = PT vm
    /\ vm va = Some ma.

(* Action Semantics - read *)

Definition readPre (s : state) (va : vadd) : Prop :=
  ctxt_vadd_accessible ctxt va = true
  /\ aos_activity s = running
  /\ (exists (ma : madd) (pg : page),
    va_mapped_to_ma s va ma
    /\ memory s ma = Some pg
    /\ isRW (page_content pg) = true).

Definition readPost (s s' : state) : Prop :=
  s = s'.

(* Action Semantics - write *)

Definition writePre (s : state) (va : vadd) (val : value) : Prop :=
  ctxt_vadd_accessible ctxt va = true
  /\ aos_activity s = running
  /\ (exists (ma : madd) (pg : page),
    va_mapped_to_ma s va ma
    /\ memory s ma = Some pg
    /\ isRW (page_content pg) = true).

Definition writePost (s s' : state) (va : vadd) (val : value) : Prop :=
  exists (ma : madd) (pg : page),
    va_mapped_to_ma s va ma
    /\ memory s' = (update (memory s) ma (Page (RW (Some val)) (Os (active_os s))))
    /\ active_os s = active_os s'
    /\ aos_exec_mode s = aos_exec_mode s'
    /\ aos_activity s = aos_activity s'
    /\ oss s = oss s'
    /\ hypervisor s = hypervisor s'
    /\ (forall (ma' : madd),
      ma <> ma'
      /\ (memory s) ma'  = (memory s') ma').

(* Action Semantics - chmod *)

Definition chmodPre (s : state) : Prop :=
  aos_activity s = waiting
  /\ (exists (o : os), oss s (active_os s) = Some o /\ hcall o = None).

Definition chmodPost (s s' : state) : Prop :=
    (ctxt_oss ctxt (active_os s) = true
    /\ active_os s = active_os s'
    /\ oss s = oss s'
    /\ hypervisor s = hypervisor s'
    /\ memory s = memory s'
    /\ (aos_exec_mode s = usr /\ aos_exec_mode s' = svc)
    /\ (aos_activity s = waiting /\ aos_activity s' = running))
  \/
    (ctxt_oss ctxt (active_os s) = false
    /\ active_os s = active_os s'
    /\ oss s = oss s'
    /\ hypervisor s = hypervisor s'
    /\ memory s = memory s'
    /\ (aos_exec_mode s = svc /\ aos_exec_mode s' = usr)
    /\ (aos_activity s = waiting /\ aos_activity s' = running)).

(* Ejercicio 7.5 *)

(* Propiedad 3 (iii)
if the hypervisor or a trusted OS is running the processor must be in
supervisor mode *)
Definition Prop3 (s : state) : Prop :=
  ((ctxt_oss ctxt (active_os s) = true /\ aos_activity s = running)
  \/ aos_activity s = waiting)
  -> aos_exec_mode s = svc.

(* Propiedad 5 (v)
the hypervisor maps an OS physical address to a machine address owned by
that same OS. This mapping is also injective *)
Definition Prop5 (s : state) : Prop :=
  forall (o : os_ident) (pa : padd),
    (forall (pm : padd -> option madd), exists (ma : madd) (pg : page),
      (hypervisor s) o = Some pm
      /\ pm pa = Some ma
      /\ memory s ma = Some pg
      /\ page_owned_by pg = Os o
      /\ forall (pa pa' : padd), pm pa = pm pa' -> pa = pa').

(* Propiedad 6 (vi)
all page tables of an OS o map accessible virtual addresses to pages owned
by o and not accessible ones to pages owned by the hypervisor *)
Definition Prop6 (s : state) : Prop :=
  forall (o : os_ident) (pg : page) (vtm : vadd -> option madd),
    (page_content pg = PT vtm /\ page_owned_by pg = Os o)
    -> forall (va : vadd) (ma : madd), exists (pg' : page),
        vtm va = Some ma
        /\ memory s ma = Some pg'
        /\ (ctxt_vadd_accessible ctxt va = true -> page_owned_by pg' = Os o)
        /\ (ctxt_vadd_accessible ctxt va = false -> page_owned_by pg' = Hyp).

Definition ValidState (s : state) : Prop :=
  Prop3 s
  /\ Prop5 s
  /\ Prop6 s.


(* Ejercicio 7.4 *)

Definition Pre (s : state) (a : action) : Prop :=
  match a with
  | read va      => readPre s va
  | write va val => writePre s va val
  | chmod        => chmodPre s
  end.

Definition Post (s s' : state) (a : action) : Prop :=
  match a with
  | read _      => readPost s s'
  | write va val => writePost s s' va val
  | chmod        => chmodPost s s'
  end.

Inductive OneStepExecution : state -> action -> state -> Prop :=
  | OSE : forall (s s' : state) (a : action),
    ValidState s -> Pre s a -> Post s s' a -> OneStepExecution s a s'.


(* Ejercicio 7.6 *)

Lemma ActionsPreserveProp3 (s s' : state) (a : action) :
  OneStepExecution s a s' -> Prop3 s'.
Proof.
  intros.
  inversion H.
  inversion H0.
  unfold Prop3; intros.
  destruct a.
  - inversion H2.
    rewrite H9 in H6.
    elim H6; intros; auto.
  - inversion H2.
    elim H9; intros; auto.
    completer.
    elim H6; intros; auto.
    elim H8; intros; auto.
    + left.
      rewrite H12.
      rewrite H14.
      split; elim H19; intros; assumption.
    + right.
      rewrite H14.
      assumption.
  - inversion H2.
    completer.
    + assumption.
    + completer.
      elim H8; intros; auto.
      * elim H19; intros.
        rewrite H10 in H9.
        rewrite H9 in H20.
        discriminate.
      * rewrite H16 in H19.
        discriminate.
Qed.


(* Ejercicio 7.7 *)

Lemma ReadIsolation (s s' : state) (va : vadd) :
  OneStepExecution s (read va) s' -> exists (ma : madd),
    va_mapped_to_ma s va ma
    /\ exists (pg : page),
      (memory s) ma = Some pg
      /\ page_owned_by pg = Os (active_os s). 
Proof.
  intros.
  inversion H.
  inversion H1.
  completer.
  elim H8; intro ma; intros.
  clear H8.
  elim H9; intro pg; intros.
  clear H9.
  completer.
  exists ma.
  split; auto.
  exists pg.
  split; auto.
  inversion H0.
  completer.
  inversion H8.
  elim H14; intro p2m; intros.
  clear H14.
  elim H15; intro ma'; intros.
  clear H15.
  elim H14; intro pg'; intros.
  clear H14.
  elim H15; intro v2m; intros.
  clear H15.
  completer.
  elim H12 with (o := active_os s) (pa := curr_page x) (pm := p2m).
  intros.
  elim H20; intro pg''; intros.
  clear H20.
  completer.
  rewrite H16 in H21.
  injection H21; intros.
  rewrite <- H25 in H22.
  rewrite H17 in H22.
  injection H22; intros.
  rewrite <- H26 in H23.
  elim H13 with (o := active_os s) (pg := pg') (vtm := v2m) (va := va) (ma := ma); intros; completer.
  - rewrite H9 in H28.
    injection H28; intros.
    rewrite H31.
    assumption.
  - assumption.
  - assumption.
Qed.

End Actions.
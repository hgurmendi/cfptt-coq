(*******************************************************************
 * Construcción Formal de Programas en Teoría de Tipos
 * Trabajo práctico final
 * Hernán Gurmendi
 ******************************************************************)

(*******************************************************************
 * Este archivo especifica el estado.
 *
 ******************************************************************)

Section State.

(** Identificadores de OSs e Hypercalls *)

Parameter os_ident : Set.
Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyperv_call: Set.


(* Memoria y direcciones *)

(* Direcciones Virtuales. *)
Parameter vadd: Set.
Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

(** Direcciones de Máquina. *)
Parameter madd :  Set.
Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

(** Direcciones Físicas : 
Los sitemas operativos utilizan este tipo de direcciones para ver regiones de memoriea
contigua. Estos no ven direcciones de máquina. *)
Parameter padd: Set.
Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

(** Memory values. *)
Parameter value: Set.
Parameter value_eq:forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


(* Environment *)
Record context : Set :=
  Context
    {(** una dirección virtual es accesible, i.e. no está reserveda 
         por el Hypervisor *)
       ctxt_vadd_accessible: vadd -> bool;
     (** guest Oss (Confiable/No Confiable) **)
       ctxt_oss : os_ident -> bool
    }.

Inductive exec_mode : Set :=
  | usr
  | svc.

Inductive os_activity : Set :=
  | running
  | waiting.

Record os : Set :=
  OS
    {
      curr_page : padd;
      hcall     : option Hyperv_call;
    }.

Definition oss_map : Set :=
  os_ident -> option os.

Definition hypervisor_map : Set :=
  os_ident -> option (padd -> option madd).

Inductive content : Set :=
  | RW (v : option value)
  | PT (va_to_ma : vadd -> option madd)
  | Other.

Definition isRW (cntnt : content) : bool :=
  match cntnt with
  | RW _ => true
  | _    => false
  end.

Inductive page_owner : Set :=
  | Hyp
  | Os (osi : os_ident)
  | No_Owner.

Record page : Set :=
  Page
    {
      page_content  : content;
      page_owned_by : page_owner;
    }.

Definition system_memory : Set :=
  madd -> option page.

Record state : Set :=
  State
    {
      active_os     : os_ident;       (* id del os activo *)
      aos_exec_mode : exec_mode;      (* modo de ejecución del os activo *)
      aos_activity  : os_activity;    (* estado de ejecución del os activo *)
      oss           : oss_map;        (* información sobre los oss *)
      hypervisor    : hypervisor_map; (* mapeos de memoria fisica a maquina segun os *)
      memory        : system_memory;  (* memoria de la plataforma *)
    }.

(* Actualiza la memoria m en la dirección de máquina ma por la página p *)
Definition update (m : system_memory) (ma : madd) (p : page) : system_memory :=
  fun (ma' : madd) => if (madd_eq ma ma')
                      then Some p
                      else m ma.

End State.

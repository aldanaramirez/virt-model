(*******************************************************************
 * This file specifies the state of the idealised model 
 * of virtualisation.
 ******************************************************************)

Section State.


(***** OS identifier and Hypercalls ******)

Parameter os_ident : Set.
Parameter os_ident_eq : forall oi1 oi2 : os_ident, {oi1 = oi2} + {oi1 <> oi2}.

Parameter Hyperv_call: Set.


(***** Memory and addresses *****)

(* Virtual address. *)
Parameter vadd: Set.
Parameter vadd_eq : forall va1 va2 : vadd, {va1 = va2} + {va1 <> va2}.

(* Machine address. *)
Parameter madd :  Set.
Parameter madd_eq : forall ma1 ma2 : madd, {ma1 = ma2} + {ma1 <> ma2}.

(* Physical address *)
Parameter padd: Set.
Parameter padd_eq : forall pa1 pa2 : padd, {pa1 = pa2} + {pa1 <> pa2}.

(* Memory values. *)
Parameter value: Set.
Parameter value_eq:forall val1 val2 : value, {val1 = val2} + {val1 <> val2}.


(***** Operating Systems *****)

(* OS information *)
Record os : Set :=
  OS
    {curr_page : padd;                (* current physical address *)
     hcall     : option Hyperv_call   (* whether the OS has a pending hypercall to be resolved *)
    }.

(* OS mappings *)
Definition oss_map : Set := os_ident -> option os.


(***** Execution Mode and State *****)

Inductive exec_mode : Set := 
    usr       (* User mode *)
  | svc       (* Supervisor mode *)
  .

Inductive os_activity : Set := 
    running   (* Actively executing a service *)
  | waiting   (* Waiting for the hypervisor to execute a service *)
  .


(***** Memory mappings *****)

(* Hypervisor map *)
Definition hypervisor_map : Set := os_ident -> option (padd -> option madd).

(* Page content *)
Inductive content : Set :=
    RW (v: option value)                  (* a readable/writeable value *)
  | PT (va_to_ma : vadd -> option madd)   (* an OS page table *)
  | Other                                 (* nothing - created but not initialised *)
  .

(* Is readeable/writeable? *)
Definition is_RW (c:content) : Prop :=
  match c with
    RW _ => True
  | _    => False
  end.

(* Page Owner *)
Inductive page_owner : Set :=
    Hyp                                   (* the hypervisor *)
  | Os (osi : os_ident)                   (* a guest OS *)
  | No_owner                              (* none *)
  .

(* Page *)
Record page : Set :=
  PAGE
    {page_content  : content;             (* page content *)
     page_owned_by : page_owner           (* reference to page owner *)
    }.

(* System memory (real platform memory) *)
Definition system_memory : Set := madd -> option page.

(* Update the system memory by assigning a given page to a given machine address *)
Definition update (m : system_memory) (ma: madd) (pg : page) : system_memory :=
  fun (ma' : madd) => if madd_eq ma ma' then Some pg else m ma'.


(***** Environment *****)

Record context : Set :=
  Context
    {ctxt_vadd_accessible : vadd -> bool;    (* an address is accesible if not reserved by hypervisor *)
     ctxt_oss : os_ident -> bool             (* determines if a guest OS is trusted *)
    }.


(***** State *****)

Record State : Set :=
  STATE
    {active_os     : os_ident;          (* the currently active OS *)
     aos_exec_mode : exec_mode;         (* its execution mode *)
     aos_activity  : os_activity;       (* its execution state *)
     oss           : oss_map;           (* information of the guest OSs *)
     hypervisor    : hypervisor_map;    (* hypervisor mapping *)
     memory        : system_memory      (* real platform memory *)
    }.


End State.
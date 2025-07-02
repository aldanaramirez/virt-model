(*******************************************************************
 * This file specifies the actions of the idealised model 
 * of virtualisation as state transformers.
 ******************************************************************)

Require Import VirtModel.State.

Section Action.


(***** Action type *****)

Inductive Action : Set :=
    read  : vadd -> Action
  | write : vadd -> value -> Action
  | chmod : Action.


(***** Action semantics *****)

(* Context *)

Parameter ctxt : context.
Definition os_accesible (va : vadd) : Prop := ctxt_vadd_accessible ctxt va = true.
Definition trusted_os (os : os_ident) : Prop := ctxt_oss ctxt os = true.

Definition va_mapped_to_ma (s : State) (va : vadd) (ma : madd) : Prop :=
  exists (o : os) (hm : padd -> option madd) (ma' : madd) (pg : page) (pt : vadd -> option madd),
     oss s (active_os s) = Some o
  /\ hypervisor s (active_os s) = Some hm
  /\ hm (curr_page o) = Some ma'
  /\ memory s ma' = Some pg
  /\ page_content pg = PT pt
  /\ pt va = Some ma.

(* Preconditions *)

Definition preRead (s : State) (va : vadd) : Prop :=
     os_accesible va
  /\ aos_activity s = running
  /\ exists (ma : madd) (pg : page),
          va_mapped_to_ma s va ma
       /\ memory s ma = Some pg
       /\ is_RW (page_content pg).

Definition preChmod (s : State) : Prop :=
     aos_activity s = waiting
  /\ exists (o : os),
          oss s (active_os s) = Some o
       /\ hcall o = None.

Definition Pre (s : State) (a : Action) : Prop :=
  match a with
    read va    => preRead s va
  | write va _ => preRead s va
  | chmod      => preChmod s
  end.

(* Postconditions *)

Definition postRead (s s' : State) : Prop :=
  s = s'.

Definition postWrite (s : State) (va : vadd) (val : value) (s' : State) : Prop :=
  exists (ma : madd),
     va_mapped_to_ma s va ma
  /\ memory s' = update (memory s) ma (PAGE (RW (Some val)) (Os (active_os s)))
  /\ active_os s = active_os s'
  /\ aos_exec_mode s = aos_exec_mode s'
  /\ aos_activity s = aos_activity s'
  /\ oss s = oss s'
  /\ hypervisor s = hypervisor s'.

Definition postChmod (s s' : State) : Prop :=
     ((trusted_os (active_os s) /\ aos_exec_mode s' = svc) \/ (~ trusted_os (active_os s) /\ aos_exec_mode s' = usr))
  /\ aos_activity s' = running
  /\ active_os s = active_os s'
  /\ oss s = oss s'
  /\ hypervisor s = hypervisor s'
  /\ memory s = memory s'.

Definition Post (s : State) (a : Action) (s' : State) : Prop :=
  match a with
    read _       => postRead s s'
  | write va val => postWrite s va val s'
  | chmod        => postChmod s s'
  end.


(***** Valid State *****)

(* Property iii: if the hypervisor or a trusted OS is running, the processor must be in supervisor mode *)

Definition valid_state_iii (s : State) : Prop :=
     aos_activity s = waiting \/ (aos_activity s = running /\ trusted_os (active_os s))
  -> aos_exec_mode s = svc.

(* Property v: the hypervisor maps an OS physical address to a machine address owned by that same OS. This mapping is injective. *)

Definition injective (hm : padd -> option madd) : Prop :=
  forall (pa1 pa2 : padd) (ma : madd),
    hm pa1 = Some ma -> hm pa2 = Some ma -> pa1 = pa2.

Definition valid_state_v (s : State) : Prop :=
  forall (os : os_ident) (hm : padd -> option madd) (pa : padd) (ma : madd) (pg : page), 
  hypervisor s os = Some hm ->
  hm pa = Some ma ->
  memory s ma = Some pg ->
     page_owned_by pg = Os os
  /\ injective hm.


(* Property vi: all page tables of an OS o map:
   - accessible virtual addresses to pages owned by o, and
   - not accessible virtual addresses to pages owned by the hypervisor *)

Definition valid_state_vi (s : State) : Prop :=
  forall (os : os_ident) (pg : page) (vm : vadd -> option madd) (va : vadd) (ma : madd) (pg' : page),
  page_content pg = PT vm ->
  page_owned_by pg = Os os ->
  vm va = Some ma ->
  memory s ma = Some pg' ->
    (os_accesible va -> page_owned_by pg' = Os os) /\ 
    (~os_accesible va -> page_owned_by pg' = Hyp).


(* Valid state definition *)

Definition valid_state (s : State) : Prop :=
   valid_state_iii s /\ valid_state_v s /\ valid_state_vi s.


(***** One-Step Execution *****)

Inductive one_step_exec : State -> Action -> State -> Prop :=
  one_step : forall (s s' : State) (a : Action), valid_state s -> Pre s a -> Post s a s' -> one_step_exec s a s'.


(***** Theorem: Actions preserve property iii *****)

Theorem actions_preserves_vs_iii :
  forall (s : State) (a : Action) (s' : State), one_step_exec s a s' -> valid_state_iii s'.
Proof.
intros.
inversion_clear H.
inversion_clear H0.
clear H3 H1.
destruct a.
(* Case read *)
- inversion H2.
  rewrite <- H0; assumption.
(* Case write *)
- unfold valid_state_iii; intro.
  unfold valid_state_iii in H.
  inversion_clear H2.
  destruct H1 as [_ [_ [H2 [H3 [H4 _]]]]].
  rewrite <- H3.
  apply H.
  rewrite -> H4, H2.
  assumption.
(* Case chmod *)
- unfold valid_state_iii; intro.
  inversion_clear H2.
  destruct H3 as [H2 [H3 _]].
  elim H1; intros.
  + destruct H4; assumption.
  + destruct H4.
    elim H0; intros.
    * rewrite -> H6 in H2.
      discriminate H2.
    * destruct H6.
      rewrite -> H3 in H4.
      absurd (trusted_os (active_os s')); assumption.
Qed.


(***** Theorem: Read Isolation *****)

Theorem read_isolation :
  forall (s s' : State) (va : vadd),
    one_step_exec s (read va) s' ->
    exists (ma : madd) (pg : page),
         va_mapped_to_ma s va ma
      /\ memory s ma = Some pg
      /\ page_owned_by pg = Os (active_os s).
Proof.
intros.
inversion_clear H.
inversion_clear H1.
destruct H3.
elim H3; clear H3; intros ma H4.
elim H4; clear H4; intros pg H5.
destruct H5 as [H3 [H4 H5]].
exists ma, pg.
split; [idtac | split].
+ assumption.
+ assumption.
+ unfold valid_state in H0.
  destruct H0 as [H0 [H6 H7]].
  unfold valid_state_vi in H7.
  unfold va_mapped_to_ma in H3.
  elim H3; clear H3; intros o H3.
  elim H3; clear H3; intros hm H3.
  elim H3; clear H3; intros ma' H3.
  elim H3; clear H3; intros pg' H3.
  elim H3; clear H3; intros pt H3.
  destruct H3 as [H8 [H9 [H10 [H11 [H12 H13]]]]].
  unfold valid_state_v in H6.
  pose proof (H6 (active_os s) hm (curr_page o) ma' pg' H9 H10 H11) as H14.
  destruct H14 as [H14 H15].
  pose proof (H7 (active_os s) pg' pt va ma pg H12 H14 H13 H4) as H16.
  destruct H16 as [H16 _].
  exact (H16 H).
Qed.


End Action.
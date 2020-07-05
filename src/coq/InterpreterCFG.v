From Coq Require Import
     Morphisms.

Require Import List.
Import ListNotations.
Require Import ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Eq.Eq.

From Vellvm Require Import
     LLVMAst
     LLVMEvents
     Util
     DynamicTypes
     DynamicValues
     Handlers.Handlers
     Refinement.

Section InterpreterCFG.

  (**
   Partial interpretations of the trees produced by the
   denotation of cfg. They differ from the ones of Vellvm programs by
   their event signature, as well as by the lack of a stack of local event.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
   *)

  (**
   NOTE: Can we avoid this duplication w.r.t. [interp_to_Li]?
   *)

  Definition interp_cfg_to_L1 {R} user_intrinsics (t: itree instr_E R)
             (from: block_id) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp L0_trace from in
    L1_trace.

  Definition interp_cfg_to_L2 {R} user_intrinsics (t: itree instr_E R)
             (from: block_id) (g: global_env) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp L0_trace from in
    let L2_trace       := interp_global L1_trace g in
    L2_trace.

  Definition interp_cfg_to_L3 {R} user_intrinsics (t: itree instr_E R)
             (from: block_id) (g: global_env) (l: local_env) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp L0_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local L2_trace l in
    L3_trace.

  Definition interp_cfg_to_L4 {R} user_intrinsics (t: itree instr_E R)
             (from: block_id) (g: global_env) (l: local_env) (m: memory_stack) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp L0_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    L4_trace.

  Definition interp_cfg_to_L5 {R} RR user_intrinsics (t: itree instr_E R)
             (from: block_id) (g: global_env) (l: local_env) (m: memory_stack) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp L0_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    let L5_trace       := model_undef RR L4_trace in
    L5_trace.

  Definition interp_cfg_to_L6 {R} RR user_intrinsics (t: itree instr_E R)
             (from: block_id) (g: global_env) (l: local_env) (m: memory_stack) :=
    let L0_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp L0_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    let L5_trace       := model_undef RR L4_trace in
    model_UB RR L5_trace.

  Lemma interp_cfg_to_L1_bind :
    forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) from, 
      interp_cfg_to_L1 ui (ITree.bind t k) from ≈
                       (ITree.bind (interp_cfg_to_L1 ui t from) (fun '(from',x) => interp_cfg_to_L1 ui (k x) from')).
  Proof.
    intros.
    unfold interp_cfg_to_L1.
    rewrite interp_intrinsics_bind, interp_jmp_bind.
    apply eutt_eq_bind; intros (? & ?); reflexivity.
  Qed.

  Lemma interp_cfg_to_L1_ret : forall ui (R : Type) from (x : R), interp_cfg_to_L1 ui (Ret x) from ≈ Ret (from,x).
  Proof.
    intros; unfold interp_cfg_to_L1.
    rewrite interp_intrinsics_ret, interp_jmp_ret; reflexivity.
  Qed.
  
  Lemma interp_cfg_to_L2_bind :
    forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) from g, 
      interp_cfg_to_L2 ui (ITree.bind t k) from g ≈
      (ITree.bind (interp_cfg_to_L2 ui t from g) (fun '(g',(from',x)) => interp_cfg_to_L2 ui (k x) from' g')).
  Proof.
    intros.
    unfold interp_cfg_to_L2.
    rewrite interp_intrinsics_bind, interp_jmp_bind, interp_global_bind.
    apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
  Qed.

  Lemma interp_cfg_to_L2_ret : forall ui (R : Type) from g (x : R), interp_cfg_to_L2 ui (Ret x) from g ≈ Ret (g,(from,x)).
  Proof.
    intros; unfold interp_cfg_to_L2.
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret; reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_bind :
    forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) from g l,
      interp_cfg_to_L3 ui (ITree.bind t k) from g l ≈
      (ITree.bind (interp_cfg_to_L3 ui t from g l) (fun '(l',(g',(from',x))) => interp_cfg_to_L3 ui (k x) from' g' l')).
  Proof.
    intros.
    unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_bind, interp_jmp_bind, interp_global_bind, interp_local_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
  Qed.

  Lemma interp_cfg_to_L3_ret : forall ui (R : Type) from g l (x : R),
      interp_cfg_to_L3 ui (Ret x) from g l ≈ Ret (l, (g, (from,x))).
  Proof.
    intros; unfold interp_cfg_to_L3.
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret, interp_local_ret; reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_bind :
    forall ui {R S} (t: itree instr_E R) (k: R -> itree instr_E S) from g l m,
      interp_cfg_to_L4 ui (ITree.bind t k) from g l m ≈
      (ITree.bind (interp_cfg_to_L4 ui t from g l m) (fun '(m',(l',(g',(from',x)))) => interp_cfg_to_L4 ui (k x) from' g' l' m')).
  Proof.
    intros.
    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_bind, interp_jmp_bind, interp_global_bind, interp_local_bind, interp_memory_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ? & ?); reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_ret :
    forall ui (R : Type) from g l m (x : R),
      interp_cfg_to_L4 ui (Ret x) from g l m ≈ Ret (m, (l, (g,(from,x)))).
  Proof.
    intros; unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret, interp_local_ret, interp_memory_ret; reflexivity.
  Qed.

  Global Instance eutt_interp_cfg_to_L1 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L1 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L1.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_cfg_to_L2 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L2 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L2.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_cfg_to_L3 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L3 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L3.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_cfg_to_L4 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_cfg_to_L4 T defs).
  Proof.
    repeat intro.
    unfold interp_cfg_to_L4.
    subst; rewrite H.
    reflexivity.
  Qed.

  (* NOTEYZ: This can probably be refined to [eqit eq] instead of [eutt eq], but I don't think it matters to us *)
  Lemma interp_cfg_to_L4_vis (defs: IS.intrinsic_definitions):
    forall T R (e : instr_E T) (k : T -> itree instr_E R) from g l m,
      interp_cfg_to_L4 defs (Vis e k) from g l m ≈ 
                       ITree.bind (interp_cfg_to_L4 defs (trigger e) from g l m)
                       (fun '(m, (l, (g, (from, x))))=> interp_cfg_to_L4 defs (k x) from g l m).
  Proof.
    intros.
    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_vis.
    rewrite interp_jmp_bind, interp_global_bind, interp_local_bind, interp_memory_bind.
    unfold trigger; rewrite interp_intrinsics_vis.
    rewrite interp_jmp_bind, interp_global_bind, interp_local_bind, interp_memory_bind.
    rewrite Eq.bind_bind.
    apply eutt_eq_bind.
    intros (? & ? & ? & ? & ?).
    do 2 match goal with
      |- context[interp ?x ?t] => replace (interp x t) with (interp_intrinsics defs t) by reflexivity
    end. 
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret, interp_local_ret, interp_memory_ret, bind_ret_l.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_bind_trigger (defs: IS.intrinsic_definitions):
    forall T R (e : instr_E T) (k : T -> itree instr_E R) from g l m,
      interp_cfg_to_L4 defs (ITree.bind (trigger e) k) from g l m ≈ 
                       ITree.bind (interp_cfg_to_L4 defs (trigger e) from g l m)
                       (fun '(m, (l, (g, (from, x)))) => interp_cfg_to_L4 defs (k x) from g l m).
  Proof.
    intros.
    rewrite bind_trigger.
    rewrite interp_cfg_to_L4_vis at 1.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_GR : forall defs id from g l m v,
      Maps.lookup id g = Some v ->
      interp_cfg_to_L4 defs (trigger (GlobalRead id)) from g l m ≈ ret (m,(l,(g,(from,v)))).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger.
    cbn; rewrite subevent_subevent.
    rewrite interp_global_bind,interp_global_trigger.
    cbn in *; rewrite LU.
    rewrite interp_local_bind, interp_local_ret, bind_ret_l.
    rewrite interp_global_ret, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_LR : forall defs id from g l m v,
      Maps.lookup id l = Some v ->
      interp_cfg_to_L4 defs (trigger (LocalRead id)) from g l m ≈ ret (m,(l,(g,(from,v)))).
  Proof.
    intros * LU.
    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_trigger.
    cbn; unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger.
    cbn; rewrite subevent_subevent.
    rewrite interp_global_bind, interp_global_trigger.
    cbn; rewrite subevent_subevent.
    rewrite bind_bind, interp_local_bind, interp_local_trigger.
    cbn in *; rewrite LU.
    rewrite 2 bind_ret_l, interp_global_ret, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_LW : forall defs id from g l m v,
      interp_cfg_to_L4 defs (trigger (LocalWrite id v)) from g l m ≈ ret (m,(Maps.add id v l, (g,(from,tt)))).
  Proof.
    intros.
    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_trigger; cbn. 
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_bind, interp_local_bind, interp_memory_bind.
    rewrite interp_global_trigger; cbn.
    rewrite interp_local_bind, interp_local_trigger; cbn.
    rewrite bind_ret_l, interp_local_ret, interp_memory_ret.
    rewrite bind_ret_l, interp_global_ret, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_GW : forall defs id from g l m v,
      interp_cfg_to_L4 defs (trigger (GlobalWrite id v)) from g l m ≈ ret (m,(l,(Maps.add id v g,(from,tt)))).
  Proof.
    intros.
    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_trigger; cbn. 
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_bind,interp_global_trigger; cbn.
    rewrite bind_ret_l, interp_global_ret, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_Load : forall defs t a from g l m val,
      read m a t = inr val ->
      interp_cfg_to_L4 defs (trigger (Load t (DVALUE_Addr a))) from g l m ≈ Ret (m,(l,(g,(from,val)))).
  Proof.
    intros * READ.
    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_bind,interp_global_trigger.
    cbn; rewrite subevent_subevent.
    rewrite bind_bind, interp_local_bind, interp_local_trigger.
    cbn; rewrite bind_bind.
    rewrite interp_memory_bind, subevent_subevent.
    rewrite interp_memory_load; eauto.
    cbn.
    rewrite 3 bind_ret_l, interp_global_ret, interp_local_ret, interp_memory_ret.
    reflexivity.
  Qed.

  Arguments allocate : simpl never.
  Lemma interp_cfg_to_L4_alloca :
    forall (defs : intrinsic_definitions) (m : memory_stack) (t : dtyp) from (g : global_env) l,
      non_void t ->
      exists m' a',
        allocate m t = inr (m', a') /\
        interp_cfg_to_L4 defs (trigger (Alloca t)) from g l m ≈ ret (m', (l, (g, (from,DVALUE_Addr a')))).
  Proof.
    intros * NV.
    unfold interp_cfg_to_L4.
    eapply interp_memory_alloca_exists in NV as [m' [a' [ALLOC INTERP]]].
    exists m'. exists a'.

    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_bind,interp_global_trigger; cbn; rewrite subevent_subevent.
    rewrite bind_bind,interp_local_bind, interp_local_trigger.
    cbn.
    rewrite bind_bind.
    rewrite interp_memory_bind.
    rewrite subevent_subevent, interp_memory_alloca; eauto.
    cbn.
    repeat rewrite bind_ret_l.
    cbn.
    rewrite interp_global_ret,interp_local_ret, interp_memory_ret.
    split; eauto.
    reflexivity.
    Unshelve.
    auto.
  Qed.

  Lemma interp_cfg_to_L4_intrinsic :
    forall (defs : intrinsic_definitions) (m : memory_stack) (τ : dtyp) from (g : global_env) l fn args df res,
      assoc Strings.String.string_dec fn (defs_assoc defs) = Some df ->
      df args = inr res ->
      interp_cfg_to_L4 defs (trigger (Intrinsic τ fn args)) from g l m ≈ ret (m, (l, (g, (from,res)))).
  Proof.
    intros * LUP RES. 
    unfold interp_cfg_to_L4.

    rewrite interp_intrinsics_trigger; cbn.
    rewrite LUP; cbn.
    rewrite RES.

    rewrite interp_jmp_ret, interp_global_ret.
    rewrite interp_local_ret.
    rewrite interp_memory_ret.

    reflexivity.
  Qed.

  Lemma interp_cfg_to_L4_GEP_array : forall defs t a size from g l m val i,
      get_array_cell m a i t = inr val ->
      exists ptr,
        interp_cfg_to_L4 defs (trigger (GEP
                                  (DTYPE_Array size t)
                                  (DVALUE_Addr a)
                                  [DVALUE_I64 (Integers.Int64.repr 0); DVALUE_I64 (Integers.Int64.repr (Z.of_nat i))])) from g l m
                      ≈ Ret (m, (l, (g, (from, DVALUE_Addr ptr)))) /\
        read m ptr t = inr val.
  Proof.
    intros * GET.
    epose proof @interp_memory_GEP_array _ (PickE +' UBE +' DebugE +' FailureE) _ _ _ t _ size _ _ _ GET as [ptr [INTERP READ]].
    exists ptr.
    split; auto.

    unfold interp_cfg_to_L4.
    rewrite interp_intrinsics_trigger; cbn.
    unfold Intrinsics.F_trigger.
    rewrite subevent_subevent.
    rewrite interp_jmp_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_bind, interp_global_trigger; cbn; rewrite subevent_subevent.
    rewrite bind_bind,interp_local_bind, interp_local_trigger.
    cbn; rewrite subevent_subevent.
    repeat rewrite interp_memory_bind.
    rewrite INTERP.
    rewrite bind_bind.
    rewrite bind_ret_l.
    rewrite interp_memory_ret.
    rewrite bind_ret_l.
    rewrite interp_local_bind, interp_local_ret.
    rewrite interp_memory_bind, interp_memory_ret.
    rewrite bind_ret_l.
    rewrite interp_global_ret, interp_local_ret, interp_memory_ret. 
    reflexivity.
  Qed.

End InterpreterCFG.

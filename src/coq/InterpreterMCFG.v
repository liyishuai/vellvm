From Coq Require Import
     Morphisms ZArith.

From ITree Require Import
     ITree
     Basics.Monad
     Events.StateFacts
     Eq.Eq.

From Vellvm Require Import
     Util
     Tactics
     LLVMEvents
     DynamicTypes
     Handlers.Handlers.

Section InterpreterMCFG.

  (**
   Partial interpretations of the trees produced by the denotation of _VIR_ programs.
   The intent is to allow us to only interpret as many layers as needed
   to perform the required semantic reasoning, and lift for free the
   equivalence down the pipe.
   This gives us a _vertical_ notion of compositionality.
   *)

  Definition interp_to_L1 {R} user_intrinsics (t: itree L0 R) from :=
    let uvalue_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace           := interp_jmp uvalue_trace from in
    L1_trace.

  Definition interp_to_L2 {R} user_intrinsics (t: itree L0 R) from g :=
    let uvalue_trace       := interp_intrinsics user_intrinsics t in
    let L1_trace           := interp_jmp uvalue_trace from in
    let L2_trace           := interp_global L1_trace g in
    L2_trace.

  Definition interp_to_L3 {R} user_intrinsics (t: itree L0 R) from g l :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp uvalue_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local_stack (handle_local (v:=uvalue)) L2_trace l in
    L3_trace.

  Definition interp_to_L4 {R} user_intrinsics (t: itree L0 R) from g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp uvalue_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local_stack (handle_local (v:=uvalue)) L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    L4_trace.

  Definition interp_to_L5 {R} RR user_intrinsics (t: itree L0 R) from g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp uvalue_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local_stack (handle_local (v:=uvalue)) L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    let L5_trace       := model_undef RR L4_trace in
    L5_trace.

  Definition interp_to_L6 {R} RR user_intrinsics (t: itree L0 R) from g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp uvalue_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local_stack (handle_local (v:=uvalue)) L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    let L5_trace       := model_undef RR L4_trace in
    model_UB RR L5_trace.

  (* The interpreter stray away from the model starting from the fourth layer: we pick an arbitrary valid path of execution *)
  Definition interp_to_L5_exec {R} user_intrinsics (t: itree L0 R) from g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp uvalue_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local_stack (handle_local (v:=uvalue)) L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    let L5_trace       := exec_undef L4_trace in
    L5_trace.

  Definition interp_to_L6_exec {R} user_intrinsics (t: itree L0 R) from g l m :=
    let uvalue_trace   := interp_intrinsics user_intrinsics t in
    let L1_trace       := interp_jmp uvalue_trace from in
    let L2_trace       := interp_global L1_trace g in
    let L3_trace       := interp_local_stack (handle_local (v:=uvalue)) L2_trace l in
    let L4_trace       := interp_memory L3_trace m in
    let L5_trace       := exec_undef L4_trace in
    exec_UB L5_trace.

  Section Structural_Lemmas.

  Lemma interp_to_L1_bind :
    forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) from, 
      interp_to_L1 ui (ITree.bind t k) from ≈
                       (ITree.bind (interp_to_L1 ui t from) (fun '(from',x) => interp_to_L1 ui (k x) from')).
  Proof.
    intros.
    unfold interp_to_L1.
    rewrite interp_intrinsics_bind, interp_jmp_bind.
    apply eutt_eq_bind; intros (? & ?); reflexivity.
  Qed.

  Lemma interp_to_L1_ret : forall ui (R : Type) from (x : R), interp_to_L1 ui (Ret x) from ≈ Ret (from,x).
  Proof.
    intros; unfold interp_to_L1.
    rewrite interp_intrinsics_ret, interp_jmp_ret; reflexivity.
  Qed.
  
  Lemma interp_to_L2_bind :
    forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) from g, 
      interp_to_L2 ui (ITree.bind t k) from g ≈
      (ITree.bind (interp_to_L2 ui t from g) (fun '(g',(from',x)) => interp_to_L2 ui (k x) from' g')).
  Proof.
    intros.
    unfold interp_to_L2.
    rewrite interp_intrinsics_bind, interp_jmp_bind, interp_global_bind.
    apply eutt_eq_bind; intros (? & ? & ?); reflexivity.
  Qed.

  Lemma interp_to_L2_ret : forall ui (R : Type) from g (x : R), interp_to_L2 ui (Ret x) from g ≈ Ret (g,(from,x)).
  Proof.
    intros; unfold interp_to_L2.
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret; reflexivity.
  Qed.

  Lemma interp_to_L3_bind :
    forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) from g l,
      interp_to_L3 ui (ITree.bind t k) from g l ≈
      (ITree.bind (interp_to_L3 ui t from g l) (fun '(l',(g',(from',x))) => interp_to_L3 ui (k x) from' g' l')).
  Proof.
    intros.
    unfold interp_to_L3.
    rewrite interp_intrinsics_bind, interp_jmp_bind, interp_global_bind, interp_local_stack_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ?); reflexivity.
  Qed.

  Lemma interp_to_L3_ret : forall ui (R : Type) from g l (x : R),
      interp_to_L3 ui (Ret x) from g l ≈ Ret (l, (g, (from,x))).
  Proof.
    intros; unfold interp_to_L3.
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret, interp_local_stack_ret; reflexivity.
  Qed.

  Lemma interp_to_L4_bind :
    forall ui {R S} (t: itree L0 R) (k: R -> itree L0 S) from g l m,
      interp_to_L4 ui (ITree.bind t k) from g l m ≈
      (ITree.bind (interp_to_L4 ui t from g l m) (fun '(m',(l',(g',(from',x)))) => interp_to_L4 ui (k x) from' g' l' m')).
  Proof.
    intros.
    unfold interp_to_L4.
    rewrite interp_intrinsics_bind, interp_jmp_bind, interp_global_bind, interp_local_stack_bind, interp_memory_bind.
    apply eutt_eq_bind; intros (? & ? & ? & ? & ?); reflexivity.
  Qed.

  Lemma interp_to_L4_ret :
    forall ui (R : Type) from g l m (x : R),
      interp_to_L4 ui (Ret x) from g l m ≈ Ret (m, (l, (g,(from,x)))).
  Proof.
    intros; unfold interp_to_L4.
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret; reflexivity.
  Qed.

  Global Instance eutt_interp_to_L1 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_to_L1 T defs).
  Proof.
    repeat intro.
    unfold interp_to_L1.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_to_L2 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_to_L2 T defs).
  Proof.
    repeat intro.
    unfold interp_to_L2.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_to_L3 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_to_L3 T defs).
  Proof.
    repeat intro.
    unfold interp_to_L3.
    subst; rewrite H.
    reflexivity.
  Qed.

  Global Instance eutt_interp_to_L4 (defs: intrinsic_definitions) {T}:
    Proper (eutt Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> Logic.eq ==> eutt Logic.eq) (@interp_to_L4 T defs).
  Proof.
    repeat intro.
    unfold interp_to_L4.
    subst; rewrite H.
    reflexivity.
  Qed.

  Lemma interp_to_L4_vis (defs: IS.intrinsic_definitions):
    forall T R (e : L0 T) (k : T -> itree L0 R) from g l m,
      interp_to_L4 defs (Vis e k) from g l m ≈ 
                   ITree.bind (interp_to_L4 defs (trigger e) from g l m)
                   (fun '(m, (l, (g, (from, x))))=> interp_to_L4 defs (k x) from g l m).
  Proof.
    intros.
    unfold interp_to_L4.
    rewrite interp_intrinsics_vis.
    rewrite interp_jmp_bind,interp_global_bind, interp_local_stack_bind, interp_memory_bind.
    unfold trigger; rewrite interp_intrinsics_vis.
    rewrite interp_jmp_bind, interp_global_bind, interp_local_stack_bind, interp_memory_bind.
    rewrite Eq.bind_bind.
    apply eutt_eq_bind.
    intros (? & ? & ? & ? & ?).
    do 2 match goal with
           |- context[interp ?x ?t] => replace (interp x t) with (interp_intrinsics defs t) by reflexivity
         end. 
    rewrite interp_intrinsics_ret, interp_jmp_ret, interp_global_ret, interp_local_stack_ret, interp_memory_ret, bind_ret_l.
    reflexivity.
  Qed.

  Lemma interp_to_L4_bind_trigger (defs: IS.intrinsic_definitions):
    forall T R (e : L0 T) (k : T -> itree L0 R) from g l m,
      interp_to_L4 defs (ITree.bind (trigger e) k) from g l m ≈ 
                   ITree.bind (interp_to_L4 defs (trigger e) from g l m)
                   (fun '(m, (l, (g, (from, x))))=> interp_to_L4 defs (k x) from g l m).
  Proof.
    intros.
    rewrite bind_trigger.
    rewrite interp_to_L4_vis at 1.
    reflexivity.
  Qed.

  Lemma interp_to_L4_GW : forall defs id from g l m v,
      interp_to_L4 defs (trigger (GlobalWrite id v)) from g l m ≈ ret (m,(l,(Maps.add id v g,(from,tt)))).
  Proof.
    intros.
    unfold interp_to_L4.
    rewrite interp_intrinsics_trigger; cbn. 
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger; cbn.
    rewrite subevent_subevent.
    rewrite interp_global_bind,interp_global_trigger; cbn.
    rewrite bind_ret_l, interp_global_ret, interp_local_stack_ret, interp_memory_ret.
    reflexivity.
  Qed.
  (* TODO: Redo this proof, it has no business unfolding so much *)
  Lemma interp_cfg_to_L4_LM : forall defs t a size offset from g l m v bytes concrete_id,
      get_logical_block m a = Some (LBlock size bytes concrete_id) ->
      deserialize_sbytes (lookup_all_index offset (sizeof_dtyp t) bytes SUndef) t = v ->
      interp_to_L4 defs (trigger (Load t (DVALUE_Addr (a, offset)))) from g l m ≈ Ret (m,(l,(g,(from,v)))).
  Proof.
    intros * LUL EQ.
    unfold interp_to_L4.
    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_bind,interp_global_trigger.
    cbn; rewrite subevent_subevent.
    rewrite bind_bind, interp_local_stack_bind.
    unfold interp_local_stack.
    rewrite interp_state_trigger; cbn; rewrite subevent_subevent.
    rewrite bind_bind.
    rewrite bind_trigger.
    rewrite interp_memory_vis.
    cbn.
    destruct m as [mem memstack]. cbn.
    cbn in LUL. unfold read.
    cbn; rewrite LUL.
    cbn; repeat rewrite bind_ret_l.
    cbn.
    rewrite interp_global_ret, interp_state_ret, interp_memory_ret.
    cbn in *.
    unfold read_in_mem_block. rewrite EQ.
    reflexivity.
  Qed.

  Lemma interp_to_L4_alloca :
    forall (defs : intrinsic_definitions) (m : memory_stack) (t : dtyp) from (g : global_env) l,
      non_void t ->
      exists m' a',
        allocate m t = inr (m', a') /\
        interp_to_L4 defs (trigger (Alloca t)) from g l m ≈ ret (m', (l, (g, (from, DVALUE_Addr a')))).
  Proof.
    intros * NV.
    unfold interp_to_L4.
    eapply interp_memory_alloca_exists in NV as [m' [a' [ALLOC INTERP]]].
    exists m'. exists a'.

    rewrite interp_intrinsics_trigger.
    cbn.
    unfold Intrinsics.F_trigger.
    rewrite interp_jmp_trigger; cbn; rewrite subevent_subevent.
    rewrite interp_global_bind, interp_global_trigger.
    cbn; rewrite bind_bind.
    unfold interp_local_stack.
    rewrite interp_state_bind.
    rewrite interp_state_trigger.
    cbn.
    rewrite bind_bind.
    rewrite interp_memory_bind.
    rewrite subevent_subevent, interp_memory_alloca; eauto.
    cbn.
    repeat rewrite bind_ret_l.
    cbn.
    rewrite interp_global_ret, interp_state_ret, interp_memory_ret.
    split; eauto.
    reflexivity.
    Unshelve.
    auto.
  Qed.

  End Structural_Lemmas.

End InterpreterMCFG.

Ltac fold_L1 :=
  match goal with
    |- context[interp_global (interp_intrinsics ?ui ?p) ?g] =>
    replace (interp_global (interp_intrinsics ui p) g) with
    (interp_to_L1 ui p g) by reflexivity
  end.

Ltac fold_L2 :=
  match goal with
    |- context[interp_local_stack ?h
                                 (interp_global (interp_intrinsics ?ui ?p) ?g) ?l] =>
    replace (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) with
    (interp_to_L2 ui p g l) by reflexivity
  end.

Ltac fold_L3 :=
  match goal with
    |- context[
          interp_memory
            (interp_local_stack ?h
                                (interp_global (interp_intrinsics ?ui ?p) ?g) ?l) ?m] =>
    replace (interp_memory (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) m) with
    (interp_to_L3 ui p g l m) by reflexivity
  end.

Ltac fold_L4 :=
  match goal with
    |- context[
          model_undef ?RR
            (interp_memory
               (interp_local_stack ?h
                                   (interp_global (interp_intrinsics ?ui ?p) ?g) ?l) ?m)] =>
    replace (model_undef ?RR (interp_memory (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) m)) with
    (interp_to_L4 RR ui p g l m) by reflexivity
  end.

Ltac fold_L5 :=
  match goal with
    |- context[model_UB ?RR (model_undef (Logic.eq) (interp_memory (interp_local_stack ?h (interp_global (interp_intrinsics ?ui ?p) ?g) ?l) ?m))] =>
    replace (model_UB ?RR (model_undef (Logic.eq) (interp_memory (interp_local_stack h (interp_global (interp_intrinsics ui p) g) l) m))) with
    (interp_to_L5 RR ui p g l m) by reflexivity
  end.

From Coq Require Import
     Morphisms
     String.

From ExtLib Require Import
     Structures.Monads
     Structures.Maps.

From ITree Require Import
     ITree
     Events.State
     Eq.Eq
     Events.StateFacts
     InterpFacts.

From Vellvm Require Import
     Util
     LLVMEvents
     LLVMAst.


Set Implicit Arguments.
Set Contextual Implicit.

Import MonadNotation.
Import ITree.Basics.Basics.Monads.
Open Scope string_scope.

Section JmpE.

  Definition handle_jmp {E} : JmpE ~> stateT block_id (itree E) :=
    fun _ e from =>
      match e with
      | ComeFrom => ret (from,from)
      | GoTo to  => ret (to,tt)
      end.

  Section PARAMS.
    Variable (E F G H : Type -> Type).
    Notation Effin := (E +' F +' JmpE +' G).
    Notation Effout := (E +' F +' G).

    Definition E_trigger {M} : forall R, E R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition F_trigger {M} : forall R, F R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition G_trigger {M} : forall R , G R -> (stateT M (itree Effout) R) :=
      fun R e m => r <- trigger e ;; ret (m, r).

    Definition interp_jmp_h := (case_ E_trigger (case_ F_trigger (case_ handle_jmp G_trigger))).
    Definition interp_jmp  : itree Effin ~> stateT block_id (itree Effout) :=
      interp_state interp_jmp_h.

    Section Structural_Lemmas.

      Lemma interp_jmp_bind :
        forall (R S : Type) (t : itree Effin R) (k : R -> itree Effin S) s,
          interp_jmp (ITree.bind t k) s ≅
                        ITree.bind (interp_jmp t s) (fun '(s',r) => interp_jmp (k r) s').
      Proof.
        intros.
        unfold interp_jmp.
        setoid_rewrite interp_state_bind.
        apply eq_itree_clo_bind with (UU := Logic.eq).
        reflexivity.
        intros [] [] EQ; inv EQ; reflexivity.
      Qed.

      Lemma interp_jmp_ret :
        forall (R : Type) g (x: R),
          interp_jmp (Ret x: itree Effin R) g ≅ Ret (g,x).
      Proof.
        intros; apply interp_state_ret.
      Qed.

      Lemma interp_jmp_vis_eqit:
        forall (from : block_id) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_jmp (Vis e kk) from ≅ ITree.bind (interp_jmp_h e from) (fun (sx : block_id * X) => Tau (interp_jmp (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_jmp.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_jmp_vis:
        forall (from : block_id) S X (kk : X -> itree Effin S) (e : Effin X),
          interp_jmp (Vis e kk) from ≈ ITree.bind (interp_jmp_h e from) (fun (sx : block_id * X) => interp_jmp (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_jmp_vis_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Lemma interp_jmp_trigger:
        forall (from : block_id) X (e : Effin X),
          interp_jmp (ITree.trigger e) from ≈ interp_jmp_h e from.
      Proof.
        intros.
        unfold interp_jmp.
        rewrite interp_state_trigger.
        reflexivity.
      Qed.

      Lemma interp_jmp_bind_trigger_eqit:
        forall (from : block_id) S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_jmp (ITree.bind (trigger e) kk) from ≅ ITree.bind (interp_jmp_h e from) (fun (sx : block_id * X) => Tau (interp_jmp (kk (snd sx)) (fst sx))).
      Proof.
        intros.
        unfold interp_jmp.
        rewrite bind_trigger.
        setoid_rewrite interp_state_vis.
        reflexivity.
      Qed.

      Lemma interp_jmp_bind_trigger:
        forall (from : block_id) S X
          (kk : X -> itree Effin S)
          (e : Effin X),
          interp_jmp (ITree.bind (trigger e) kk) from ≈ ITree.bind (interp_jmp_h e from) (fun (sx : block_id * X) => interp_jmp (kk (snd sx)) (fst sx)).
      Proof.
        intros.
        rewrite interp_jmp_bind_trigger_eqit.
        apply eutt_eq_bind.
        intros ?; tau_steps; reflexivity.
      Qed.

      Global Instance eutt_interp_jmp {R} :
        Proper (eutt eq ==> eq ==> eutt eq) (@interp_jmp R). 
      Proof.
        repeat intro.
        unfold interp_jmp.
        subst; rewrite H0.
        reflexivity.
      Qed.

    End Structural_Lemmas.

  End PARAMS.

End JmpE.

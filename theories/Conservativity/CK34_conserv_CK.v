Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_seg_completeness.
Require Import CK34_soundness.
Require Import CK4_soundness.
Require Import conserv_prelims.

Require Import Classical.


Section forming_k34_model.

Variable M : model.

Definition k34ireach := fun w v => (@ireachable (@fra M)) w v \/ v = expl.

Lemma k34ireach_refl u : k34ireach u u.
Proof.
unfold k34ireach ; left ; apply ireach_refl.
Qed.

Lemma k34ireach_tran u v w : k34ireach u v -> k34ireach v w -> k34ireach u w.
Proof.
intros. unfold k34ireach in *. destruct H ; subst.
- destruct H0 ; subst ; auto. left. apply ireach_tran with v ; auto.
- destruct H0 ; subst ; auto. right. apply ireach_expl in H ; auto.
Qed.

Lemma k34ireach_expl u : k34ireach (@expl (@fra M)) u -> u = (@expl (@fra M)).
Proof.
intros. unfold k34ireach in *. destruct H ; auto. apply ireach_expl in H ; auto.
Qed.

Definition k34mreach := fun w v => (@mreachable (@fra M)) w v \/ v = expl.

Lemma k34mreach_expl u : k34mreach (@expl (@fra M)) u <-> u = (@expl (@fra M)).
Proof.
split ; intros ; unfold k34mreach in * ; subst ; auto.
destruct H ; subst ; auto. apply mreach_expl in H ; subst ; auto.
Qed.

Instance k34_frame_former : frame :=
      {|
        nodes := (@nodes (@fra M))  ;
        expl := (@expl (@fra M)) ;

        ireachable := k34ireach ;
        ireach_refl := k34ireach_refl ;
        ireach_tran := k34ireach_tran ;
        ireach_expl := k34ireach_expl ;

        (* Modal Relation *)
        mreachable := k34mreach ;
        mreach_expl := k34mreach_expl ;
      |}.

(* The frame we built is a k3_frame. *)

Lemma k34_frame_former_k3_frame : k3_frame k34_frame_former.
Proof.
intros x y z ixy ixz Hy Hz. exfalso. apply Hy. exists expl. split. apply In_singleton.
unfold mreachable. cbn. right ; auto.
Qed.

(* It is also a k4_frame. *)

Lemma k34_frame_former_k4_frame : k4_frame k34_frame_former.
Proof.
intros x y z ixy myz Hz. exists x. exists x. exists y. repeat split ; auto.
1,3: apply ireach_refl.
intros w Hw. right. exists expl. split. apply In_singleton. right ; auto.
Qed.

Definition k34val := val.

Lemma k34persist : forall u v, k34ireach u v -> forall p, k34val u p -> k34val v p.
Proof.
intros. unfold k34val in *. destruct H ; subst ; auto.
- apply persist with u ; auto.
- apply val_expl.
Qed.

Lemma k34val_expl : forall p, k34val expl p.
Proof.
intros. unfold k34val. apply val_expl.
Qed.

Instance k34_model_former : model :=
      {|
        fra := k34_frame_former ;

        val := k34val ;
        persist := k34persist ;
        val_expl := k34val_expl
      |}.

Lemma model_forces_iff_k34_model_forces : forall φ, diam_free φ ->
        forall x, forces M x φ <-> forces k34_model_former x φ.
Proof.
induction φ ; intros Hφ x ; cbn ; split ; intro H ; subst ; auto.
(* And *)
- destruct H. firstorder.
- destruct H. firstorder.
(* Or *)
- destruct H ; firstorder.
- destruct H ; firstorder.
(* Imp *)
- intros. inversion Hφ. destruct H0 ; subst.
  + apply IHφ2 ; auto. apply H ; auto. apply IHφ1 ; auto.
  + pose (Expl φ2 k34_model_former) ; auto.
- intros. inversion Hφ. apply IHφ2 ; auto. apply H. left ; cbn.
  repeat split ; auto. apply IHφ1 ; auto.
(* Box *)
- intros. cbn in Hφ. destruct H0 ; subst.
  + destruct H1 ; subst.
    * apply IHφ ; auto. apply H with v ; auto.
    * pose (Expl φ k34_model_former) ; auto.
  + destruct H1 ; subst.
    * apply mreach_expl in H0 ; subst. pose (Expl φ k34_model_former) ; auto.
    * pose (Expl φ k34_model_former) ; auto.
- intros. cbn in Hφ. apply IHφ ; auto. apply H with v.
  left ; auto. left ; auto.
(* Diam *)
- exfalso ; cbn in * ; auto.
- exfalso ; cbn in * ; auto.
Qed.

End forming_k34_model.


Section CK34_conserv_CK.

Theorem diam_free_eq_CK34_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CK34H_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro H0. apply CK_Strong_Completeness. apply CK34_Soundness in H0.
  intros M T w Hw.
  assert (forall ψ : form, In form Γ ψ -> forces (k34_model_former M) w ψ).
  intros. pose (Hw _ H1). apply model_forces_iff_k34_model_forces in f ; auto.
  apply H0 in H1. apply model_forces_iff_k34_model_forces ; auto.
  split. apply k34_frame_former_k3_frame. apply k34_frame_former_k4_frame.
Qed.

End CK34_conserv_CK.





Section CK4_conserv_CK.

Theorem diam_free_eq_CK4_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CK4H_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro. apply diam_free_eq_CK34_CK ; auto.
  eapply (more_AdAx_more_prv _ _ _ _ _ H0).
  Unshelve. intros A HA. inversion HA ; subst ; auto.
  destruct H1 ; subst. exists x, x0 ; auto.
Qed.

End CK4_conserv_CK.


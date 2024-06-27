Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_seg_completeness.
Require Import CK35_soundness.
Require Import WK_soundness.
Require Import conserv_prelims.

Require Import Classical.


Section forming_k35_model.

Variable M : model.

Definition k35ireach := fun (w v : prod bool (@nodes (@fra M))) =>
      (@ireachable (@fra M)) (snd w) (snd v) /\ v <> (false, (@expl (@fra M))) /\ w <> (false, (@expl (@fra M))) \/
      (w = v).

Lemma k35ireach_refl u : k35ireach u u.
Proof.
destruct u ; unfold k35ireach ; cbn. auto.
Qed.

Lemma k35ireach_tran u v w : k35ireach u v -> k35ireach v w -> k35ireach u w.
Proof.
intros. destruct u, v ,w ; unfold k35ireach in * ; cbn in *. destruct H.
- destruct H. destruct H1 ; subst. destruct H0.
  + destruct H0 ; subst ; auto. destruct H3 ; subst ; auto. left. repeat split ; auto ; apply ireach_tran with n0 ; auto.
  + inversion H0 ; subst. auto.
- destruct H0.
  + destruct H0 ; subst ; auto. destruct H1 ; subst ; auto. inversion H ; subst ; auto.
  + inversion H0 ; subst. inversion H ; subst ; auto.
Qed.

Lemma k35ireach_expl u : k35ireach (true , (@expl (@fra M))) u -> u = (true , (@expl (@fra M))).
Proof.
intros. destruct u ; unfold k35ireach in * ; cbn in *. destruct H ; auto.
destruct H. destruct H0. apply ireach_expl in H. subst ; auto. destruct b ; auto. exfalso ; auto.
Qed.

Definition k35mreach := fun (w v : prod bool (@nodes (@fra M))) =>
      (@mreachable (@fra M)) (snd w) (snd v) /\ (fst v = true  /\ fst w = true).

Lemma k35mreach_expl u : k35mreach (true , (@expl (@fra M))) u <-> u = (true , (@expl (@fra M))).
Proof.
split ; intros ; destruct u ; unfold k35mreach in * ; cbn in *.
- destruct H ; cbn in *. apply mreach_expl in H ; subst. destruct b ; auto. destruct H0. discriminate.
- inversion H ; subst. repeat split ; auto. apply mreach_expl ; auto.
Qed.

Instance k35_frame_former : frame :=
      {|
        nodes := prod bool (@nodes (@fra M))  ;
        expl := (true , (@expl (@fra M))) ;

        ireachable := k35ireach ;
        ireach_refl := k35ireach_refl ;
        ireach_tran := k35ireach_tran ;
        ireach_expl := k35ireach_expl ;

        (* Modal Relation *)
        mreachable := k35mreach ;
        mreach_expl := k35mreach_expl ;
      |}.

(* The frame we built is a k3_frame. *)

Lemma k35_frame_former_k3_frame : k3_frame k35_frame_former.
Proof.
intros x y z ixy ixz Hy Hz. destruct x. exists (false, n).
repeat split.
- unfold ireachable ; cbn ; unfold k35ireach ; cbn. destruct b. left.
  + repeat split. apply ireach_refl.
     intro. inversion H ; subst. apply Hy. exists expl. split. apply In_singleton. unfold mreachable ; cbn.
     unfold k35mreach ; cbn. destruct y ; cbn in *. apply k35ireach_expl in ixy. inversion ixy ; subst.
     repeat split ; auto. apply mreach_expl ; auto. intro. inversion H ; contradiction.
  + right ; auto.
- intros w Hw ; unfold In in *. destruct Hw. destruct H. inversion H ; subst. exfalso.
  destruct H0 ; cbn in *. destruct H1. discriminate.
- intros w Hw ; unfold In in *. destruct Hw. destruct H. inversion H ; subst. exfalso.
  destruct H0 ; cbn in *. destruct H1. discriminate.
Qed.

(* It is also a k5_frame. *)

Lemma k35_frame_former_k5_frame : k5_frame k35_frame_former.
Proof.
intros x Hx. destruct (classic (x = expl)) ; auto. destruct x ; cbn in *. exfalso.
assert (k35ireach (b,n) (false,n)). unfold k35ireach ; cbn ; auto. destruct b ; auto.
left. repeat split ; auto. apply ireach_refl. 1-2: intro H0 ; inversion H0 ; subst ; auto.
apply Hx in H0. destruct H0 ; cbn in *. destruct H1 ; discriminate.
Qed.

Definition k35val := fun (w : prod bool (@nodes (@fra M))) (n : nat) =>
      w <> (false,expl) /\
      (@val M) (snd w) n.

Lemma k35persist : forall u v, k35ireach u v -> forall p, k35val u p -> k35val v p.
Proof.
intros. destruct u,v ; cbn in *. destruct H ; cbn in *.
- destruct H. destruct H1. destruct H0 ; cbn in *. split ; cbn ; auto.
  apply persist with n ; auto.
- inversion H ; subst. destruct H0 ; cbn in * ; split ; auto.
Qed.

Lemma k35val_expl : forall p, k35val expl p.
Proof.
intros. cbn. unfold k35val. cbn ; split ; auto. 
intro. inversion H ; discriminate.
apply val_expl.
Qed.

Instance k35_model_former : model :=
      {|
        fra := k35_frame_former ;

        val := k35val ;
        persist := k35persist ;
        val_expl := k35val_expl
      |}.

Lemma model_forces_iff_k35_model_forces : forall φ, diam_free φ ->
        forall x, forces M x φ <-> forces k35_model_former (true,x) φ.
Proof.
induction φ ; intros Hφ x ; cbn ; split ; intro H ; subst ; auto.
(* Var *)
- split ; cbn ; auto. intro. inversion H0.
- destruct H ; auto.
(* Bot *)
- inversion H ; auto.
(* And *)
- destruct H. firstorder.
- destruct H. firstorder.
(* Or *)
- destruct H ; firstorder.
- destruct H ; firstorder.
(* Imp *)
- intros. inversion Hφ. destruct v. destruct H0 ; cbn in *.
  + destruct H0. destruct H4. apply Persistence with (true,n).
    * apply IHφ2 ; auto. apply H ; auto. apply IHφ1 ; auto.
      apply Persistence with (b,n) ; auto. left ; cbn ; auto. repeat split ; auto.
      apply ireach_refl. intro H6 ; inversion H6.
    * unfold ireachable ; cbn ; unfold k35ireach ; cbn. left. repeat split ; auto.
      apply ireach_refl. intro H6 ; inversion H6.
  + inversion H0 ; subst. apply IHφ2 ; auto. apply H ; auto. apply ireach_refl.
     apply IHφ1 ; auto.
- intros. inversion Hφ. apply IHφ2 ; auto. apply H. left ; cbn.
  repeat split ; auto. 1-2: intro K ; inversion K.
  apply IHφ1 ; auto.
(* Box *)
- intros. cbn in Hφ. destruct v, u, H0 ; cbn in *.
  + destruct H0. destruct H2. destruct H1 ; cbn in *. destruct H4 ; subst.
     apply IHφ ; auto. apply H with n ; auto.
  + inversion H0 ; subst. destruct H1 ; cbn in *. destruct H2 ; subst.
     apply IHφ ; auto. apply H with n ; auto. apply ireach_refl.
- intros. cbn in Hφ. apply IHφ ; auto. apply H with (true,v).
  left ; cbn. repeat split ; auto. 1-2: intro K ; inversion K.
  split ; cbn ; auto.
(* Diam *)
- exfalso ; cbn in * ; auto.
- exfalso ; cbn in * ; auto.
Qed.

End forming_k35_model.


Section CK35_conserv_CK.

Theorem diam_free_eq_CK35_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CK35H_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro H0. apply CK_Strong_Completeness. apply CK35_Soundness in H0.
  intros M T w Hw.
  assert (forall ψ : form, In form Γ ψ -> forces (k35_model_former M) (true,w) ψ).
  intros. pose (Hw _ H1). apply model_forces_iff_k35_model_forces in f ; auto.
  apply H0 in H1. apply model_forces_iff_k35_model_forces ; auto.
  split. apply k35_frame_former_k3_frame. apply k35_frame_former_k5_frame.
Qed.

End CK35_conserv_CK.





Section CK3_conserv_CK.

Theorem diam_free_eq_CK3_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CK3H_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro. apply diam_free_eq_CK35_CK ; auto.
  eapply (more_AdAx_more_prv _ _ _ _ _ H0).
  Unshelve. intros A HA. inversion HA ; subst ; auto.
Qed.

End CK3_conserv_CK.



Section WK_conserv_CK.

Theorem diam_free_eq_WK_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> WKH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro. apply diam_free_eq_CK35_CK ; auto.
  eapply (more_AdAx_more_prv _ _ _ _ _ H0).
  Unshelve. intros A HA. inversion HA ; subst ; auto.
Qed.

End WK_conserv_CK.
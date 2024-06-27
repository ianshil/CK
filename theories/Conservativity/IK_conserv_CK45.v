Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK45_segP_completeness.
Require Import IK_soundness.
Require Import conserv_prelims.

Require Import Classical.


(* Section forming_k345_model.

Variable M : model.

Hypothesis k4_k5_frame : suff_k4_frame (@fra M) /\ suff_k5_frame (@fra M).

Definition k345ireach := fun (w v : prod bool (@nodes (@fra M))) =>
      (@ireachable (@fra M)) (snd w) (snd v) /\ v <> (false, (@expl (@fra M))) /\ w <> (false, (@expl (@fra M))) \/
      (w = v).

Lemma k345ireach_refl u : k345ireach u u.
Proof.
destruct u ; unfold k345ireach ; cbn. auto.
Qed.

Lemma k345ireach_tran u v w : k345ireach u v -> k345ireach v w -> k345ireach u w.
Proof.
intros. destruct u, v ,w ; unfold k345ireach in * ; cbn in *. destruct H.
- destruct H. destruct H1 ; subst. destruct H0.
  + destruct H0 ; subst ; auto. destruct H3 ; subst ; auto. left. repeat split ; auto ; apply ireach_tran with n0 ; auto.
  + inversion H0 ; subst. auto.
- destruct H0.
  + destruct H0 ; subst ; auto. destruct H1 ; subst ; auto. inversion H ; subst ; auto.
  + inversion H0 ; subst. inversion H ; subst ; auto.
Qed.

Lemma k345ireach_expl u : k345ireach (true , (@expl (@fra M))) u -> u = (true , (@expl (@fra M))).
Proof.
intros. destruct u ; unfold k345ireach in * ; cbn in *. destruct H ; auto.
destruct H. destruct H0. apply ireach_expl in H. subst ; auto. destruct b ; auto. exfalso ; auto.
Qed.

Definition k345mreach := fun (w v : prod bool (@nodes (@fra M))) =>
      (@mreachable (@fra M)) (snd w) (snd v) /\ (fst w = true /\ ~ (fst v = false /\ snd v = (@expl (@fra M)))).

Lemma k345mreach_expl u : k345mreach (true , (@expl (@fra M))) u <-> u = (true , (@expl (@fra M))).
Proof.
split ; intros ; destruct u ; unfold k345mreach in * ; cbn in *.
- destruct H ; cbn in *. apply mreach_expl in H ; subst. destruct b ; auto. destruct H0. exfalso ; auto.
- inversion H ; subst. repeat split ; auto. apply mreach_expl ; auto.
  intro. destruct H0 ; discriminate.
Qed.

Instance k345_frame_former : frame :=
      {|
        nodes := prod bool (@nodes (@fra M))  ;
        expl := (true , (@expl (@fra M))) ;

        ireachable := k345ireach ;
        ireach_refl := k345ireach_refl ;
        ireach_tran := k345ireach_tran ;
        ireach_expl := k345ireach_expl ;

        (* Modal Relation *)
        mreachable := k345mreach ;
        mreach_expl := k345mreach_expl ;
      |}.

(* The frame we built is a k3_frame. *)

Lemma k345_frame_former_k3_frame : k3_frame k345_frame_former.
Proof.
intros x y z ixy ixz Hy Hz. destruct x. exists (false, n).
repeat split.
- unfold ireachable ; cbn ; unfold k345ireach ; cbn. destruct b. left.
  + repeat split. apply ireach_refl.
     intro. inversion H ; subst. apply Hy. exists expl. split. apply In_singleton. unfold mreachable ; cbn.
     unfold k345mreach ; cbn. destruct y ; cbn in *. apply k345ireach_expl in ixy. inversion ixy ; subst.
     repeat split ; auto. apply mreach_expl ; auto. intro. destruct H0 ; discriminate.
     intro. inversion H ; contradiction.
  + right ; auto.
- intros w Hw ; unfold In in *. destruct Hw. destruct H. inversion H ; subst. exfalso.
  destruct H0 ; cbn in *. destruct H1. discriminate.
- intros w Hw ; unfold In in *. destruct Hw. destruct H. inversion H ; subst. exfalso.
  destruct H0 ; cbn in *. destruct H1. discriminate.
Qed.

(* And it is a k5_frame. *)

Lemma k345_frame_former_k5_frame : suff_k5_frame k345_frame_former.
Proof.
intros x Hx. apply mreach_expl. unfold mreachable ; cbn.
unfold k345mreach ; cbn ; auto. repeat split ; auto. destruct x ; cbn.
destruct k4_k5_frame. destruct Hx ; cbn in *. destruct H2 ; subst. apply mreach_expl.
apply H0 ; auto. intro. destruct H ; subst. destruct Hx. destruct x ; destruct H2 ; cbn in * ; subst.
discriminate.
Qed.

(* It is also a k4_frame. *)

Lemma k345_frame_former_k4_frame : suff_k4_frame k345_frame_former.
Proof.
intros x y z mxy iyz. destruct y, z, x ; cbn in *.
assert (mreachable n1 n).
{ destruct mxy ; cbn in * ; auto. }
assert (ireachable n n0).
{ destruct iyz ; cbn in *. destruct H0. destruct H1. auto. inversion H0 ; subst. apply ireach_refl. }
destruct k4_k5_frame.
destruct (H1 _ _ _ H H0) as (u & Hu0 & Hu1 & Hu2).
destruct mxy ; cbn in *. destruct H4 ; subst ; cbn in *.
exists (true,u). split ; auto.
- left ; cbn ; repeat split ; auto. 1-2: intro K ; inversion K.
- split.
  + intros w Hw ; unfold In in * ; cbn in *. destruct Hw ; subst. destruct H4.
     inversion H4 ; subst. destruct w ; cbn in *.
     destruct Hu1 with n2. unfold In. exists u. split. apply In_singleton.
     destruct H6 ; cbn in *. destruct H6 ; auto. inversion H6 ; subst. apply ireach_refl.
     destruct H7. destruct H7. destruct H7. inversion H7 ; subst.
     admit. (* exists (true, x). split.
     * exists (b0, x0). split. apply In_singleton. left ; cbn ; repeat split ; auto. intro K ; inversion K.
       intro. inversion H10 ; subst.
     * split ; cbn ; auto. split ; auto. destruct H5 ; cbn in *. destruct H5. destruct H9.

destruct b ; split ; auto.
       exfalso. destruct H6 ; cbn in *. destruct H6. destruct H10.



     destruct H5 ; cbn in *.
     destruct H5. destruct H6. destruct Hu1 with n2 ; auto. exists u. split ; auto.
     apply In_singleton. destruct H8. destruct H8. destruct H8. inversion H8 ; subst.
  

  destruct Hu1 with n2. unfold In. exists u. split. apply In_singleton.
  destruct H6 ; cbn in *. destruct H6 ; auto. inversion H6 ; subst. apply ireach_refl.
  destruct H7. destruct H7. destruct H7. inversion H7 ; subst.
  exists (true, x). split. *)
  + repeat split ; cbn ; auto. intro. destruct H4 ; subst.
     destruct iyz ; cbn in *. destruct H4. destruct H6. auto. inversion H4 ; auto.


exists (b0, x0). split. apply In_singleton.
     destruct b0 ; cbn ; auto. left ; cbn ; repeat split ; auto. 1-2: intro K ; inversion K.
     left ; cbn. repeat split ; auto. 1-2: intro K ; inversion K ; subst. destruct iyz ; cbn in * ; subst ; auto.
     destruct H10. destruct H11. auto. inversion H10 ; subst. destruct H ; cbn in * ; auto.
     destruct H11 ; discriminate.
  + split ; cbn ; auto. destruct b2 ; split ; auto.
     exfalso. destruct H6 ; cbn in *. destruct H6. destruct H10.


destruct iyz ; cbn in *.
- destruct H6. destruct H7. destruct H0 ; cbn in *. destruct H0. destruct H9.
  

exists (true,u). repeat split ; auto.
- apply k345ireach_tran with (true, n1). destruct b1 ; cbn in * ; auto.
  left ; cbn ; auto. split. apply ireach_refl. split ; intro K ; inversion K.
  left ; cbn ; auto. split. apply ireach_refl. split ; intro K ; inversion K ; subst.
  destruct H ; cbn in *. destruct H5 ; discriminate.
  left ; cbn ; auto. repeat split ; auto. 1-2: intro K ; inversion K.
- intros w Hw ; unfold In in * ; cbn in *. destruct Hw ; subst. destruct H5.
  inversion H5 ; subst. destruct w ; cbn in *.
  destruct Hu1 with n2. unfold In. exists u. split. apply In_singleton.
  destruct H6 ; cbn in *. destruct H6 ; auto. inversion H6 ; subst. apply ireach_refl.
  destruct H7. destruct H7. destruct H7. inversion H7 ; subst.
  exists (true, x). split.
  + exists (b0, x0). split. apply In_singleton.
     destruct b0 ; cbn ; auto. left ; cbn ; repeat split ; auto. 1-2: intro K ; inversion K.
     left ; cbn. repeat split ; auto. 1-2: intro K ; inversion K ; subst. destruct iyz ; cbn in * ; subst ; auto.
     destruct H10. destruct H11. auto. inversion H10 ; subst. destruct H ; cbn in * ; auto.
     destruct H11 ; discriminate.
  + split ; cbn ; auto. destruct b2 ; split ; auto.
     exfalso. destruct H6 ; cbn in *. destruct H6. destruct H10.
     

  exists (true, x). split.
  + exists (b0, x0). split. apply In_singleton.
     destruct b0 ; cbn ; auto. left ; cbn ; repeat split ; auto. 1-2: intro K ; inversion K.
     left ; cbn. repeat split ; auto. 1-2: intro K ; inversion K ; subst. destruct iyz ; cbn in * ; subst ; auto.
     destruct H10. destruct H11. auto. inversion H10 ; subst. destruct H ; cbn in * ; auto.
     destruct H11 ; discriminate.
  + split ; cbn ; auto. destruct b2 ; split ; auto.
     exfalso. destruct H6 ; cbn in *. destruct H6. destruct H10.

 inversion H10 ; subst. destruct H.
Qed.

Definition k345val := fun (w : prod bool (@nodes (@fra M))) (n : nat) =>
      w <> (false,expl) /\
      (@val M) (snd w) n.

Lemma k345persist : forall u v, k345ireach u v -> forall p, k345val u p -> k345val v p.
Proof.
intros. destruct u,v ; cbn in *. destruct H ; cbn in *.
- destruct H. destruct H1. destruct H0 ; cbn in *. split ; cbn ; auto.
  apply persist with n ; auto.
- inversion H ; subst. destruct H0 ; cbn in * ; split ; auto.
Qed.

Lemma k345val_expl : forall p, k345val expl p.
Proof.
intros. cbn. unfold k345val. cbn ; split ; auto. 
intro. inversion H ; discriminate.
apply val_expl.
Qed.

Instance k345_model_former : model :=
      {|
        fra := k345_frame_former ;

        val := k345val ;
        persist := k345persist ;
        val_expl := k345val_expl
      |}.

Lemma model_forces_iff_k345_model_forces : forall φ, diam_free φ ->
        forall x, forces M x φ <-> forces k345_model_former (true,x) φ.
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
    * unfold ireachable ; cbn ; unfold k345ireach ; cbn. left. repeat split ; auto.
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

End forming_k345_model.


Section CK345_conserv_CK.

Theorem diam_free_eq_CK345_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CK345H_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro H0. apply CK_Strong_Completeness. apply CK345_Soundness in H0.
  intros M T w Hw.
  assert (forall ψ : form, In form Γ ψ -> forces (k345_model_former M) (true,w) ψ).
  intros. pose (Hw _ H1). apply model_forces_iff_k345_model_forces in f ; auto.
  apply H0 in H1. apply model_forces_iff_k345_model_forces ; auto.
  split. apply k345_frame_former_k3_frame. apply k345_frame_former_k5_frame.
Qed.

End CK345_conserv_CK.





Section CK3_conserv_CK.

Theorem diam_free_eq_CK3_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CK3H_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro. apply diam_free_eq_CK345_CK ; auto.
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
- intro. apply diam_free_eq_CK345_CK ; auto.
  eapply (more_AdAx_more_prv _ _ _ _ _ H0).
  Unshelve. intros A HA. inversion HA ; subst ; auto.
Qed.

End WK_conserv_CK. *)
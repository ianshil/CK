Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_seg_completeness.
Require Import CK_Cd_Nd_soundness.
Require Import WK_soundness.


Section forming_CdNd_model.

(* To show that the logic CK + Cd + Nd is diamond-free conservative over CK
    we show that one can transform a CK model into a CK + Cd + Nd model
    which satisfies the same diamond-free formulas. 

    We proceed to define the formation of a CK + Cd + Nd model 
    from a CK model. *)

Variable M : model.

(* Intuitionistic relation. *)

Definition CdNdireach := fun (w v : prod bool (@nodes (@fra M))) =>
      (@ireachable (@fra M)) (snd w) (snd v) /\ v <> (false, (@expl (@fra M))) /\ w <> (false, (@expl (@fra M))) \/
      (w = v).

Lemma CdNdireach_refl u : CdNdireach u u.
Proof.
destruct u ; unfold CdNdireach ; cbn. auto.
Qed.

Lemma CdNdireach_tran u v w : CdNdireach u v -> CdNdireach v w -> CdNdireach u w.
Proof.
intros. destruct u, v ,w ; unfold CdNdireach in * ; cbn in *. destruct H.
- destruct H. destruct H1 ; subst. destruct H0.
  + destruct H0 ; subst ; auto. destruct H3 ; subst ; auto. left. repeat split ; auto ; apply ireach_tran with n0 ; auto.
  + inversion H0 ; subst. auto.
- destruct H0.
  + destruct H0 ; subst ; auto. destruct H1 ; subst ; auto. inversion H ; subst ; auto.
  + inversion H0 ; subst. inversion H ; subst ; auto.
Qed.

Lemma CdNdireach_expl u : CdNdireach (true , (@expl (@fra M))) u -> u = (true , (@expl (@fra M))).
Proof.
intros. destruct u ; unfold CdNdireach in * ; cbn in *. destruct H ; auto.
destruct H. destruct H0. apply ireach_expl in H. subst ; auto. destruct b ; auto. exfalso ; auto.
Qed.

(* Modal relation. *)

Definition CdNdmreach := fun (w v : prod bool (@nodes (@fra M))) =>
      (@mreachable (@fra M)) (snd w) (snd v) /\ (fst v = true  /\ fst w = true).

Lemma CdNdmreach_expl u : CdNdmreach (true , (@expl (@fra M))) u <-> u = (true , (@expl (@fra M))).
Proof.
split ; intros ; destruct u ; unfold CdNdmreach in * ; cbn in *.
- destruct H ; cbn in *. apply mreach_expl in H ; subst. destruct b ; auto. destruct H0. discriminate.
- inversion H ; subst. repeat split ; auto. apply mreach_expl ; auto.
Qed.

Instance CdNd_frame_former : frame :=
      {|
        nodes := prod bool (@nodes (@fra M))  ;
        expl := (true , (@expl (@fra M))) ;

        ireachable := CdNdireach ;
        ireach_refl := CdNdireach_refl ;
        ireach_tran := CdNdireach_tran ;
        ireach_expl := CdNdireach_expl ;

        (* Modal Relation *)
        mreachable := CdNdmreach ;
        mreach_expl := CdNdmreach_expl ;
      |}.

(* The frame we built is a Cd_frame. *)

Lemma CdNd_frame_former_Cd_frame : Cd_frame CdNd_frame_former.
Proof.
intros x y z ixy ixz Hy Hz. destruct x. exists (false, n).
repeat split.
- unfold ireachable ; cbn ; unfold CdNdireach ; cbn. destruct b. left.
  + repeat split. apply ireach_refl.
     intro. inversion H ; subst. apply Hy. exists expl. split. apply In_singleton. unfold mreachable ; cbn.
     unfold CdNdmreach ; cbn. destruct y ; cbn in *. apply CdNdireach_expl in ixy. inversion ixy ; subst.
     repeat split ; auto. apply mreach_expl ; auto. intro. inversion H ; contradiction.
  + right ; auto.
- intros w Hw ; unfold In in *. destruct Hw. destruct H. inversion H ; subst. exfalso.
  destruct H0 ; cbn in *. destruct H1. discriminate.
- intros w Hw ; unfold In in *. destruct Hw. destruct H. inversion H ; subst. exfalso.
  destruct H0 ; cbn in *. destruct H1. discriminate.
Qed.

(* It is also a Nd_frame. *)

Lemma CdNd_frame_former_Nd_frame : Nd_frame CdNd_frame_former.
Proof.
intros x Hx. destruct (LEM (x = expl)) ; auto. destruct x ; cbn in *. exfalso.
assert (CdNdireach (b,n) (false,n)). unfold CdNdireach ; cbn ; auto. destruct b ; auto.
left. repeat split ; auto. apply ireach_refl. 1-2: intro H0 ; inversion H0 ; subst ; auto.
apply Hx in H0. destruct H0 ; cbn in *. destruct H1 ; discriminate.
Qed.

(* We now define the valuation. *)

Definition CdNdval := fun (w : prod bool (@nodes (@fra M))) (n : nat) =>
      w <> (false,expl) /\
      (@val M) (snd w) n.

Lemma CdNdpersist : forall u v, CdNdireach u v -> forall p, CdNdval u p -> CdNdval v p.
Proof.
intros. destruct u,v ; cbn in *. destruct H ; cbn in *.
- destruct H. destruct H1. destruct H0 ; cbn in *. split ; cbn ; auto.
  apply persist with n ; auto.
- inversion H ; subst. destruct H0 ; cbn in * ; split ; auto.
Qed.

Lemma CdNdval_expl : forall p, CdNdval expl p.
Proof.
intros. cbn. unfold CdNdval. cbn ; split ; auto. 
intro. inversion H ; discriminate.
apply val_expl.
Qed.

(* We finally have our CK + Cd + Nd model. *)

Instance CdNd_model_former : model :=
      {|
        fra := CdNd_frame_former ;

        val := CdNdval ;
        persist := CdNdpersist ;
        val_expl := CdNdval_expl
      |}.

(* We can show an agreement results on diamond-free formulas
    between both models. *)

Lemma model_forces_iff_CdNd_model_forces : forall φ, diam_free φ ->
        forall x, forces M x φ <-> forces CdNd_model_former (true,x) φ.
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
    * unfold ireachable ; cbn ; unfold CdNdireach ; cbn. left. repeat split ; auto.
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

End forming_CdNd_model.


Section CKCdNd_conserv_CK.

(* We can finally show that the logic CK and CK + Cd + Nd agree on
    diamond-free formulas. *)

Theorem diam_free_eq_CKCdNd_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CKCdNdH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro H0. apply CK_Strong_Completeness. apply CKCdNd_Soundness in H0.
  intros M T w Hw.
  assert (forall ψ : form, In form Γ ψ -> forces (CdNd_model_former M) (true,w) ψ).
  intros. pose (Hw _ H1). apply model_forces_iff_CdNd_model_forces in f ; auto.
  apply H0 in H1. apply model_forces_iff_CdNd_model_forces ; auto.
  split. apply CdNd_frame_former_Cd_frame. apply CdNd_frame_former_Nd_frame.
Qed.

End CKCdNd_conserv_CK.


Section CKCdNdb_conserv_CK.

(* We can also show that the logic CK + Cd + Nd extends CK + Cd + Ndb. *)

Lemma CKCdNd_extends_CKCdNdb : forall Γ φ, CKCdNdbH_prv Γ φ -> CKCdNdH_prv Γ φ.
Proof.
intros Γ φ H ; induction H.
- apply Id ; auto.
- destruct H ; subst. apply Ax ; auto. destruct H ; subst.
  apply Ax ; auto. eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; right ; right ; reflexivity. apply EFQ.
- eapply MP. apply IHextCKH_prv1 ; intros ; subst ; auto. destruct H0 ; subst ; auto.
- apply Nec ; auto.
Qed.

(* Which we use to show that the logic CK and CK + Cd + Ndb also agree on
    diamond-free formulas. *)

Theorem diam_free_eq_CKCdNdb_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CKCdNdbH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro H0. apply diam_free_eq_CKCdNd_CK ; auto. apply CKCdNd_extends_CKCdNdb ; auto.
Qed.

End CKCdNdb_conserv_CK.


Section CKCd_conserv_CK.

(* This agreement also holds between CK and CK + Cd. *)

Theorem diam_free_eq_CKCd_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CKCdH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro. apply diam_free_eq_CKCdNd_CK ; auto.
  eapply (more_AdAx_more_prv _ _ _ _ _ H0).
  Unshelve. intros A HA. inversion HA ; subst ; auto.
Qed.

End CKCd_conserv_CK.



Section WK_conserv_CK.

(* Between CK and WK as well. *)

Theorem diam_free_eq_WK_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> WKH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro. apply diam_free_eq_CKCdNd_CK ; auto.
  eapply (more_AdAx_more_prv _ _ _ _ _ H0).
  Unshelve. intros A HA. inversion HA ; subst ; auto.
Qed.

End WK_conserv_CK.



Section CKNdb_conserv_CK.

(* As WK extends CK + Ndb. *)

Lemma WK_extends_CKNdb : forall Γ φ, CKNdbH_prv Γ φ -> WKH_prv Γ φ.
Proof.
intros Γ φ H ; induction H.
- apply Id ; auto.
- destruct H ; subst. apply Ax ; auto.
  eapply MP. eapply MP. apply Imp_trans.
  apply Ax ; right ; reflexivity. apply EFQ.
- eapply MP. apply IHextCKH_prv1 ; intros ; subst ; auto. destruct H0 ; subst ; auto.
- apply Nec ; auto.
Qed.

(* We have that CK and CK + Ndb agree on diamond-free formulas. *)

Theorem diam_free_eq_CKNdb_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CKNdbH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro H0. apply diam_free_eq_WK_CK ; auto. apply WK_extends_CKNdb ; auto.
Qed.

End CKNdb_conserv_CK.
Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_seg_completeness.
Require Import CK_Cd_Idb_soundness.
Require Import CK_Idb_soundness.


Section forming_CdIdb_model.

(* To show that the logic CK + Idb is diamond-free conservative over CK
    we show that one can transform a CK model into a CK + Idb model
    which satisfies the same diamond-free formulas. 

    We proceed to define the formation of a CK + Idb model
    from a CK model. *)

Variable M : model.

(* Intuitionistic relation. *)

Definition CdIdbireach := fun w v => (@ireachable (@fra M)) w v \/ v = expl.

Lemma CdIdbireach_refl u : CdIdbireach u u.
Proof.
unfold CdIdbireach ; left ; apply ireach_refl.
Qed.

Lemma CdIdbireach_tran u v w : CdIdbireach u v -> CdIdbireach v w -> CdIdbireach u w.
Proof.
intros. unfold CdIdbireach in *. destruct H ; subst.
- destruct H0 ; subst ; auto. left. apply ireach_tran with v ; auto.
- destruct H0 ; subst ; auto. right. apply ireach_expl in H ; auto.
Qed.

Lemma CdIdbireach_expl u : CdIdbireach (@expl (@fra M)) u -> u = (@expl (@fra M)).
Proof.
intros. unfold CdIdbireach in *. destruct H ; auto. apply ireach_expl in H ; auto.
Qed.

(* Modal relation. *)

Definition CdIdbmreach := fun w v => (@mreachable (@fra M)) w v \/ v = expl.

Lemma CdIdbmreach_expl u : CdIdbmreach (@expl (@fra M)) u <-> u = (@expl (@fra M)).
Proof.
split ; intros ; unfold CdIdbmreach in * ; subst ; auto.
destruct H ; subst ; auto. apply mreach_expl in H ; subst ; auto.
Qed.

Instance CdIdb_frame_former : frame :=
      {|
        nodes := (@nodes (@fra M))  ;
        expl := (@expl (@fra M)) ;

        ireachable := CdIdbireach ;
        ireach_refl := CdIdbireach_refl ;
        ireach_tran := CdIdbireach_tran ;
        ireach_expl := CdIdbireach_expl ;

        (* Modal Relation *)
        mreachable := CdIdbmreach ;
        mreach_expl := CdIdbmreach_expl ;
      |}.

(* The frame we built is a suff_Cd_frame. *)

Lemma CdIdb_frame_former_strong_Cd_frame : strong_Cd_frame CdIdb_frame_former.
Proof.
intros x y z ixy mxz. exists expl ; split ; right ; auto.
Qed.

(* It is also a Idb_frame. *)

Lemma CdIdb_frame_former_Idb_frame : Idb_frame CdIdb_frame_former.
Proof.
intros x y z ixy myz Hz. exists x. exists y. repeat split ; auto.
apply ireach_refl.
intros w Hw. right. exists expl. split. apply In_singleton. right ; auto.
Qed.

(* We now define the valuation. *)

Definition CdIdbval := val.

Lemma CdIdbpersist : forall u v, CdIdbireach u v -> forall p, CdIdbval u p -> CdIdbval v p.
Proof.
intros. unfold CdIdbval in *. destruct H ; subst ; auto.
- apply persist with u ; auto.
- apply val_expl.
Qed.

Lemma CdIdbval_expl : forall p, CdIdbval expl p.
Proof.
intros. unfold CdIdbval. apply val_expl.
Qed.

(* We finally have our CK + Cd + Idb model. *)

Instance CdIdb_model_former : model :=
      {|
        fra := CdIdb_frame_former ;

        val := CdIdbval ;
        persist := CdIdbpersist ;
        val_expl := CdIdbval_expl
      |}.

(* We can show an agreement results on diamond-free formulas
    between both models. *)

Lemma model_forces_iff_CdIdb_model_forces : forall φ, diam_free φ ->
        forall x, forces M x φ <-> forces CdIdb_model_former x φ.
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
  + pose (Expl φ2 CdIdb_model_former) ; auto.
- intros. inversion Hφ. apply IHφ2 ; auto. apply H. left ; cbn.
  repeat split ; auto. apply IHφ1 ; auto.
(* Box *)
- intros. cbn in Hφ. destruct H0 ; subst.
  + destruct H1 ; subst.
    * apply IHφ ; auto. apply H with v ; auto.
    * pose (Expl φ CdIdb_model_former) ; auto.
  + destruct H1 ; subst.
    * apply mreach_expl in H0 ; subst. pose (Expl φ CdIdb_model_former) ; auto.
    * pose (Expl φ CdIdb_model_former) ; auto.
- intros. cbn in Hφ. apply IHφ ; auto. apply H with v.
  left ; auto. left ; auto.
(* Diam *)
- exfalso ; cbn in * ; auto.
- exfalso ; cbn in * ; auto.
Qed.

End forming_CdIdb_model.


Section CKCdIdb_conserv_CK.

(* We can finally show that the logic CK and CK + Cd + Idb agree on
    diamond-free formulas. *)

Theorem diam_free_eq_CKCdIdb_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CKCdIdbH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro H0. apply CK_Strong_Completeness. apply CKCdIdb_Soundness in H0.
  intros M T w Hw.
  assert (forall ψ : form, In form Γ ψ -> forces (CdIdb_model_former M) w ψ).
  intros. pose (Hw _ H1). apply model_forces_iff_CdIdb_model_forces in f ; auto.
  apply H0 in H1. apply model_forces_iff_CdIdb_model_forces ; auto.
  split. apply suff_impl_Cd. apply strong_impl_suff_Cd.
  apply CdIdb_frame_former_strong_Cd_frame. apply CdIdb_frame_former_Idb_frame.
Qed.

End CKCdIdb_conserv_CK.





Section CKIdb_conserv_CK.

(* This implies that CK and CK + Idb also agree on diamond-free formulas. *)

Theorem diam_free_eq_CKIdb_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ <-> CKIdbH_prv Γ φ.
Proof.
intros. split.
- intro D. apply more_AdAx_more_prv with (fun x => False) ; auto.
  intros A F ; contradiction.
- intro. apply diam_free_eq_CKCdIdb_CK ; auto.
  eapply (more_AdAx_more_prv _ _ _ _ _ H0).
  Unshelve. intros A HA. inversion HA ; subst ; auto.
  destruct H1 ; subst. exists x, x0 ; auto.
Qed.

End CKIdb_conserv_CK.


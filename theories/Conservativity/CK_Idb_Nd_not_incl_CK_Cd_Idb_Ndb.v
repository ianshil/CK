Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.
Require Import Bool.
Require Import Btauto.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_Cd_Idb_Ndb_soundness.
Require Import CK_Idb_Nd_not_conserv_CK.


Section CKIdbNd_not_incl_CKCdIdbNdb.

(* The bf frame from the file CK_Idb_Nd_not_conserv_CK
    satisfies the following properties. *)

Lemma bF_strong_Cd : strong_Cd_frame bF.
Proof.
intros w v u iwv mwu.
unfold mreachable in mwu ; cbn in mwu ; unfold bmreach in mwu.
unfold ireachable in iwv ; cbn in iwv ; unfold bireach in iwv.
destruct w ; destruct u ; destruct v ; cbn in * ; auto.
destruct (eqb b b3) eqn:E0; cbn in *.
destruct (eqb b0 b4) eqn:E1; cbn in *.
destruct b1 ; destruct b2 ; cbn in * ; auto ; try contradiction.
destruct b ; cbn in * ; auto.
destruct b3 ; cbn in * ; auto. exists (true,true).
split. destruct b4 ; cbn ; auto. cbn ; auto. discriminate.
contradiction. destruct b ; cbn in * ; try contradiction.
destruct b0 ; cbn in * ; try contradiction.
destruct b3 ; cbn in * ; try discriminate.
destruct b4 ; cbn in * ; try discriminate.
exists (false,true) ; split ; cbn ; auto.
destruct b ; cbn in * ; try contradiction.
destruct b0 ; cbn in * ; try contradiction.
contradiction. destruct b3 ; cbn in * ; try contradiction.
destruct (eqb b0 b4) eqn:E1 ; cbn in * ; auto.
destruct b1 ; cbn in * ; try contradiction.
destruct b2 ; cbn in * ; try contradiction.
destruct b ; cbn in * ; try contradiction. discriminate.
destruct b ; cbn in * ; try contradiction.
destruct b0 ; cbn in * ; try contradiction.
destruct b2 ; cbn in * ; try contradiction.
destruct b4 ; cbn in * ; try contradiction. discriminate.
exists (true,true) ; cbn ; auto.
contradiction.
Qed.

Lemma bF_suff_Ndb : suff_Ndb_frame bF.
Proof.
intros w mwe v mwv.
unfold mreachable in mwe ; cbn in mwe ; unfold bmreach in mwe.
unfold mreachable in mwv ; cbn in mwv ; unfold bmreach in mwv.
destruct w ; destruct v ; cbn in * ; auto.
destruct b1 ; destruct b2 ; cbn in * ; auto ; try contradiction.
destruct b ; cbn in * ; try contradiction.
destruct b ; cbn in * ; try contradiction.
Qed.

Lemma bF_suff_Idb : suff_Idb_frame bF.
Proof.
intros w v u mwv ivu.
unfold mreachable in mwv ; cbn in mwv ; unfold bmreach in mwv.
unfold ireachable in ivu ; cbn in ivu ; unfold bireach in ivu.
destruct w ; destruct v ; destruct u ; cbn in * ; auto.
destruct b1 ; destruct b2 ; cbn in * ; auto ; try contradiction.
destruct b ; cbn in * ; try contradiction.
destruct b3 ; cbn in * ; try contradiction.
destruct b4 ; cbn in * ; try contradiction.
- exists (true,b0) ; repeat split ; auto.
  + destruct b0 ; auto.
  + intros p Hp. destruct Hp. destruct x. destruct H. inversion H ; subst.
     unfold ireachable in H0 ; cbn in H0 ; unfold bireach in H0 ; cbn in *.
     destruct p ; cbn in *. destruct b ; cbn in * ; try contradiction.
     exists (true,true) ; split ; auto. exists (true,true) ; split ; auto.
     apply In_singleton.
- destruct b ; cbn in * ; try contradiction.
  destruct b0 ; cbn in * ; try contradiction.
  destruct b3 ; cbn in * ; try contradiction.
  destruct b4 ; cbn in * ; try contradiction.
  exists (true,false). repeat split ; auto.
  intros p Hp. destruct Hp. destruct x. destruct H. inversion H ; subst.
  unfold ireachable in H0 ; cbn in H0 ; unfold bireach in H0 ; cbn in *.
  destruct p ; cbn in *. destruct b ; cbn in * ; try contradiction.
  exists (true,true) ; split ; auto. exists (true,true) ; split ; auto.
  apply In_singleton.
  destruct b4 ; cbn in * ; try contradiction.
  exists (false,false) ; cbn ; repeat split ; auto.
  intros p Hp. destruct Hp. destruct x. destruct H. inversion H ; subst.
  unfold ireachable in H0 ; cbn in H0 ; unfold bireach in H0 ; cbn in *.
  destruct p ; cbn in *. destruct b ; cbn in * ; try contradiction.
  destruct b0 ; cbn in * ; try contradiction. exists (true,true). split ; auto.
  exists (false,true) ; cbn ; split ; auto. apply In_singleton.
  destruct b0 ; cbn in * ; try contradiction.
  exists (false,true) ; split ; auto. exists (false,true) ; split ; auto.
  apply In_singleton.
- destruct b ; cbn in * ; try contradiction.
  destruct b0 ; cbn in * ; try contradiction.
Qed.

(* We can thus use this frame to show that the logic CK + Idb + Nd is
    not included in CK + Cd + Idb + Ndb. *)

Theorem CKIdbNd_not_included_CKCdIdbNdb : 
               CKIdbNdH_prv (Empty_set _) ((¬ ¬ ☐ (#0)) --> ☐ ¬ ¬ (#0)) /\
                ~ CKCdIdbNdbH_prv (Empty_set _) ((¬ ¬ ☐ (#0)) --> ☐ ¬ ¬ (#0)).
Proof.
split.
- apply negneg_box_prv.
- intro. repeat apply extCKH_Detachment_Theorem in H. apply CKCdIdbNdb_Soundness in H.
  assert (forces bM (false,false) (¬ (¬ (☐ (#0))))).
  { intros b ifb Hb. exfalso. destruct b ; cbn in * ; unfold bireach in ifb ; cbn in ifb ; auto.
    destruct b ; cbn in *.
    - destruct b0 ; cbn in * ; auto ; try contradiction.
      assert (bmreach (true, false) (true, true)) ; cbn ; auto.
      assert (forall v : (bool * bool), bireach (true, false) v ->
      forall u : (bool * bool), bmreach v u -> forces bM u (#0)).
      { intros. destruct v ; cbn in * ; try contradiction.
        destruct b ; destruct b0 ; cbn in * ; auto ; try contradiction. }
      pose (Hb (true,false) I H1). inversion e.
    - destruct b0 ; cbn in * ; auto ; try contradiction.
      assert (bmreach (true, false) (true, true)) ; cbn ; auto.
      assert (forall v : (bool * bool), bireach (true, false) v ->
      forall u : (bool * bool), bmreach v u -> forces bM u (#0)).
      { intros. destruct v ; cbn in * ; try contradiction.
        destruct b ; destruct b0 ; cbn in * ; auto ; try contradiction. }
      pose (Hb (true,false) I H1). inversion e. }
  assert (~ forces bM (false,false) (☐ ¬ ¬ (#0))).
  { intro.
    assert (forall v : bool * bool, bireach (false, true) v -> bval v 0 -> v = (true, true)).
    { intros. destruct v ; cbn in * ; auto.
      destruct b ; destruct b0 ; cbn in * ; auto ; try contradiction. }
    pose (H1 (false,false) I (false,true) I (false,true) I H2) ; cbn in f. inversion f. }
  apply H1. apply H ; auto.
  + repeat split.
     * apply suff_impl_Cd. apply strong_is_suff_Cd. apply bF_strong_Cd.
     * apply suff_impl_Idb. apply bF_suff_Idb.
     * apply suff_impl_Ndb. apply bF_suff_Ndb.
  + intros. inversion H2 ; subst. inversion H3 ; subst.
     inversion H3 ; subst ; auto.
Qed.

End CKIdbNd_not_incl_CKCdIdbNdb.



Section CKIdbNd_not_incl_CKIdbNdb.

(* We can also show that the logic CK + Idb + Nd is
    not included in CK + Idb + Ndb. *)

Theorem CKIdbNd_not_included_CKIdbNdb :
               CKIdbNdH_prv (Empty_set _) ((¬ ¬ ☐ (#0)) --> ☐ ¬ ¬ (#0)) /\
                ~ CKIdbNdbH_prv (Empty_set _) ((¬ ¬ ☐ (#0)) --> ☐ ¬ ¬ (#0)).
Proof.
split.
- apply negneg_box_prv.
- intro. apply CKIdbNd_not_included_CKCdIdbNdb.
  apply more_AdAx_more_prv with (fun x => (exists A B, Idb A B = x) \/ Ndb = x).
  firstorder. auto.
Qed.

End CKIdbNd_not_incl_CKIdbNdb.






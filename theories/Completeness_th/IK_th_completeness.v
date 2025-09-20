From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_th_completeness.

Section IK_completeness.

Definition is_Nd := (fun x => Nd = x).

Lemma CF_suff_Nd : suff_Nd_frame (CF is_Nd).
Proof.
intros w (H & H0).
apply cworld_prf_irrel.
apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
- unfold AllForm ; auto.
- apply (Closed is_Nd) ; auto. eapply MP. apply EFQ.
  eapply MP. apply Ax. right. left. reflexivity. apply Id.
  apply H0 ; auto.
Qed.

Lemma CF_Nd : Nd_frame (CF is_Nd).
Proof.
apply suff_impl_Nd. apply CF_suff_Nd.
Qed.

Theorem suff_suff_suff_IK_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => suff_Cd_frame F /\ suff_Idb_frame F /\ suff_Nd_frame F) Γ φ -> IKH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCdIdb is_Nd).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:= fun F => suff_Cd_frame F /\ suff_Idb_frame F /\ suff_Nd_frame F) ; auto.
  repeat split ; auto.
  + apply strong_is_suff_Cd. apply CF_strong_Cd_weak_Idb.
  + apply CF_suff_Idb.
  + apply CF_suff_Nd.
Qed.

Theorem IK_Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => Cd_frame F /\ Idb_frame F /\ Nd_frame F) Γ φ -> IKH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCdIdb is_Nd).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:= fun F => Cd_frame F /\ Idb_frame F /\ Nd_frame F) ; auto.
  repeat split ; auto. 1-2: apply CF_CdIdb. apply CF_Nd.
Qed.

End IK_completeness.
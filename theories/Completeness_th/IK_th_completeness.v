Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_th_completeness.

Section IK_completeness.

Definition is_Nd := (fun x => Nd = x).

Lemma CF_Nd : Nd_frame (CF is_Nd).
Proof.
intros w Hw.
apply cmreach_expl ; auto.
unfold cmreach ; cbn. split ; intros A HA.
- pose (Hw _ (ireach_refl w)). destruct m.
  apply Closed. eapply MP. apply EFQ. eapply MP.
  apply Ax ; right ; left ; reflexivity. apply Id. apply H0.
  unfold th ; unfold cexpl ; cbn ; unfold AllForm ; auto.
- unfold AllForm ; auto.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => Cd_frame F /\ Idb_frame F /\ Nd_frame F) Γ φ -> IKH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCdIdb is_Nd).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (ClassF:= fun F => Cd_frame F /\ Idb_frame F /\ Nd_frame F) ; auto.
  repeat split ; auto. 1-2: apply CF_CdIdb. apply CF_Nd.
Qed.

End IK_completeness.
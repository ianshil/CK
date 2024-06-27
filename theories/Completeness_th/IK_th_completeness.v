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

Definition is_k5 := (fun x => k5 = x).

Lemma CF_k5 : k5_frame (CF is_k5).
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
    loc_conseq (fun F => k3_frame F /\ k4_frame F /\ k5_frame F) Γ φ -> IKH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk34 is_k5).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (FraP:= fun F => k3_frame F /\ k4_frame F /\ k5_frame F) ; auto.
  repeat split ; auto. 1-2: apply CF_k34. apply CF_k5.
Qed.

End IK_completeness.
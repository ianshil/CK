Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_th_completeness.

Section CK34Ndb_completeness.

Definition is_Ndb := (fun x => Ndb = x).

Lemma CF_Ndb : Ndb_frame (CF is_Ndb).
Proof.
intros w Hw u v iwu muv.
pose (Hw _ iwu).
apply cmreach_expl ; auto.
unfold cmreach ; cbn. split ; intros A HA.
- pose (Hw _ (ireach_refl w)). destruct m.
  apply Closed. eapply MP. apply EFQ. apply Id.
  apply muv. apply Closed. eapply MP.
  apply Ax ; right ; left ; reflexivity. apply Id. apply H0.
  cbn. unfold AllForm ; auto.
- unfold AllForm ; auto.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => k3_frame F /\ k4_frame F /\ Ndb_frame F) Γ φ -> CK34NdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk34 is_Ndb).
- intros A HA. destruct HA ; auto.
- apply Strong_Completeness with (FraP:= fun F => k3_frame F /\ k4_frame F /\ Ndb_frame F) ; auto.
  repeat split ; auto. 1-2: apply CF_k34. apply CF_Ndb.
Qed.

End CK34Ndb_completeness.
Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_th_completeness.

Section CK34_completeness.

Definition NoAdAxk34 := (fun (ax : form) => False).

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq (fun F => k3_frame F /\ k4_frame F) Γ φ -> CK34H_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk34 NoAdAxk34).
- intros A HA. destruct HA ; auto. destruct H0 ; auto.
- apply Strong_Completeness with (FraP:= fun F => k3_frame F /\ k4_frame F) ; auto.
  apply CF_k34.
Qed.

End CK34_completeness.

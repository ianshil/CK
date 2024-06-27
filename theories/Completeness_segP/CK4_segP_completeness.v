Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segP_completeness.

Require Import Classical.

Section CK4_completeness.

Definition NoAdAxk4 := (fun (ax : form) => False).

Theorem suff_k4_Strong_Completeness : forall Γ φ,
    loc_conseq suff_k4_frame Γ φ -> CK4H_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk4 NoAdAxk4).
- intros A HA. destruct HA ; auto. destruct H0 ; auto.
- apply Strong_Completeness with (FraP:= suff_k4_frame) ; auto.
  apply CF_suff_k4.
Qed.

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq k4_frame Γ φ -> CK4H_prv Γ φ.
Proof.
intros. apply suff_k4_Strong_Completeness.
intros M HM w Hw. apply H ; auto. apply suff_impl_k4 ; auto.
Qed.

End CK4_completeness.
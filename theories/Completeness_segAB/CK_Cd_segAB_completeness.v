Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segAB_completeness.

Section CK_Cd_completeness.

(* For CK with Cd, we do not add any additional axiom to get completeness
    using the AB-segments canonical model. *)

Definition NoAdAxCd := (fun (ax : form) => False).

Theorem suff_CKCd_Strong_Completeness : forall Γ φ,
    loc_conseq suff_Cd_frame Γ φ -> CKCdH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxCd NoAdAxCd).
- intros A HA. destruct HA ; auto. destruct H0 ; auto.
- apply Strong_Completeness with (ClassF:= suff_Cd_frame); auto.
  apply CF_suff_Cd.
Qed.

Theorem CKCd_Strong_Completeness : forall Γ φ,
    loc_conseq Cd_frame Γ φ -> CKCdH_prv Γ φ.
Proof.
intros. apply suff_CKCd_Strong_Completeness.
intros M HM w Hw ; apply H ; auto. apply suff_impl_Cd ; auto.
Qed.

End CK_Cd_completeness.
Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_segAB_completeness.

Require Import Classical.

Section CK3_completeness.

Definition NoAdAxk3 := (fun (ax : form) => False).

Theorem Strong_Completeness : forall Γ φ,
    loc_conseq k3_frame Γ φ -> CK3H_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (AdAxk3 NoAdAxk3).
- intros A HA. destruct HA ; auto. destruct H0 ; auto.
- apply Strong_Completeness with (FraP:= k3_frame) ; auto.
  apply CF_k3.
Qed.

End CK3_completeness.
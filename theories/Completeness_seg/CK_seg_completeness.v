From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_seg_completeness.

Section CK_completeness.

Definition NoAdAx := fun (x : form) => False.

Theorem CK_Strong_Completeness : forall Γ φ,
    loc_conseq (fun x => True) Γ φ -> CKH_prv Γ φ.
Proof.
intros. apply Strong_Completeness with (ClassF:=fun x => True) ; auto.
Qed.

End CK_completeness.
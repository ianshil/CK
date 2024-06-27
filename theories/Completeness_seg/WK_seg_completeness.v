Require Import List.
Export ListNotations.
Require Import PeanoNat.
Require Import Lia.
Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_seg_completeness.



Section WK_completeness.

Definition is_k5 := (fun x => k5 = x).

Lemma CF_k5 Γ : k5_frame (CF is_k5 Γ).
Proof.
intros w Hw.
assert (@head _ _ w = Clos Γ).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - apply (segInclClos is_k5) in HA ; auto.
  - apply (segClosed is_k5) ; auto. eapply MP. apply EFQ.
    eapply MP. apply Ax. right. reflexivity.
    apply Id. apply (truth_lemma is_k5).
    right ; auto.
    intros v Hv. apply Hw in Hv. exists (cexpl is_k5 Γ). split ; auto.
    cbn ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H. apply In_singleton.
Qed.

Theorem WK_Strong_Completeness : forall Γ φ,
    loc_conseq k5_frame Γ φ -> WKH_prv Γ φ.
Proof.
apply Strong_Completeness with (FraP:= k5_frame) ; auto.
apply CF_k5.
Qed.

End WK_completeness.

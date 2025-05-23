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

Definition is_Nd := (fun x => Nd = x).

Lemma CF_Nd : Nd_frame (CF is_Nd).
Proof.
intros w Hw.
assert (@head _ w = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (segClosed is_Nd) ; auto. eapply MP. apply EFQ.
    eapply MP. apply Ax. right. reflexivity.
    apply Id. apply (truth_lemma is_Nd).
    intros v Hv. apply Hw in Hv. exists (cexpl is_Nd). split ; auto.
    cbn ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H. apply In_singleton.
Qed.

Theorem WK_Strong_Completeness : forall Γ φ,
    loc_conseq Nd_frame Γ φ -> WKH_prv Γ φ.
Proof.
intros. apply Strong_Completeness with (ClassF:=Nd_frame) ; auto.
intros ; subst. apply CF_Nd.
Qed.

End WK_completeness.

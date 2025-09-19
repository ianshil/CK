From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import PeanoNat.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import general_seg_completeness.


Section CKNdb_completeness.

Definition is_Ndb := (fun x => Ndb = x).

Lemma CF_Ndb : Ndb_frame (CF is_Ndb).
Proof.
intros w Hw u v iwu muv.
pose (Hw _ iwu).
assert (@head _ v = AllForm).
{ apply Extensionality_Ensembles ; split ; intros A HA ; unfold In, head in * ; cbn in *.
  - unfold AllForm ; auto.
  - apply (segClosed is_Ndb) ; auto. eapply MP. apply EFQ. apply Id. unfold In ; cbn.
    apply (boxreflect is_Ndb) with (A:=⊥) in muv ; auto.
    apply (@segClosed is_Ndb u) ; auto.
    eapply MP. apply Ax. right. reflexivity.
    apply Id. apply (truth_lemma is_Ndb).
    intros z Hz. exists (cexpl is_Ndb). split ; auto.
    2: cbn ; auto. apply Hw. apply cireach_trans with u ; auto. }
apply cmreach_expl ; auto.
unfold cmreach ; cbn. rewrite H. apply In_singleton.
Qed.

Theorem CKNdb_Strong_Completeness : forall Γ φ,
    loc_conseq Ndb_frame Γ φ -> CKNdbH_prv Γ φ.
Proof.
intros. apply Strong_Completeness with (ClassF:=Ndb_frame) ; auto.
intros ; subst. apply CF_Ndb.
Qed.

End CKNdb_completeness.

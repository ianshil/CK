Require Import Arith.
Require Import Lia.
Require Import Ensembles.
Require Import Init.Wf.

Require Import im_syntax.

Section kripke_sem.

(* We define frames. *)

    Class frame :=
      {
        (* Nodes *)
        nodes : Type ;
        expl: nodes ; (* exploding node *)

        (* Intuitionistic Relation *)
        ireachable : nodes -> nodes -> Prop ;
        ireach_refl u : ireachable u u ;
        ireach_tran u v w : ireachable u v -> ireachable v w -> ireachable u w ;
        ireach_expl u : ireachable expl u -> u = expl ;

        (* Modal Relation *)
        mreachable : nodes -> nodes -> Prop ;
        mreach_expl u : mreachable expl u <-> u = expl ;
      }.

(* Then models. *)

    Class model :=
      {
        (* Frame *)
        fra : frame ;

        (* Valuation *)
        val : nodes -> nat -> Prop ;
        persist :  forall u v, ireachable u v -> forall p, val u p -> val v p ;
        val_expl :  forall p, val expl p
      }.

(* We can now define the notion of forcing, which interprets
    formulas in points of models. *)

Fixpoint forces (M: model) w (φ : form) : Prop :=
match φ with
  | Var p => val w p
  | Bot => w = expl
  | ψ ∧ χ => (forces M w ψ) /\ (forces M w χ)
  | ψ ∨ χ => (forces M w ψ) \/ (forces M w χ)
  | ψ --> χ => forall v, ireachable w v -> forces M v ψ -> forces M v χ
  | Box ψ => forall v, ireachable w v -> forall u, mreachable v u -> forces M u ψ
  | Diam ψ => forall v, ireachable w v -> exists u, mreachable v u /\ forces M u ψ
end.

(* Persistence holds in our semantics. *)

  Lemma Persistence : forall A M w, forces M w A ->
              (forall v, ireachable w v -> forces M v A).
  Proof.
  induction A ; cbn ; intros ; subst ; auto.
  - apply persist with w ; auto.
  - apply ireach_expl in H0 ; auto.
  - inversion H ; split. apply IHA1 with (w:=w) ; auto.
    apply IHA2 with (w:=w) ; auto.
  - inversion H. left. apply IHA1 with (w:=w) ; auto.
    right. apply IHA2 with (w:=w) ; auto.
  - apply H with (v:=v0) ; auto. apply ireach_tran with v ; auto.
  - apply H with v0 ; auto. apply ireach_tran with v ; auto.
  - destruct (H v0) as (u & Hu0 & Hu1). apply ireach_tran with v ; auto.
    exists u ; split ; auto.
  Qed.

(* As expected, the exploding world forces all formulas. *)

  Lemma Expl : forall A M, forces M expl A.
  Proof.
  induction A ; cbn ; intros ; subst ; auto.
  - apply val_expl.
  - apply ireach_expl in H ; auto ; subst ; auto.
  - apply ireach_expl in H ; subst. apply mreach_expl in H0 ; auto ; subst ; auto.
  - apply ireach_expl in H ; subst. exists expl ; split ; auto. apply mreach_expl ; auto.
  Qed.

(* We define notions of validity on models and frames, as well as the local
    semantic consequence relation. *)

  Definition mvalid (M : model) φ := forall w, forces M w φ.

  Definition fvalid (F : frame) φ := forall (M : model), fra = F -> mvalid M φ.

  Definition loc_conseq (C : frame -> Prop) (Γ : Ensemble form) (φ : form) :=
  forall M, C fra -> forall w, (forall ψ, (In _ Γ ψ) -> forces M w ψ) -> (forces M w φ).

End kripke_sem.


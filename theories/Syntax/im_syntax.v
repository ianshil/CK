Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.

(* First, let us define propositional formulas. *)

Inductive form : Type :=
 | Var : nat -> form
 | Bot : form
 | And : form -> form -> form
 | Or : form -> form -> form
 | Imp : form -> form -> form
 | Box : form -> form
 | Diam : form -> form.

(* We define negation and top. *)

Definition Neg (A : form) := Imp A (Bot).
Definition Top := Imp Bot Bot.

(* We use the following notations for modal formulas. *)

Notation "# p" := (Var p) (at level 1).
Notation "¬ φ" := (Imp φ Bot) (at level 75, φ at level 75).
Notation " ⊥ " := Bot.
Notation " ⊤ " := Top.
Notation " φ ∧ ψ" := (And φ ψ) (at level 80, ψ at level 80).
Notation " φ ∨ ψ" := (Or φ ψ) (at level 85, ψ at level 85).
Notation " φ → ψ" := (Imp φ ψ) (at level 99, ψ at level 200).
Notation "□ φ" := (Box φ) (at level 75, φ at level 75).
Notation "◊ φ" := (Diam φ) (at level 42).

(* We define the property of formulas of being diamond-free. *)

Fixpoint diam_free φ : Prop :=
match φ with
| # p => True
| ⊥ => True
| ψ ∧ χ => diam_free ψ /\ diam_free χ
| ψ ∨ χ => diam_free ψ /\ diam_free χ
| ψ → χ => diam_free ψ /\ diam_free χ
| □ ψ => diam_free ψ
| ◊ ψ => False
end.


(* Next, we define the set of subformulas of a formula, and
    extend this notion to lists of formulas. *)

Fixpoint subform (φ : form) : Ensemble form :=
match φ with
| Var p => Singleton _ (Var p)
| ⊥ => Singleton _ ⊥
| ψ ∧ χ => Union _ (Singleton _ (ψ ∧ χ)) (Union _ (subform ψ) (subform χ))
| ψ ∨ χ => Union _ (Singleton _ (ψ ∨ χ)) (Union _ (subform ψ) (subform χ))
| ψ → χ => Union _ (Singleton _ (ψ → χ)) (Union _ (subform ψ) (subform χ))
| □ ψ => Union _ (Singleton _ (□ ψ)) (subform ψ)
| ◊ ψ => Union _ (Singleton _ (◊ ψ)) (subform ψ)
end.

Lemma subform_id : forall φ, (subform φ) φ.
Proof.
destruct φ ; cbn. 1-2: split. all: left ; split.
Qed.

Fixpoint subformlist (φ : form) : list form :=
match φ with
| Var p => (Var p) :: nil
| ⊥ => [⊥]
| ψ ∧ χ => (ψ ∧ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ ∨ χ => (ψ ∨ χ) :: (subformlist ψ) ++ (subformlist χ)
| ψ → χ => (Imp ψ χ) :: (subformlist ψ) ++ (subformlist χ)
| □ ψ => (□ ψ) :: (subformlist ψ)
| ◊ ψ => (◊ ψ) :: (subformlist ψ)
end.

Lemma subform_trans : forall φ ψ χ, List.In φ (subformlist ψ) ->
  List.In χ (subformlist φ) -> List.In χ (subformlist ψ).
Proof.
intros φ ψ χ. revert ψ χ φ. induction ψ.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
  apply in_app_or in H ; destruct H. right. apply in_or_app ; left.
  apply IHψ1 with (φ:=φ) ; auto. right. apply in_or_app ; right.
  apply IHψ2 with (φ:=φ) ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
  apply in_app_or in H ; destruct H. right. apply in_or_app ; left.
  apply IHψ1 with (φ:=φ) ; auto. right. apply in_or_app ; right.
  apply IHψ2 with (φ:=φ) ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto.
  apply in_app_or in H ; destruct H. right. apply in_or_app ; left.
  apply IHψ1 with (φ:=φ) ; auto. right. apply in_or_app ; right.
  apply IHψ2 with (φ:=φ) ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto. right.
  apply IHψ with (φ:=φ) ; auto.
- intros. simpl. simpl in H. destruct H ; subst ; auto. right.
  apply IHψ with (φ:=φ) ; auto.
Qed.

(* Equality is decidable over formulas. *)

Lemma eq_dec_form : forall x y : form, {x = y}+{x <> y}.
Proof.
repeat decide equality.
Qed.

(* We define the notion of uniform substitution. *)

Fixpoint subst (σ : nat -> form) (φ : form) : form :=
match φ with
| # p => (σ p)
| ⊥ => ⊥
| ψ ∧ χ => (subst σ ψ) ∧ (subst σ χ)
| ψ ∨ χ => (subst σ ψ) ∨ (subst σ χ)
| ψ → χ => (subst σ ψ) → (subst σ χ)
| □ ψ => □ (subst σ ψ)
| ◊ ψ => ◊ (subst σ ψ)
end.

Fixpoint list_Imp (A : form) (l : list form) : form :=
match l with
 | nil => A
 | h :: t => h → (list_Imp A t)
end.

Definition Box_list (l : list form) : list form := map Box l.

Lemma In_form_dec : forall l (A : form), {List.In A l} + {List.In A l -> False}.
Proof.
induction l ; simpl ; intros ; auto.
destruct (IHl A) ; auto.
destruct (eq_dec_form a A) ; auto.
right. intro. destruct H ; auto.
Qed.

Definition UnBox φ : form :=
  match φ with
  | Box ψ => ψ
  | _ => φ
  end.





(** Theory of countability from Iris *)
From stdpp Require Import countable.
From Stdlib Require Import Program.Equality.

Require Import im_syntax.

Global Instance fomula_bottom : base.Bottom form := Bot.
Global Instance fomula_top : base.Top form := Top.

Fixpoint occurs_in (x : nat) (φ : form) :=
match φ with
| Var y => x = y
| Bot => False
| And φ ψ => (occurs_in x φ) \/ (occurs_in x ψ)
| Or φ ψ => (occurs_in x φ) \/ (occurs_in x ψ)
| φ → ψ => (occurs_in x φ) \/ (occurs_in x ψ)
| Box φ => occurs_in x φ
| Diam φ => occurs_in x φ
end.

Definition occurs_in_opt (x : nat) (φ : option form) :=
match φ with
| None => False
| Some ϕ => occurs_in x ϕ
end.

Ltac solve_trivial_decision :=
  match goal with
  | |- Decision (?P) => apply _
  | |- sumbool ?P (¬?P) => change (Decision P); apply _
  end.
Ltac solve_decision :=
  unfold EqDecision; intros; first
    [ solve_trivial_decision
    | unfold Decision; decide equality; solve_trivial_decision ].

(** Formulas have decidable equality. *)
Global Instance form_eq_dec : EqDecision form.
Proof.
(* solve decision does not support the modality parameter). *)
Local Ltac ctac Hn := right; let Heq := fresh "Heq" in intro Heq;
                contradict Hn; dependent destruction Heq; now subst.
Local Ltac dec := now subst; left.
intros φ. induction φ; intro ψ; dependent destruction ψ;
try solve[right; discriminate].
- case (decide (n = n0)) as [Heq|Hn]; [dec|ctac Hn].
- dec.
- destruct (IHφ1 ψ1) as [Heq|Hn]; [|ctac Hn].
  destruct (IHφ2 ψ2) as [Heq'|Hn]; [dec|ctac Hn].
- destruct (IHφ1 ψ1) as [Heq|Hn]; [|ctac Hn].
  destruct (IHφ2 ψ2) as [Heq'|Hn]; [dec|ctac Hn].
- destruct (IHφ1 ψ1) as [Heq|Hn]; [|ctac Hn].
  destruct (IHφ2 ψ2) as [Heq'|Hn]; [dec|ctac Hn].
- destruct (IHφ ψ) as [Heq|Hn]; [dec |ctac Hn].
- destruct (IHφ ψ) as [Heq|Hn]; [dec |ctac Hn].
Defined. (* solve decision *)

Section CountablyManyFormulas.

(** ** Countability of the set of formulas *)
(** We prove that there are countably many formulas by exhibiting an injection
  into general trees over nat for countability. *)
Local Fixpoint form_to_gen_tree  (φ : form) : gen_tree (option nat) :=
match φ with
| ⊥ => GenLeaf  None
| Var v => GenLeaf (Some v)
| φ ∧ ψ => GenNode 0 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ ∨ ψ => GenNode 1 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| φ →  ψ => GenNode 2 [form_to_gen_tree φ ; form_to_gen_tree ψ]
| □ φ => GenNode 3 [form_to_gen_tree φ]
| ◊ φ => GenNode 4 [form_to_gen_tree φ]
end.

Local Fixpoint gen_tree_to_form  (t : gen_tree (option nat)) : option form :=
match t with
| GenLeaf None => Some ⊥
| GenLeaf (Some v) => Some (Var v)
| GenNode 0 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ ∧ ψ)
| GenNode 1 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ ∨ ψ)
| GenNode 2 [t1 ; t2] =>
    gen_tree_to_form t1 ≫= fun φ => gen_tree_to_form t2 ≫= fun ψ =>
      Some (φ →  ψ)
| GenNode 3 [t] => gen_tree_to_form t ≫= fun φ => Some (□φ)
| GenNode 4 [t] => gen_tree_to_form t ≫= fun φ => Some (◊φ)
| _=> None
end.

Global Instance form_count : Countable form.
Proof.
  eapply inj_countable with (f := form_to_gen_tree) (g := gen_tree_to_form).
  intro φ; induction φ; simpl; trivial; now rewrite IHφ1, IHφ2 || rewrite  IHφ.
Defined.

End CountablyManyFormulas.

Inductive subformP : form -> form -> Prop :=
| SubEq : ∀ φ, subformP φ φ
| SubAnd : ∀ φ ψ1 ψ2, (subformP φ ψ1 + subformP φ ψ2) -> subformP φ (ψ1 ∧ ψ2)
| SubOr : ∀ φ ψ1 ψ2, (subformP φ ψ1 + subformP φ ψ2) -> subformP φ (ψ1 ∨ ψ2)
| SubImpl : ∀ φ ψ1 ψ2, (subformP φ ψ1 + subformP φ ψ2) -> subformP φ (ψ1 → ψ2)
| SubBox : ∀ φ ψ, subformP φ ψ -> subformP φ (□ ψ)
| SubDiam : ∀ φ ψ, subformP φ ψ -> subformP φ (◊ ψ).
Local Hint Constructors subformP : dyckhoff.

(** ** Weight

We define the weight function on formulas, following (Dyckhoff Negri 2000) *)
Fixpoint weight  (φ : form) : nat := match φ with
| ⊥ => 1
| Var _ => 1
| φ ∧ ψ => 2 + weight φ + weight ψ
| φ ∨ ψ => 1 + weight φ + weight ψ
| φ → ψ => 1 + weight φ + weight ψ
| □φ => 1 + weight φ
| ◊φ => 1 + weight φ
end.

Lemma weight_pos  φ : weight φ > 0.
Proof. induction φ; simpl; lia. Qed.

(** We obtain an induction principle based on weight. *)
Definition weight_ind  (P : form -> Type) :
 (forall ψ, (∀ φ, (weight φ < weight ψ) -> P φ) -> P ψ) ->
 (∀ φ, P φ).
Proof.
  intros Hc φ. remember (weight φ) as w.
  assert(Hw : weight φ ≤ w) by now subst. clear Heqw.
  revert φ Hw. induction w; intros φ Hw.
  - pose (Hw' := weight_pos φ). auto with *.
  - destruct φ; simpl in Hw; trivial;
    apply Hc; intros φ' Hw'; apply IHw; simpl in Hw'; lia.
Defined.

Definition form_order  φ ψ := weight φ > weight ψ.

Global Instance transitive_form_order  : Transitive form_order.
Proof. unfold form_order. auto with *. Qed.

Global Instance irreflexive_form_order  : Irreflexive form_order.
Proof. unfold form_order. intros x y. lia. Qed.

Notation "φ ≺f ψ" := (form_order ψ φ) (at level 149).


(* A result about lists of formulas in Type *)
Lemma in_app_orT l0 l1 (ϕ : form) : In ϕ (l0 ++ l1) -> ({In ϕ l0} + {In ϕ l1}).
Proof.
revert l1 ϕ.
induction l0 ; cbn ; intros ; auto.
destruct (eq_dec_form a ϕ) ; subst ; auto.
assert (In ϕ (l0 ++ l1)). destruct H ; firstorder.
apply IHl0 in H0. destruct H0 ; auto.
Qed.
Require Export Environments.

Open Scope stdpp_scope.

(** * Sequent calculus G4WK *)

(** We implement the sequent calculus G4WK, a single-succedent 
  sequent calculus capturing the intuitionistic modal logic WK.
  It extends the calculus G4ip for intuitionistic logic. 
  
  The formalisation of this sequent is based on the work of 
  Férée and van Gool "Formalizing and Computing Propositional Quantifiers" (2023).
  The formalisation is hosted here: https://github.com/hferee/rocq-pil *)

(** ** Definition of provability in G4WK *)

(* To simulate succedents of "at most one formula", we use "option" type:
   "None" will simulate the empty succedent, and "Some ϕ" the singleton succedent. *)

(* We define the operation of undiamonding such a succedent:
   it results in a non-empty succedent only when the succedent
   it is applied to is non-empty and is a diamond formula. *)

Definition oud (oφ : option form) : option form :=
match oφ with
  | Some (◊ ψ) => Some ψ
  | _ => None
end.

(** ** Definition of provability in G4WK *)
Reserved Notation "Γ ⊢ φ" (at level 90).
Inductive Provable : env -> option form -> Type :=
| Atom :    ∀ Γ p, Γ • (Var p) ⊢ Some (Var p)
| ExFalso : ∀ Γ oφ, Γ • ⊥ ⊢ oφ
| AndR : ∀ Γ φ ψ,
    Γ ⊢ Some φ ->    Γ ⊢ Some ψ ->
      Γ ⊢ Some (φ ∧ ψ)
| AndL : ∀ Γ φ ψ oθ,
    Γ • φ • ψ ⊢ oθ ->
      Γ • (φ ∧ ψ) ⊢ oθ
| OrR1 :    ∀ Γ φ ψ,
    Γ ⊢ Some φ ->
      Γ ⊢ Some (φ ∨ ψ)
| OrR2 :    ∀ Γ φ ψ,
    Γ ⊢ Some ψ ->
      Γ ⊢ Some (φ ∨ ψ)
| OrL :     ∀ Γ φ ψ oθ,
    Γ • φ  ⊢ oθ -> Γ • ψ ⊢ oθ ->
      Γ • (φ ∨ ψ) ⊢ oθ
| ImpR :    ∀ Γ φ ψ,
    Γ • φ ⊢ Some ψ ->
      Γ ⊢ Some (φ → ψ)
| ImpLVar : ∀ Γ p φ oψ,
    Γ • Var p • φ ⊢ oψ ->
      Γ • Var p • (Var p → φ) ⊢ oψ
| ImpLAnd : ∀  Γ φ1 φ2 φ3 oψ,
    Γ • (φ1 → (φ2 → φ3)) ⊢ oψ ->
      Γ • ((φ1 ∧ φ2) → φ3) ⊢ oψ
| ImpLOr :  ∀  Γ φ1 φ2 φ3 oψ,
    Γ • (φ1 → φ3) • (φ2 → φ3) ⊢ oψ ->
      Γ • ((φ1 ∨ φ2) → φ3) ⊢ oψ
| ImpLImp : ∀  Γ φ1 φ2 φ3 oψ,
    Γ • (φ2 → φ3) ⊢ Some (φ1 → φ2) ->Γ • φ3 ⊢ oψ ->
      Γ • ((φ1 → φ2) → φ3) ⊢ oψ
| ImpBox : ∀ (Γ : env) φ1 φ2 oψ,
    (⊗ Γ) ⊢ Some φ1 ->
    Γ • φ2 ⊢ oψ ->
      Γ • ((□ φ1) → φ2) ⊢ oψ
| ImpDiam : ∀ (Γ : env) (φ1 φ2 χ : form) oψ,
    (⊗ Γ) • χ ⊢ Some φ1 ->
    Γ • (◊ χ) • φ2 ⊢ oψ ->
      Γ • (◊ χ) • ((◊ φ1) → φ2) ⊢ oψ
| BoxR : ∀ Γ φ, (⊗ Γ) ⊢ Some φ -> Γ ⊢ Some (□ φ)
| DiamL : ∀ Γ oφ ψ, (⊗ Γ) • ψ ⊢ oud oφ -> Γ • ◊ ψ ⊢ oφ
where "Γ ⊢ φ" := (Provable Γ φ).

Notation "Γ ⊢WK φ" := (Provable Γ φ) (at level 90).

Global Hint Constructors Provable : proof.

(** We show that equivalent multisets prove the same things. *)
Global Instance proper_Provable  : Proper ((≡@{env}) ==> (=) ==> (=)) Provable.
Proof. intros Γ Γ' Heq φ φ' Heq'. ms. Qed.

Global Ltac equiv_tac :=
  repeat rewrite <- list_to_set_disj_rm;
  repeat rewrite <- list_to_set_disj_env_add;
  repeat (rewrite <- difference_singleton; trivial);
  try rewrite <- list_to_set_disj_rm;
  try (rewrite union_difference_L by trivial);
  try (rewrite union_difference_R by trivial);
  try ms.

(** We introduce a tactic "peapply" which allows for application of a G4ip rule
   even in case the environment needs to be reordered *)
Ltac peapply th :=
  (erewrite proper_Provable;  [| |reflexivity]);  [eapply th|try ms].

(** ** Tactics *)

(** We introduce a few tactics that we will need to prove the admissibility of
  the weakening and exchange rules in the proof calculus. *)

(** The tactic "exch" swaps the nth pair of formulas of a sequent, counting from the right. *)

Ltac exch n := match n with
| O => match goal with |- ?a • ?b • ?c ⊢ _ =>
  rewrite (proper_Provable _ _ (env_add_comm a b c) _ _ eq_refl) end
| S O => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (env_add_comm _ _ _)) _ _ eq_refl)
| S (S O) => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_add_comm _ _ _))) _ _ eq_refl)
| S (S (S O)) => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_add_comm _ _ _)))) _ _ eq_refl)
end.
(** The tactic "exhibit" exhibits an element that is in the environment. *)
Ltac exhibit Hin n := match n with
| 0 => rewrite (proper_Provable _ _ (difference_singleton _ _ Hin) _ _ eq_refl)
| 1 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (difference_singleton _ _ Hin)) _ _ eq_refl)
| 2 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (difference_singleton _ _ Hin))) _ _ eq_refl)
| 3 => rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (difference_singleton _ _ Hin)))) _ _ eq_refl)
end.

(** The tactic "forward" tries to change a goal of the form :

((Γ•φ ∖ {[ψ]}•…) ⊢ …

into

((Γ ∖ {[ψ]}•…•φ) ⊢ … ,

by first proving that ψ ∈ Γ. *)

Ltac forward := match goal with
| |- (?Γ•?φ) ∖ {[?ψ]} ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (env_replace φ Hin) _ _ eq_refl)
| |- (?Γ•?φ) ∖ {[?ψ]}•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (env_replace φ Hin)) _ _ eq_refl);
  exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))) _ _ eq_refl);
  exch 1; exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))) _ _ eq_refl);
  exch 2; exch 1; exch 0
| |- (?Γ•?φ) ∖ {[?ψ]}•_•_•_•_ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by ms;
  rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))))) _ _ eq_refl);
  exch 3; exch 2; exch 1; exch 0
end.

(** The tactic "backward" changes a goal of the form :

((Γ ∖ {[ψ]}•…•φ) ⊢ …

into

((Γ•φ ∖ {[ψ]}•…) ⊢ …,

by first proving that ψ ∈ Γ.

*)

Ltac backward := match goal with
| |- ?Γ ∖ {[?ψ]}•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof);
  rewrite (proper_Provable _ _ (symmetry(env_replace _ Hin)) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); try exch 0;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r (env_replace _ Hin))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1; exch 2;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin))))) _ _ eq_refl)
| |- ?Γ ∖ {[?ψ]}•_•_•_•_•?φ ⊢ _ =>
  let Hin := fresh "Hin" in
  assert(Hin : ψ ∈ Γ) by (ms || eauto with proof); exch 0; exch 1; exch 2; exch 3;
  rewrite (proper_Provable _ _ (symmetry(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (env_replace φ Hin)))))) _ _ eq_refl)
end.

(** The tactic "rw" rewrites the environment equivalence Heq under the nth formula in the premise. *)
Ltac rw Heq n := match n with
| 0 => erewrite (proper_Provable _ _ Heq _ _ eq_refl)
| 1 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r Heq) _ _ eq_refl)
| 2 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r Heq)) _ _ eq_refl)
| 3 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r Heq))) _ _ eq_refl)
| 4 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r Heq)))) _ _ eq_refl)
| 5 => erewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r Heq))))) _ _ eq_refl)
end.

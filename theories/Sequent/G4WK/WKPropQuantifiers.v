(** * Propositional Quantifiers

The main theorem proved in this file was first proved as Theorem 1 in:

(Pitts 1992). A. M. Pitts. On an interpretation of second order quantification in first order intuitionistic propositional logic. J. Symb. Log., 57(1):33–52.
It has been further extended to handle CK

It consists of two parts:

1) the inductive construction of the propositional quantifiers;

2) a proof of its correctness. *)

Require Import WKSequents im_syntax syntax_facts.
Require Import WKSequentProps WKOrder (* Optimizations *).
From Stdlib Require Import Program.Equality. (* for dependent induction *)
(* Require Import ISL.Simplifications. *)
From Equations Require Import Equations.

(* We define propositional quantifiers given a simplification method
  for formulas and contexts *)

(* Module PropQuant (Import S : SimpT). *)

(** ** Definition of propositional quantifiers. *)

Section PropQuantDefinition.

(** Throughout the construction and proof, we fix a variable p, with respect to
  which the propositional quantifier will be computed. *)
Variable p : nat.
(** We define the formulas Eφ and Aφ associated to any formula φ. This
  is an implementation of Pitts' Table 5, together with a (mostly automatic)
  proof that the definition terminates*)

(* solves the obligations of the following programs *)
Obligation Tactic := intros; repeat rewrite <- Eqdep.EqdepTheory.eq_rect_eq in * ; order_tac ;
try match goal with
| ϕ : option form |- _ ≺ listform_opt_add2 _ ?ϕ => destruct ϕ ; cbn ; repeat rewrite <- Eqdep.EqdepTheory.eq_rect_eq in * ; order_tac
end.

Notation "□⁻¹ Γ" := (l_open_boxes Γ) (at level 75).

Open Scope list_scope.

(** First, the implementation of the rules for calculating E. The names of the rules
  refer to the table in Pitts' paper. *)
(** note the use of  "lazy" conjunctions, disjunctions and implications *)

(* I took the decision of having None in the recursive calls
   instead of ϕ. *)
Equations e_rule {Δ : list form} {ϕ : option form }
  {E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  {A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  (θ: form) {Hin : θ ∈ Δ} : form :=
(* E0 *)
| ⊥ := ⊥;
| Var q :=
  if decide (p = q) then ⊤ (* default *)
  else # q (* E1 modified *);
(* E2 *)
| δ₁ ∧ δ₂ := let Δ' := rm (δ₁ ∧ δ₂) Δ in
  E (Δ' • δ₁ • δ₂, None) _;
(* E3 *)
| δ₁ ∨ δ₂ := let Δ' := rm (δ₁ ∨ δ₂) Δ in
  E (Δ' • δ₁, None) _ ∨ E (Δ' • δ₂, None) _;
| Var q → δ := let Δ' := rm (Var q → δ) Δ in
    if decide (Var q ∈ Δ) then E (Δ'•δ, None) _ (* E5 modified *)
    else if decide (p = q) then ⊤
    else # q  → E (Δ'•δ, None) _ ; (* E4 *)
(* E6 *)
| (δ₁ ∧ δ₂)→ δ₃ := let Δ' := rm ((δ₁ ∧ δ₂)→ δ₃) Δ in
  E (Δ'•(δ₁ → (δ₂ → δ₃)), None) _;
(* E7 *)
| (δ₁ ∨ δ₂)→ δ₃ := let Δ' := rm ((δ₁ ∨ δ₂)→ δ₃) Δ in
  E (Δ' • (δ₁ → δ₃)•(δ₂ → δ₃), None) _;
(* E8 modified *)
| (δ₁ → δ₂ )→ δ₃ := let Δ' := rm ((δ₁ → δ₂)→ δ₃) Δ in
  (E (Δ'•(δ₂ → δ₃) • δ₁, None) _  → A (Δ'•(δ₂ → δ₃) • δ₁, Some δ₂) _)  → E (Δ'• δ₃, None) _;
| ⊥ → _ := ⊤;
(* Instance of E9 *)
| □ φ := □E ((□⁻¹ (rm (□ φ) Δ)) • φ, None) _;
(* E10 *)
| □δ1 → δ2 := let Δ' := rm (□δ1 → δ2) Δ in
  (□(E(□⁻¹ Δ', None) _
     → A(□⁻¹ Δ', Some δ1) _))
     → E(Δ' • δ2, None) _;
(* E11 *)
| ◊ φ := ◊E ((□⁻¹ (rm (◊ φ) Δ)) • φ, None) _;
(* E13*)
| ◊δ1 → δ2 := let Δ' := rm (◊δ1 → δ2) Δ in
  (◊(E((□⁻¹ Δ'), None) _
     → A((□⁻¹ Δ'), Some δ1) _))
     → E(Δ' • δ2, None) _.


Equations e_rule_9 (Δ : list form) {ϕ : option form}
  {E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  {A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form} : form :=
  | [] := ⊤
  | ψ :: Δ := let Δ' := □⁻¹ (ψ :: Δ) in 
              (□ E (Δ' , None) _).
Next Obligation.
all : destruct (is_box ψ) eqn:E0 ;
[ destruct ψ ; cbn in * ; try discriminate ; auto ;
  try do 2 (apply env_order_0' ; apply env_order_env_order_refl) ;
  apply env_order_compat ; cbn ; try lia ; apply l_open_boxes_env_order | 
  destruct ψ ; cbn ; cbn in E0 ; try discriminate ; auto ; try do 2 (apply env_order_0' ; apply env_order_env_order_refl) ;
  apply env_order_0' ; try apply l_open_boxes_env_order].
Qed.

Equations e_rule_12 {Δ : list form} {ϕ : option form}
  {E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  {A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  (θ₁ θ₂ : form) {Hin1 : θ₁ ∈ Δ} {Hin2 : θ₂ ∈ Δ} : form :=
  | ◊ δ1 → δ2, ◊ δ3 => let Δ' := rm (◊ δ1 → δ2) Δ in
                       let Δ'' := rm (◊δ3) Δ' in
                        (□(E((□⁻¹ Δ'') • δ3, None) _
                           → A((□⁻¹ Δ'') • δ3, Some δ1) _))
                           → E(Δ' • δ2, None) _
  | _ , _ => ⊤ (* default case, quite annoying as it will create a lot of duplicates. *).
Next Obligation.
enough ((□⁻¹ rm (◊ δ3) (rm (◊ δ1 → δ2) Δ)) = □⁻¹ rm (◊ δ3) Δ) ;
[ rewrite H ; apply env_order_0' ; apply env_order_env_order_refl ; apply env_order_compat ; cbn ; [ lia | apply l_open_boxes_env_order] |
  repeat rewrite l_open_boxes_rm ; auto].
enough ((□⁻¹ rm (◊ δ3) (rm (◊ δ1 → δ2) Δ)) = □⁻¹ rm (◊ δ3) Δ) ;
[ rewrite H ; apply env_order_compat ; cbn ; [ lia | apply l_open_boxes_env_order] |
  repeat rewrite l_open_boxes_rm ; auto].
Qed.
Next Obligation.
apply env_order_0' ; apply env_order_env_order_refl.
all: rewrite rm_comm ; apply env_order_lt_le_trans with (rm (◊ δ1 → δ2) (rm (◊ δ3) Δ) • ◊ δ3 • (◊ δ1 → δ2)) ;
[ apply env_order_2 ; cbn ; try lia ;
  apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia ;
  apply l_open_boxes_env_order | 
  eapply (Proper_env_order_refl _ (rm (◊ δ1 → δ2) (rm (◊ δ3) Δ) • (◊ δ1 → δ2) • ◊ δ3)) ; [ | apply Permutation_refl | ] ;
  [ apply Permutation_swap |
    apply env_order_refl_add ; apply remove_In_env_order_refl ;
    apply in_in_rm ; auto ; apply elem_of_list_In_1 ; auto]].
Qed.

Hint Extern 2 (_ <= _) => lia : order.

(** The implementation of the rules for defining A is separated into two pieces.
    Referring to Table 5 in Pitts, the definition a_rule_env handles A1-8 and A10,
    and the definition a_rule_form handles A9 and A11-13. *)
Equations a_rule_env  {Δ : list form} {ϕ : option form}
  {E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  {A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  (θ: form) {Hin : θ ∈ Δ} : form :=
| Var q :=
    if decide (p = q) then
      if decide (Some (Var p) = ϕ) then ⊤ (* A10 *)
      else ⊥
    else ⊥; (* A1 modified : A (Δ', ϕ) can be removed *)
(* A2 *)
| δ₁ ∧ δ₂ := let Δ' := rm (δ₁ ∧ δ₂) Δ in A ((Δ'•δ₁)•δ₂, ϕ) _;
(* A3 *)
| δ₁ ∨ δ₂ := let Δ' := rm (δ₁ ∨ δ₂) Δ in
      (E (Δ'•δ₁, None) _  → A (Δ'•δ₁, ϕ) _)
  (* ⊼ *) ∧ (E (Δ'•δ₂, None) _  → A (Δ'•δ₂, ϕ) _);
| Var q → δ := let Δ' := rm (Var q → δ) Δ in
    if decide (Var q ∈ Δ) then A (Δ'•δ, ϕ) _ (* A5 modified *)
    else if decide (p = q) then ⊥
    else Var q (* ⊼ *) ∧ A (Δ'•δ, ϕ) _; (* A4 *)
(* A6 *)
| (δ₁ ∧ δ₂)→ δ₃ := let Δ' := rm ((δ₁ ∧ δ₂)→ δ₃) Δ in
  A (Δ'•(δ₁ → (δ₂ → δ₃)), ϕ) _;
(* A7 *)
| (δ₁ ∨ δ₂)→ δ₃ := let Δ' := rm ((δ₁ ∨ δ₂)→ δ₃) Δ in
  A ((Δ'•(δ₁ → δ₃))•(δ₂ → δ₃), ϕ) _;
(* A8 modified*)
| (δ₁→ δ₂)→ δ₃ := let Δ' := rm ((δ₁→ δ₂)→ δ₃) Δ in
  (E (Δ'•(δ₂ → δ₃) • δ₁, None) _  → A (Δ'•(δ₂ → δ₃) • δ₁, Some δ₂) _)
  (* ⊼ *) ∧ A (Δ'• δ₃, ϕ) _;
| Bot := ⊥;
| Bot → _ := ⊥;
| □δ := ⊥;
(* A15 *)
| (□δ1) → δ2 :=
  let Δ' := rm ((□δ1) → δ2) Δ in
  let Δ'' := □⁻¹ Δ' in
   (□(E(Δ'', None) _  → A(Δ'', Some δ1) _)) ∧ A(Δ' • δ2, ϕ) _ ;
(* A16 *)
| ◊δ := let Δ' := rm (◊δ) Δ in
              (□(E(□⁻¹ Δ' • δ, None) _  → A(□⁻¹ Δ' • δ , oud ϕ) _)) ;
(* A19 *)
| (◊δ1) → δ2 :=
  let Δ' := rm ((◊δ1) → δ2) Δ in
   (◊(E(□⁻¹ Δ', None) _  → A(□⁻¹ Δ', Some δ1) _)) ∧ A(Δ' • δ2, ϕ) _.
Next Obligation.
destruct f ; order_tac.
Qed.

Equations a_rule_env17 {Δ : list form} {ϕ : option form}
  {E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  {A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  (θ₁ θ₂ : form) {Hin1 : θ₁ ∈ Δ} {Hin2 : θ₂ ∈ Δ} : form :=
  | ◊ δ1 → δ2, ◊ δ3 => let Δ' := rm (◊ δ1 → δ2) Δ in
                       let Δ'' := rm (◊δ3) Δ' in
                        (□(E((□⁻¹ Δ'') • δ3, None) _
                           → A((□⁻¹ Δ'') • δ3, Some δ1) _))
                                  ∧ A(Δ' • δ2, ϕ) _
  | _ , _ => ⊥ (* default case, quite annoying as it will create a lot of duplicates. *).
Next Obligation.
apply env_order_0' ; apply env_order_env_order_refl.
all : enough ((□⁻¹ rm (◊ δ3) (rm (◊ δ1 → δ2) Δ)) = □⁻¹ rm (◊ δ3) Δ) ;
[ rewrite H ; apply env_order_compat ; cbn ; [ lia | apply l_open_boxes_env_order] |
 repeat rewrite l_open_boxes_rm ; auto].
Qed.
Next Obligation.
apply env_order_0' ; apply env_order_env_order_refl.
all : rewrite rm_comm ; apply env_order_lt_le_trans with (rm (◊ δ1 → δ2) (rm (◊ δ3) Δ) • ◊ δ3 • (◊ δ1 → δ2)) ;
[ apply env_order_2 ; cbn ; try lia ; apply env_order_env_order_refl ;
  apply env_order_compat ; cbn ; try lia ; apply l_open_boxes_env_order |
  eapply (Proper_env_order_refl _ (rm (◊ δ1 → δ2) (rm (◊ δ3) Δ) • (◊ δ1 → δ2) • ◊ δ3)) ; [ | apply Permutation_refl | ] ; 
  [ apply Permutation_swap |
   apply env_order_refl_add ; apply remove_In_env_order_refl ;
    apply in_in_rm ; auto ; apply elem_of_list_In_1 ; auto ]].
Qed.

Equations a_rule_form  {Δ : list form} (ϕ : option form)
  {E : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form}
  {A : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form} : form :=
| None := ⊥ (* This may cause problems. It could be a default case though. *)
| Some (Var q) :=
    if decide (p = q) (* TODO : change this to p∈Vars(ϕ) *)
    then ⊥
    else Var q; (* A9 *)
(* A11 *)
| Some (ϕ₁ ∧ ϕ₂) := A (Δ, Some ϕ₁) _ (* ⊼ *) ∧ A (Δ, Some ϕ₂) _;
(* A12 *)
| Some (ϕ₁ ∨ ϕ₂) := A (Δ, Some ϕ₁) _ (* ⊻ *) ∨ A (Δ, Some ϕ₂) _;
(* A13 *)
| Some (ϕ₁ → ϕ₂) := E (Δ•ϕ₁, None) _  → A (Δ•ϕ₁, Some ϕ₂) _;
(* Is it safe to put ⊥ in E? Not sure given the clause for ◊ in a_rule_env *)
| Some Bot := ⊥;
(* A14 *)
| Some (□δ) := □((E ((□⁻¹ Δ), None) _)  → A((□⁻¹ Δ), Some δ) _)
(* A18 *)
| Some (◊δ) := ◊((E ((□⁻¹ Δ), None) _)  → A((□⁻¹ Δ), Some δ) _).

Instance WF_pointed_env_order  : WellFounded pointed_env_order := wf_pointed_order.

Obligation Tactic := (eapply env_order_lt_le_trans; [eassumption|]; order_tac).
Equations EA (b : bool) (pe : pointed_env) : form by wf pe pointed_env_order :=
(* E *)
EA true pe :=
  let Δ := pe.1 in 
  let ϕ := pe.2 in
  let E pe H := EA true pe in
  let A pe H := EA false pe in
    list_conj ((@e_rule_9 Δ ϕ E A) (* E9 *)
    :: (in_map Δ (@e_rule Δ ϕ E A)) (* E0-8,10-11,13 *)
    ++ (in_map2 Δ (@e_rule_12 Δ ϕ E A)) (* E12 *)) ;
(* A *)
EA false pe :=
  let Δ := pe.1 in
  let ϕ := pe.2 in
  let E pe H := EA true pe in
  let A pe H := EA false pe in
    list_disj ((@a_rule_form Δ ϕ E A) (* A11-14,18*)
    :: (in_map Δ (@a_rule_env Δ ϕ E A)) (* A1-8,10,15-16,19 *)
    ++ (in_map2 Δ (@a_rule_env17 Δ ϕ E A))) (* A17 *). 


Definition E Δ:= EA true (Δ, None).
Definition A := EA false.

Definition Ef (ψ : form) := (E ([ψ])).
Definition Af (ψ : form) := (A ([], Some ψ)).

End PropQuantDefinition.

(** Congruence lemmas: if we apply any of e_rule, e_rule_9, e_rule_12, a_rule_env, or a_rule_form
  to two equal environments, then they give the same results. *)


Lemma e_rules_cong p Δ ϕ:
(forall θ Hin,
((@e_rule p Δ ϕ
(λ pe0 (_ : pe0 ≺· (Δ, ϕ)), EA p true pe0)
(λ pe0 (_ : pe0 ≺· (Δ, ϕ)), EA p false pe0)) θ Hin
= (@e_rule p Δ None
    (λ pe0 (_ : pe0 ≺· (Δ, None)), EA p true pe0)
    (λ pe0 (_ : pe0 ≺· (Δ, None)), EA p false pe0)) θ Hin))
*
((@e_rule_9 Δ ϕ
(λ pe0 (_ : pe0 ≺· (Δ, ϕ)), EA p true pe0)
(λ pe0 (_ : pe0 ≺· (Δ, ϕ)), EA p false pe0))
= (@e_rule_9 Δ None
    (λ pe0 (_ : pe0 ≺· (Δ, None)), EA p true pe0)
    (λ pe0 (_ : pe0 ≺· (Δ, None)), EA p false pe0)))
*
(forall θ₁ θ₂ Hin1 Hin2,
((@e_rule_12 Δ ϕ
(λ pe0 (_ : pe0 ≺· (Δ, ϕ)), EA p true pe0)
(λ pe0 (_ : pe0 ≺· (Δ, ϕ)), EA p false pe0)) θ₁ θ₂ Hin1 Hin2
= (@e_rule_12 Δ None
    (λ pe0 (_ : pe0 ≺· (Δ, None)), EA p true pe0)
    (λ pe0 (_ : pe0 ≺· (Δ, None)), EA p false pe0)) θ₁ θ₂ Hin1 Hin2)).
Proof.
pose (Δ, ϕ) as pe.
remember pe as pe'.
replace Δ with pe'.1 by now subst.
replace ϕ with pe'.2 by now subst. clear Heqpe' Δ ϕ pe. revert pe'.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros (Δ, ϕ) Hind.
repeat split. cbn. funelim (e_rule_9 Δ) ; cbn ; cbn in Heqcall ; auto.
Qed.

Lemma e_rule_cong_strong  p Δ ϕ θ (Hin1 Hin2: θ ∈ Δ) E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @e_rule p Δ ϕ E1 A1 θ Hin1 = @e_rule p Δ ϕ E2 A2 θ Hin2.
Proof.
intros HeqE HeqA.
  destruct θ; simp a_rule_env; simp e_rule; simpl; trivial; repeat (destruct decide).
  - f_equal; repeat erewrite ?HeqE, ?HeqA; trivial;
    destruct θ1; try (destruct decide); trivial; simp e_rule; simpl;
    repeat erewrite ?HeqE, ?HeqA; trivial.
  - destruct θ1; try (destruct decide); trivial; simp e_rule; simpl;
    repeat erewrite ?HeqE, ?HeqA; trivial.
    repeat destruct decide ; auto ; repeat erewrite ?HeqE, ?HeqA; trivial.
  - f_equal. apply HeqE.
  - repeat erewrite ?HeqE, ?HeqA; trivial.
Qed.

Lemma e_rule_9_cong_strong  Δ ϕ E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @e_rule_9 Δ ϕ E1 A1 = @e_rule_9 Δ ϕ E2 A2.
Proof.
intros HeqE HeqA.
destruct Δ ; simp a_rule_env; simp e_rule_9; simpl; trivial. f_equal. trivial.
Qed.

Lemma e_rule_12_cong_strong  Δ ϕ θ₁ θ₂ (Hin11 Hin12: θ₁ ∈ Δ) (Hin21 Hin22: θ₂ ∈ Δ) E1 A1 E2 A2:
(forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
(forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
@e_rule_12 Δ ϕ E1 A1 θ₁ θ₂ Hin11 Hin21 = @e_rule_12 Δ ϕ E2 A2 θ₁ θ₂ Hin12 Hin22.
Proof.
  intros HeqE HeqA.
  destruct θ₁; simp a_rule_env; simp e_rule_12 ; simpl; trivial; repeat (destruct decide).
  destruct θ₁1; simp a_rule_env; simp e_rule_12 ; simpl; trivial; repeat (destruct decide).
  destruct θ₂; simp a_rule_env; simp e_rule_12 ; simpl; trivial; repeat (destruct decide).
  repeat erewrite ?HeqE, ?HeqA; trivial.
Qed.

Lemma a_rule_env_cong_strong  p Δ ϕ θ Hin1 Hin2  E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @a_rule_env p Δ ϕ E1 A1 θ Hin1 = @a_rule_env p Δ ϕ E2 A2 θ Hin2.
Proof.
intros HeqE HeqA.
  destruct θ; simp a_rule_env; simpl; trivial; repeat (destruct decide).
  - f_equal; repeat erewrite ?HeqE, ?HeqA; trivial;
    destruct θ1; try (destruct decide); trivial; simp a_rule_env; simpl;
    repeat erewrite ?HeqE, ?HeqA; trivial.
  - destruct θ1; try (destruct decide); trivial; simp a_rule_env; simpl;
    repeat erewrite ?HeqE, ?HeqA; trivial. repeat destruct decide ; auto.
    repeat erewrite ?HeqE, ?HeqA; trivial.
  - f_equal ; f_equal ; [ apply HeqE | apply HeqA].
Qed.

Lemma a_rule_form_cong_strong  p Δ ϕ E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @a_rule_form p Δ ϕ E1 A1 = @a_rule_form p Δ ϕ E2 A2.
Proof.
intros HeqE HeqA.
destruct ϕ as [ ϕ | ] ;
[ destruct ϕ ; simp a_rule_form; simpl; trivial; repeat (destruct decide) ;
f_equal ; repeat erewrite ?HeqE, ?HeqA; trivial | auto].
Qed.

Lemma a_rule_env17_cong_strong  Δ ϕ θ1 θ2 Hin11 Hin12 Hin21 Hin22  E1 A1 E2 A2:
  (forall pe Hpe1 Hpe2, E1 pe Hpe1 = E2 pe Hpe2) ->
  (forall pe Hpe1 Hpe2, A1 pe Hpe1 = A2 pe Hpe2) ->
  @a_rule_env17 Δ ϕ E1 A1 θ1 θ2 Hin11 Hin21 = @a_rule_env17 Δ ϕ E2 A2 θ1 θ2 Hin12 Hin22.
Proof.
intros HeqE HeqA.
destruct θ1; simp a_rule_env17; simpl; trivial; repeat (destruct decide).
destruct θ1_1; simp a_rule_env17; simpl; trivial; repeat (destruct decide).
destruct θ2; simp a_rule_env17; simpl; trivial; repeat (destruct decide).
f_equal; repeat erewrite ?HeqE, ?HeqA; trivial.
Qed.

Lemma EA_cong  p Δ ϕ: EA p true (Δ, ϕ) = EA p true (Δ, None).
Proof.
simp EA; simpl. f_equal. apply e_rules_cong.
Qed.


(** ** Correctness *)
Section Correctness.
Context {p : nat}.


(** This section contains the proof of Proposition 5, the main correctness result, stating that the E- and A-formulas defined above are indeed existential and universal propositional quantified versions of the original formula, respectively. *)

(** *** (i) Variables *)
Section VariablesCorrect.

(** In this subsection we prove (i), which states that the variable p no longer
  occurs in the E- and A-formulas, and that the E- and A-formulas contain no more variables than the original formula.
  *)

(* A general tactic for variable occurrences *)

(* I modified it from Hugo's work, but it only partially works. *)

Ltac vars_tac :=
intros; subst;
repeat match goal with
| HE : context [occurs_in ?x (?E _ _)], H : occurs_in ?x (?E _ _) |- _ =>
    apply HE in H
end;
intuition;
repeat match goal with | H : exists x, _ |- _ => destruct H end;
intuition;
simpl in *; in_tac; try (split; [tauto || auto with *|]); simpl in *;
try match goal with
| H : occurs_in _ (?a  → (?b  → ?c)) |- _ => apply occurs_in in H
| H : occurs_in _ (?a ∨ ?b) |- _ => apply occurs_in in H
| H : occurs_in _ (?a ∧ ?b) |- _ => apply occurs_in in H
|H1 : ?x0 ∈ (⊗ ?Δ), H2 : occurs_in ?x ?x0 |- _ =>
      apply (occurs_in_map_l_open_boxes _ _ _ H2) in H1
|H1 : ?x0 ∈ (l_open_boxes ?Δ), H2 : occurs_in ?x ?x0 |- _ =>
      apply (occurs_in_map_l_open_boxes _ _ _ H2) in H1
end; repeat rewrite elem_of_cons in * ; intuition; subst;
repeat match goal with | H : exists x, _ |- _ => destruct H end; intuition;
try multimatch goal with
| H : ?θ0 ∈ ?Δ0 |- context [exists θ, θ ∈ ?Δ /\ occurs_in ?x θ] =>
  solve[try right; exists θ0; split; [eauto using remove_include|simpl; tauto]; eauto] end.

(** **** (a)  *)

Lemma e_rule_vars  Δ (θ : form) (Hin : θ ∈ Δ) (ϕ : option form)
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HE0 : ∀ pe Hpe,
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in_opt x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))) :
occurs_in x (@e_rule p _ _ E0 A0 θ Hin) -> x ≠ p ∧ ∃ θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
destruct θ; simp e_rule ; repeat case decide ; try now repeat vars_tac.
- intro. destruct θ1; simp e_rule in H ; repeat case decide ; try now repeat vars_tac.
  + case decide in H.
      * apply HE0 in H. firstorder. inversion H0 ; subst.
        -- exists (# n → θ2) ; split ; cbn ; auto.
        -- exists x0; split; [eauto using remove_include |simpl; tauto]; eauto.
      * case decide in H ; cbn in H ; [ subst ; exfalso ; firstorder | ].
        destruct H ; subst ; firstorder. apply HE0 in H. vars_tac.
Qed.

Lemma e_rule_9_vars  Δ (ϕ : option form)
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HE0 : ∀ pe Hpe,
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in_opt x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))) :
occurs_in x (@e_rule_9 _ _ E0 A0) -> x ≠ p ∧ ∃ θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
destruct Δ; simp e_rule_9 ; try now vars_tac. cbn. destruct f; simp e_rule_9 ; vars_tac.
1-5: exists x1 ; split ; [ right ; auto |simpl; tauto]; eauto.
- exists (□ f) ; split ; [  eauto using remove_include, l_open_boxes_in ; left ; auto|simpl; tauto]; eauto.
- exists (□ x0) ; split ; [  right ; eauto using remove_include, l_open_boxes_in |simpl; tauto]; eauto.
- exists x1 ; split ; [  right ; eauto using remove_include, l_open_boxes_in |simpl; tauto]; eauto.
Qed.

Lemma e_rule_12_vars  Δ (θ1 θ2 : form) (Hin1 : θ1 ∈ Δ) (Hin2 : θ2 ∈ Δ) (ϕ : option form)
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HE0 : ∀ pe Hpe,
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in_opt x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))) :
occurs_in x (@e_rule_12 _ _ E0 A0 θ1 θ2 Hin1 Hin2) -> x ≠ p ∧ ∃ θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
destruct θ1; simp e_rule_12 ; repeat case decide ; try now repeat vars_tac.
destruct θ1_1; simp e_rule_12 ; repeat case decide ; try now repeat vars_tac.
destruct θ2; simp e_rule_12 ; repeat case decide ; try now repeat vars_tac.
cbn ; intro H. destruct H as [ [ H | H ] | H] ; try now repeat vars_tac.
- vars_tac. exists (□ x0) ; split ; [ |simpl; tauto]; eauto.
  apply l_open_boxes_in in H. do 2 apply remove_include in H ; auto.
  all: apply elem_of_list_In ; apply in_in_rm ; auto ; apply elem_of_list_In ; auto.
- apply HE0 in H. firstorder. cbn in H0 ; inversion H0 ; subst ; try now vars_tac.
  apply l_open_boxes_in in H4. do 2 apply remove_include in H4 ; auto. vars_tac.
  all: apply elem_of_list_In ; apply in_in_rm ; auto ; apply elem_of_list_In ; auto.
Qed.


(** **** (b) *)

Lemma a_rule_env_vars  Δ θ Hin ϕ
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HEA0 : ∀ pe Hpe,
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in_opt x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))):
occurs_in x (@a_rule_env p _ _ E0 A0 θ Hin) -> x ≠ p ∧ (occurs_in_opt x ϕ \/ ∃ θ, θ ∈ Δ /\ occurs_in x θ).
Proof.
destruct θ; simp a_rule_env; simpl; try tauto; try solve [repeat case decide; repeat vars_tac].
destruct θ1; simp a_rule_env; repeat case decide; repeat vars_tac.
intros ; split ; repeat vars_tac.
left. destruct ϕ ; cbn in * ; try contradiction.
destruct f ; cbn in * ; try contradiction ; auto.
Qed.


Lemma a_rule_form_vars  Δ ϕ
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HEA0 : ∀ pe Hpe,
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in_opt x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))):
  occurs_in x (@a_rule_form p _ _ E0 A0) -> x ≠ p ∧ (occurs_in_opt x ϕ \/ ∃ θ, θ ∈ Δ /\ occurs_in x θ).
Proof.
destruct ϕ as [ϕ | ] ; 
[ destruct ϕ; simp a_rule_form; simpl; try tauto; try solve [repeat case decide; repeat vars_tac] | 
  auto].
Qed.

Lemma a_rule_env17_vars  Δ θ1 θ2 Hin1 Hin2 ϕ
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
   x
  (HEA0 : ∀ pe Hpe,
      (occurs_in x (E0 pe Hpe) -> x ≠ p ∧ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ) /\
      (occurs_in x (A0 pe Hpe) -> x ≠ p ∧ (occurs_in_opt x pe.2 \/ ∃ θ, θ ∈ pe.1 /\ occurs_in x θ))):
  occurs_in x (@a_rule_env17 _ _ E0 A0 θ1 θ2 Hin1 Hin2) -> x ≠ p ∧ (occurs_in_opt x ϕ \/ ∃ θ, θ ∈ Δ /\ occurs_in x θ).
Proof.
destruct θ1; simp a_rule_env17; simpl; try tauto; try solve [repeat case decide; repeat vars_tac].
destruct θ1_1; simp a_rule_env17; simpl; try tauto; try solve [repeat case decide; repeat vars_tac].
destruct θ2; simp a_rule_env17; simpl; try tauto; try solve [repeat case decide; repeat vars_tac].
cbn ; intro. destruct H as [ [ H | H ] | H] ; try now vars_tac.
- apply HEA0 in H. firstorder. cbn in H0. inversion H0 ; subst.
  + right ; exists (◊θ2) ; split ; auto.
  + right ; exists (□ x0) ; split ; auto. apply l_open_boxes_in in H4. do 2 apply remove_include in H4 ; auto.
    all: apply elem_of_list_In ; apply in_in_rm ; auto ; apply elem_of_list_In ; auto.
- apply HEA0 in H. firstorder. cbn in H0. inversion H0 ; subst.
  + right ; exists (◊θ2) ; split ; auto.
  + right ; exists (□ x0) ; split ; auto. apply l_open_boxes_in in H4. do 2 apply remove_include in H4 ; auto.
    all: apply elem_of_list_In ; apply in_in_rm ; auto ; apply elem_of_list_In ; auto.
Qed.

Proposition EA_vars  Δ ϕ x:
  (occurs_in x (E p Δ) -> x <> p /\ ∃ θ, θ ∈ Δ /\ occurs_in x θ) /\
  (occurs_in x (A p (Δ, ϕ)) -> x <> p /\ (occurs_in_opt x ϕ \/ (∃ θ, θ ∈ Δ /\ occurs_in x θ))).
Proof.
remember (Δ, ϕ) as pe.
replace Δ with pe.1 by now subst.
replace ϕ with pe.2 by now subst. clear Heqpe Δ ϕ.
unfold E, A in *. simp EA; simpl. revert pe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros [Δ ϕ] Hind. simpl. split.
(* E *)
- intros Hocc. destruct Hocc.
  + apply e_rule_9_vars in H ; auto.
    intros pe Hpe. eapply pointed_env_order_None_R in Hpe.
    apply Hind in Hpe. destruct (e_rules_cong p pe.1 pe.2) as ((He & He9) & He12).
    rewrite <- He9 in Hpe.
    destruct Hpe. split ; auto.
    * intro. apply H0. simp EA in H2 ; cbn in H2. destruct H2.
      -- left. exact H2.
      -- right. erewrite in_map_ext, in_map2_ext. exact H2. all: auto.
    * intro. apply H1. simp EA in H2 ; cbn in H2. auto.
  + apply occurs_in_list_conj in H as (θ & H & H0).
    apply elem_of_app in H. destruct H.
    * apply in_in_map in H as (ψ&Hin&Heq). subst.
      apply e_rule_vars in H0 ; auto.
      intros pe Hpe. eapply pointed_env_order_None_R in Hpe.
      apply Hind in Hpe. destruct (e_rules_cong p pe.1 pe.2) as ((He & He9) & He12).
      rewrite <- He9 in Hpe.
      destruct Hpe. split ; auto.
      -- intro. apply H. simp EA in H2 ; cbn in H2. destruct H2.
        ++ left. exact H2.
        ++ right. erewrite in_map_ext, in_map2_ext. exact H2. all: auto.
      -- intro. apply H1. simp EA in H2 ; cbn in H2. auto.
    * apply in_in_map2 in H as (ψ1 & ψ2 & Hin1 & Hin2 & Heq). subst.
      apply e_rule_12_vars in H0 ; auto.
      intros pe Hpe. eapply pointed_env_order_None_R in Hpe.
      apply Hind in Hpe. destruct (e_rules_cong p pe.1 pe.2) as ((He & He9) & He12).
      rewrite <- He9 in Hpe.
      destruct Hpe. split ; auto.
      -- intro. apply H. simp EA in H2 ; cbn in H2. destruct H2.
        ++ left. exact H2.
        ++ right. erewrite in_map_ext, in_map2_ext. exact H2. all: auto.
      -- intro. apply H1. simp EA in H2 ; cbn in H2. auto.
(* A *)
- intro Hocc. destruct Hocc.
  + apply a_rule_form_vars in H ; auto.
    intros pe Hpe. apply Hind in Hpe.
    destruct (e_rules_cong p pe.1 pe.2) as ((He & He9) & He12).
    rewrite <- He9 in Hpe.
    destruct Hpe. split ; auto.
    * intro. apply H0. simp EA in H2 ; cbn in H2. destruct H2.
      -- left. exact H2.
      -- right. erewrite in_map_ext, in_map2_ext. exact H2. all: auto.
    * intro. apply H1. simp EA in H2 ; cbn in H2. auto.
  + apply occurs_in_list_disj in H as (θ & H & H0).
    apply elem_of_app in H. destruct H.
    * apply in_in_map in H as (ψ & Hin & Heq). subst.
      apply a_rule_env_vars in H0 ; auto.
      intros pe Hpe. apply Hind in Hpe.
      destruct (e_rules_cong p pe.1 pe.2) as ((He & He9) & He12).
      rewrite <- He9 in Hpe.
      destruct Hpe. split ; auto.
      -- intro. apply H. simp EA in H2 ; cbn in H2. destruct H2.
        ++ left. exact H2.
        ++ right. erewrite in_map_ext, in_map2_ext. exact H2. all: auto.
      -- intro. apply H1. simp EA in H2 ; cbn in H2. auto.
    * apply in_in_map2 in H as (ψ1 & ψ2 & Hin1 & Hin2 & Heq). subst.
      apply a_rule_env17_vars in H0 ; auto.
      intros pe Hpe. apply Hind in Hpe.
      destruct (e_rules_cong p pe.1 pe.2) as ((He & He9) & He12).
      rewrite <- He9 in Hpe.
      destruct Hpe. split ; auto.
      -- intro. apply H. simp EA in H2 ; cbn in H2. destruct H2.
        ++ left. exact H2.
        ++ right. erewrite in_map_ext, in_map2_ext. exact H2. all: auto.
      -- intro. apply H1. simp EA in H2 ; cbn in H2. auto.
Qed.

End VariablesCorrect.

Ltac foldEA := repeat match goal with
| |- context C [EA _ true ?pe] => fold (@E p _ pe)
| |- context C [EA _ false ?pe] => fold (@A p _ pe)
end.

(** *** (ii) Entailment *)
Section EntailmentCorrect.

(** In this section we prove (ii), which states that the E- and A-formula are
  entailed by the original formula and entail the original formula,
  respectively. *)

Ltac l_tac := repeat rewrite list_to_set_disj_open_boxes;
    rewrite (proper_Provable _ _ (list_to_set_disj_env_add _ _) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _))) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)))) _ _ eq_refl).

Ltac equivbox := apply env_equiv_eq ; apply list_to_set_disj_perm ; apply l_open_boxes_perm ;
         apply gmultiset_elements_list_to_set_disj.

Lemma a_rule_env_spec  (Δ : list form) θ ϕ Hin
  (E0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (A0 : ∀ pe (Hpe : pe ≺· (Δ, ϕ)), form)
  (HEA : forall Δ ϕ Hpe, (list_to_set_disj Δ ⊢ Some (E0 (Δ, ϕ) Hpe)) * (list_to_set_disj  Δ• A0 (Δ, ϕ) Hpe ⊢ ϕ)) :
  (list_to_set_disj  Δ • @a_rule_env p _ _ E0 A0 θ Hin ⊢ ϕ).
Proof with (auto with proof).
assert (HE := λ Δ0 ϕ0 Hpe, fst (HEA Δ0 ϕ0 Hpe)).
assert (HA := λ Δ0 ϕ0 Hpe, snd (HEA Δ0 ϕ0 Hpe)).
clear HEA.
assert(Hi : θ ∈ list_to_set_disj  Δ) by now apply elem_of_list_to_set_disj.
destruct θ; simp a_rule_env; simpl; exhibit Hi 1;
match goal with |- ?d ∖ {[?f]} • _ • _ ⊢ _ => rw (list_to_set_disj_rm Δ f) 2 end.
- simpl; case decide; intro Hp.
  + subst. case_decide; subst; auto with proof.
  + exch 0...
- constructor 2.
- simpl; exch 0. apply AndL. exch 1; exch 0. do 2 l_tac...
- exch 0. apply OrL; exch 0.
  + apply AndL. exch 0. l_tac. apply ImpL... exch 0 ; apply weakening...
  + apply AndL. l_tac. exch 0...
- destruct θ1; simp a_rule_env; simpl.
  + case decide; intro Hp.
    * assert (Hin'' : Var n ∈ (list_to_set_disj (rm (#n → θ2) Δ) : env))
       by (rewrite <- list_to_set_disj_rm; apply in_difference; try easy; now apply elem_of_list_to_set_disj).
       exhibit Hin'' 2. exch 0; exch 1. apply ImpLVar. exch 0. backward.
       rewrite env_add_remove. exch 0. l_tac...
    * case decide; intro; subst.
     -- apply ExFalso.
     -- constructor 4. exch 0. exch 1. exch 0. apply ImpLVar.
         exch 0. exch 1. l_tac. apply weakening...
  + constructor 2.
  + exch 0. apply ImpLAnd. exch 0. l_tac...
  + exch 0. apply ImpLOr. exch 1. l_tac. exch 0. l_tac...
  + exch 0. apply ImpLImp; exch 0.
      * apply AndL. exch 0. l_tac.
         apply ImpR. exch 0.  exch 1. l_tac...
      * apply AndL. exch 0. l_tac. apply weakening, HA.
  + apply AndL. exch 1. exch 0. apply ImpBox.
    * repeat rewrite open_boxes_disj_union. rewrite open_boxes_singleton_t ; [ | cbn ; auto].
      apply generalised_weakeningR. apply weak_ImpL.
      -- peapply HE. rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox.
      -- peapply HA. apply equiv_disj_union_compat_r. rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox.
    * exch 1. exch 0. apply weakening. exch 0. peapply HA.
      apply equiv_disj_union_compat_r. ms.
  + apply AndL. exch 0. exch 1. exch 0. apply ImpDiam.
    * remember (A0 ((rm (◊ θ1 → θ2) Δ • θ2)%list, ϕ) (a_rule_env_obligations_obligation_18 Δ ϕ E0 A0 θ1 θ2 Hin)) as ψ.
      (* Inelegant case distinction but which is proof-theoretically relevant. *)
      destruct (is_box ψ) eqn:E.
      -- rewrite open_boxes_add_t ; auto. exch 0. apply weakening.
         apply weak_ImpL.
         ++ peapply HE. rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox.
         ++ peapply HA. apply equiv_disj_union_compat_r. rewrite open_boxes_open_boxes'. unfold open_boxes'.
            equivbox.
      -- rewrite open_boxes_add_f ; auto. apply weak_ImpL.
         ++ peapply HE. rewrite open_boxes_open_boxes'. unfold open_boxes'.
            equivbox.
         ++ peapply HA. apply equiv_disj_union_compat_r. rewrite open_boxes_open_boxes'. unfold open_boxes'.
            equivbox.
    * exch 0. apply weakening. exch 0. peapply HA.
      apply equiv_disj_union_compat_r. ms.
- auto with proof.
- exch 0 ; apply DiamL. rewrite open_boxes_add_t ; auto ; cbn.
  exch 0 ; apply weak_ImpL.
  + peapply HE. rewrite <- list_to_set_disj_env_add.
    rewrite open_boxes_open_boxes'.
    enough (open_boxes' (list_to_set_disj (rm (◊ θ) Δ)) ≡ list_to_set_disj (l_open_boxes (rm (◊ θ) Δ))) by ms.
    rewrite <- open_boxes_open_boxes'.  rewrite list_to_set_disj_open_boxes.
    rewrite l_open_boxes_open_boxes_perm ; auto.
  + peapply HA.
    enough ((⊗ list_to_set_disj (rm (◊ θ) Δ) • θ) ≡ list_to_set_disj (l_open_boxes (rm (◊ θ) Δ) • θ)).
    * erewrite <- H. ms.
    * rewrite list_to_set_disj_open_boxes. rewrite <- list_to_set_disj_env_add.
      rewrite l_open_boxes_open_boxes_perm ; reflexivity.
Qed.

Proposition entail_correct Δ ϕ :
  (list_to_set_disj Δ ⊢ Some (E p Δ)) *
  (list_to_set_disj Δ•A p (Δ, ϕ) ⊢ ϕ).
Proof with (auto with proof).
remember (Δ, ϕ) as pe.
replace Δ with pe.1 by now subst.
replace ϕ with pe.2 by now subst. clear Heqpe Δ ϕ. revert pe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
unfold pointed_env_order.
intros (Δ, ϕ) Hind. simpl.
unfold E, A. simp EA. simpl.
(* uncurry the induction hypothesis for convenience *)
assert (HE := fun d x=> fst (Hind (d, None) x)).
assert (HA := fun d f x=> snd (Hind (d, f) x)).
unfold E, A in *; simpl in HE, HA.
simpl in *. clear Hind.
split.
{
(* E *)
apply AndR.
- destruct Δ ; simp e_rule_9 ; [ cbn ; apply ImpR ; apply ExFalso | ].
  apply BoxR. peapply HE.
  + order_tac. destruct (is_box f) eqn:E.
    * destruct f ; cbn in E ; try discriminate. destruct ϕ ; order_tac.
    * destruct f ; cbn in E ; try discriminate ; destruct ϕ ; order_tac.
  + rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox.
- apply list_conjR. intros φ Hin. apply in_app_orT in Hin. destruct Hin as [Hin | Hin].
  + apply elem_of_list_In in Hin. apply in_in_map in Hin.
    destruct Hin as (ψ & Hin & Heq). subst φ.
    assert(Hi : ψ ∈ list_to_set_disj  Δ) by now apply elem_of_list_to_set_disj.
    dependent destruction ψ; simp e_rule; exhibit Hi 0;
    match goal with |- ?d ∖ {[?f]} • _ ⊢ _ => rw (list_to_set_disj_rm Δ f) 1 end.
    * case decide; intro; subst; simpl; auto using HE with proof. apply ImpR ; apply ExFalso.
    * auto with proof.
    * apply AndL. do 2 l_tac... peapply HE. destruct ϕ ; order_tac.
    * apply OrL.
      -- l_tac. apply OrR1, HE. destruct ϕ ; order_tac.
      -- l_tac. apply OrR2, HE. destruct ϕ ; order_tac.
    * dependent destruction ψ1; simp e_rule; simpl; auto 3 using HE with proof.
      -- case decide; intro Hp.
        ++ assert(Hin'' : Var n ∈ (list_to_set_disj (rm (#n → ψ2) Δ) : env))
              by (rewrite <- list_to_set_disj_rm; apply in_difference; try easy; now apply elem_of_list_to_set_disj).
              exhibit Hin'' 1. apply ImpLVar. exch 0. backward. rewrite env_add_remove.
              l_tac. apply HE... destruct ϕ ; order_tac.
        ++ case decide; intro; subst.
          ** apply ImpR, ExFalso.
          ** apply ImpR. exch 0. apply ImpLVar. exch 0.
              l_tac. apply weakening, HE. destruct ϕ ; order_tac.
      -- apply ImpR, ExFalso.
      -- apply ImpLAnd. l_tac... peapply HE. destruct ϕ ; order_tac.
      -- apply ImpLOr. do 2 l_tac... peapply HE. destruct ϕ ; order_tac.
      -- apply ImpR. exch 0. apply ImpLImp.
        ++ exch 0. l_tac. apply ImpR. exch 0. l_tac. apply weak_ImpL.
          ** apply HE. destruct ϕ ; order_tac.
          ** peapply HA. destruct ϕ ; order_tac.
        ++ exch 0. l_tac. apply weakening. apply HE. destruct ϕ ; order_tac.
      -- apply ImpR. exch 0. apply ImpBox.
        ++ rewrite open_boxes_add_t ; cbn ; auto. apply weak_ImpL.
          ** rewrite open_boxes_open_boxes'. unfold open_boxes'. peapply HE ; [destruct ϕ ; order_tac | equivbox ].
          ** rewrite open_boxes_open_boxes'. unfold open_boxes'. peapply HA.
             Unshelve. 3: exact (l_open_boxes (rm (□ ψ1 → ψ2) Δ)).
             --- destruct ϕ ; order_tac.
             --- apply equiv_disj_union_compat_r. equivbox.
        ++ exch 0. l_tac. apply weakening, HE. destruct ϕ ; order_tac.
      -- apply ImpR. exch 0 ; apply ImpDiam.
        ++ apply weak_ImpL.
          ** rewrite open_boxes_open_boxes'. unfold open_boxes'. peapply HE ; [destruct ϕ ; order_tac | equivbox].
          ** rewrite open_boxes_open_boxes'. unfold open_boxes'. peapply HA.
             Unshelve. 3: exact (l_open_boxes (rm (◊ ψ1 → ψ2) Δ)).
             --- destruct ϕ ; order_tac.
             --- apply equiv_disj_union_compat_r. equivbox.
        ++ exch 0. l_tac. apply weakening, HE. destruct ϕ ; order_tac.
    * apply BoxR. rewrite open_boxes_add_t ; cbn ; auto.
      rewrite open_boxes_open_boxes'. unfold open_boxes'. peapply HE ; [destruct ϕ ; order_tac | ].
      repeat rewrite <- list_to_set_disj_env_add. apply env_equiv_eq. f_equal. 
      apply list_to_set_disj_perm ; apply l_open_boxes_perm ; apply gmultiset_elements_list_to_set_disj.
    * apply DiamL. rewrite open_boxes_open_boxes'. unfold open_boxes'. peapply HE ; [destruct ϕ ; order_tac | ].
      repeat rewrite <- list_to_set_disj_env_add. apply env_equiv_eq. f_equal. 
      apply list_to_set_disj_perm ; apply l_open_boxes_perm ; apply gmultiset_elements_list_to_set_disj.
  + apply elem_of_list_In in Hin. apply in_in_map2 in Hin.
    destruct Hin as (ψ1 & ψ2 & Hin1 & Hin2 & Heq). subst φ.
    assert(Hi : ψ1 ∈ list_to_set_disj Δ) by now apply elem_of_list_to_set_disj.
    dependent destruction ψ1; simp e_rule_12; exhibit Hi 0;
    match goal with |- ?d ∖ {[?f]} • _ ⊢ _ => rw (list_to_set_disj_rm Δ f) 1 end ; try now (apply ImpR,ExFalso).
    dependent destruction ψ1_1; simp e_rule_12 ; try now (apply ImpR,ExFalso).
    dependent destruction ψ2; simp e_rule_12 ; try now (apply ImpR,ExFalso).
    eassert (Hii : ◊ ψ2 ∈ (list_to_set_disj (rm (◊ ψ1_1 → ψ1_2) Δ))).
    { apply elem_of_list_to_set_disj. apply elem_of_list_In,in_in_rm ; auto. 
      apply elem_of_list_In ; auto. }
    exhibit Hii 1. cbn. apply ImpR. exch 0 ; exch 1. apply ImpDiam.
    * rewrite open_boxes_add_t ; cbn ; auto. exch 0. apply weak_ImpL.
      -- repeat rewrite l_open_boxes_rm ; cbn ; auto. peapply HE.
        ++ destruct ϕ as [ϕ | ] ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl).
           all: apply env_order_lt_le_trans with (rm (◊ ψ2) Δ • (◊ ψ2))%list ; [ | apply remove_In_env_order_refl ; apply elem_of_list_In ; auto] ; 
           apply env_order_compat ; [ cbn ; lia | ] ;
           rewrite <- l_open_boxes_rm with (ϕ:=◊ ψ2) ; [ | cbn ; auto] ;
           apply l_open_boxes_env_order.
        ++ rewrite open_boxes_open_boxes'. unfold open_boxes'.
           repeat rewrite <- list_to_set_disj_env_add. apply env_equiv_eq. f_equal. 
           apply list_to_set_disj_perm. rewrite l_open_boxes_perm ; [ | apply elements_setminus].
           rewrite l_open_boxes_rm ; cbn ; auto.
           rewrite l_open_boxes_perm ; [ | rewrite <- list_to_set_disj_rm ; apply elements_setminus].
           rewrite l_open_boxes_rm ; cbn ; auto.
           apply l_open_boxes_perm. apply gmultiset_elements_list_to_set_disj.
      -- rewrite open_boxes_open_boxes'. unfold open_boxes'. peapply HA.
         Unshelve. 3: exact ((l_open_boxes (rm (◊ ψ2) (rm (◊ ψ1_1 → ψ1_2) Δ)) • ψ2)%list).
        ++ repeat rewrite l_open_boxes_rm ; cbn ; auto. destruct ϕ ; order_tac.
           do 2 apply env_order_cancel_right. 
           all: apply env_order_lt_le_trans with (rm (◊ ψ1_1 → ψ1_2) (rm (◊ ψ2) Δ) • (◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list ;
           [  apply env_order_2 ; cbn ; try lia ; apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia ;
              rewrite <- l_open_boxes_rm with (ϕ:=◊ ψ2) ; [ | cbn ; auto] ;
              rewrite <- l_open_boxes_rm with (ϕ:=(◊ ψ1_1 → ψ1_2)) ; [ | cbn ; auto] ;
              apply l_open_boxes_env_order | 
              apply env_order_refl_trans with ((rm (◊ ψ2) Δ) • (◊ ψ2))%list ;
              [ | apply remove_In_env_order_refl ; apply elem_of_list_In ; auto] ;
              apply env_order_refl_trans with (rm (◊ ψ1_1 → ψ1_2) ((rm (◊ ψ2) Δ) • ◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list ;
              [ cbn ; left | apply remove_In_env_order_refl ; apply elem_of_list_In ; auto] ;
              apply elem_of_list_In ; right ; apply in_in_rm ; auto ; apply elem_of_list_In ; auto].
        ++ apply equiv_disj_union_compat_r.
           repeat rewrite <- list_to_set_disj_env_add. apply env_equiv_eq. f_equal. 
           apply list_to_set_disj_perm. 
           rewrite l_open_boxes_perm ; [ | apply elements_setminus].
           rewrite l_open_boxes_rm ; cbn ; auto.
           rewrite l_open_boxes_perm ; [ | rewrite <- list_to_set_disj_rm ; apply elements_setminus].
           repeat (rewrite l_open_boxes_rm ; cbn ; auto).
           apply l_open_boxes_perm. apply gmultiset_elements_list_to_set_disj.
    * exch 1 ; exch 0. apply weakening. peapply HE ; [ destruct ϕ ; order_tac | ].
      rewrite <- list_to_set_disj_env_add. apply equiv_disj_union_compat_r.
      rewrite <- difference_singleton ; auto.
} 
(* A *)
apply OrL.
- destruct ϕ as [ ϕ | ].
  { destruct ϕ; simp a_rule_form. 
  + case decide; intro; subst; [constructor 2|constructor 1].
  + auto using HE with proof.
  + apply AndR; apply AndL; auto using HE with proof.
  + auto using HE with proof.
  + apply ImpR. exch 0. l_tac. apply ImpL; auto using HE, HA with proof.
  + apply BoxR. rewrite open_boxes_add_t ; cbn ; auto. apply weak_ImpL.
    * peapply HE. order_tac. rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox. 
    * peapply HA. Unshelve. 3: exact (l_open_boxes Δ). order_tac.
      apply equiv_disj_union_compat_r. rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox.
  + apply DiamL. apply weak_ImpL.
    * peapply HE. order_tac. rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox.
    * peapply HA. Unshelve. 3: exact (l_open_boxes Δ). order_tac.
      apply equiv_disj_union_compat_r. rewrite open_boxes_open_boxes'. unfold open_boxes'. equivbox. }
  { simp a_rule_form. apply ExFalso. }
- apply list_disjL. intros φ Hin. apply in_app_orT in Hin ; destruct Hin as [Hin | Hin].
  + apply elem_of_list_In in Hin. apply in_in_map in Hin as (φ' & Heq & Hφ'). subst φ.
    apply a_rule_env_spec; intros.
    rewrite EA_cong. split ; apply HE || apply HA; destruct ϕ ; order_tac ;
    eapply pointed_env_order_None_L in Hpe ; exact Hpe.

  + apply elem_of_list_In in Hin. apply in_in_map2 in Hin as (ψ1 & ψ2 & Hin1 & Hin2 & Heq). subst φ.
      destruct ψ1 ; simp a_rule_env17 ; try now apply ExFalso.
      destruct ψ1_1 ; simp a_rule_env17 ; try now apply ExFalso.
      destruct ψ2 ; simp a_rule_env17 ; try now apply ExFalso.
      cbn. apply elem_of_list_to_set_disj in Hin1. exhibit Hin1 1.
      apply elem_of_list_to_set_disj in Hin2.
      eassert (Hin2' : ◊ ψ2 ∈ list_to_set_disj Δ ∖ {[◊ ψ1_1 → ψ1_2]}).
      apply in_difference ; auto. exact Hin2. exhibit Hin2' 2. apply AndL.
      exch 1 ; exch 2 ; exch 0 ; exch 1. apply ImpDiam.
      -- destruct (is_box (EA p false ((rm (◊ ψ1_1 → ψ1_2) Δ • ψ1_2)%list, ϕ))) eqn:E.
         ++ rewrite open_boxes_add_t ; cbn ; auto. exch 0. apply weakening.
            rewrite open_boxes_add_t ; cbn ; auto. exch 0. apply weak_ImpL.
            ** peapply HE.
               --- destruct ϕ as [ϕ | ] ; cbn ; order_tac.
                   +++ apply env_order_cancel_right. rewrite rm_comm. apply env_order_1' ; [ cbn ; lia | ].
                       rewrite l_open_boxes_rm ; auto. apply l_open_boxes_env_order.
                   +++ rewrite rm_comm. apply env_order_1' ; [ cbn ; lia | rewrite l_open_boxes_rm ; auto ; apply l_open_boxes_env_order].
               --- rewrite open_boxes_open_boxes'. unfold open_boxes'.
                   rewrite <- list_to_set_disj_env_add.
                   apply equiv_disj_union_compat_r.
                   apply env_equiv_eq. apply list_to_set_disj_perm. 
                   rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                   rewrite l_open_boxes_rm ; cbn ; auto.
                   rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                   repeat (rewrite l_open_boxes_rm ; cbn ; auto). apply l_open_boxes_perm ;
                   apply gmultiset_elements_list_to_set_disj.
            ** peapply HA. Unshelve. 3: exact ((l_open_boxes (rm (◊ ψ2) (rm (◊ ψ1_1 → ψ1_2) Δ)) • ψ2)%list).
               --- destruct ϕ ; order_tac.
                    *** apply env_order_0'. apply env_order_env_order_refl. rewrite rm_comm.
                        apply env_order_lt_le_trans with (rm (◊ ψ1_1 → ψ1_2) (rm (◊ ψ2) Δ) • (◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list.
                        ---- apply env_order_2 ; cbn ; try lia. apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia.
                             apply l_open_boxes_env_order.
                        ---- apply env_order_refl_trans with (rm (◊ ψ1_1 → ψ1_2) ((rm (◊ ψ2) Δ) • ◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list ;
                              [ cbn ; left | apply remove_In_env_order_refl ; apply elem_of_list_In ; auto].
                              apply elem_of_list_In. right. apply in_in_rm ; auto. apply elem_of_list_In ; auto.
                    *** rewrite rm_comm.
                        apply env_order_lt_le_trans with (rm (◊ ψ1_1 → ψ1_2) (rm (◊ ψ2) Δ) • (◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list.
                        ---- apply env_order_2 ; cbn ; try lia. apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia.
                             apply l_open_boxes_env_order.
                        ---- apply env_order_refl_trans with (rm (◊ ψ1_1 → ψ1_2) ((rm (◊ ψ2) Δ) • ◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list ;
                              [ cbn ; left | apply remove_In_env_order_refl ; apply elem_of_list_In ; auto].
                              apply elem_of_list_In. right. apply in_in_rm ; auto. apply elem_of_list_In ; auto.
               --- apply equiv_disj_union_compat_r. rewrite open_boxes_open_boxes'. unfold open_boxes'.
                   rewrite <- list_to_set_disj_env_add.
                   apply equiv_disj_union_compat_r.
                   apply env_equiv_eq. apply list_to_set_disj_perm. 
                   rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                   rewrite l_open_boxes_rm ; cbn ; auto.
                   rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                   repeat (rewrite l_open_boxes_rm ; cbn ; auto). apply l_open_boxes_perm ;
                   apply gmultiset_elements_list_to_set_disj.
         ++ rewrite open_boxes_add_f ; cbn ; auto.
            rewrite open_boxes_add_t ; cbn ; auto. exch 0. apply weak_ImpL.
            ** peapply HE.
               --- destruct ϕ as [ ϕ | ]; order_tac.
                   +++ apply env_order_cancel_right. rewrite rm_comm.
                       rewrite l_open_boxes_rm ; cbn ; auto.
                       apply env_order_compat ; cbn ; try lia. apply l_open_boxes_env_order.
                   +++ rewrite rm_comm.
                       rewrite l_open_boxes_rm ; cbn ; auto.
                       apply env_order_compat ; cbn ; try lia. apply l_open_boxes_env_order.
               --- rewrite open_boxes_open_boxes'. unfold open_boxes'.
                   rewrite <- list_to_set_disj_env_add.
                   apply equiv_disj_union_compat_r.
                   apply env_equiv_eq. apply list_to_set_disj_perm. 
                   rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                   rewrite l_open_boxes_rm ; cbn ; auto.
                   rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                   repeat (rewrite l_open_boxes_rm ; cbn ; auto). apply l_open_boxes_perm ;
                   apply gmultiset_elements_list_to_set_disj.
            ** peapply HA. Unshelve. 3: exact ((l_open_boxes (rm (◊ ψ2) (rm (◊ ψ1_1 → ψ1_2) Δ)) • ψ2)%list).
               --- destruct ϕ ; order_tac.
                    *** apply env_order_0'. apply env_order_env_order_refl. rewrite rm_comm.
                        apply env_order_lt_le_trans with (rm (◊ ψ1_1 → ψ1_2) (rm (◊ ψ2) Δ) • (◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list.
                        ---- apply env_order_2 ; cbn ; try lia. apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia.
                             apply l_open_boxes_env_order.
                        ---- apply env_order_refl_trans with (rm (◊ ψ1_1 → ψ1_2) ((rm (◊ ψ2) Δ) • ◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list ;
                             [ cbn ; left | apply remove_In_env_order_refl ; apply elem_of_list_In ; auto].
                             apply elem_of_list_In. right. apply in_in_rm ; auto. apply elem_of_list_In ; auto.
                    *** rewrite rm_comm.
                        apply env_order_lt_le_trans with (rm (◊ ψ1_1 → ψ1_2) (rm (◊ ψ2) Δ) • (◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list.
                        ---- apply env_order_2 ; cbn ; try lia. apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia.
                             apply l_open_boxes_env_order.
                        ---- apply env_order_refl_trans with (rm (◊ ψ1_1 → ψ1_2) ((rm (◊ ψ2) Δ) • ◊ ψ2) • (◊ ψ1_1 → ψ1_2))%list ;
                             [ cbn ; left | apply remove_In_env_order_refl ; apply elem_of_list_In ; auto].
                             apply elem_of_list_In. right. apply in_in_rm ; auto. apply elem_of_list_In ; auto.
                --- apply equiv_disj_union_compat_r. rewrite open_boxes_open_boxes'. unfold open_boxes'.
                    rewrite <- list_to_set_disj_env_add.
                    apply equiv_disj_union_compat_r.
                    apply env_equiv_eq. apply list_to_set_disj_perm. 
                    rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                    rewrite l_open_boxes_rm ; cbn ; auto.
                    rewrite l_open_boxes_perm ; [ | apply elements_setminus].
                    repeat (rewrite l_open_boxes_rm ; cbn ; auto). apply l_open_boxes_perm ;
                    apply gmultiset_elements_list_to_set_disj.
      -- exch 2; exch 1 ; exch 0. apply weakening. exch 1 ; exch 0. peapply HA.
         Unshelve. 3: exact ((rm (◊ ψ1_1 → ψ1_2) Δ • ψ1_2)%list). destruct ϕ ; order_tac.
        apply equiv_disj_union_compat_r. rewrite <- list_to_set_disj_env_add.
        apply equiv_disj_union_compat_r. rewrite <- difference_singleton ; [ | ms].
        rewrite list_to_set_disj_rm ; auto.
Qed.

End EntailmentCorrect.

(** *** (iii) Uniformity *)
Section PropQuantCorrect.

(** The proof in this section, which is the most complex part of the argument,
  shows that the E- and A-formulas constructed above are indeed their propositionally quantified versions, that is, *any* formula entailed by the original formula and
  using only variables from that formula except p is already a consequence of
  the E-quantified version, and similarly on the other side for the A-quantifier.
*)

Lemma E_left  {Γ θ} {Δ : list form} {φ : form}: ∀ (Hin : φ ∈ Δ),
(Γ • @e_rule p _ _ (λ pe (_ : pe ≺· (Δ, None)),  E p pe.1) (λ pe (_ : pe ≺· (Δ, None)),  A p pe)  φ Hin) ⊢ θ ->
Γ • E p Δ ⊢ θ.
Proof.
intros Hin Hp.
unfold E. erewrite <- EA_cong . simp EA. simpl.
match goal with |- context C [in_map ?Γ ?f] =>
  edestruct (@in_map_in _ form_eq_dec _ f _ Hin) as [Hin' Hrule]
end.
eapply AndL. eapply list_conjL with (ψ:= e_rule p φ).
- apply in_or_app ; left ; apply elem_of_list_In ; exact Hrule.
- exch 0. apply weakening. erewrite e_rule_cong_strong.
  + exact Hp.
  + simpl. intros. unfold E. destruct pe. simpl. apply EA_cong.
  + trivial.
Qed.

Lemma E9_left  {Γ θ} {Δ : list form} :
(Γ • @e_rule_9 _ _ (λ pe (_ : pe ≺· (Δ, None)),  E p pe.1) (λ pe (_ : pe ≺· (Δ, None)),  A p pe)) ⊢ θ ->
Γ • E p Δ ⊢ θ.
Proof.
unfold E. erewrite <- EA_cong . simp EA. simpl.
intro Hrule.
eapply AndL. apply weakening. erewrite e_rule_9_cong_strong.
- exact Hrule.
- simpl. intros. unfold E. destruct pe. simpl. apply EA_cong.
- trivial.
Qed.

Lemma E12_left  {Γ θ} {Δ : list form} {φ1 φ2 : form}: ∀ (Hin1 : φ1 ∈ Δ) (Hin2 : φ2 ∈ Δ),
(Γ • @e_rule_12 _ _ (λ pe (_ : pe ≺· (Δ, None)),  E p pe.1) (λ pe (_ : pe ≺· (Δ, None)),  A p pe)  φ1 φ2 Hin1 Hin2) ⊢ θ ->
Γ • E p Δ ⊢ θ.
Proof.
intros Hin1 Hin2 Hp.
unfold E. erewrite <- EA_cong . simp EA. simpl.
match goal with |- context C [in_map2 ?Γ ?f] =>
  edestruct (@in_map2_in _ f _ _ Hin1 Hin2) as [Hin1' [Hin2' Hrule]]
end.
eapply AndL. eapply list_conjL with (ψ:= e_rule_12 φ1 φ2).
- apply in_or_app ; right ; apply elem_of_list_In ; exact Hrule.
- exch 0. apply weakening. erewrite e_rule_12_cong_strong.
  + exact Hp.
  + simpl. intros. unfold E. destruct pe. simpl. apply EA_cong.
  + trivial.
Qed.

(* Ian: May need to generalise this lemma to include A16 and A17 (and others?). *)
Local Lemma A_right  {Γ Δ φ φ'} : ∀ (Hin : φ ∈ Δ),
Γ ⊢ Some (@a_rule_env p _ _ (λ pe (_ : pe ≺· (Δ, φ')), E p pe.1) (λ pe (_ : pe ≺· (Δ, φ')), A p pe) φ Hin) ->
Γ ⊢ Some (A p (Δ, φ')).
Proof. 
intros Hin Hp. unfold A; simp EA; simpl.
assert(Hin' := Hin).
eapply in_map_in in Hin'. destruct Hin' as [Hin' Hrule].
eapply OrR2, list_disjR.
- apply in_or_app ; left ; apply elem_of_list_In ; exact Hrule.
- erewrite a_rule_env_cong_strong.
  + exact Hp.
  + simpl. intros. unfold E. destruct pe. simpl. apply EA_cong.
  + trivial.
Unshelve. exact form_eq_dec.
Qed.

Local Lemma Af_right {Γ Δ φ'} :
Γ ⊢ Some (@a_rule_form p _ _ (λ pe (_ : pe ≺· (Δ, φ')), E p pe.1) (λ pe (_ : pe ≺· (Δ, φ')), A p pe)) ->
Γ ⊢ Some (A p (Δ, φ')).
Proof. 
intros Hp. unfold A; simp EA; simpl.
eapply OrR1. erewrite a_rule_form_cong_strong.
  + exact Hp.
  + simpl. intros. unfold E. destruct pe. simpl. apply EA_cong.
  + trivial.
Qed.

Local Lemma A17_right  {Γ Δ ψ1 ψ2 φ'} : ∀ (Hin1 : ψ1 ∈ Δ) (Hin2 : ψ2 ∈ Δ),
Γ ⊢ Some (@a_rule_env17 _ _ (λ pe (_ : pe ≺· (Δ, φ')), E p pe.1) (λ pe (_ : pe ≺· (Δ, φ')), A p pe) ψ1 ψ2 Hin1 Hin2) ->
Γ ⊢ Some (A p (Δ, φ')).
Proof. 
intros Hin1 Hin2 Hp. unfold A; simp EA; simpl.
assert(Hin2' := Hin2).
eapply (in_map2_in Hin1) in Hin2'. destruct Hin2' as [Hin1' [Hin2' Hrule]].
eapply OrR2, list_disjR.
- apply in_or_app ; right ; apply elem_of_list_In ; exact Hrule.
- erewrite a_rule_env17_cong_strong.
  + exact Hp.
  + simpl. intros. unfold E. destruct pe. simpl. apply EA_cong.
  + trivial.
Qed.


Proposition pq_correct  Γ Δ ϕ:
  (∀ φ0, φ0 ∈ Γ -> ¬ occurs_in p φ0) ->
  (Γ ⊎ list_to_set_disj Δ ⊢ ϕ) ->
  (¬ occurs_in_opt p ϕ -> Γ • E p Δ ⊢ ϕ) * (Γ • E p Δ ⊢ Some (A p (Δ, ϕ))).
Proof.
(* This proof goes by induction on the ordering w.r.t (Γ ⊎ Δ, ϕ)
  instead of on the structure of Γ ⊎ Δ ⊢ ϕ, to allow better rules *)

  (* we want to use an E environment rule *)
Local Ltac Etac := foldEA; intros; match goal with
| Hin : ?a ∈ list_to_set_disj ?Δ' |- _ • E _ ?Δ' ⊢ _=>
    apply (E_left (proj1 (elem_of_list_to_set_disj _ _) Hin)); simp e_rule end.

  (* we want to use the E9 rule *)
Local Ltac E9tac := foldEA; intros; match goal with
| |- _ • E _ ?Δ' ⊢ _=>
    apply (E9_left (proj1 (elem_of_list_to_set_disj _ _))); simp e_rule_9 end.

  (* we want to use the E12 rule *)
Local Ltac E12tac := foldEA; intros; match goal with
| Hin1 : ?a ∈ list_to_set_disj ?Δ' , Hin2 : ?b ∈ list_to_set_disj ?Δ' |- _ • E _ ?Δ' ⊢ _ =>
    apply (E12_left (proj1 (elem_of_list_to_set_disj _ _) Hin1 Hin2)); simp e_rule_12 end.

  (* we want to use an A rule defined in a_rule_env *)
Local Ltac Atac := match goal with
| Hin : ?a ∈ list_to_set_disj ?Δ  |- _  ⊢ Some (A _ (?Δ, _)) =>
  apply (A_right (proj1 (elem_of_list_to_set_disj _ _) Hin)); simp a_rule_env end.

  (* we want to use an A rule defined in a_rule_form *)
Local Ltac Atac' := unfold A; simp EA; simpl; simp a_rule_form;
  apply OrR1; simpl.

  (* we want to use the A17 rule *)
Local Ltac A17tac := match goal with
| Hin1 : ?a ∈ list_to_set_disj ?Δ , Hin2 : ?b ∈ list_to_set_disj ?Δ  |- _  ⊢ Some (A _ (?Δ, _)) =>
  apply (A17_right (proj1 (elem_of_list_to_set_disj _ _) Hin1 Hin2)); simp a_rule_env17 end.

Local Ltac occ := simpl; tauto ||
match goal with
| Hnin : ∀ φ0 : form, φ0 ∈ ?Γ → ¬ occurs_in p φ0  |- _ =>

  let Hin := fresh "Hin" in
  try (match goal with |Hocc : ?a ∈ ?Γ |- _ =>   let Hocc' := fresh "Hocc" in assert (Hocc' := Hnin _ Hocc); simpl in Hocc'  end);
  intro; repeat rewrite env_in_add; repeat rewrite difference_include; simpl;
  intro Hin; try tauto;
  try (destruct Hin as [Hin|[Hin|Hin]] ||destruct Hin as [Hin|Hin]);
  subst; simpl; try tauto;
  repeat (apply difference_include in Hin; [|assumption]);
  try (now apply Hnin)
end.

Local Ltac equiv_tac :=
multimatch goal with
| Heq' : _•_ ≡ _ |- _ => fail
| Heq' : _ ≡ _ |- _ ≡ _ =>
  try (rewrite <- difference_singleton; trivial);
  try rewrite Heq';
  repeat rewrite <- list_to_set_disj_env_add;
  try rewrite <- list_to_set_disj_rm;
  try (rewrite union_difference_L by trivial);
  try (rewrite union_difference_R by trivial);
  try ms
end.

Local Ltac peapply' th := (erewrite proper_Provable;  [| |reflexivity]);  [eapply th|equiv_tac].

remember (elements Γ++ Δ, ϕ) as pe.
revert pe Γ Δ ϕ Heqpe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros (ΓΔ, ϕ0) Hind Γ Δ ϕ Heq Hnin Hp.
inversion Heq; subst; clear Heq.
dependent destruction Hp;
(* try and solve the easy case where the main formula is on the left *)
 try match goal with
| H : (?Γ0•?a•?b) = Γ ⊎ list_to_set_disj Δ |- _ => rename H into Heq;
      pose(Heq' := env_equiv_eq _ _ Heq); apply env_add_inv' in Heq'
| H : ((?Γ0 • ?a) = Γ ⊎ list_to_set_disj Δ) |- _ => rename H into Heq;
  assert(Hin : a ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq; ms);
  pose(Heq' := env_equiv_eq _ _ Heq); apply env_add_inv' in Heq';
  try (case (decide (a ∈ Γ)); intro Hin0;
  [split; intros; exhibit Hin0 1|
   case (decide (a ∈ (list_to_set_disj Δ : env))); intro Hin0';
  [|apply gmultiset_elem_of_disj_union in Hin; exfalso; tauto]])
end; simpl.

(* Atom *)
- auto 2 with proof.
- Atac'. case decide; intro; subst; [exfalso; now apply (Hnin _ Hin0)|]; auto with proof.
- split.
  + intro Hneq. Etac. rewrite decide_False. auto with proof. trivial.
  + case (decide (p = p0)).
    * intro Heqp0. Atac. rewrite decide_True by (f_equal; trivial).
      rewrite decide_True by (f_equal ; f_equal; trivial). apply ImpR ; apply ExFalso.
    * intro Hneq. Etac. Atac'. do 2 rewrite decide_False by trivial. apply Atom.
(* ExFalso *)
- auto 2 with proof.
- auto 2 with proof.
-  split; Etac; auto with proof.
(* AndR *)
- split.
  + intro Hocc. apply AndR ; eapply Hind ; auto with proof ; order_tac.
  + Atac'. foldEA. apply AndR ; eapply Hind ; auto ; order_tac.
(* AndL *)
- exch 0. apply AndL. exch 1; exch 0. peapply Hind; auto with proof.
  destruct oθ ; order_tac. occ. peapply' Hp.
- exch 0. apply AndL. exch 1; exch 0. peapply Hind; auto with proof. destruct oθ ; order_tac. occ. peapply' Hp.
-  split.
   + Etac. foldEA. eapply Hind; auto with proof. destruct oθ ; order_tac. simpl. peapply' Hp.
   + Atac. Etac. eapply Hind; auto; auto with proof. destruct oθ ; order_tac. peapply' Hp.
(* OrR1 & OrR2 *)
- split.
  + intro Hocc. apply OrR1. eapply Hind; auto with proof. order_tac.
  + foldEA. unfold A. simp EA; simpl. apply OrR1.
    simp a_rule_form. apply OrR1. foldEA. eapply Hind; auto with proof. order_tac.
- simpl. split.
  + intro Hocc. apply OrR2. eapply Hind; auto with proof ; order_tac.
  + foldEA. unfold A. simp EA; simpl. apply OrR1.
    simp a_rule_form. apply OrR2. foldEA. eapply Hind; auto with proof ; order_tac.
(* OrL *)
- exch 0. apply OrL; exch 0.
 + eapply Hind; auto with proof. destruct oθ ; order_tac. occ. peapply' Hp1.
 + eapply Hind; auto with proof. destruct oθ ; order_tac. occ. peapply' Hp2.
- exch 0. apply OrL; exch 0.
  + eapply Hind; auto with proof. destruct oθ ; order_tac. occ. peapply' Hp1.
  + eapply Hind; auto with proof. destruct oθ ; order_tac. occ. peapply' Hp2.
- split.
  + Etac. apply OrL; eapply Hind; auto with proof; simpl. 1,3: destruct oθ ; order_tac.
      * peapply' Hp1.
      * peapply' Hp2.
  + Atac. apply weakening. apply AndR.
    * apply ImpR. eapply Hind; auto with proof. destruct oθ ; order_tac. peapply' Hp1.
    * apply ImpR. eapply Hind; auto with proof. destruct oθ ; order_tac. peapply' Hp2.
(* ImpR *)
- split.
  + intro Hocc. apply ImpR. exch 0.
      eapply Hind; auto with proof. order_tac. occ. peapply Hp.
  + Atac'. apply weakening, ImpR. eapply Hind; auto with proof. order_tac.
      * rewrite <- Permutation_middle. order_tac.
      * simpl. peapply Hp.
(* ImpLVar *)
- pose(Heq'' := Heq'); apply env_add_inv' in Heq''.
  case (decide ((Var p0 → φ) ∈ Γ)).
  + intro Hin0.
    assert (Hocc' := Hnin _ Hin0). simpl in Hocc'.
    case (decide (Var p0 ∈ Γ)); intro Hin1.
    * (* subcase 1: p0, (p0 → φ) ∈ Γ *)
      assert (Hin2 : Var p0 ∈ Γ ∖ {[Var p0 → φ]}) by (apply in_difference; trivial; discriminate).
      clear Hin1.
      split; [intro Hocc|]; exhibit Hin0 1; exhibit Hin2 2; exch 0; exch 1; apply ImpLVar; exch 1; exch 0;
      (eapply Hind; auto with proof; [ destruct oψ ; order_tac | occ | peapply' Hp]).
    * assert(Hin0' : Var p0 ∈ (Γ0•Var p0•(Var p0 → φ))) by ms. rewrite Heq in Hin0'.
      case (decide (Var p0 ∈ (list_to_set_disj Δ: env))); intro Hp0;
      [|apply gmultiset_elem_of_disj_union in Hin0'; exfalso; tauto].
      (* subcase 3: p0 ∈ Δ ; (p0 → φ) ∈ Γ *)
      clear Heq''.
      split; try case decide; intros.
      -- apply contraction. Etac. rewrite decide_False by tauto.
          exhibit Hin0 2. exch 1. exch 0. apply ImpLVar. exch 0. apply weakening. exch 0.
         eapply Hind; auto with proof. destruct oψ ; order_tac. occ. peapply' Hp.
      -- apply contraction. Etac. rewrite decide_False by tauto.
          exhibit Hin0 2. exch 1; exch 0. apply ImpLVar. exch 0. apply weakening.
          exch 0. foldEA. eapply Hind; auto with proof. destruct oψ ; order_tac. occ. peapply' Hp.
  + intro.
    assert(Hin : (Var p0 → φ) ∈ (Γ0•Var p0•(Var p0 → φ))) by ms.
    rewrite Heq in Hin.
    case (decide ((Var p0 → φ) ∈ (list_to_set_disj Δ : env))); intro Hin0;
    [|apply gmultiset_elem_of_disj_union in Hin; exfalso; tauto].
    case (decide (Var p0 ∈ Γ)); intro Hin1.
    * (* subcase 2: p0 ∈ Γ ; (p0 → φ) ∈ Δ *)
      do 2 exhibit Hin1 1.
      split; [intro Hocc|].
      -- Etac. case decide; intro Hp0;[|case decide; intro; subst; [auto with *|]].
         ++ foldEA. simpl. eapply Hind; auto with proof. destruct oψ ; order_tac.
            1-2: apply env_order_add_compat ; apply env_order_disj_union_compat_strong_left ; auto ;
            [ left ; auto | order_tac].
            occ. peapply' Hp.
         ++ apply ImpLVar. exch 0. backward. rewrite env_add_remove.
            eapply Hind; auto with proof. destruct oψ ; order_tac. simpl. peapply' Hp.
      -- Etac. Atac. case decide; intro Hp0;[|case decide; intro; subst; [auto with *|]].
        ++ foldEA. eapply Hind; auto with proof; [ destruct oψ ; order_tac | occ | peapply' Hp].
           all: apply env_order_add_compat ; apply env_order_disj_union_compat_strong_left ; auto ; [left ; auto | order_tac].
        ++ apply ImpLVar. apply AndR; auto 2 with proof. exch 0. backward. rewrite env_add_remove.
           eapply Hind; auto with proof. destruct oψ ; order_tac. peapply' Hp.
    * assert(Hin': Var p0 ∈ Γ ⊎ list_to_set_disj Δ) by (rewrite <- Heq; ms).
       apply gmultiset_elem_of_disj_union in Hin'.
       case (decide (Var p0 ∈ (list_to_set_disj Δ: env))); intro Hin1'; [|exfalso; tauto].
      (* subcase 4: p0,(p0 → φ) ∈ Δ *)
      case (decide (p = p0)); intro.
      -- (* subsubcase p = p0 *)
        apply elem_of_list_to_set_disj in Hin1'.
        split; Etac; repeat rewrite decide_True by trivial.
        ++ clear Heq. eapply Hind; auto with proof. destruct oψ ; order_tac. simpl.  peapply' Hp.
        ++ Atac. repeat rewrite decide_True by trivial. clear Heq.
           eapply Hind; auto with proof. destruct oψ ; order_tac. peapply' Hp.
      -- (* subsubcase p ≠ p0 *)
         split; [intro Hocc|].
         ++ apply contraction. Etac. rewrite decide_False by trivial. exch 0.
            assert((Var p0 → φ) ∈ list_to_set_disj Δ) by ms. Etac.
            rewrite decide_True by now apply elem_of_list_to_set_disj.
            exch 0. apply weakening. eapply Hind; auto with proof. destruct oψ ; order_tac. simpl. peapply' Hp.
         ++ apply contraction. Etac. exch 0. assert((#p0 → φ) ∈ list_to_set_disj Δ) by ms.
            Etac; Atac. rewrite decide_False by trivial.
            do 2 rewrite decide_True by now apply elem_of_list_to_set_disj.
            exch 0. apply weakening.
            eapply Hind; auto with proof. destruct oψ ; order_tac. peapply' Hp.
(* ImpLAnd *)
- exch 0. apply ImpLAnd. exch 0. eapply Hind; auto with proof; [ destruct oψ ; order_tac | occ |peapply' Hp].
- exch 0. apply ImpLAnd. exch 0. eapply Hind; auto with proof; [ destruct oψ ; order_tac | occ |peapply' Hp].
- split; Etac.
  + eapply Hind; auto with proof. simpl. destruct oψ ; order_tac. peapply' Hp.
    rewrite list_to_set_disj_rm. ms.
  + Atac. simpl. eapply Hind; auto with proof. destruct oψ ; order_tac. peapply' Hp.
(* ImpLOr *)
- exch 0; apply ImpLOr. exch 1; exch 0. eapply Hind; auto with proof. destruct oψ ; order_tac. occ. peapply' Hp.
- exch 0; apply ImpLOr. exch 1; exch 0. eapply Hind; auto with proof ; [destruct oψ ; order_tac | occ|peapply' Hp].
- split; Etac.
  + eapply Hind; auto with proof. destruct oψ ;  order_tac. simpl. peapply' Hp.
  + Atac. eapply Hind; auto with proof. destruct oψ ; order_tac. peapply' Hp.
(* ImpLImp *)
- (* subcase 1: ((φ1 → φ2) → φ3) ∈ Γ *)
  assert(oψ ≠ Some (Var p)) by (intro; subst; simpl in *; tauto).
  exch 0; apply ImpLImp; exch 0.
  + eapply Hind; auto with proof. destruct oψ ; order_tac. occ. peapply' Hp1.
    simpl. apply Hnin in Hin0. simpl in *. tauto.
  + eapply Hind; auto with proof. destruct oψ ; order_tac. occ. peapply' Hp2.
- exch 0; apply ImpLImp; exch 0.
  + eapply Hind; auto with proof. destruct oψ ; order_tac. occ. peapply' Hp1.
    simpl. apply Hnin in Hin0. simpl in Hin0. tauto.
  + eapply Hind; auto with proof. destruct oψ ; order_tac. occ. peapply' Hp2.
- (* subcase 2: ((φ1 → φ2) → φ3) ∈ Δ *)
  split.
  + Etac. simpl. apply ImpLImp.
    * apply weakening. apply ImpR.
       eapply Hind; auto with proof.
       -- destruct oψ ; order_tac. all: repeat rewrite Permutation_middle ; order_tac.
       -- repeat setoid_rewrite gmultiset_disj_union_assoc.
          setoid_rewrite gmultiset_disj_union_comm.
          repeat setoid_rewrite gmultiset_disj_union_assoc.
          match goal with |- ?a • ?b • ?c ⊢ _ => rewrite (proper_Provable _ _ (env_add_comm a b c) _ _ eq_refl) end.
          apply ImpR_rev. peapply' Hp1.
    * eapply Hind; auto with proof. destruct oψ ; order_tac. simpl. peapply' Hp2.
  + Atac. apply AndR.
    * apply weakening. apply ImpR. foldEA.
       eapply Hind; auto with proof.
       -- destruct oψ ; order_tac. all: repeat rewrite Permutation_middle ; order_tac.
       -- repeat setoid_rewrite gmultiset_disj_union_assoc.
           setoid_rewrite gmultiset_disj_union_comm.
           repeat setoid_rewrite gmultiset_disj_union_assoc.
           exch 0. apply ImpR_rev.
           peapply' Hp1.
    * Etac. simpl. apply ImpLImp.
      -- apply weakening. apply ImpR. foldEA.
         eapply Hind; auto with proof.
       ++ destruct oψ ; order_tac. all: repeat rewrite Permutation_middle ; order_tac.
       ++ repeat setoid_rewrite gmultiset_disj_union_assoc.
          setoid_rewrite gmultiset_disj_union_comm.
          repeat setoid_rewrite gmultiset_disj_union_assoc.  exch 0. apply ImpR_rev.
          peapply' Hp1.
      -- eapply Hind; auto with proof. destruct oψ ; order_tac. peapply' Hp2.   
(* ImpBox *)
- exch 0. apply weak_ImpL.
  + apply E9_left. apply BoxR. destruct Δ ; simp e_rule_9.
    * rewrite open_boxes_add_f ; auto. peapply Hp1.
      rewrite open_boxes_remove_f ; auto. cbn in Heq.
      assert (Γ = Γ ⊎ ∅) by ms. rewrite <- H0 in Heq. rewrite <- Heq. 
      rewrite open_boxes_add_f ; auto.
    * rewrite open_boxes_add_t ; auto. cbn. eapply Hind; auto with proof.
      -- destruct oψ ; order_tac. do 2 apply env_order_cancel_right.
         all: apply env_order_2 ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ;
         [ apply elements_open_boxes_order | 
           destruct (is_box f) eqn:E ;
           [ destruct f ; cbn in E ; try discriminate ;
             apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia ;
             apply l_open_boxes_env_order |
             destruct f ; cbn in E ; try discriminate ; apply env_order_env_order_refl ; 
             apply env_order_0' ; apply l_open_boxes_env_order]].
      -- intros. apply elem_of_open_boxes in H0 as [χ [Hχ1 Hχ2]] ; subst.
         apply difference_include in Hχ2 ; auto. apply Hnin in Hχ2. cbn in Hχ2 ; auto.
      -- peapply Hp1.
         rewrite open_boxes_remove_f ; auto. enough ((⊗ (Γ0 • (□ φ1 → φ2)))≡ (⊗ Γ0)).
         ++ rewrite <- H0. rewrite Heq. rewrite open_boxes_disj_union. apply proper_disj_union ; auto.
            rewrite list_to_set_disj_open_boxes. apply env_equiv_eq.
            apply list_to_set_disj_perm. rewrite <- l_open_boxes_open_boxes_perm. auto.
         ++ rewrite open_boxes_add_f ; auto. 
      -- apply Hnin in Hin0 ; cbn in Hin0 ; auto.
  + exch 0. peapply Hind ; auto with proof ; [ destruct oψ ; order_tac | occ | ].
    peapply Hp2. enough (Γ0 ≡ Γ ∖ {[□ φ1 → φ2]} ⊎ list_to_set_disj Δ).
    ms. rewrite <- union_difference_L ; auto.
- exch 0. apply weak_ImpL.
  + apply E9_left. apply BoxR. destruct Δ ; simp e_rule_9.
    * rewrite open_boxes_add_f ; auto. peapply Hp1.
      rewrite open_boxes_remove_f ; auto. cbn in Heq.
      assert (Γ = Γ ⊎ ∅) by ms. rewrite <- H in Heq. rewrite <- Heq. 
      rewrite open_boxes_add_f ; auto.
    * rewrite open_boxes_add_t ; auto. cbn. eapply Hind; auto with proof.
      -- destruct oψ ; order_tac. do 2 apply env_order_cancel_right.
         all: apply env_order_2 ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ;
         [ apply elements_open_boxes_order |
           destruct (is_box f) eqn:E ;
           [ destruct f ; cbn in E ; try discriminate ;
             apply env_order_env_order_refl ; apply env_order_compat ; cbn ; try lia ;
             apply l_open_boxes_env_order |
             destruct f ; cbn in E ; try discriminate ; apply env_order_env_order_refl ; 
             apply env_order_0' ; apply l_open_boxes_env_order]].
      -- intros. apply elem_of_open_boxes in H as [χ [Hχ1 Hχ2]] ; subst.
         apply difference_include in Hχ2 ; auto. apply Hnin in Hχ2. cbn in Hχ2 ; auto.
      -- peapply Hp1.
         rewrite open_boxes_remove_f ; auto. enough ((⊗ (Γ0 • (□ φ1 → φ2)))≡ (⊗ Γ0)).
         ++ rewrite <- H. rewrite Heq. rewrite open_boxes_disj_union. apply proper_disj_union ; auto.
            rewrite list_to_set_disj_open_boxes. apply env_equiv_eq.
            apply list_to_set_disj_perm. rewrite <- l_open_boxes_open_boxes_perm. auto.
         ++ rewrite open_boxes_add_f ; auto. 
      -- apply Hnin in Hin0 ; cbn in Hin0 ; auto.
  + exch 0. peapply Hind ; auto with proof ; [ destruct oψ ; order_tac | occ | ].
    peapply Hp2. enough (Γ0 ≡ Γ ∖ {[□ φ1 → φ2]} ⊎ list_to_set_disj Δ).
    ms. rewrite <- union_difference_L ; auto.
- split ; [intro Hocc | ].
  + Etac. cbn. apply weak_ImpL.
    * apply BoxR,ImpR. eapply Hind ; auto with proof.
      -- destruct oψ ; order_tac. do 2 (apply env_order_cancel_right).
         all: do 2 (rewrite Permutation_middle) ;
         apply env_order_disj_union_compat_strong_left ;
         [ apply elements_open_boxes_order | 
           eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl ; apply elem_of_list_In in Hin0' ; exact Hin0'] ;
            apply env_order_2 ; cbn ; try lia ; apply l_open_boxes_env_order].
      -- intros χ Hχ1 Hχ2. apply elem_of_open_boxes in Hχ1 as [δ [Hδ1 Hδ2]] ; subst.
         apply Hnin in Hδ2. cbn in Hδ2 ; auto.
      -- peapply Hp1. rewrite l_open_boxes_rm ; auto.
          enough ((⊗ (Γ0 • (□ φ1 → φ2)))≡ (⊗ Γ0)).
        ++ rewrite <- H. rewrite Heq. rewrite open_boxes_disj_union. apply proper_disj_union ; auto.
            rewrite list_to_set_disj_open_boxes. apply env_equiv_eq.
            apply list_to_set_disj_perm. rewrite <- l_open_boxes_open_boxes_perm. auto.
        ++ rewrite open_boxes_add_f ; auto.
    * peapply Hind ; auto with proof ; [ destruct oψ ; order_tac | ].
      peapply Hp2. rewrite Heq'. rewrite <- list_to_set_disj_env_add.
      rewrite <- list_to_set_disj_rm. repeat rewrite <- env_replace ; auto.
      rewrite <- union_difference_R ; auto. ms. ms.
  + Atac ; cbn. apply AndR.
    * apply BoxR,ImpR. rewrite open_boxes_disj_union. rewrite open_boxes_singleton_f ;
      [ | unfold E ; simp EA ; cbn ; auto].
      eapply Hind ; auto with proof.
      -- destruct oψ ; order_tac. do 2 (apply env_order_cancel_right).
         all: do 2 (rewrite Permutation_middle) ;
         apply env_order_disj_union_compat_strong_left ;
         [ assert ((⊗ Γ) ⊎ ∅ = ⊗ Γ)  by ms ; rewrite H ; apply elements_open_boxes_order | 
           eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl ; apply elem_of_list_In in Hin0' ; exact Hin0'] ; 
            apply env_order_2 ; cbn ; try lia ; apply l_open_boxes_env_order].
      -- intros χ Hχ1 Hχ2. apply gmultiset_elem_of_disj_union in Hχ1.
         destruct Hχ1 as [Hχ1 | Hχ1] ; [ | apply gmultiset_elem_of_empty in Hχ1 ; auto].
         apply elem_of_open_boxes in Hχ1 as [δ [Hδ1 Hδ2]] ; subst.
         apply Hnin in Hδ2. cbn in Hδ2 ; auto.
      -- peapply Hp1. rewrite l_open_boxes_rm ; auto.
          enough ((⊗ (Γ0 • (□ φ1 → φ2)))≡ (⊗ Γ0)).
        ++ rewrite <- H. rewrite Heq. rewrite open_boxes_disj_union. apply proper_disj_union ; auto. ms.
            rewrite list_to_set_disj_open_boxes. apply env_equiv_eq.
            apply list_to_set_disj_perm. rewrite <- l_open_boxes_open_boxes_perm. auto.
        ++ rewrite open_boxes_add_f ; auto.
    * assert (Hin'': (□ φ1 → φ2) ∈ Δ). apply elem_of_list_to_set_disj ; auto.
      apply E_left with Hin'' ; simp e_rule ; cbn. apply ImpBox.
      -- apply ImpR. peapply Hind ; auto with proof ; [ order_tac | | ].
        ++ destruct oψ ; order_tac. do 2 (apply env_order_cancel_right).
           all: do 2 (rewrite Permutation_middle) ;
           apply env_order_disj_union_compat_strong_left ;
           [ apply elements_open_boxes_order |
             eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl ; apply elem_of_list_In in Hin0' ; exact Hin0'] ;
                apply env_order_2 ; cbn ; try lia ; apply l_open_boxes_env_order].
        ++ intros χ Hχ1 Hχ2. apply elem_of_open_boxes in Hχ1 as [δ [Hδ1 Hδ2]] ; subst.
           apply Hnin in Hδ2. cbn in Hδ2 ; auto.
        ++ peapply Hp1. rewrite l_open_boxes_rm ; auto.
           enough ((⊗ (Γ0 • (□ φ1 → φ2)))≡ (⊗ Γ0)).
          ** rewrite <- H. rewrite Heq. rewrite open_boxes_disj_union. apply proper_disj_union ; auto.
              rewrite list_to_set_disj_open_boxes. apply env_equiv_eq.
              apply list_to_set_disj_perm. rewrite <- l_open_boxes_open_boxes_perm. auto.
          ** rewrite open_boxes_add_f ; auto.
      -- peapply Hind ; auto with proof ; [ destruct oψ ; order_tac | ].
         peapply Hp2. rewrite Heq'. rewrite <- list_to_set_disj_env_add.
         rewrite <- list_to_set_disj_rm. repeat rewrite <- env_replace ; auto.
         rewrite <- union_difference_R ; auto. ms. ms.
(* ImpDiam *)
- split ; [intro Hocc | ].
  + case (decide ((◊ φ1 → φ2) ∈ Γ)); intro Hin1.
    * case (decide ((◊ χ) ∈ Γ)); intro Hin2.
      (* Both principal formulas are in Γ *)
      -- apply contraction. exhibit Hin1 2.
         assert (Hin2' : ◊ χ ∈ (Γ ∖ {[◊ φ1 → φ2]})).
         { apply in_difference ; auto. }
         apply E9_left.
         exhibit Hin2' 3. exch 1 ; exch 2 ; exch 0 ; exch 1. apply ImpDiam.
         ++ destruct Δ ; simp e_rule_9.
            ** unfold E ; simp EA ; cbn. simp e_rule_9. cbn in *. peapply Hp1.
               enough ((⊗ (Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]} • ⊤ ∧ ⊤ • ⊤)) ≡ (⊗ Γ0)) by ms.
               do 2 (rewrite open_boxes_add_f ; cbn ; auto).
               do 2 (rewrite open_boxes_remove_f ; cbn ; auto).
               transitivity (⊗ (Γ0 • ◊ χ • (◊ φ1 → φ2))).
               --- apply proper_open_boxes. rewrite Heq. ms.
               --- do 2 (rewrite open_boxes_add_f ; cbn ; auto).
            ** remember (l_open_boxes (Δ • f)) as Δ' ; cbn.
               rewrite open_boxes_add_t ; [ | cbn ; auto]. cbn. destruct (is_box (E p (Δ • f))) eqn:E.
               --- rewrite open_boxes_add_t ; cbn ; auto ; destruct (WKPropQuantifiers.E p (Δ • f)) ; cbn in E ; try discriminate ; cbn.
                   exch 1 ; exch 0. apply weakening ; exch 0. eapply Hind; auto with proof.
                   +++ destruct oψ ; order_tac. do 2 (apply env_order_cancel_right).
                       all: do 4 (rewrite Permutation_middle) ;
                       apply (@env_order_equiv_left_compat _ _ ((elements (⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) • φ1 • φ1) ++ (l_open_boxes (Δ • f) • χ))) ;
                       [ do 2 rewrite (perm_swap χ) ; do 3 rewrite -> Permutation_cons_append ; cbn ; do 2 rewrite Permutation_middle ;
                         apply Permutation_app_head ; do 3 rewrite <- Permutation_middle ; cbn ;
                         repeat rewrite app_nil_r ;  do 2 rewrite (perm_swap χ) ; auto | ].
                       all: apply env_order_disj_union_compat_strong_right ;
                       [ eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ] | ].
                       2,5: apply elem_of_list_In ; apply gmultiset_elem_of_elements ; apply in_difference ; auto.
                       2,4: apply env_order_env_order_refl ; apply env_order_1' ; [cbn ; try lia | ] ; apply l_open_boxes_env_order.
                       all: apply env_order_2 ; cbn ; try lia ; rewrite <- elements_setminus ;
                       assert (H: (⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) ≡ (⊗ Γ ∖ {[◊ χ]} ∖ {[◊ φ1 → φ2]})) by (repeat rewrite open_boxes_remove_f ; auto ; apply in_difference ; auto) ;
                       rewrite H ; apply elements_open_boxes_order.
                   +++ intros φ0 H Hocc'. apply env_in_add in H ; destruct H as [H | H] ; subst.
                       { apply Hnin in Hin2 ; apply Hin2. cbn ; auto. }
                       { apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                         do 2 (apply difference_include in H0 ; auto). }
                   +++ subst. erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                       assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                       { rewrite open_boxes_add_f ; auto. }
                       rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                       rewrite open_boxes_remove_f ; auto. rewrite open_boxes_remove_f ; auto.
                       { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                         rewrite <- l_open_boxes_open_boxes_perm. ms. }
                       { apply gmultiset_elem_of_disj_union ; auto. }
                   +++ intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
               --- rewrite open_boxes_add_f ; cbn ; auto.
                   exch 0. eapply Hind; auto with proof.
                   +++ destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl).
                       all: do 4 (rewrite Permutation_middle) ;
                       apply (@env_order_equiv_left_compat _ _ ((elements (⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) • φ1 • φ1) ++ (l_open_boxes (Δ • f) • χ))) ;
                       [ do 2 rewrite (perm_swap χ) ; do 3 rewrite -> Permutation_cons_append ; cbn ; do 2 rewrite Permutation_middle ;
                         apply Permutation_app_head ; do 3 rewrite <- Permutation_middle ; cbn ; repeat rewrite app_nil_r ;  do 2 rewrite (perm_swap χ) ; auto |
                         apply env_order_disj_union_compat_strong_right ;
                         [ eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ] | ]].
                         2,5: apply elem_of_list_In ; apply gmultiset_elem_of_elements ; apply in_difference ; auto.
                         2,4: apply env_order_env_order_refl ; apply env_order_1' ; [cbn ; try lia | ] ; apply l_open_boxes_env_order.
                         all: apply env_order_2 ; cbn ; try lia ; rewrite <- elements_setminus ;
                         assert (H: (⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) ≡ (⊗ Γ ∖ {[◊ χ]} ∖ {[◊ φ1 → φ2]})) by (repeat rewrite open_boxes_remove_f ; auto ; apply in_difference ; auto) ;
                         rewrite H ; apply elements_open_boxes_order.
                   +++ intros φ0 H Hocc'. apply env_in_add in H ; destruct H as [H | H] ; subst.
                       { apply Hnin in Hin2 ; apply Hin2. cbn ; auto. }
                       { apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                       do 2 (apply difference_include in H0 ; auto). }
                   +++ subst. erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                       assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                       { rewrite open_boxes_add_f ; auto. }
                       rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                       rewrite open_boxes_remove_f ; auto. rewrite open_boxes_remove_f ; auto.
                       { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                         rewrite <- l_open_boxes_open_boxes_perm. ms. }
                       { apply gmultiset_elem_of_disj_union ; auto. }
                   +++ intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
         ++ exch 1 ; exch 0. apply weakening. exch 1 ; exch 0. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac.
               all: apply (@env_order_equiv_left_compat _ _ ((elements (Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) • φ2) ++ (Δ • ◊ χ))) ;
               [ rewrite (perm_swap (◊ χ)) ; do 3 rewrite -> Permutation_cons_append ; cbn ; rewrite Permutation_middle ;
                 repeat rewrite <- app_assoc ; apply Permutation_app_head ; rewrite (perm_swap _ φ2) ;
                 rewrite (Permutation_cons_append Δ) ; rewrite (Permutation_cons_append (Δ ++ [φ2])) ; rewrite <- app_assoc ; auto |
                 rewrite Permutation_middle ; apply env_order_disj_union_compat_strong_right ; [ | left ; auto] ;
                 eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ] ].
                 2,4: apply elem_of_list_In ; apply gmultiset_elem_of_elements ; apply in_difference ; auto.
                 all: apply env_order_1' ; cbn ; try lia ; rewrite <- elements_setminus ;
                 assert (H: (Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) ≡ (Γ ∖ {[◊ χ]} ∖ {[◊ φ1 → φ2]})) by 
                 (repeat apply env_add_inv' ; rewrite env_add_comm ; repeat rewrite <- difference_singleton ; auto) ;
                 rewrite H ; left ; auto.
            ** occ. intro H. apply Hnin in Hin1 ; apply Hin1 ; cbn ; auto.
            ** peapply Hp2. rewrite Heq'. rewrite union_difference_L ; auto. rewrite <- difference_singleton ; auto. ms.
      (* Only ◊ φ1 → φ2 is in Γ. *)
      -- apply contraction.
         assert (Hin3: ◊ χ ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert (◊ χ ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         apply E_left with Hin3. simp e_rule. cbn.
         exhibit Hin1 2. exch 1 ; exch 0 ; apply ImpDiam.
         ++ destruct (is_box (E p Δ)) eqn:E.
            ** rewrite open_boxes_add_t ; cbn ; auto ; destruct (WKPropQuantifiers.E p Δ) ; cbn in E ; try discriminate ; cbn.
               exch 0 ; apply weakening. eapply Hind; auto with proof.
               --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
                   all: apply env_order_2 ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ; 
                   [ apply elements_open_boxes_order |
                     eapply env_order_refl_trans ; [ | apply remove_In_env_order_refl with (φ:=◊ χ) ; apply elem_of_list_In in Hin3 ; auto] ;
                     apply env_order_env_order_refl ; apply env_order_1' ; cbn ; try lia ;
                       apply l_open_boxes_env_order].
               --- intros φ0 H Hocc'. apply Hnin with (□ φ0) ; cbn ; auto.
                   apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                   do 2 (apply difference_include in H0 ; auto).
               --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                   assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                   { rewrite open_boxes_add_f ; auto. }
                   rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                   rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
                   { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                     rewrite <- l_open_boxes_open_boxes_perm. ms. }
                   { apply gmultiset_elem_of_disj_union ; auto. }
               --- intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
            ** rewrite open_boxes_add_f ; cbn ; auto.
               eapply Hind; auto with proof.
               --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
                   all: apply env_order_2 ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ; 
                   [ apply elements_open_boxes_order | 
                     eapply env_order_refl_trans ; [ | apply remove_In_env_order_refl with (φ:=◊ χ) ; apply elem_of_list_In in Hin3 ; auto] ;
                       apply env_order_env_order_refl ; apply env_order_1' ; cbn ; try lia ;
                       apply l_open_boxes_env_order].
               --- intros φ0 H Hocc'. apply Hnin with (□ φ0) ; cbn ; auto.
                   apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                   do 2 (apply difference_include in H0 ; auto).
               --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                   assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                   { rewrite open_boxes_add_f ; auto. }
                   rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                   rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
                   { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                     rewrite <- l_open_boxes_open_boxes_perm. ms. }
                   { apply gmultiset_elem_of_disj_union ; auto. }
               --- intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
         ++ exch 0 ; apply weakening ; exch 0. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac.
            ** occ.
            ** erewrite proper_Provable ; [ exact Hp2 | | reflexivity]. rewrite Heq'.
               rewrite union_difference_L ; auto. ms.
    * case (decide ((◊ χ) ∈ Γ)); intro Hin2.
      (* Only ◊ χ is in Γ. *)
      -- apply contraction.
         assert (Hin3: (◊ φ1 → φ2) ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert ((◊ φ1 → φ2) ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         apply E_left with Hin3. simp e_rule. cbn.
         exhibit Hin2 2. exch 1 ; apply ImpDiam.
         ++ apply ImpR. destruct (is_box (E p Δ)) eqn:E.
            ** rewrite open_boxes_add_t ; cbn ; auto ; destruct (WKPropQuantifiers.E p Δ) ; cbn in E ; try discriminate ; cbn.
               exch 1 ; exch 0 ; apply weakening. eapply Hind; auto with proof.
               --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
                   all: do 4 (rewrite Permutation_middle) ; apply env_order_disj_union_compat_strong_left ;
                   [ apply elements_open_boxes_order |
                     apply (@env_order_equiv_left_compat _ _ (l_open_boxes (rm (◊ φ1 → φ2) Δ) • φ1 • φ1 • χ)) ;
                     [ repeat rewrite (perm_swap χ) ; auto |
                       apply env_order_1' ; cbn ; try lia ; eapply env_order_refl_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto]]].
                       all: apply env_order_env_order_refl ; apply env_order_2 ; cbn ; try lia ;
                           apply l_open_boxes_env_order.
               --- intros φ0 H Hocc'. apply env_in_add in H ; destruct H as [H | H] ; subst.
                   { apply Hnin in Hin2 ; apply Hin2. cbn ; auto. }
                   { apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                     do 2 (apply difference_include in H0 ; auto). }
               --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                   assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                   { rewrite open_boxes_add_f ; auto. }
                   rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                   rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
                   { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                     rewrite <- l_open_boxes_open_boxes_perm. ms. }
                   { apply gmultiset_elem_of_disj_union ; right. apply elem_of_list_to_set_disj ; auto. }
            ** rewrite open_boxes_add_f ; cbn ; auto.
               eapply Hind; auto with proof.
               --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
                   all: do 4 (rewrite Permutation_middle) ; apply env_order_disj_union_compat_strong_left ;
                   [ apply elements_open_boxes_order |
                     apply (@env_order_equiv_left_compat _ _ (l_open_boxes (rm (◊ φ1 → φ2) Δ) • φ1 • φ1 • χ)) ;
                     [ repeat rewrite (perm_swap χ) ; auto |
                       apply env_order_1' ; cbn ; try lia ; eapply env_order_refl_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto] ;
                       apply env_order_env_order_refl ; apply env_order_2 ; cbn ; try lia ;
                       apply l_open_boxes_env_order]].
               --- intros φ0 H Hocc'. apply env_in_add in H ; destruct H as [H | H] ; subst.
                   { apply Hnin in Hin2 ; apply Hin2. cbn ; auto. }
                   { apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                     do 2 (apply difference_include in H0 ; auto). }
               --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                   assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                   { rewrite open_boxes_add_f ; auto. }
                   rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                   rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
                   { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                     rewrite <- l_open_boxes_open_boxes_perm. ms. }
                   { apply gmultiset_elem_of_disj_union ; right. apply elem_of_list_to_set_disj ; auto. }
         ++ exch 1 ; exch 0 ; apply weakening. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac.
               all: apply env_order_add_compat ; apply env_order_disj_union_compat_strong_left ;
               [ left ; auto |
                 eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto] ;
                   apply env_order_1 ; cbn ; try lia].
            ** occ.
            ** erewrite proper_Provable ; [ exact Hp2 | | reflexivity].
               rewrite Heq'. rewrite union_difference_R ; auto.
               --- rewrite <- difference_singleton ; auto. rewrite list_to_set_disj_rm. ms.
               --- apply elem_of_list_to_set_disj ; auto.
      (* No principal formula is in Γ *)
      -- assert (Hin3: (◊ φ1 → φ2) ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert ((◊ φ1 → φ2) ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         assert (Hin4: (◊ χ) ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert ((◊ χ) ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         apply E12_left with Hin3 Hin4. simp e_rule_12. cbn.
         apply ImpBox.
         ++ apply ImpR. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl).
               all: do 2 (rewrite Permutation_middle) ; apply env_order_disj_union_compat_strong_left ; 
               [ apply elements_open_boxes_order | 
                 eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto] ;
                   apply env_order_2 ; cbn ; try lia ; apply env_order_env_order_refl ;
                   eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ χ)) ; apply elem_of_list_In in Hin4 ; apply in_in_rm ; auto] ;
                   apply env_order_1' ; cbn ; try lia ;
                   apply l_open_boxes_env_order].
            ** intros φ0 H Hocc'. apply Hnin with (□ φ0) ; cbn ; auto.
               apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst ; auto.
            ** erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
               assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
               { rewrite open_boxes_add_f ; auto. }
               rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
               rewrite l_open_boxes_rm ; auto. rewrite l_open_boxes_rm ; auto.
               { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                 rewrite <- l_open_boxes_open_boxes_perm. ms. }
               { apply gmultiset_elem_of_disj_union ; right. apply elem_of_list_to_set_disj ; auto. }
         ++ eapply Hind; auto with proof.
            ** destruct oψ ; order_tac.
            ** erewrite proper_Provable ; [ exact Hp2 | | reflexivity].
               rewrite Heq'. rewrite union_difference_R ; auto.
               --- rewrite list_to_set_disj_rm. ms.
               --- apply elem_of_list_to_set_disj ; auto.
  + case (decide ((◊ φ1 → φ2) ∈ Γ)); intro Hin1.
    * case (decide ((◊ χ) ∈ Γ)); intro Hin2.
      (* Both principal formulas are in Γ *)
      -- exhibit Hin1 1.
         assert (Hin2' : ◊ χ ∈ (Γ ∖ {[◊ φ1 → φ2]})).
         { apply in_difference ; auto. }
         apply contraction.
         apply E9_left.
         exhibit Hin2' 3. exch 1 ; exch 2 ; exch 0 ; exch 1. apply ImpDiam.
         ++ destruct Δ ; simp e_rule_9.
            ** unfold E ; simp EA ; cbn. simp e_rule_9. cbn in *. peapply Hp1.
               enough ((⊗ (Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]} • ⊤ ∧ ⊤ • ⊤)) ≡ (⊗ Γ0)) by ms.
               do 2 (rewrite open_boxes_add_f ; cbn ; auto).
               do 2 (rewrite open_boxes_remove_f ; cbn ; auto).
               transitivity (⊗ (Γ0 • ◊ χ • (◊ φ1 → φ2))).
               --- apply proper_open_boxes. rewrite Heq. ms.
               --- do 2 (rewrite open_boxes_add_f ; cbn ; auto).
            ** remember (l_open_boxes (Δ • f)) as Δ' ; cbn.
               rewrite open_boxes_add_t ; [ | cbn ; auto]. cbn. destruct (is_box (E p (Δ • f))) eqn:E.
               --- rewrite open_boxes_add_t ; cbn ; auto ; destruct (WKPropQuantifiers.E p (Δ • f)) ; cbn in E ; try discriminate ; cbn.
                   exch 1 ; exch 0. apply weakening ; exch 0. eapply Hind; auto with proof.
                   +++ destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl).
                       all: apply (@env_order_equiv_left_compat _ _ (elements ((⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) • φ1 • φ1) ++ l_open_boxes (Δ • f) • χ)) ;
                       [ do 2 rewrite (perm_swap χ) ; do 2 rewrite elements_env_add ;
                         do 4 rewrite Permutation_middle ; cbn ; 
                         do 3 rewrite -> Permutation_cons_append ; cbn ; do 2 rewrite Permutation_middle ;
                         apply Permutation_app_head ; do 3 rewrite <- Permutation_middle ; cbn ;
                         repeat rewrite app_nil_r ;  do 2 rewrite (perm_swap χ) ; auto |
                         apply env_order_1' ; [ cbn ; try lia | ] ; apply env_order_env_order_refl ;
                         apply env_order_disj_union_compat_strong_right ; [ | apply l_open_boxes_env_order] ;
                         eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ] ].
                         2,4: apply elem_of_list_In ; apply gmultiset_elem_of_elements ; apply in_difference ; auto.
                         all: do 2 rewrite elements_env_add ; apply env_order_2 ; cbn ; try lia ; rewrite <- elements_setminus ;
                         assert (H: (⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) ≡ (⊗ Γ ∖ {[◊ χ]} ∖ {[◊ φ1 → φ2]})) by
                         (repeat rewrite open_boxes_remove_f ; auto ; apply in_difference ; auto) ;
                         rewrite H ; apply elements_open_boxes_order.
                   +++ intros φ0 H Hocc'. apply env_in_add in H ; destruct H as [H | H] ; subst.
                       { apply Hnin in Hin2 ; apply Hin2. cbn ; auto. }
                       { apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                         do 2 (apply difference_include in H0 ; auto). }
                   +++ subst. erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                       assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                       { rewrite open_boxes_add_f ; auto. }
                       rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                       rewrite open_boxes_remove_f ; auto. rewrite open_boxes_remove_f ; auto.
                       { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                         rewrite <- l_open_boxes_open_boxes_perm. ms. }
                       { apply gmultiset_elem_of_disj_union ; auto. }
                   +++ intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
               --- rewrite open_boxes_add_f ; cbn ; auto.
                   exch 0. eapply Hind; auto with proof.
                   +++ destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl).
                       all: apply (@env_order_equiv_left_compat _ _ (elements ((⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) • φ1 • φ1) ++ l_open_boxes (Δ • f) • χ)) ;
                       [ do 2 rewrite (perm_swap χ) ; do 2 rewrite elements_env_add ;
                         do 4 rewrite Permutation_middle ; cbn ;
                         do 3 rewrite -> Permutation_cons_append ; cbn ; do 2 rewrite Permutation_middle ;
                         apply Permutation_app_head ; do 3 rewrite <- Permutation_middle ; cbn ;
                         repeat rewrite app_nil_r ;  do 2 rewrite (perm_swap χ) ; auto |
                         apply env_order_1' ; [ cbn ; lia | ] ; apply env_order_env_order_refl ;
                         apply env_order_disj_union_compat_strong_right ; [ | apply l_open_boxes_env_order] ;
                         rewrite (@elements_elem_of (Γ ∖ {[◊ χ]}) (◊ φ1 → φ2)) ; [ | apply in_difference ; auto] ;
                         do 2 rewrite elements_env_add ; apply env_order_2 ; cbn ; try lia ;
                         assert (H: (⊗ Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) ≡ (⊗ Γ ∖ {[◊ χ]} ∖ {[◊ φ1 → φ2]})) by
                         (repeat rewrite open_boxes_remove_f ; auto ; apply in_difference ; auto) ;
                         rewrite H ; apply elements_open_boxes_order].    
                   +++ intros φ0 H Hocc'. apply env_in_add in H ; destruct H as [H | H] ; subst.
                       { apply Hnin in Hin2 ; apply Hin2. cbn ; auto. }
                       { apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                         do 2 (apply difference_include in H0 ; auto). }
                   +++ subst. erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                       assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                       { rewrite open_boxes_add_f ; auto. }
                       rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                       rewrite open_boxes_remove_f ; auto. rewrite open_boxes_remove_f ; auto.
                       { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                         rewrite <- l_open_boxes_open_boxes_perm. ms. }
                       { apply gmultiset_elem_of_disj_union ; auto. }
                   +++ intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
         ++ exch 1 ; exch 0. apply weakening. exch 1 ; exch 0. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac.
               all: apply (@env_order_equiv_left_compat _ _ (elements ((Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) • φ2) ++ Δ • ◊ χ)) ;
               [ rewrite (perm_swap (◊ χ)) ; rewrite elements_env_add ;
                 do 3 rewrite -> Permutation_cons_append ; cbn ; do 2 rewrite Permutation_middle ; repeat rewrite <- app_assoc ;
                 apply Permutation_app_head ; rewrite (Permutation_cons_append Δ) ; rewrite (Permutation_cons_append (Δ ++ [φ2])) ; rewrite <- app_assoc ; auto |
                 apply env_order_add_compat ; apply env_order_disj_union_compat_strong_right ; [ | left ; auto] ;
                 rewrite (@elements_elem_of (Γ ∖ {[◊ χ]}) (◊ φ1 → φ2)) ; [ | apply in_difference ; auto] ;
                 rewrite elements_env_add ; apply env_order_1' ; cbn ; try lia ;
                 assert (H: (Γ ∖ {[◊ φ1 → φ2]} ∖ {[◊ χ]}) ≡ (Γ ∖ {[◊ χ]} ∖ {[◊ φ1 → φ2]})) by
                 ( repeat apply env_add_inv' ; rewrite env_add_comm ; repeat rewrite <- difference_singleton ; auto) ;
                 rewrite H ; left ; auto].
            ** occ. intro H. apply Hnin in Hin1 ; apply Hin1 ; cbn ; auto.
            ** peapply Hp2. rewrite Heq'. rewrite union_difference_L ; auto.
               rewrite <- difference_singleton ; auto. ms.
      (* Only ◊ φ1 → φ2 is in Γ. *)
      -- apply contraction.
         assert (Hin3: ◊ χ ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert (◊ χ ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         apply E_left with Hin3. simp e_rule. cbn.
         exhibit Hin1 2. exch 1 ; exch 0 ; apply ImpDiam.
         ++ destruct (is_box (E p Δ)) eqn:E.
            ** rewrite open_boxes_add_t ; cbn ; auto ; destruct (WKPropQuantifiers.E p Δ) ; cbn in E ; try discriminate ; cbn.
               exch 0 ; apply weakening. eapply Hind; auto with proof.
               --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
                   all: apply env_order_2 ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ; 
                   [ apply elements_open_boxes_order |
                     apply env_order_env_order_refl ;
                     eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ χ)) ; apply elem_of_list_In in Hin3 ; auto] ;
                     apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order].
               --- intros φ0 H Hocc'. apply Hnin with (□ φ0) ; cbn ; auto.
                   apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                   do 2 (apply difference_include in H0 ; auto).
               --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                   assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                   { rewrite open_boxes_add_f ; auto. }
                   rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                   rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
                   { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                     rewrite <- l_open_boxes_open_boxes_perm. ms. }
                   { apply gmultiset_elem_of_disj_union ; auto. }
               --- intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
            ** rewrite open_boxes_add_f ; cbn ; auto.
               eapply Hind; auto with proof.
               --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
                   all: apply env_order_2 ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ; 
                   [ apply elements_open_boxes_order |
                     apply env_order_env_order_refl ;
                     eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ χ)) ; apply elem_of_list_In in Hin3 ; auto] ;
                     apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order].
               --- intros φ0 H Hocc'. apply Hnin with (□ φ0) ; cbn ; auto.
                   apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                   do 2 (apply difference_include in H0 ; auto).
               --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                   assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                   { rewrite open_boxes_add_f ; auto. }
                   rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                   rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
                   { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                     rewrite <- l_open_boxes_open_boxes_perm. ms. }
                   { apply gmultiset_elem_of_disj_union ; auto. }
               --- intro H. apply Hnin in Hin1 ; cbn in Hin1 ; auto. 
         ++ exch 0 ; apply weakening ; exch 0. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac.
            ** occ.
            ** erewrite proper_Provable ; [ exact Hp2 | | reflexivity].
               rewrite Heq'. rewrite union_difference_L ; auto. ms.
    * case (decide ((◊ χ) ∈ Γ)); intro Hin2.
      (* Only ◊ χ is in Γ. *)
      -- assert (Hin3: (◊ φ1 → φ2) ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert ((◊ φ1 → φ2) ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         apply E_left with Hin3. simp e_rule. cbn.
         exhibit Hin2 1. apply ImpDiam.
         ++ apply ImpR. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
               all: apply (@env_order_equiv_left_compat _ _ (elements ((⊗ Γ ∖ {[◊ χ]})) ++ l_open_boxes (rm (◊ φ1 → φ2) Δ) • φ1 • φ1 • χ)) ;
               [ repeat rewrite (perm_swap χ) ; auto |
                 apply env_order_1' ; [cbn ; try lia | ] ;
                 do 2 (rewrite Permutation_middle) ; apply env_order_env_order_refl ;
                 apply env_order_disj_union_compat_strong_left ; [ apply elements_open_boxes_order | ] ;
                 eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto] ;
                 apply env_order_2 ; cbn ; try lia ; apply l_open_boxes_env_order].
            ** intros φ0 H Hocc'. apply env_in_add in H ; destruct H as [H | H] ; subst.
               { apply Hnin in Hin2 ; apply Hin2. cbn ; auto. }
               { apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst.
                 do 2 (apply difference_include in H0 ; auto). }
            ** erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
               assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
               { rewrite open_boxes_add_f ; auto. }
               rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
               rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
               { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                 rewrite <- l_open_boxes_open_boxes_perm. ms. }
               { apply gmultiset_elem_of_disj_union ; right. apply elem_of_list_to_set_disj ; auto. }
         ++ apply A_right with Hin3. simp a_rule_env ; cbn. apply AndR.
            ** apply weakening,DiamL,ImpR. eapply Hind; auto with proof.
              --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl).
                  all: apply (@env_order_equiv_left_compat _ _ (elements ((⊗ Γ ∖ {[◊ χ]})) ++ l_open_boxes (rm (◊ φ1 → φ2) Δ) • φ1 • φ1 • χ)) ;
                  [ repeat rewrite (perm_swap χ) ; auto |
                    apply env_order_1' ; [cbn ; try lia | ] ;
                    do 2 (rewrite Permutation_middle) ; apply env_order_env_order_refl ;
                    apply env_order_disj_union_compat_strong_left ; [ apply elements_open_boxes_order | ] ;
                    eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto] ;
                    apply env_order_2 ; cbn ; try lia ; apply l_open_boxes_env_order].
              --- occ. intro H. apply Hnin with (□ φ0) ; cbn ; auto.
                  apply elem_of_open_boxes in Hin as [φ3 [H1 H0]] ; subst.
                  apply difference_include in H0 ; auto.
              --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                  assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                   { rewrite open_boxes_add_f ; auto. }
                   rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                   rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
                   { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                     rewrite <- l_open_boxes_open_boxes_perm. ms. }
                   { apply gmultiset_elem_of_disj_union ; right. apply elem_of_list_to_set_disj ; auto. }
            ** eapply Hind; auto with proof.
              --- destruct oψ ; order_tac. all: apply env_order_add_compat ; order_tac.
              --- occ.
              --- erewrite proper_Provable ; [ exact Hp2 | | reflexivity].
                  rewrite Heq'. rewrite union_difference_R ; auto.
                  +++ rewrite <- difference_singleton ; auto. rewrite list_to_set_disj_rm. ms.
                  +++ apply elem_of_list_to_set_disj ; auto.
      (* No principal formula is in Γ *)
      -- assert (Hin3: (◊ φ1 → φ2) ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert ((◊ φ1 → φ2) ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         assert (Hin4: (◊ χ) ∈ Δ).
         { apply elem_of_list_to_set_disj.
           assert ((◊ χ) ∈ (Γ ⊎ list_to_set_disj Δ)) by (rewrite <- Heq ; ms).
           apply gmultiset_elem_of_disj_union in H ; destruct H as [H | H] ; [ exfalso ; auto | auto]. }
         apply E12_left with Hin3 Hin4. simp e_rule_12. cbn.
         apply ImpBox.
         ++ apply ImpR. eapply Hind; auto with proof.
            ** destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl).
               all: do 2 (rewrite Permutation_middle) ;
               apply env_order_disj_union_compat_strong_left ; [ apply elements_open_boxes_order | ] ;
               eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto] ;
               apply env_order_2 ; cbn ; try lia ; apply env_order_env_order_refl ;
               eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ χ)) ; apply elem_of_list_In in Hin4 ; apply in_in_rm ; auto] ;
               apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order.
            ** intros φ0 H Hocc'. apply Hnin with (□ φ0) ; cbn ; auto.
               apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst ; auto.
            ** erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
               assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
               { rewrite open_boxes_add_f ; auto. }
               rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
               rewrite l_open_boxes_rm ; auto. rewrite l_open_boxes_rm ; auto.
               { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                 rewrite <- l_open_boxes_open_boxes_perm. ms. }
               { apply gmultiset_elem_of_disj_union ; right. apply elem_of_list_to_set_disj ; auto. }
         ++ apply A17_right with Hin3 Hin4. simp a_rule_env17 ; cbn. apply AndR.
            ** apply weakening,BoxR,ImpR. eapply Hind; auto with proof.
              --- destruct oψ ; order_tac. do 2 (apply env_order_0' ; apply env_order_env_order_refl). 
                  all: do 2 (rewrite Permutation_middle) ;
                  apply env_order_disj_union_compat_strong_left ; [ apply elements_open_boxes_order | ] ;
                  eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ φ1 → φ2)) ; apply elem_of_list_In in Hin3 ; auto] ;
                  apply env_order_2 ; cbn ; try lia ; apply env_order_env_order_refl ;
                  eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ χ)) ; apply elem_of_list_In in Hin4 ; apply in_in_rm ; auto] ;
                  apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order.
              --- intros φ0 H Hocc'. apply Hnin with (□ φ0) ; cbn ; auto.
                  apply elem_of_open_boxes in H as [φ3 [H H0]] ; subst ; auto.
              --- erewrite proper_Provable ; [ exact Hp1 | | reflexivity].
                  assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ χ)).
                  { rewrite open_boxes_add_f ; auto. }
                  rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
                  rewrite l_open_boxes_rm ; auto. rewrite l_open_boxes_rm ; auto.
                  { rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
                    rewrite <- l_open_boxes_open_boxes_perm. ms. }
                  { apply gmultiset_elem_of_disj_union ; right. apply elem_of_list_to_set_disj ; auto. }
            ** eapply Hind; auto with proof.
              --- destruct oψ ; order_tac.
              --- erewrite proper_Provable ; [ exact Hp2 | | reflexivity].
                  rewrite Heq'. rewrite union_difference_R ; auto.
                  +++ rewrite list_to_set_disj_rm. ms.
                  +++ apply elem_of_list_to_set_disj ; auto.
(* BoxR *)
- split.
  + intro Hocc. destruct Δ.
    * unfold E ; simp EA ; cbn ; simp e_rule_9. cbn in *.
      apply AndL ; do 2 (apply weakening). apply BoxR. peapply Hp.
      rewrite open_boxes_disj_union. ms.
    * apply E9_left ; simp e_rule_9. remember (l_open_boxes (Δ • f)) as Δ' ; cbn.
      apply BoxR. rewrite open_boxes_add_t ; cbn ; auto. subst.
      eapply Hind; auto with proof.
      -- order_tac. apply env_order_2 ; try (cbn ; lia). apply env_order_env_order_refl.
         apply env_order_0'. apply env_order_refl_disj_union_compat.
         ++ apply elements_open_boxes_order.
         ++ pose (l_open_boxes_env_order (Δ • f)). cbn in e ; auto.
      -- intros ψ H H0. apply Hnin with (□ ψ) ; cbn ; auto.
         apply elem_of_open_boxes in H as [φ3 [H H1]] ; subst ; auto.
      -- erewrite proper_Provable ; [ exact Hp | | reflexivity].
         rewrite <- list_to_set_disj_env_add. rewrite open_boxes_disj_union.
         enough (list_to_set_disj (l_open_boxes (Δ • f)) ≡ (⊗ (list_to_set_disj Δ • f))) by ms.
         rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
         rewrite <- l_open_boxes_open_boxes_perm.
         destruct (is_box f) eqn:E.
         ++ rewrite open_boxes_singleton_t ; auto. destruct f ; cbn in E ; try discriminate.
            simpl (l_open_boxes (Δ • □ f)). rewrite list_to_set_disj_env_add. cbn ; auto.
         ++ rewrite open_boxes_singleton_f ; auto.
            assert (l_open_boxes (Δ • f) = l_open_boxes Δ).
            { destruct f ; cbn ; auto. cbn in E ; discriminate. }
            rewrite H. ms.
  + Atac' ; cbn. apply weakening. apply BoxR. apply ImpR.
    cbn. eapply Hind ; [ | reflexivity | | ].
    * order_tac. apply env_order_2 ; try (cbn ; lia). apply env_order_env_order_refl.
      apply env_order_0'. apply env_order_refl_disj_union_compat.
      -- apply elements_open_boxes_order.
      -- apply l_open_boxes_env_order.
    * intros ψ H H0. apply Hnin with (□ ψ) ; cbn ; auto.
      apply elem_of_open_boxes in H as [φ3 [H H1]] ; subst ; auto.
    * (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
      rewrite open_boxes_disj_union.
      enough (list_to_set_disj (l_open_boxes Δ) ≡ (⊗ (list_to_set_disj Δ))) by ms.
      rewrite list_to_set_disj_open_boxes. rewrite <- l_open_boxes_open_boxes_perm ; auto.
(* DiamL *)
- apply E9_left. exch 0. apply DiamL.
  destruct Δ ; simp e_rule_9.
  + rewrite open_boxes_add_f ; auto. cbn in *. peapply Hp.
    apply proper_disj_union ; auto. apply proper_open_boxes.
    assert (Γ ⊎ ∅ = Γ) by ms. rewrite H0 in Heq. rewrite <- Heq. ms.
  + remember (l_open_boxes (Δ • f)) as Δ' ; cbn. rewrite open_boxes_add_t ; cbn ; auto.
    exch 0. eapply Hind; auto with proof.
    * destruct oφ as [ φ | ]; order_tac.
      -- destruct φ ; cbn ; order_tac.
         1-6: do 2 (apply env_order_cancel_right) ;
              apply env_order_1' ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ;
              [ apply elements_open_boxes_order | pose (l_open_boxes_env_order (Δ • f)) ; cbn in e ; auto].
         do 2 (apply env_order_1' ; try (cbn ; lia) ; apply env_order_env_order_refl).
         apply env_order_1' ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ;
         [ apply elements_open_boxes_order | pose (l_open_boxes_env_order (Δ • f)) ; cbn in e ; auto].
      -- apply env_order_1' ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ;
         [ apply elements_open_boxes_order | pose (l_open_boxes_env_order (Δ • f)) ; cbn in e ; auto].
    * intros φ0 H0 H1. apply env_in_add in H0 ; destruct H0 as [H0 | H0] ; subst.
      -- apply Hnin in Hin0. cbn ; auto.
      -- apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H0 as [φ3 [H0 H2]] ; subst.
         apply difference_include in H2 ; auto.
    * subst. (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
      assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ ψ)).
      { rewrite open_boxes_add_f ; auto. }
      rewrite H0. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
      rewrite open_boxes_add_f ; auto. rewrite open_boxes_remove_f ; auto.
      rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
      rewrite <- l_open_boxes_open_boxes_perm. ms.
    * intros H0. destruct oφ ; cbn in H0 ; try contradiction.
      destruct f0 ; cbn in * ; occ.
- destruct oφ as [φ | ]; cbn in *.
  + destruct φ.
    1-6: apply E9_left ; apply emptyweakR ; exch 0 ; apply DiamL ; cbn ; 
    destruct Δ ; simp e_rule_9 ;
    [ rewrite open_boxes_add_f ; auto ; peapply Hp ;
      rewrite open_boxes_remove_f ; auto ;
      rewrite Heq' ; rewrite open_boxes_remove_f ; auto ;
      rewrite open_boxes_disj_union ; ms
      | rewrite open_boxes_add_t ; auto ; exch 0 ; cbn ; eapply Hind ; auto with proof].
      1,4,7,10,13,16: order_tac ; do 2 apply env_order_cancel_right ; apply env_order_1' ; try (cbn ; lia) ; apply env_order_refl_disj_union_compat ;
      [ apply elements_open_boxes_order |
        destruct f ; try (apply env_order_env_order_refl ; apply env_order_0' ; apply l_open_boxes_env_order) ;
        apply env_order_env_order_refl ; apply env_order_1' ; [ cbn ; lia | apply l_open_boxes_env_order]].
      1,3,5,7,9,11: occ ; intro ; rewrite open_boxes_remove_f in Hin1 ; auto ;
      apply elem_of_open_boxes in Hin1 ; destruct Hin1 as [χ [Heqχ Hin']] ; subst ;
      apply Hnin in Hin' ; auto.
      1-6: peapply Hp ; rewrite Heq' ; repeat rewrite open_boxes_remove_f ; auto ;
      rewrite open_boxes_disj_union ; rewrite list_to_set_disj_open_boxes ;
      rewrite <- l_open_boxes_open_boxes_perm ; ms.
    Atac'. apply weakening. apply DiamL. apply ImpR.
    eapply Hind; auto with proof. 
    * order_tac. do 2 (apply env_order_1' ; try (cbn ; lia) ; apply env_order_env_order_refl).
      apply env_order_1' ; try (cbn ; lia). apply env_order_refl_disj_union_compat.
      -- apply elements_open_boxes_order.
      -- apply l_open_boxes_env_order.
    * occ. intro H. apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in Hin1 as [φ3 [H0 H2]] ; subst.
      apply difference_include in H2 ; auto.
    * (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
      assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ ψ)).
      { rewrite open_boxes_add_f ; auto. }
      rewrite H. rewrite Heq'. rewrite open_boxes_remove_f ; auto.
      rewrite open_boxes_add_f ; auto. rewrite open_boxes_remove_f ; auto.
      rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
      rewrite <- l_open_boxes_open_boxes_perm. ms.
  + apply E9_left ; apply emptyweakR ; exch 0 ; apply DiamL ; cbn.
    destruct Δ ; simp e_rule_9.
    * rewrite open_boxes_add_f ; auto. peapply Hp.
      rewrite open_boxes_remove_f ; auto.
      rewrite Heq'. rewrite open_boxes_remove_f ; auto.
      rewrite open_boxes_disj_union. ms.
    * rewrite open_boxes_add_t ; auto. exch 0. cbn. eapply Hind ; auto with proof.
      -- order_tac. apply env_order_1' ; try (cbn ; lia). apply env_order_refl_disj_union_compat.
         ++ apply elements_open_boxes_order.
         ++ destruct f. 1-5,7: apply env_order_env_order_refl ; apply env_order_0' ; apply l_open_boxes_env_order.
            apply env_order_env_order_refl ; apply env_order_1' ; [ cbn ; lia | apply l_open_boxes_env_order].
      -- occ. intro. rewrite open_boxes_remove_f in Hin1 ; auto.
         apply elem_of_open_boxes in Hin1. destruct Hin1 as [χ [Heqχ Hin']] ; subst.
         apply Hnin in Hin'. auto.
      -- peapply Hp. rewrite Heq'. repeat rewrite open_boxes_remove_f ; auto.
         rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
         rewrite <- l_open_boxes_open_boxes_perm. ms.
- split. 
  + intro H. assert (◊ ψ ∈ Δ) by (apply elem_of_list_to_set_disj ; ms).
    apply E_left with H0. simp e_rule ; cbn. apply DiamL.
    eapply Hind; auto with proof. 
    * destruct oφ ; order_tac.
      -- destruct f ; order_tac.
         1-6: do 2 apply env_order_cancel_right ; apply env_order_disj_union_compat_strong_left ;
         [ apply elements_open_boxes_order |
           eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ ψ)) ; apply elem_of_list_In in H0 ; auto] ; 
          apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order].
         apply env_order_2 ; try (cbn ; lia). apply env_order_env_order_refl ; apply env_order_cancel_right.
         apply env_order_disj_union_compat_strong_left ;
         [ apply elements_open_boxes_order |
           eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ ψ)) ; apply elem_of_list_In in H0 ; auto] ; 
          apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order].
      -- apply env_order_disj_union_compat_strong_left.
         ++ apply elements_open_boxes_order.
         ++ eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ ψ)) ; apply elem_of_list_In in H0 ; auto]. 
            apply env_order_1' ; cbn ; try lia. apply l_open_boxes_env_order.
    * intros φ0 H1 H2. apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H1 as [φ3 [H3 H4]] ; subst ; auto.
    * (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
      assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ ψ)).
      { rewrite open_boxes_add_f ; auto. }
      rewrite H1. rewrite Heq'. rewrite open_boxes_add_f ; auto.
      rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
      rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
      rewrite <- l_open_boxes_open_boxes_perm. ms.
    * intros H1. destruct oφ ; cbn in H0 ; try contradiction.
      destruct f ; cbn in * ; occ.
  + Atac ; cbn. apply weakening. apply BoxR,ImpR. eapply Hind; auto with proof.
    * destruct oφ ; order_tac.
      -- destruct f ; order_tac.
         1-6: do 2 apply env_order_cancel_right ; apply env_order_disj_union_compat_strong_left ;
         [ apply elements_open_boxes_order | 
           eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ ψ)) ; apply elem_of_list_In in Hin0' ; auto] ;
           apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order].
         apply env_order_2 ; try (cbn ; lia) ; apply env_order_env_order_refl. apply env_order_cancel_right.
         apply env_order_disj_union_compat_strong_left ;
         [ apply elements_open_boxes_order | 
           eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ ψ)) ; apply elem_of_list_In in Hin0' ; auto] ;
           apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order].
      -- apply env_order_disj_union_compat_strong_left ;
         [ apply elements_open_boxes_order | 
           eapply env_order_lt_le_trans ; [ | apply remove_In_env_order_refl with (φ:=(◊ ψ)) ; apply elem_of_list_In in Hin0' ; auto] ;
           apply env_order_1' ; cbn ; try lia ; apply l_open_boxes_env_order].
    * intros φ0 H1 H2. apply Hnin with (□ φ0) ; cbn ; auto. apply elem_of_open_boxes in H1 as [φ3 [H3 H4]] ; subst ; auto.
    * (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp|].
      assert ((⊗ Γ0) ≡ ⊗ (Γ0 • ◊ ψ)).
      { rewrite open_boxes_add_f ; auto. }
      rewrite H. rewrite Heq'. rewrite open_boxes_add_f ; auto.
      rewrite open_boxes_remove_f ; auto. rewrite l_open_boxes_rm ; auto.
      rewrite open_boxes_disj_union. rewrite list_to_set_disj_open_boxes.
      rewrite <- l_open_boxes_open_boxes_perm. ms.
Qed.

End PropQuantCorrect.

End Correctness.




(** ** Main uniform interpolation Theorem *)

Open Scope type_scope.

Lemma E_of_empty  p : E p [] = (And ⊤ ⊤).
Proof.
  unfold E; simp EA; simp e_rule_9 ; simpl. f_equal.
Qed.

(* A simple lemma about (⊤ ∧ ⊤) *)
Require Import WKCut.
Lemma AndTopL_rev Γ ϕ : Γ • (And ⊤ ⊤) ⊢ ϕ -> Γ ⊢ ϕ.
Proof.
intro Hp.
eapply additive_cut ; [ apply ImpR,ExFalso |].
eapply additive_cut ; [ apply ImpR,ExFalso |].
apply AndL_rev in Hp. exact Hp.
Qed.


Definition vars_incl  φ l := forall x, occurs_in x φ -> In x l.

(**  The overall correctness result is summarized here. *)

Theorem WK_uniform_interpolation  p V: p ∉ V ->
  ∀ φ, vars_incl φ (p :: V) ->
    (vars_incl (Ef p φ) V)
  * ({[φ]} ⊢ Some (Ef p φ))
  * (∀ ψ, vars_incl ψ V -> {[φ]} ⊢ Some ψ -> {[Ef p φ]} ⊢ Some ψ)
  * (vars_incl (Af p φ) V)
  * ({[Af p φ]} ⊢ Some φ)
  * (∀ θ, vars_incl θ V -> {[θ]} ⊢ Some φ -> {[θ]} ⊢ Some (Af p φ)).
Proof.
unfold Ef, Af.
intros Hp φ Hvarsφ; repeat split.
  + intros x Hx.
    apply (@EA_vars p _ None x) in Hx.
    destruct Hx as [Hneq [θ [Hθ Hocc]]]. apply elem_of_list_singleton in Hθ. subst.
    apply Hvarsφ in Hocc. destruct Hocc; subst; tauto.
  + replace {[φ]} with (list_to_set_disj [φ] : env) by ms.
    peapply (@entail_correct p [φ] None).
  + intros ψ Hψ Hyp. rewrite elem_of_list_In in Hp.
    peapply (@pq_correct p ∅ [φ] (Some ψ)).
    * intros θ Hin. inversion Hin.
    * peapply Hyp.
    * intro HF. apply Hψ in HF. tauto.
  + intros x Hx.
    apply EA_vars in Hx.
    destruct Hx as [Hneq [Hx | [θ [Hθ Hocc]]]].
    * apply Hvarsφ in Hx. simpl in Hx.
      firstorder. subst. tauto.
    * inversion Hθ.
  + peapply (@entail_correct p []).
  + intros ψ Hψ Hyp. rewrite elem_of_list_In in Hp.
    apply AndTopL_rev. peapply (@pq_correct p {[ψ]} []).
      * intros φ0 Hφ0. apply gmultiset_elem_of_singleton in Hφ0. subst.
        intro Ho; auto with *.
      * simpl. peapply Hyp.
      * rewrite E_of_empty. ms.
Qed.

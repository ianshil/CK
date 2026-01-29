(** * Environments

  An environment is a multiset of formulas. We rely on stdpp multisets
  mostly for their powerful multiset equivalence tactic.*)

(** Notion of wellfoundedness *)
From Stdlib Require Import Program.Wf.

(** Stdpp implementation of multisets *)
Require Export stdpp.gmultiset.

(** Our propositional formulas, including their countability. *)
Require Export im_syntax.
Require Export syntax_facts.

From Stdlib Require Import Program.Equality.

(** An environment is defined as a finite multiset of formulas
(in the sense of the stdpp library).
This requires decidable equality and countability of the underlying set. *)
Definition env  := @gmultiset form form_eq_dec form_count.

Global Instance singleton  : Singleton form env := gmultiset_singleton.
Global Instance singletonMS  : SingletonMS form env := base.singleton.

Global Hint Unfold mult empty singleton union intersection env : mset.
(* useful notations :
  {[ x ]} : singleton
      ⊎ : disjoint union
   \: difference (setminus)
   {[ x; y; … ]} union of singletons
   [{[+ x; y; … +]}] *disjoint* union of singletons
      ⊂@ : include
*)

Definition empty  := ∅ : env.

Ltac ms :=
  unfold base.singletonMS, singletonMS, base.empty, gmultiset_empty in *;
  autounfold with mset in *; autounfold with mset;
  repeat rewrite gmultiset_elem_of_disj_union; try tauto;
  multiset_solver.

Notation "Γ • φ" := (disj_union Γ (base.singletonMS φ)) (at level 105, φ at level 85, left associativity).

Section GeneralEnvironments.

Global Instance proper_elem_of : Proper ((=) ==> (≡@{env}) ==> (fun x y => x <-> y)) elem_of.
Proof. intros Γ Γ' Heq φ φ' Heq'. ms. Qed.

Global Instance proper_disj_union : Proper ((≡@{env}) ==> (≡@{env}) ==> (≡@{env})) disj_union.
Proof. intros Γ Γ' Heq Δ Δ' Heq'. ms. Qed.

Lemma elements_env_add (Γ : env) φ : elements(Γ • φ) ≡ₚ φ :: elements Γ.
Proof.
setoid_rewrite (gmultiset_elements_disj_union Γ).
setoid_rewrite (gmultiset_elements_singleton φ).
symmetry. apply Permutation_cons_append.
Qed.

(** ** Multiset utilities *)

Lemma multeq_meq (M N: env) : (forall x, multiplicity x M = multiplicity x N) -> M ≡  N.
  Proof. multiset_solver. Qed.

Lemma diff_mult (M N : env) x:
  multiplicity x (M ∖ N) = (multiplicity x M - multiplicity x N)%nat.
Proof. apply multiplicity_difference. Qed.

Lemma union_mult (M N : env) x :
  multiplicity x (M ⊎ N) = (multiplicity x M + multiplicity x N)%nat.
Proof. apply multiplicity_disj_union. Qed.

Lemma singleton_mult_in x y: x = y -> multiplicity x {[+ y +]} = 1.
Proof.
  intro Heq. rewrite Heq. apply multiplicity_singleton. Qed.

Lemma singleton_mult_notin x y: x <> y -> multiplicity x {[y]} = 0.
Proof. apply multiplicity_singleton_ne. Qed.

(* Two useful basic facts about multisets containing (or not) certain elements. *)
Lemma env_replace {Γ : env} φ {ψ}:
  (ψ ∈ Γ) -> (Γ • φ) ∖ {[ψ]} ≡ (Γ ∖ {[ψ]} • φ).
Proof.
intro Hin. apply multeq_meq. intros θ.
rewrite diff_mult, union_mult, union_mult, diff_mult.
apply PeanoNat.Nat.add_sub_swap.
case (decide (θ = ψ)); intro; subst.
- now rewrite singleton_mult_in.
- rewrite singleton_mult_notin; trivial. lia.
Qed.

Lemma diff_not_in (Γ : env) φ : φ ∉ Γ -> Γ ∖ {[φ]} ≡ Γ.
Proof.
intro Hf. apply multeq_meq. intros ψ.
rewrite diff_mult. rewrite (elem_of_multiplicity φ Γ) in Hf.
unfold mult.
case (decide (φ = ψ)).
- intro; subst. lia.
- intro Hneq. setoid_rewrite (multiplicity_singleton_ne ψ φ); trivial. lia.
  auto.
Qed.

Lemma env_add_remove : ∀ (Γ: env) φ, (Γ • φ) ∖ {[φ]} = Γ.
Proof. intros; ms. Qed.

Definition irreducible (Γ : env) :=
  (∀ p φ, (Var p → φ) ∈ Γ -> ¬ Var p ∈ Γ) /\
  ¬ ⊥ ∈ Γ /\
  ∀ φ ψ, ¬ (φ ∧ ψ) ∈ Γ /\ ¬ (φ ∨ ψ) ∈ Γ.


Definition is_double_negation φ ψ := φ = ¬ ¬ ψ.
Global Instance decidable_is_double_negation φ ψ :
  Decision (is_double_negation φ ψ) := decide (φ =  ¬ ¬ ψ).

Definition is_implication  (φ ψ : form) := exists θ, φ = (θ → ψ).
Global Instance decidable_is_implication φ ψ : Decision (is_implication φ ψ).
Proof.
unfold is_implication.
destruct φ; try solve[right; intros [θ Hθ]; discriminate].
case (decide (φ2 = ψ)).
- intro; subst. left. eexists; reflexivity.
- intro n. right; intros [θ Hθ]. now dependent destruction Hθ.
Defined.

Definition is_negation φ ψ := φ = ¬ ψ.
Global Instance decidable_is_negation φ ψ : Decision (is_negation φ ψ) := decide (φ =  ¬ ψ).

Definition is_diam_implication  (φ : form) := exists θ ψ, φ = ((◊ θ) → ψ).
Global Instance decidable_is_diam_implication φ : Decision (is_diam_implication φ).
Proof.
unfold is_diam_implication.
destruct φ.
1-4,6-7: right ; intro H ; destruct H as [θ [ψ H]] ; discriminate.
destruct φ1.
1-6: right ; intro H ; destruct H as [θ [ψ H]] ; discriminate.
left ; do 2 (eexists ; auto).
Defined.

Definition is_diam_implication_b (φ : form) := match φ with
| φ1 → φ2 => match φ1 with
             | ◊ _ => true
             | _ => false
             end
| _ => false
end.

Lemma diamimp_partition l : 
  List.filter is_diam_implication_b l ++ List.filter (λ φ0 : form, negb (is_diam_implication_b φ0)) l ≡ₚ l.
Proof.
induction l ; cbn ; auto.
destruct (is_diam_implication_b a) eqn:E ; cbn.
- rewrite IHl ; auto.
- rewrite <- Permutation_middle. rewrite IHl ; auto. 
Qed.

(** ** A dependent version of `map` *)
(* a dependent map on lists, with knowledge that we are on that list *)
(* should work with any set-like type *)

Program Fixpoint in_map_aux {A : Type} (Γ : list form) (f : forall φ, (φ ∈ Γ) -> A)
 Γ' (HΓ' : Γ' ⊆ Γ) : list A:=
match Γ' with
| [] => []
| a::Γ' => f a _ :: in_map_aux Γ f Γ' _
end.
Next Obligation.
intros. auto with *.
Qed.
Next Obligation. auto with *. Qed.


Definition in_map {A : Type} Γ
  (f : forall φ, (φ ∈ Γ) -> A) : list A :=
  in_map_aux Γ f Γ (reflexivity _).


Program Fixpoint in_map2_aux {A : Type} (Γ : list form) (f : forall φ ψ, (φ ∈ Γ) -> (ψ ∈ Γ) -> A)
 Γ' (HΓ' : Γ' ⊆ Γ) : list A :=
match Γ' with
| [] => []
| a:: Γ'' => in_map Γ (fun b (Hinb : b ∈ Γ) => f a b _ Hinb) ++ in_map2_aux Γ f Γ'' _
end.
Next Obligation. intros. auto with *. Qed.
Next Obligation. intros. auto with *. Qed.

Definition in_map2 {A : Type} Γ
  (f : forall φ ψ, (φ ∈ Γ) -> (ψ ∈ Γ) -> A) : list A :=
  in_map2_aux Γ f Γ (reflexivity _).


(* This generalises to any type. decidability of equality over this type is necessary for a result in "Type" *)
Lemma in_in_map {A : Type} {HD : forall a b : A, Decision (a = b)}
  Γ (f : forall φ, (φ ∈ Γ) -> A) ψ :
  ψ ∈ (in_map Γ f) -> {ψ0 & {Hin | ψ = f ψ0 Hin}}.
Proof.
unfold in_map.
assert(Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ), ψ ∈ in_map_aux Γ f Γ' HΓ'
  → {ψ0 & {Hin : ψ0 ∈ Γ | ψ = f ψ0 Hin}}); [|apply Hcut].
induction Γ'; simpl; intros HΓ' Hin.
- contradict Hin. auto. now rewrite elem_of_nil.
- match goal with | H : ψ ∈ ?a :: (in_map_aux _ _ _ ?HΓ'') |- _ =>
  case (decide (ψ = a)); [| pose (myHΓ' := HΓ'')] end.
  + intro Heq; subst. exists a. eexists. reflexivity.
  + intro Hneq. apply (IHΓ' myHΓ').
    apply elem_of_cons in Hin. tauto.
Qed.

Lemma in_in_map2 Γ (f : forall φ ψ, (φ ∈ Γ) -> (ψ ∈ Γ) -> form) ψ :
  ψ ∈ (in_map2 Γ f) -> {ψ0 & {ψ1 & {Hin1 | {Hin2 | ψ = f ψ0 ψ1 Hin1 Hin2}}}}.
Proof.
unfold in_map2.
assert(Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ), ψ ∈ in_map2_aux Γ f Γ' HΓ'
  → {ψ0 & {ψ1 & {Hin1 | {Hin2 | ψ = f ψ0 ψ1 Hin1 Hin2}}}}); [|apply Hcut].
induction Γ'; simpl; intros HΓ' Hin.
- rewrite elem_of_nil in Hin ; contradiction.
- apply elem_of_list_In in Hin ; apply in_app_orT in Hin.
  destruct Hin.
  + apply elem_of_list_In,in_in_map in i. destruct i as [ψ0 [Hin' Heq]] ; subst.
    eexists. eexists. eexists. eexists. reflexivity.
  + apply elem_of_list_In in i. apply IHΓ' in i. auto.
Qed.

Local Definition in_subset {Γ : env} {Γ'} (Hi : Γ' ⊆ elements Γ) {ψ0} (Hin : ψ0 ∈ Γ') : ψ0 ∈ Γ.
Proof. apply gmultiset_elem_of_elements,Hi, Hin. Defined.

(* converse *)
Lemma in_map_in {A : Type} {HD : forall a b : A, Decision (a = b)}
  {Γ} {f : forall φ, (φ ∈ Γ) -> A} {ψ0} (Hin : ψ0 ∈ Γ):
  {Hin' | f ψ0 Hin' ∈ (in_map Γ f)}.
Proof.
unfold in_map.
assert(Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ) ψ0 (Hin : In ψ0 Γ'),
  {Hin' | f ψ0 Hin' ∈ in_map_aux Γ f Γ' HΓ'}).
- induction Γ'; simpl; intros HΓ' ψ' Hin'; [auto with *|].
  case (decide (ψ' = a)).
  + intro; subst a. eexists. left.
  + intro Hneq. assert (Hin'' : In ψ' Γ') by (destruct Hin'; subst; tauto).
      pose (Hincl := (in_map_aux_obligation_2 Γ (a :: Γ') HΓ' a Γ' eq_refl)).
      destruct (IHΓ' Hincl ψ' Hin'') as [Hin0 Hprop].
      eexists. right. apply Hprop.
- destruct (Hcut Γ (reflexivity Γ) ψ0) as [Hin' Hprop].
  + auto. now apply elem_of_list_In.
  + exists Hin'. exact Hprop.
Qed.

Lemma in_map2_in
  {Γ} {f : forall φ1 φ2, (φ1 ∈ Γ) -> (φ2 ∈ Γ) -> form} {ψ1 ψ2} (Hin1 : ψ1 ∈ Γ) (Hin2 : ψ2 ∈ Γ):
  {Hin1' | {Hin2' | f ψ1 ψ2 Hin1' Hin2' ∈ (in_map2 Γ f)}}.
Proof.
unfold in_map2.
assert (Hcut : forall Γ' (HΓ' : Γ' ⊆ Γ) ψ1 ψ2 (Hin1 : In ψ1 Γ') (Hin2 : In ψ2 Γ),
  {Hin1' | {Hin2' | f ψ1 ψ2 Hin1' Hin2' ∈ in_map2_aux Γ f Γ' HΓ'}}).
- induction Γ'; simpl; intros HΓ' ψ1' ψ2' Hin1' Hin2' ; [auto with *|].
  case (decide (ψ1' = a)).
  + intro; subst a. destruct (@in_map_in _ _ _ (λ (b : form) (Hinb : b ∈ Γ),
    f ψ1' b (in_map2_aux_obligation_1 Γ (ψ1' :: Γ') HΓ' ψ1' Γ' eq_refl b Hinb)
    Hinb) ψ2'). apply elem_of_list_In ; auto. eexists ; eexists. apply elem_of_list_In ;
    apply in_or_app ; left ; apply elem_of_list_In ; exact e.
  + intro. assert (H0 : Γ' ⊆ Γ) by (intros z Hz ; apply HΓ' ; right ; auto).
    edestruct (IHΓ' (in_map2_aux_obligation_2 Γ (a :: Γ') HΓ' a Γ' eq_refl) ψ1') ; auto ; [ destruct Hin1' ; auto ; exfalso ; auto | exact Hin2' | ].
    destruct s as (Hin2'' & H1). eexists ; eexists. apply elem_of_list_In ;
    apply in_or_app ; right ; apply elem_of_list_In. exact H1.
- destruct (Hcut Γ (reflexivity Γ) ψ1 ψ2) as [Hin' Hprop].
  + now apply elem_of_list_In.
  + now apply elem_of_list_In.
  + exists Hin'. exact Hprop.
Qed.

Lemma in_map_empty A f : @in_map A [] f = [].
Proof. auto with *. Qed.

Lemma in_map_ext {A} Δ f g:
  (forall φ H, f φ H = g φ H) -> @in_map A Δ f = in_map Δ g.
Proof.
  intros Heq.
  unfold in_map.
  assert(forall Γ HΓ, in_map_aux Δ f Γ  HΓ = in_map_aux Δ g Γ  HΓ); [|trivial].
  induction Γ; intro HΓ.
  - trivial.
  - simpl. now rewrite Heq, IHΓ.
Qed.

Lemma in_map2_ext {A} Δ f g:
  (forall φ ψ Hφ Hψ, f φ ψ Hφ Hψ = g φ ψ Hφ Hψ) -> @in_map2 A Δ f = in_map2 Δ g.
Proof.
  intros Heq.
  unfold in_map2.
  assert(forall Γ HΓ, in_map2_aux Δ f Γ  HΓ = in_map2_aux Δ g Γ  HΓ); [|trivial].
  induction Γ; intro HΓ.
  - trivial.
  - simpl. f_equal ; [ | now rewrite IHΓ].
    erewrite in_map_ext ; auto.
Qed. 

Lemma difference_singleton (Δ: env) φ: φ ∈ Δ -> Δ ≡ ((Δ ∖ {[φ]}) • φ).
Proof.
intro Hin. rewrite (gmultiset_disj_union_difference {[φ]}) at 1. ms.
now apply gmultiset_singleton_subseteq_l.
Qed.

Lemma env_in_add (Δ : env) ϕ φ: φ ∈ (Δ • ϕ) <-> φ = ϕ \/ φ ∈ Δ.
Proof.
rewrite (gmultiset_elem_of_disj_union Δ), gmultiset_elem_of_singleton.
tauto.
Qed.

Lemma equiv_disj_union_compat_r {Δ Δ' Δ'' : env} : Δ ≡ Δ'' -> Δ ⊎ Δ' ≡ Δ'' ⊎ Δ'.
Proof. ms. Qed.

  Lemma equiv_disj_union_compat_l {Δ Δ' Δ'' : env} : Δ ≡ Δ'' -> Δ' ⊎ Δ ≡ Δ' ⊎ Δ''.
Proof. ms. Qed.

Lemma env_add_comm (Δ : env) φ ϕ : (Δ • φ • ϕ) ≡ (Δ • ϕ • φ).
Proof. ms. Qed.

Lemma in_difference (Δ : env) φ ψ : φ ≠ ψ -> φ ∈ Δ -> φ ∈ Δ ∖ {[ψ]}.
Proof.
intros Hne Hin.
unfold elem_of, gmultiset_elem_of.
rewrite (multiplicity_difference Δ {[ψ]} φ).
assert( HH := multiplicity_singleton_ne φ ψ Hne).
unfold singletonMS, base.singletonMS in HH.
unfold base.singleton, Environments.singleton. ms.
Qed.

Hint Resolve in_difference : multiset.

(* could be used in disj_inv *)
Lemma env_add_inv (Γ Γ' : env) φ ψ:
  φ ≠ ψ ->
  ((Γ • φ) ≡ (Γ' • ψ)) ->
    (Γ' ≡  ((Γ ∖ {[ψ]}) • φ)).
Proof.
intros Hneq Heq. rewrite <- env_replace.
- ms.
- assert(ψ ∈ (Γ • φ)); [rewrite Heq|]; ms.
Qed.

Lemma env_add_inv' (Γ Γ' : env) φ: (Γ • φ) ≡ Γ' -> (Γ ≡  (Γ' ∖ {[φ]})).
Proof. intro Heq. ms. Qed.

Lemma env_equiv_eq (Γ Γ' :env) : Γ =  Γ' -> Γ ≡  Γ'.
Proof. intro; subst; trivial. Qed.

(* reprove the following principles, proved in stdpp for Prop, but
   we need them in Type *)
Lemma gmultiset_choose_or_empty (X : env) : {x | x ∈ X} + {X = ∅}.
Proof.
  destruct (elements X) as [|x l] eqn:HX; [right|left].
  - by apply gmultiset_elements_empty_inv.
  - exists x. rewrite <- (gmultiset_elem_of_elements x X).
    replace (elements X) with (x :: l). left.
Qed.

(* We need this induction principle in type. *)
Lemma gmultiset_rec (P : env → Type) :
  P ∅ → (∀ x X, P X → P ({[+ x +]} ⊎ X)) → ∀ X, P X.
Proof.
  intros Hemp Hinsert X. induction (gmultiset_wf X) as [X _ IH].
  destruct (gmultiset_choose_or_empty X) as [[x Hx]| ->]; auto.
  rewrite (gmultiset_disj_union_difference' x X) by done.
  apply Hinsert, IH; multiset_solver.
Qed.


Lemma difference_include θ θ' (Δ : env) :
  (θ' ∈ Δ) ->
  θ ∈ Δ ∖ {[θ']} -> θ ∈ Δ.
Proof.
intros Hin' Hin.
rewrite gmultiset_disj_union_difference with (X := {[θ']}).
- apply gmultiset_elem_of_disj_union. tauto.
- now apply gmultiset_singleton_subseteq_l.
Qed.

Fixpoint rm x l := match l with
| h :: t => if form_eq_dec x h then t else h :: rm x t
| [] => []
end.

Lemma rm_comm l x y : rm x (rm y l) = rm y (rm x l).
Proof.
induction l ; cbn ; auto.
do 2 destruct form_eq_dec ; subst ; cbn ; auto.
- destruct form_eq_dec ; [auto | contradiction].
- destruct form_eq_dec ; [auto | contradiction].
- repeat destruct form_eq_dec ; subst ; auto ; try contradiction.
  rewrite IHl ; auto.
Qed.

Lemma in_rm l x y: In x (rm y l) -> In x l.
Proof.
induction l; simpl. tauto.
destruct form_eq_dec. tauto. firstorder.
Qed.

Lemma in_in_rm l x y: x ≠ y -> In x l -> In x (rm y l).
Proof.
intro H.
induction l; simpl ; auto. 
intro H0. destruct H0 ; subst ; destruct form_eq_dec ; subst ; try contradiction ; firstorder.
Qed.

Lemma remove_include θ θ' Δ : (θ' ∈ Δ) -> θ ∈ rm θ' Δ -> θ ∈ Δ.
Proof. intros Hin' Hin. eapply elem_of_list_In, in_rm, elem_of_list_In, Hin. Qed.

Lemma rm_notin l ψ : ψ ∉ l -> rm ψ l = l.
Proof.
induction l ; cbn ; auto.
intro. destruct (form_eq_dec ψ a) ; subst.
- exfalso. apply H ; left ; auto.
- f_equal. apply IHl. intro ; apply H ; right ; auto.
Qed. 




(* technical lemma : one can constructively find whether an environment contains
   an element satisfying a decidable property *)
Lemma decide_in (P : _ -> Prop) (Γ : env) :
  (forall φ, Decision (P φ)) ->
  {φ | (φ ∈ Γ) /\ P φ} + {forall φ, φ ∈ Γ -> ¬ P φ}.
Proof.
intro HP.
induction Γ using gmultiset_rec.
- right. intros φ Hφ; inversion Hφ.
- destruct IHΓ as [(φ&Hφ) | HF].
  + left. exists φ. ms.
  + case (HP x); intro Hx.
    * left; exists x. ms.
    * right. intros. ms.
Qed.

Lemma union_difference_L (Γ : env) Δ ϕ: ϕ ∈ Γ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ∖{[ϕ]} ⊎ Δ.
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Lemma union_difference_R (Γ : env) Δ ϕ: ϕ ∈ Δ -> (Γ ⊎ Δ) ∖ {[ϕ]} ≡ Γ ⊎ (Δ ∖{[ϕ]}).
Proof. intro Hin. pose (difference_singleton _ _ Hin). ms. Qed.

Global Instance equiv_assoc : @Assoc env equiv disj_union.
Proof. intros x y z. ms. Qed.

Global Instance proper_difference : Proper ((≡@{env}) ==> eq ==> (≡@{env})) difference.
Proof. intros Γ Γ' Heq Δ Heq'. ms. Qed.

Definition var_not_in_env p (Γ : env):=  (∀ φ0, φ0 ∈ Γ -> ¬ occurs_in p φ0).

(** ** Tactics *)
(* helper tactic split cases given an assumption about belonging to a multiset *)

End GeneralEnvironments.

Global Ltac in_tac :=
repeat
match goal with
| H : ?θ  ∈ {[?θ1; ?θ2]} |- _ => apply gmultiset_elem_of_union in H; destruct H as [H|H]; try subst
| H : ?θ ∈ (?Δ ∖ {[?θ']}) |- _ => apply difference_include in H; trivial
| H : context [?θ  ∈ (?d • ?θ2)] |- _ =>
    rewrite (env_in_add d) in H; destruct H as [H|H]; try subst
| H : context [?θ ∈ {[ ?θ2 ]}] |- _ => rewrite gmultiset_elem_of_singleton in H; subst
end.


Global Hint Immediate equiv_assoc : proof.

Definition open_box  (φ : form) : form := match φ with
| □ φ => φ
| φ => φ
end.

Definition is_box (φ : form) := match φ with
| □ _ => true
| _ => false
end.

(* inefficient conversion from multisets to lists and back *)
Definition open_boxes  (Γ : env) : env :=
  list_to_set_disj (map open_box (List.filter is_box (elements Γ))).

Fixpoint l_open_boxes (l : list form) :=
match l with
| [] => []
| φ :: l => match φ with
            | □ ψ => ψ :: l_open_boxes l
            | _ => l_open_boxes l
            end
end.

Lemma l_open_boxes_rm l ϕ : is_box ϕ = false -> l_open_boxes (rm ϕ l) = l_open_boxes l.
Proof.
intro H.
induction l ; cbn ; auto.
destruct (form_eq_dec ϕ a).
- destruct a ; cbn in H ; auto ; try discriminate.
  rewrite e in H ; cbn in H ; discriminate.
- destruct a ; cbn in H ; auto ; try discriminate.
  cbn ; rewrite IHl ; auto.
Qed.

Lemma l_open_boxes_app l0 l1 : l_open_boxes (l0 ++ l1) = l_open_boxes l0 ++ l_open_boxes l1.
Proof.
revert l1 ; induction l0 ; cbn ; auto.
destruct a ; cbn ; auto. intro l1. f_equal ; auto.
Qed.

Lemma l_open_boxes_in l ϕ : ϕ ∈ l_open_boxes l -> (□ ϕ) ∈ l.
Proof.
induction l ; intro H ; [ inversion H | ].
destruct a ; cbn in H ; cbn ; auto.
1-5,7: right ; auto. inversion H ; subst ; [left ; auto | right ; auto].
Qed.

Lemma in_l_open_boxes l ϕ : (□ ϕ) ∈ l -> ϕ ∈ l_open_boxes l.
Proof.
induction l ; intro H ; [ inversion H | ].
inversion H ; subst ; cbn ; [ left ; auto | ].
destruct a ; cbn in H ; cbn ; auto.
right. auto.
Qed.

Lemma l_open_boxes_open_boxes_perm l :
  l_open_boxes l ≡ₚ map open_box (List.filter is_box l).
Proof.
induction l ; cbn ; auto.
destruct a ; cbn ; auto.
Qed.

Definition open_boxes' (Γ : env) : env :=
  list_to_set_disj (l_open_boxes (elements Γ)).

Lemma open_boxes_open_boxes' (Γ : env) : open_boxes Γ = open_boxes' Γ.
Proof.
unfold open_boxes,open_boxes'. f_equal.
induction (elements Γ) ; cbn ; auto.
destruct (is_box a) eqn:E.
- destruct a ; cbn ; cbn in E ; try discriminate ; rewrite IHl ; auto.
- destruct a ; cbn ; cbn in E ; try discriminate ; auto.
Qed.

Notation "⊙ φ" := (open_box φ) (at level 75).
Notation "⊗ Γ" := (open_boxes Γ) (at level 75).

Section Modal.

Global Instance proper_open_boxes' : Proper ((≡@{env}) ==> (≡@{env})) open_boxes'.
Proof. intros Γ Heq Δ Heq'. ms. Qed.

Global Instance proper_open_boxes : Proper ((≡@{env}) ==> (≡@{env})) open_boxes.
Proof. intros Γ Heq Δ Heq'. ms. Qed.

Lemma open_boxes_empty : open_boxes ∅ = ∅.
Proof. auto. Qed.


Lemma Listfilter_Permutation (P : form -> bool) l0 l1 : l0 ≡ₚ l1 -> List.filter P l0 ≡ₚ List.filter P l1.
Proof.
revert l1 ; induction l0 as [ | x l0 Hl0].
- intros l1 H. apply Permutation_nil in H ; subst ; auto.
- intros l1 H. symmetry in H.
  destruct (Permutation_vs_cons_inv H) as (l1' & l1'' & H0) ; subst.
  rewrite filter_app. rewrite Permutation_app_comm.
  cbn. destruct (P x).
  + cbn. rewrite <- filter_app. rewrite (Hl0 (l1'' ++ l1')) ; auto.
    rewrite <- Permutation_middle in H.
    apply Permutation_cons_inv in H. symmetry. rewrite <- H.
    apply Permutation_app_comm.
  + rewrite <- filter_app. apply Hl0. rewrite <- Permutation_middle in H.
    apply Permutation_cons_inv in H. symmetry. rewrite <- H.
    apply Permutation_app_comm.
Qed.

Lemma filter_disj_union (Γ Δ : env) (P : form -> bool) :
  (List.filter P (elements (Γ ⊎ Δ))) ≡ₚ (List.filter P (elements Γ)) ++ (List.filter P (elements Δ)).
Proof.
pose (gmultiset_elements_disj_union Γ Δ).
apply (Listfilter_Permutation P) in p. rewrite p.
rewrite filter_app ; auto.
Qed.

Lemma open_boxes_disj_union Γ Δ : (open_boxes (Γ ⊎ Δ)) = (open_boxes Γ ⊎ open_boxes Δ).
Proof.
unfold open_boxes. rewrite filter_disj_union.
rewrite map_app. apply list_to_set_disj_app.
Qed.

Lemma open_boxes_singleton_t φ : is_box φ = true -> open_boxes {[φ]} = {[⊙ φ]}.
Proof.
intro Hφ.
unfold open_boxes.
assert (HH := gmultiset_elements_singleton φ).
unfold elements, base.singletonMS, singletonMS, base.singleton, Environments.singleton in *.
rewrite HH. cbn. rewrite Hφ. ms.
Qed.

Lemma open_boxes_singleton_f φ : is_box φ = false -> open_boxes {[φ]} = ∅.
Proof.
intro Hφ.
unfold open_boxes.
assert (HH := gmultiset_elements_singleton φ).
unfold elements, base.singletonMS, singletonMS, base.singleton, Environments.singleton in *.
rewrite HH. cbn. rewrite Hφ. ms.
Qed.

Lemma open_boxes_add_t (Γ : env) φ : is_box φ = true -> (⊗ (Γ • φ)) = (⊗ Γ • ⊙ φ).
Proof.
intro Hφ.
rewrite open_boxes_disj_union.
unfold open_boxes. f_equal. apply open_boxes_singleton_t ; auto.
Qed.

Lemma open_boxes_add_f (Γ : env) φ : is_box φ = false -> (⊗ (Γ • φ)) = ⊗ Γ.
Proof.
intro Hφ.
rewrite open_boxes_disj_union.
unfold open_boxes.
unfold elements, base.singletonMS, singletonMS, base.singleton, Environments.singleton in *.
assert ([φ] = (gmultiset_elements (gmultiset_singleton φ))).
{ rewrite <- gmultiset_elements_singleton. ms. }
rewrite <- H ; cbn. rewrite Hφ ; cbn. ms.
Qed.

Lemma elem_of_open_boxes (φ : form) Δ : φ ∈ (⊗Δ) ->
  exists ψ, φ = ψ /\ (□ ψ) ∈ Δ.
Proof.
intro Hin. 
induction Δ as [|θ Δ Hind] using gmultiset_rec.
- inversion Hin.
- rewrite open_boxes_disj_union in Hin.
  apply gmultiset_elem_of_disj_union in Hin.
  destruct Hin as [Hθ | HΔ].
  + clear Hind. unfold open_boxes in Hθ.
    apply elem_of_list_to_set_disj in Hθ ; apply elem_of_list_In in Hθ.
    apply in_map_iff in Hθ. destruct Hθ as (ψ & H & H0) ; subst.
    apply filter_In in H0. destruct H0 as (H & H0).
    destruct ψ ; cbn in H0 ; try discriminate.
    exists ψ ; repeat split ; auto.
    apply gmultiset_elem_of_disj_union ; left. apply elem_of_list_In in H.
    apply gmultiset_elem_of_elements in H ; auto.
  + destruct (Hind HΔ) as [ψ (Heq & HIn)] ; subst.
    exists ψ ; split ; auto.
    apply gmultiset_elem_of_disj_union ; right ; auto.
Qed.

Lemma occurs_in_open_boxes x (φ : form) Δ :
  occurs_in x φ -> φ ∈ (⊗Δ) -> exists θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
intros Hx Hφ. apply elem_of_open_boxes in Hφ. destruct Hφ as [ψ (H0 & H1)]; eauto.
subst. exists (□ψ); split ; eauto.
Qed.

Lemma occurs_in_map_open_box x (φ : form) Δ :
  occurs_in x φ -> φ ∈ (map open_box Δ) -> exists θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
intros Hx Hφ. apply elem_of_list_In, in_map_iff in Hφ.
destruct Hφ as [ψ [Hφ Hin]]; subst.
exists ψ. split. now apply elem_of_list_In. dependent destruction ψ; trivial.
Qed.

Lemma occurs_in_map_l_open_boxes x (φ : form) Δ :
  occurs_in x φ -> φ ∈ (l_open_boxes Δ) -> exists θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
intros Hx Hφ. induction Δ ; cbn in * ; try now inversion Hφ.
destruct a ; cbn in * ; try now (destruct (IHΔ Hφ) as (θ & H & H0) ; exists θ ; split ; [ right ; auto | auto]).
inversion Hφ ; subst.
- eexists ; split ; [ left ; split | auto].
- exists (□φ) ; split ; [ right ; auto | auto].
  apply l_open_boxes_in ; auto.
Qed.

Lemma occurs_in_list_conj x Δ :
  occurs_in x (list_conj Δ) -> exists θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
induction Δ ; cbn ; intro H ; try now firstorder.
destruct H.
- exists a ; split ; [ left ; split | auto].
- destruct (IHΔ H) as (θ & H0 & H1) ; exists θ ; split ; [ right ; auto | auto].
Qed.

Lemma occurs_in_list_disj x Δ :
  occurs_in x (list_disj Δ) -> exists θ, θ ∈ Δ /\ occurs_in x θ.
Proof.
induction Δ ; cbn ; intro H ; try now firstorder.
destruct H.
- exists a ; split ; [ left ; split | auto].
- destruct (IHΔ H) as (θ & H0 & H1) ; exists θ ; split ; [ right ; auto | auto].
Qed.

Lemma open_boxes_remove_t Γ φ : is_box φ = true -> φ ∈ Γ -> (≡@{env}) (⊗ (Γ ∖ {[φ]})) ((⊗ Γ) ∖ {[⊙ φ]}).
Proof.
intros Hφ Hin.
 pose (difference_singleton Γ φ Hin). rewrite e at 2.
rewrite open_boxes_add_t ; auto. ms.
Qed.

Lemma open_boxes_remove_f Γ φ : is_box φ = false -> φ ∈ Γ -> (≡@{env}) (⊗ (Γ ∖ {[φ]})) (⊗ Γ).
Proof.
intros Hφ Hin.
 pose (difference_singleton Γ φ Hin). rewrite e at 2.
rewrite open_boxes_add_f ; auto.
Qed.

Lemma is_not_box_open_box φ : is_box φ = false -> (⊙φ) = φ.
Proof. unfold is_box. dependent destruction φ; simpl; intuition. discriminate. Qed.

Lemma In_open_boxes_t (Γ : env) φ : is_box φ = true -> (φ ∈ Γ) -> open_box φ ∈ open_boxes Γ.
Proof.
intros Hφ Hin. apply difference_singleton in Hin.
rewrite Hin,  open_boxes_add_t ; auto. auto with *.
Qed.

Global Instance Proper_elements:
  Proper ((≡) ==> (≡ₚ)) ((λ Γ : env, gmultiset_elements Γ)).
Proof.
intros Γ Δ Heq ; apply AntiSymm_instance_0; apply gmultiset_elements_submseteq; ms.
Qed.

Lemma elements_open_boxes Γ: elements (⊗ Γ) ≡ₚ map open_box (List.filter is_box (elements Γ)).
Proof.
unfold open_boxes. remember (elements Γ) as l. clear Γ Heql.
induction l as [| a l].
- ms.
- cbn. destruct (is_box a) ; auto. setoid_rewrite gmultiset_elements_disj_union.
  rewrite IHl. setoid_rewrite gmultiset_elements_singleton. trivial.
Qed.

Lemma list_to_set_disj_env_add Δ v:
  ((list_to_set_disj Δ : env) • v : env) ≡ list_to_set_disj (v :: Δ).
Proof. ms. Qed.

Lemma list_to_set_disj_rm Δ v:
  (list_to_set_disj Δ : env) ∖ {[v]} ≡ list_to_set_disj (rm v Δ).
Proof.
induction Δ as [|φ Δ]; simpl; [ms|].
case form_eq_dec; intro; subst; [ms|].
simpl. rewrite <- IHΔ. case (decide (v ∈ (list_to_set_disj Δ: env))).
- intro. rewrite union_difference_R by assumption. ms.
- intro. rewrite diff_not_in by auto with *. rewrite diff_not_in; auto with *.
Qed.


Lemma gmultiset_elements_list_to_set_disj (l : list form):
  gmultiset_elements(list_to_set_disj l) ≡ₚ l.
Proof.
induction l as [| x l]; [ms|].
rewrite Proper_elements; [|symmetry; apply list_to_set_disj_env_add].
setoid_rewrite elements_env_add; rewrite IHl. trivial.
Qed.

Lemma gmultiset_elements_list_to_set_disj_perm (l0 l1 : list form):
  l0 ≡ₚ l1 -> gmultiset_elements(list_to_set_disj l0) ≡ₚ l1.
Proof.
revert l1. induction l0 as [| x l]; [ms|]. intro.
rewrite Proper_elements ; [|symmetry; apply list_to_set_disj_env_add].
setoid_rewrite elements_env_add ; rewrite IHl ; auto. trivial.
Qed.

Lemma list_to_set_disj_open_boxes Δ: ((⊗ (list_to_set_disj Δ)) = list_to_set_disj (map open_box (List.filter is_box Δ))).
Proof.
induction Δ as [|φ Δ]; simpl; [ms|].
destruct (is_box φ) eqn:E.
- simpl (map open_box (φ :: List.filter is_box Δ)).
  simpl (list_to_set_disj ((⊙ φ) :: map open_box (List.filter is_box Δ))).
  rewrite open_boxes_disj_union.
  rewrite  open_boxes_singleton_t ; auto. ms.
- rewrite open_boxes_disj_union.
  rewrite  open_boxes_singleton_f ; auto. ms.
Qed.

Lemma l_open_boxes_perm : Proper ((≡ₚ@{form}) ==> (≡ₚ@{form})) l_open_boxes.
Proof.
intros l0. induction l0.
- cbn ; intros. apply Permutation_nil_l in H ; subst ; auto.
- intros. symmetry in H. destruct (Permutation_vs_cons_inv H) as (y0 & y1 & Hy). subst.
  rewrite l_open_boxes_app. cbn. destruct (is_box a) eqn:E.
  + destruct a ; cbn in E ; try discriminate. apply Permutation_cons_app.
    rewrite <- l_open_boxes_app. apply IHl0. symmetry in H.
    apply Permutation_cons_app_inv in H ; auto.
  + destruct a ; cbn in E ; try discriminate ; rewrite <- l_open_boxes_app ; 
    apply IHl0 ; symmetry in H ; apply Permutation_cons_app_inv in H ; auto.
Qed.

Lemma rm_perm_inside l0 l1 ψ ϕ : rm ψ (ϕ :: l0 ++ l1) ≡ₚ rm ψ (l0 ++ ϕ :: l1).
Proof.
revert l1 ψ ϕ.
induction l0 ; intros ; cbn ; auto.
destruct (form_eq_dec ψ ϕ) ; subst.
- destruct (form_eq_dec ϕ a) ; subst ; auto.
  + apply Permutation_middle.
  + rewrite <- IHl0 ; cbn. destruct (form_eq_dec ϕ ϕ) ; subst ; try contradiction.
    auto.
- destruct (form_eq_dec ϕ a) ; subst ; auto.
  + destruct (form_eq_dec ψ a) ; try contradiction ; auto. rewrite <- IHl0 ; cbn.
    destruct (form_eq_dec ψ a) ; try contradiction ; auto.
  + destruct (form_eq_dec ψ a) ; try contradiction ; auto.
    * apply Permutation_middle.
    * rewrite <- IHl0 ; cbn. destruct (form_eq_dec ψ ϕ) ; subst ; try contradiction.
      apply perm_swap.
Qed.

Lemma rm_perm ψ : Proper ((≡ₚ@{form}) ==> (≡ₚ@{form})) (rm ψ).
Proof.
intros l0. induction l0.
- cbn ; intros. apply Permutation_nil_l in H ; subst ; auto.
- intros. symmetry in H. destruct (Permutation_vs_cons_inv H) as (y0 & y1 & Hy). subst.
  symmetry in H ; apply Permutation_cons_app_inv in H ; auto.
  pose (IHl0 _ H). rewrite <- rm_perm_inside.
  cbn ; destruct (form_eq_dec ψ a) ; subst ; auto.
Qed.

Lemma elements_setminus (Γ : env) ψ : elements (Γ ∖ {[ψ]}) ≡ₚ rm ψ (elements Γ).
Proof.
case (decide (ψ ∈ Γ)) ; intro H.
- apply difference_singleton in H.
  assert (elements Γ ≡ₚ elements (Γ ∖ {[ψ]} • ψ)) by (rewrite <- H ; auto).
  rewrite rm_perm ; [ | exact H0]. 
  rewrite rm_perm ; [ | apply elements_env_add].
  cbn. destruct (form_eq_dec ψ ψ) ; try contradiction ; auto.
- rewrite diff_not_in ; auto. rewrite rm_notin ; auto. intro.
  apply H. apply gmultiset_elem_of_elements ; auto.
Qed.

End Modal.


Global Hint Resolve In_open_boxes_t : proof.
Global Hint Unfold open_box : proof.
Global Hint Rewrite (@open_boxes_empty) : proof.
Global Hint Rewrite (@open_boxes_add_t) : proof.
Global Hint Rewrite (@open_boxes_add_f) : proof.
Global Hint Rewrite (@open_boxes_remove_t) : proof.
Global Hint Rewrite (@open_boxes_remove_f) : proof.
Global Hint Rewrite (@open_boxes_singleton_t): proof.
Global Hint Rewrite (@open_boxes_singleton_f): proof.


Lemma elements_list_to_set_disj (Γ : env) : (≡@{env}) Γ (list_to_set_disj (elements Γ)).
Proof.
  induction (gmultiset_wf Γ) as [Γ _ IH].
  destruct (gmultiset_choose_or_empty Γ) as [[φ Hφ]| ->]; auto.
  rewrite (gmultiset_disj_union_difference' φ Γ) by done.
  etransitivity ; [ | apply env_equiv_eq ; apply list_to_set_disj_perm ; symmetry ; apply gmultiset_elements_disj_union ].
  rewrite list_to_set_disj_app.
  rewrite <- (IH (Γ ∖ {[+ φ +]})).
  - apply equiv_disj_union_compat_r ; auto. rewrite gmultiset_elements_singleton.
    rewrite list_to_set_disj_cons. ms.
  - split.
    + ms.
    + intro. pose (H φ). rewrite diff_mult in l. rewrite singleton_mult_in in l ; auto. cbn in l.
      pose (elem_of_multiplicity φ). rewrite i in Hφ. lia.
Qed.


Lemma rm_add Γ φ : In φ Γ -> Γ ≡ₚ φ :: rm φ Γ.
Proof.
revert φ. induction Γ ; intros φ Hin ; [ inversion Hin | ].
inversion Hin ; subst.
- cbn. destruct (form_eq_dec φ φ) ; [ auto | exfalso ; auto].
- cbn ; destruct (form_eq_dec φ a) ; subst ; auto.
  rewrite perm_swap. rewrite <- IHΓ ; auto.
Qed.
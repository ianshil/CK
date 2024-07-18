Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Lia.
Require Import Ensembles.
Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import im_syntax.
Require Import CKH.
Require Import logic.
Require Import properties.
Require Import enum.

Section General_Lind.

Variable AdAx : form -> Prop.


Section Sets_of_forms.

Definition SubTheory (Γ Δ : @Ensemble form) (Incl: Included _ Δ Γ) := forall φ, (extCKH_prv AdAx Δ φ /\ In _ Γ φ) -> In _ Δ φ.

Definition closed Γ :=
  forall φ, extCKH_prv AdAx Γ φ -> Γ φ.

Definition restr_closed Γ Δ :=
  forall φ, extCKH_prv AdAx Δ φ -> Γ φ -> Δ φ.

Definition prime (Γ : @Ensemble form) :=
  forall φ ψ, Γ (Or φ ψ) -> Γ φ \/ Γ ψ.

Definition quasi_prime (Γ : @Ensemble form) :=
  forall φ ψ, Γ (Or φ ψ) -> ~ ~ (Γ φ \/ Γ ψ).

End Sets_of_forms.


Section prelims.

Lemma prime_list_disj l Δ :
  prime Δ -> Δ (list_disj l) -> exists A, (List.In A l \/ A = Bot) /\ Δ A.
Proof.
induction l ; cbn ; intros.
- exists Bot ; auto.
- destruct (H _ _ H0). exists a ; split ; auto. apply IHl in H1 ; auto.
  destruct H1 as (A & [H2 | H2] & H3). exists A ; split ; auto. subst.
  exists Bot ; split ; auto.
Qed.

Definition Theory Γ := closed Γ /\ prime Γ.

Definition AllForm := fun (A: form) => True.

Lemma Theory_AllForm : Theory AllForm.
Proof.
split.
- intros A HA. unfold AllForm ; auto.
- intros A B Hor. left ; unfold AllForm ; auto.
Qed.

End prelims.






Section Prime.

(* We define the step-by-step construction of the Lindenbaum extension. *)

Definition choice_form Γ Δ ψ φ: Ensemble form :=
fun x => Δ x \/ (Γ x /\ ~ (extCKH_prv AdAx (Union _ Δ (Singleton _ x)) ψ) /\ φ = x).

Definition choice_code Γ Δ ψ (n :nat) : @Ensemble form := (choice_form Γ Δ ψ (form_enum n)).

Fixpoint nLind_theory Γ Δ ψ n : @Ensemble form :=
match n with
| 0 => Δ
| S m => choice_code Γ (nLind_theory Γ Δ ψ m) ψ m
end.

(* The Lindenbaum extension is then defined as follows. *)

Definition Lind_theory Γ Δ ψ : @Ensemble form :=
  fun x => (exists n, In _ (nLind_theory Γ Δ ψ n) x).

End Prime.









Section PrimeProps.

(* The Lindenbaum theory is an extension of the initial set of formulas. *)

Lemma nLind_theory_extens : forall n Γ Δ ψ φ,
    In _ Δ φ -> In _ (nLind_theory Γ Δ ψ n) φ.
Proof.
induction n.
- cbn. intros. unfold In. unfold choice_code. unfold choice_form. auto.
- cbn. intros. pose (IHn Γ Δ ψ φ H). unfold choice_code.
  unfold choice_form. cbn. unfold In ; auto.
Qed.

Lemma nLind_theory_extens_le : forall m n Γ Δ ψ φ,
    In _ (nLind_theory Γ Δ ψ n) φ -> (le n m) -> In _ (nLind_theory Γ Δ ψ m) φ.
Proof.
induction m.
- intros. cbn. inversion H0. subst. cbn in H. auto.
- intros. inversion H0.
  + subst. auto.
  + subst. cbn. unfold In. apply IHm in H ; auto. unfold choice_code.
     unfold choice_form. unfold In ; auto.
Qed.

Lemma Lind_theory_extens : forall Γ Δ ψ φ,
    In _ Δ φ -> In _ (Lind_theory Γ Δ ψ) φ.
Proof.
intros. unfold Lind_theory. unfold In. exists 0. unfold nLind_theory.
unfold choice_code. unfold choice_form ; auto.
Qed.

Lemma incl_nLind_theory : forall n Γ Δ ψ,
    Included _ Δ Γ ->
    Included _ (nLind_theory Γ Δ ψ n) Γ.
Proof.
induction n.
- cbn. intros. intros φ H0. unfold In in * ; apply H ; auto.
- cbn. intros. intros φ H0. pose (IHn Γ Δ ψ H φ).
  unfold choice_code in H0. unfold choice_form in H0.
  destruct H0 ; auto. destruct H0 ; auto.
Qed.

Lemma incl_Lind_theory : forall Γ Δ ψ,
    Included _ Δ Γ ->
    Included _ (Lind_theory Γ Δ ψ) Γ.
Proof.
intros Γ Δ ψ H φ H0. unfold Lind_theory in H0. unfold In in *.
destruct H0. apply incl_nLind_theory in H0 ; auto.
Qed.

(* The Lindenbaum theory preserves derivability from the initial set of formulas. *)

Lemma der_nLind_theory_mLind_theory_le : forall n m Γ Δ ψ φ,
  (extCKH_prv AdAx (nLind_theory Γ Δ ψ n) φ) -> (le n m) ->
    (extCKH_prv AdAx (nLind_theory Γ Δ ψ m) φ).
Proof.
intros. apply (extCKH_monot _ _ _ H) ; auto.
intros C HC ; apply nLind_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma der_Lind_theory_nLind_theory : forall Γ Δ ψ A, extCKH_prv AdAx (Lind_theory Γ Δ ψ) A ->
                                        exists n, extCKH_prv AdAx (nLind_theory Γ Δ ψ n) A.
Proof.
intros Γ Δ ψ A D. remember (Lind_theory Γ Δ ψ) as X. revert Γ Δ ψ HeqX.
induction D ; cbn ; intros ; subst.
- destruct H as (n & Hn). exists n ; apply Id ; auto.
- exists 0 ; apply Ax ; auto.
- destruct (IHD2 Γ0 Δ ψ) ; auto. destruct (IHD1 Γ0 Δ ψ) ; auto.
  exists (max x x0). eapply MP. apply der_nLind_theory_mLind_theory_le with x0.
  exact H0. lia. apply der_nLind_theory_mLind_theory_le with x. exact H. lia.
- exists 0. apply Nec ; auto.
Qed.

(* Each step of the construction preserves underivability of the formula ψ. *)

Lemma Under_nLind_theory : forall n Γ Δ ψ,
  Included _ Δ Γ ->
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (nLind_theory Γ Δ ψ n) ψ.
Proof.
induction n ; intros ; cbn in * ; auto.
specialize (IHn _ _ _ H H0). intro.
apply IHn. unfold choice_code in *. unfold choice_form in *.
apply (extCKH_monot _ _ _ H1).
intros a Ha ; cbn in Ha. unfold In in *. destruct Ha ; auto.
destruct H2. destruct H3 ; subst. exfalso.
apply H3. apply (extCKH_monot _ _ _ H1).
intros a Ha ; cbn in Ha. unfold In in *. destruct Ha.
left ; auto. destruct H4 ; destruct H5 ; subst.
right ; apply In_singleton.
Qed.

(* The Lindenbaum theory does not derive ψ. *)

Lemma Under_Lind_theory: forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (Lind_theory Γ Δ ψ) ψ.
Proof.
intros Γ Δ ψ Incl H H0.
destruct (der_Lind_theory_nLind_theory _ _ _ _ H0).
pose (Under_nLind_theory x _ _ _ Incl H). auto.
Qed.

(* The Lindenbaum theory is closed under derivation. *)

Lemma restr_closeder_Lind_theory : forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ extCKH_prv AdAx Δ ψ ->
  restr_closed Γ (Lind_theory Γ Δ ψ).
Proof.
intros Γ Δ ψ Incl H. intros A H0. unfold Lind_theory. exists (S (form_index A)). unfold In. cbn.
unfold choice_code. unfold choice_form. right. repeat split ; auto. 2: apply form_enum_index.
intro. eapply Under_Lind_theory ; auto. exact Incl. exact H.
eapply MP. 2: exact H0. apply extCKH_Deduction_Theorem in H2.
apply (extCKH_monot _ _ _ H2). intros C HC. exists (form_index A) ; auto.
Qed.

(* Not being in Lind_theory implies not being derivable from the theory. *)

Lemma not_In_Lind_theory_deriv : forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ extCKH_prv AdAx Γ ψ ->
  forall A, Γ A -> ~ (Lind_theory Γ Δ ψ A) ->
    ~~ extCKH_prv AdAx (Union _ (Lind_theory Γ Δ ψ) (Singleton _ A)) ψ.
Proof.
intros Γ Δ ψ Incl H A HA H0 H1. apply H0. exists (S (form_index A)).
cbn. unfold In. unfold choice_code. unfold choice_form ; cbn.
right. repeat split ; auto. 2: apply form_enum_index.
intro. apply H1. apply (extCKH_monot _ _ _ H2). intros C HC. unfold In in *. inversion HC ; subst.
unfold In in *. left. exists (form_index A) ; auto. right ; auto.
Qed.

(* The Lindenbaum theory is quasi-prime. *)

Lemma quasi_prime_Lind_theory: forall Γ Δ ψ,
  Included _ Δ (Clos Γ) ->
  ~ extCKH_prv AdAx Δ ψ ->
  quasi_prime (Lind_theory (Clos Γ) Δ ψ).
Proof.
intros Γ Δ ψ Incl H0 a b Hor H1. remember (Clos Γ) as CΓ.
apply H1. left. exists (S (form_index a)). cbn.
unfold choice_code. unfold choice_form. unfold In.
right. repeat split ; auto. 3: apply form_enum_index.
subst. apply Incl_ClosSubform_Clos. exists (a ∨ b). split ; auto.
apply incl_Lind_theory in Hor ; auto.
cbn. right ; apply in_or_app ; left ; destruct a ; cbn ; auto.
intro. apply H1. right. exists (S (form_index b)). cbn.
subst. unfold choice_code. unfold choice_form. right. repeat split.
apply Incl_ClosSubform_Clos. exists (a ∨ b). split ; auto.
apply incl_Lind_theory in Hor ; auto.
cbn. right ; apply in_or_app ; right ; destruct b ; cbn ; auto.
2: apply form_enum_index. intro.
pose (Under_Lind_theory (Clos Γ) Δ ψ Incl H0). apply n.
eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity.
apply extCKH_Deduction_Theorem.
apply extCKH_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form a)) in H. exact H.
cbn ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists (form_index a) ; auto.
inversion H3 ; subst ; apply Union_intror ; apply In_singleton.
apply extCKH_Deduction_Theorem.
apply extCKH_monot with (Γ1:=Union form (Lind_theory (Clos Γ) Δ ψ) (Singleton form b)) in H2. exact H2.
cbn ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists (form_index b) ; auto.
inversion H3 ; subst ; apply Union_intror ; apply In_singleton.
apply Id ; auto.
Qed.

(* The Lindenbaum theory preserves consistency. *)

Lemma Consist_nLind_theory : forall n Γ Δ ψ,
  Included _ Δ Γ ->
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (nLind_theory Γ Δ ψ n) ⊥.
Proof.
intros n Γ Δ ψ Incl H H0. pose (Under_nLind_theory n Γ Δ ψ Incl H).
apply n0. eapply MP. apply EFQ. auto.
Qed.

Lemma Consist_Lind_theory : forall Γ Δ ψ,
  Included _ Δ Γ ->
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (Lind_theory Γ Δ ψ) ⊥.
Proof.
intros Γ Δ ψ H H0 H1.
pose (Under_Lind_theory Γ Δ ψ H H0). apply n. eapply MP.
apply EFQ. auto.
Qed.

End PrimeProps.




Section Lindenbaum_lemma.

(* Lindenbaum lemma. *)

Lemma Lindenbaum Γ Δ ψ :
  In _ (Clos Γ) ψ ->
  Included _ Δ (Clos Γ) ->
  ~ extCKH_prv AdAx Δ ψ ->
  { Δm | Included _ Δ Δm
           /\ Included _ Δm (Clos Γ)
           /\ restr_closed (Clos Γ) Δm
           /\ quasi_prime Δm
           /\ ~ extCKH_prv AdAx Δm ψ}.
Proof.
intros.
exists (Lind_theory (Clos Γ) Δ ψ).
repeat split.
- intro. apply Lind_theory_extens.
- apply incl_Lind_theory ; auto.
- apply restr_closeder_Lind_theory ; auto.
- pose quasi_prime_Lind_theory ; auto.
- intro. apply Under_Lind_theory with (Γ:=(Clos Γ)) in H1 ; auto.
Qed.

End Lindenbaum_lemma.


End General_Lind.


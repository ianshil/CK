From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.
From Stdlib Require Import Ensembles.
From Stdlib Require Import Logic.Description.
From Stdlib Require Import Logic.FunctionalExtensionality.

Require Import im_syntax.
Require Import CKH.
Require Import logic.
Require Import properties.
Require Import enum.
Require Import Lindenbaum_lem.

Section General_Lind_pair.

Variable AdAx : form -> Prop.

Section Pair.

Definition pair_extCKH_prv Γ Δ := exists l, (forall A, List.In A l -> Δ A) /\
                                                                    extCKH_prv AdAx Γ (list_disj l) .

End Pair.





Section Prime.

Definition pair_choice_form Δ Ψ φ: Ensemble form :=
fun x => Δ x \/ (~ (pair_extCKH_prv (Union _ Δ (Singleton _ x)) Ψ) /\ φ = x).

Definition pair_choice_code Δ Ψ (n :nat) : @Ensemble form := (pair_choice_form Δ Ψ (form_enum n)).

Fixpoint npair_Lind_theory Δ Ψ n : @Ensemble form :=
match n with
| 0 => Δ
| S m => pair_choice_code (npair_Lind_theory Δ Ψ m) Ψ m
end.

Definition pair_Lind_theory Δ Ψ : @Ensemble form :=
  fun x => (exists n, In _ (npair_Lind_theory Δ Ψ n) x).

End Prime.









Section PrimeProps.

(* The Lindenbaum theory is an extension of the initial set of formulas. *)

Lemma npair_Lind_theory_extens : forall n Δ ψ φ,
    In _ Δ φ -> In _ (npair_Lind_theory Δ ψ n) φ.
Proof.
induction n.
- cbn. intros. unfold In. unfold pair_choice_code. unfold pair_choice_form. auto.
- cbn. intros. pose (IHn Δ ψ φ H). unfold pair_choice_code.
  unfold pair_choice_form. cbn. unfold In ; auto.
Qed.

Lemma npair_Lind_theory_extens_le : forall m n Δ ψ φ,
    In _ (npair_Lind_theory Δ ψ n) φ -> (le n m) -> In _ (npair_Lind_theory Δ ψ m) φ.
Proof.
induction m.
- intros. cbn. inversion H0. subst. cbn in H. auto.
- intros. inversion H0.
  + subst. auto.
  + subst. cbn. unfold In. apply IHm in H ; auto. unfold pair_choice_code.
     unfold pair_choice_form. unfold In ; auto.
Qed.

Lemma pair_Lind_theory_extens : forall Δ ψ φ,
    In _ Δ φ -> In _ (pair_Lind_theory Δ ψ) φ.
Proof.
intros. unfold pair_Lind_theory. unfold In. exists 0. unfold npair_Lind_theory.
unfold pair_choice_code. unfold pair_choice_form ; auto.
Qed.

(* The Lindenbaum theory preserves derivability from the initial set of formulas. *)

Lemma der_npair_Lind_theory_mpair_Lind_theory_le : forall n m Δ ψ φ,
  (extCKH_prv AdAx (npair_Lind_theory Δ ψ n) φ) -> (le n m) ->
    (extCKH_prv AdAx (npair_Lind_theory Δ ψ m) φ).
Proof.
intros. apply (extCKH_monot _ _ _ H) ; auto.
intros C HC ; apply npair_Lind_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma der_pair_Lind_theory_npair_Lind_theory : forall Δ ψ A, extCKH_prv AdAx (pair_Lind_theory Δ ψ) A ->
                                        exists n, extCKH_prv AdAx (npair_Lind_theory Δ ψ n) A.
Proof.
intros Δ ψ A D. remember (pair_Lind_theory Δ ψ) as X. revert Δ ψ HeqX.
induction D ; cbn ; intros ; subst.
- destruct H as (n & Hn). exists n ; apply Id ; auto.
- exists 0 ; apply Ax ; auto.
- destruct (IHD2 Δ ψ) ; auto. destruct (IHD1 Δ ψ) ; auto.
  exists (max x x0). eapply MP. apply der_npair_Lind_theory_mpair_Lind_theory_le with x0.
  exact H0. lia. apply der_npair_Lind_theory_mpair_Lind_theory_le with x. exact H. lia.
- exists 0. apply Nec ; auto.
Qed.

(* Each step of the construction preserves underivability of the set of formulas ψ. *)

Lemma Under_npair_Lind_theory : forall n Δ ψ,
  ~ pair_extCKH_prv Δ ψ ->
  ~ pair_extCKH_prv (npair_Lind_theory Δ ψ n) ψ.
Proof.
induction n ; intros ; cbn in * ; auto.
specialize (IHn _ _ H). intro.
apply IHn. unfold pair_choice_code in *. unfold pair_choice_form in *.
destruct H0 as (l & Hl0 & Hl1). exists l. split ; auto.
apply (extCKH_monot _ _ _ Hl1).
intros a Ha ; cbn in Ha. unfold In in *. destruct Ha ; auto.
destruct H0. destruct H1 ; subst. exfalso.
apply H0. exists l ; split ; auto.
apply (extCKH_monot _ _ _ Hl1).
intros a Ha ; cbn in Ha. unfold In in *. destruct Ha.
left ; auto. destruct H1 ; destruct H2 ; subst.
right ; apply In_singleton.
Qed.

(* The Lindenbaum theory does not derive ψ. *)

Lemma Under_pair_Lind_theory: forall Δ ψ,
  ~ pair_extCKH_prv Δ ψ ->
  ~ pair_extCKH_prv (pair_Lind_theory Δ ψ) ψ.
Proof.
intros Δ ψ H H0.
destruct H0 as (l & J0 & J1).
destruct (der_pair_Lind_theory_npair_Lind_theory _ _ _ J1).
pose (Under_npair_Lind_theory x _ _ H). 
apply n. exists l ; split ; auto.
Qed.

(* The Lindenbaum theory is closed under derivation. *)

Lemma closeder_pair_Lind_theory : forall Δ ψ,
  ~ pair_extCKH_prv Δ ψ ->
  closed AdAx (pair_Lind_theory Δ ψ).
Proof.
intros Δ ψ H. intros A H0. unfold pair_Lind_theory. exists (S (form_index A)). unfold In. cbn.
unfold pair_choice_code. unfold pair_choice_form. right. repeat split ; auto. 2: apply form_enum_index.
intro. eapply Under_pair_Lind_theory ; auto. exact H.
destruct H1 as (l & J0 & J1). exists l ; split ; auto.
eapply MP. 2: exact H0. apply extCKH_Deduction_Theorem in J1.
apply (extCKH_monot _ _ _ J1). intros C HC. exists (form_index A) ; auto.
Qed.

(* Not in pair_Lind_theory does not derive *)

Lemma not_In_pair_Lind_theory_deriv : forall Δ ψ,
  forall A, ~ (pair_Lind_theory Δ ψ A) ->
    ~~ pair_extCKH_prv (Union _ (pair_Lind_theory Δ ψ) (Singleton _ A)) ψ.
Proof.
intros Δ ψ A H0 H1. apply H0. exists (S (form_index A)).
cbn. unfold In. unfold pair_choice_code. unfold pair_choice_form ; cbn.
right. repeat split ; auto. 2: apply form_enum_index.
intro. apply H1.
destruct H as (l & J0 & J1). exists l ; split ; auto.
apply (extCKH_monot _ _ _ J1). intros C HC. unfold In in *. inversion HC ; subst.
unfold In in *. left. exists (form_index A) ; auto. right ; auto.
Qed.

(* The Lindenbaum theory is quasi-prime. *)

Lemma quasi_prime_pair_Lind_theory: forall Δ ψ,
  ~ pair_extCKH_prv Δ ψ ->
  quasi_prime (pair_Lind_theory Δ ψ).
Proof.
intros Δ ψ H0 a b Hor H1.
apply H1. left. exists (S (form_index a)). cbn.
unfold pair_choice_code. unfold pair_choice_form. unfold In.
right. repeat split ; auto. 2: apply form_enum_index.
intro. apply H1. right. exists (S (form_index b)). cbn.
subst. unfold pair_choice_code. unfold pair_choice_form. right. repeat split.
2: apply form_enum_index. intro.
pose (Under_pair_Lind_theory Δ ψ H0). apply n.
destruct H as (la & J0 & J1). destruct H2 as (lb & J2 & J3).
exists (la ++ lb) ; split.
- intros. apply in_app_or in H ; destruct H ; auto.
- eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity.
  apply extCKH_Deduction_Theorem.
  apply extCKH_monot with (Γ1:=Union form (pair_Lind_theory Δ ψ) (Singleton form a)) in J1.
  apply IdL_list_disj ; exact J1.
  cbn ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists (form_index a) ; auto.
  inversion H ; subst ; apply Union_intror ; apply In_singleton.
  apply extCKH_Deduction_Theorem.
  apply extCKH_monot with (Γ1:=Union form (pair_Lind_theory Δ ψ) (Singleton form b)) in J3.
  apply IdR_list_disj ; exact J3.
  cbn ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists (form_index b) ; auto.
  inversion H ; subst ; apply Union_intror ; apply In_singleton.
  apply Id ; exact Hor.
Qed.

(* The Lindenbaum theory preserves consistency. *)

Lemma Consist_npair_Lind_theory : forall n Δ ψ,
  ~ pair_extCKH_prv Δ ψ ->
  ~ extCKH_prv AdAx (npair_Lind_theory Δ ψ n) ⊥.
Proof.
intros n Δ ψ H H0. pose (Under_npair_Lind_theory n Δ ψ H).
apply n0. exists []. split ; auto. intros A HA ; inversion HA.
Qed.

Lemma Consist_pair_Lind_theory : forall Δ ψ,
  ~ pair_extCKH_prv Δ ψ ->
  ~ extCKH_prv AdAx (pair_Lind_theory Δ ψ) ⊥.
Proof.
intros Δ ψ H0 H1.
pose (Under_pair_Lind_theory Δ ψ H0). apply n. exists []. split ; auto.
 intros A HA ; inversion HA.
Qed.

End PrimeProps.




Section Lindenbaum_lemma.

(* Lindenbaum lemma. *)

Lemma Lindenbaum_pair Δ ψ :
  ~ pair_extCKH_prv Δ ψ ->
  { Δm | Included _ Δ Δm
           /\ closed AdAx Δm
           /\ quasi_prime Δm
           /\ ~ pair_extCKH_prv Δm ψ}.
Proof.
intros.
exists (pair_Lind_theory Δ ψ).
repeat split.
- intro. apply pair_Lind_theory_extens.
- apply closeder_pair_Lind_theory ; auto.
- pose quasi_prime_pair_Lind_theory ; auto.
- intro. apply Under_pair_Lind_theory in H0 ; auto.
Qed.

End Lindenbaum_lemma.


End General_Lind_pair.


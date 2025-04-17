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

Definition choice_form Δ ψ φ: Ensemble form :=
fun x => Δ x \/ (~ (extCKH_prv AdAx (Union _ Δ (Singleton _ x)) ψ) /\ φ = x).

Definition choice_code Δ ψ (n :nat) : @Ensemble form := (choice_form Δ ψ (form_enum n)).

Fixpoint nLind_theory Δ ψ n : @Ensemble form :=
match n with
| 0 => Δ
| S m => choice_code (nLind_theory Δ ψ m) ψ m
end.

(* The Lindenbaum extension is then defined as follows. *)

Definition Lind_theory Δ ψ : @Ensemble form :=
  fun x => (exists n, In _ (nLind_theory Δ ψ n) x).

End Prime.









Section PrimeProps.

(* The Lindenbaum theory is an extension of the initial set of formulas. *)

Lemma nLind_theory_extens : forall n Δ ψ φ,
    In _ Δ φ -> In _ (nLind_theory Δ ψ n) φ.
Proof.
induction n.
- cbn. intros. unfold In. unfold choice_code. unfold choice_form. auto.
- cbn. intros. pose (IHn Δ ψ φ H). unfold choice_code.
  unfold choice_form. cbn. unfold In ; auto.
Qed.

Lemma nLind_theory_extens_le : forall m n Δ ψ φ,
    In _ (nLind_theory Δ ψ n) φ -> (le n m) -> In _ (nLind_theory Δ ψ m) φ.
Proof.
induction m.
- intros. cbn. inversion H0. subst. cbn in H. auto.
- intros. inversion H0.
  + subst. auto.
  + subst. cbn. unfold In. apply IHm in H ; auto. unfold choice_code.
     unfold choice_form. unfold In ; auto.
Qed.

Lemma Lind_theory_extens : forall Δ ψ φ,
    In _ Δ φ -> In _ (Lind_theory Δ ψ) φ.
Proof.
intros. unfold Lind_theory. unfold In. exists 0. unfold nLind_theory.
unfold choice_code. unfold choice_form ; auto.
Qed.

(* The Lindenbaum theory preserves derivability from the initial set of formulas. *)

Lemma der_nLind_theory_mLind_theory_le : forall n m Δ ψ φ,
  (extCKH_prv AdAx (nLind_theory Δ ψ n) φ) -> (le n m) ->
    (extCKH_prv AdAx (nLind_theory Δ ψ m) φ).
Proof.
intros. apply (extCKH_monot _ _ _ H) ; auto.
intros C HC ; apply nLind_theory_extens_le with (n:=n) ; auto.
Qed.

Lemma der_Lind_theory_nLind_theory : forall Δ ψ A, extCKH_prv AdAx (Lind_theory Δ ψ) A ->
                                        exists n, extCKH_prv AdAx (nLind_theory Δ ψ n) A.
Proof.
intros Δ ψ A D. remember (Lind_theory Δ ψ) as X. revert Δ ψ HeqX.
induction D ; cbn ; intros ; subst.
- destruct H as (n & Hn). exists n ; apply Id ; auto.
- exists 0 ; apply Ax ; auto.
- destruct (IHD2 Δ ψ) ; auto. destruct (IHD1 Δ ψ) ; auto.
  exists (max x x0). eapply MP. apply der_nLind_theory_mLind_theory_le with x0.
  exact H0. lia. apply der_nLind_theory_mLind_theory_le with x. exact H. lia.
- exists 0. apply Nec ; auto.
Qed.

(* Each step of the construction preserves underivability of the formula ψ. *)

Lemma Under_nLind_theory : forall n Δ ψ,
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (nLind_theory Δ ψ n) ψ.
Proof.
induction n ; intros ; cbn in * ; auto.
specialize (IHn _ _ H). intro.
apply IHn. unfold choice_code in *. unfold choice_form in *.
apply (extCKH_monot _ _ _ H0).
intros a Ha ; cbn in Ha. unfold In in *. destruct Ha ; auto.
destruct H1. destruct H2 ; subst. exfalso.
apply H1. apply (extCKH_monot _ _ _ H0).
intros a Ha ; cbn in Ha. unfold In in *. destruct Ha.
left ; auto. destruct H2 ; destruct H3 ; subst.
right ; apply In_singleton.
Qed.

(* The Lindenbaum theory does not derive ψ. *)

Lemma Under_Lind_theory: forall Δ ψ,
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (Lind_theory Δ ψ) ψ.
Proof.
intros Δ ψ H H0.
destruct (der_Lind_theory_nLind_theory _ _ _ H0).
pose (Under_nLind_theory x _ _ H). auto.
Qed.

(* The Lindenbaum theory is closed under derivation. *)

Lemma closeder_Lind_theory : forall Δ ψ,
  ~ extCKH_prv AdAx Δ ψ ->
  closed (Lind_theory Δ ψ).
Proof.
intros Δ ψ Incl. intros A H0. unfold Lind_theory. exists (S (form_index A)). unfold In. cbn.
unfold choice_code. unfold choice_form. right. repeat split ; auto. 2: apply form_enum_index.
intro. eapply Under_Lind_theory ; auto. exact Incl.
eapply MP. 2: exact H0. apply extCKH_Deduction_Theorem in H.
apply (extCKH_monot _ _ _ H). intros C HC. exists (form_index A) ; auto.
Qed.

(* Not being in Lind_theory implies not being derivable from the theory. *)

Lemma not_In_Lind_theory_deriv : forall Δ ψ,
  ~ extCKH_prv AdAx Δ ψ ->
  forall A, ~ (Lind_theory Δ ψ A) ->
    ~~ extCKH_prv AdAx (Union _ (Lind_theory Δ ψ) (Singleton _ A)) ψ.
Proof.
intros Δ ψ H A H0 H1. apply H0. exists (S (form_index A)).
cbn. unfold In. unfold choice_code. unfold choice_form ; cbn.
right. repeat split ; auto. 2: apply form_enum_index.
intro. apply H1. apply (extCKH_monot _ _ _ H2). intros C HC. unfold In in *. inversion HC ; subst.
unfold In in *. left. exists (form_index A) ; auto. right ; auto.
Qed.

(* The Lindenbaum theory is quasi-prime. *)

Lemma quasi_prime_Lind_theory: forall Δ ψ,
  ~ extCKH_prv AdAx Δ ψ ->
  quasi_prime (Lind_theory Δ ψ).
Proof.
intros Δ ψ H0 a b Hor H1.
apply H1. left. exists (S (form_index a)). cbn.
unfold choice_code. unfold choice_form.
right. repeat split ; auto. 2: apply form_enum_index.
intro. apply H1. right. exists (S (form_index b)). cbn.
subst. unfold choice_code. unfold choice_form. right. repeat split.
2: apply form_enum_index.
intro. pose (Under_Lind_theory Δ ψ H0). apply n.
eapply MP. eapply MP. eapply MP. apply Ax ; left ; left ; eapply IA5 ; reflexivity.
apply extCKH_Deduction_Theorem.
apply extCKH_monot with (Γ1:=Union form (Lind_theory Δ ψ) (Singleton form a)) in H. exact H.
cbn ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists (form_index a) ; auto.
inversion H3 ; subst ; apply Union_intror ; apply In_singleton.
apply extCKH_Deduction_Theorem.
apply extCKH_monot with (Γ1:=Union form (Lind_theory Δ ψ) (Singleton form b)) in H2. exact H2.
cbn ; intros c Hc. inversion Hc ; subst. apply Union_introl. unfold In. exists (form_index b) ; auto.
inversion H3 ; subst ; apply Union_intror ; apply In_singleton.
apply Id ; auto.
Qed.

(* The Lindenbaum theory preserves consistency. *)

Lemma Consist_nLind_theory : forall n Δ ψ,
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (nLind_theory Δ ψ n) ⊥.
Proof.
intros n Δ ψ H H0. pose (Under_nLind_theory n Δ ψ H).
apply n0. eapply MP. apply EFQ. auto.
Qed.

Lemma Consist_Lind_theory : forall Δ ψ,
  ~ extCKH_prv AdAx Δ ψ ->
  ~ extCKH_prv AdAx (Lind_theory Δ ψ) ⊥.
Proof.
intros Δ ψ H0 H1.
pose (Under_Lind_theory Δ ψ H0). apply n. eapply MP.
apply EFQ. auto.
Qed.

End PrimeProps.




Section Lindenbaum_lemma.

(* Lindenbaum lemma. *)

Lemma Lindenbaum Δ ψ :
  ~ extCKH_prv AdAx Δ ψ ->
  { Δm | Included _ Δ Δm
           /\ closed Δm
           /\ quasi_prime Δm
           /\ ~ extCKH_prv AdAx Δm ψ}.
Proof.
intros.
exists (Lind_theory Δ ψ).
repeat split.
- intro. apply Lind_theory_extens.
- apply closeder_Lind_theory ; auto.
- pose quasi_prime_Lind_theory ; auto.
- intro. apply Under_Lind_theory in H0 ; auto.
Qed.

End Lindenbaum_lemma.


End General_Lind.


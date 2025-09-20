From Stdlib Require Import Ensembles.

Require Import im_syntax syntax_facts. (* Syntax *)
Require Import CKSequents CKSequentProps CKOrder CKCut. (* Sequent calculus *)
Require Import CKH_export. (* Hilbert calculus *)
Require Import CKDecisionProcedure.

Section Soundness.

(* First we need some theorems about CKH_prv relating to the 
   syntactic definitions pertaining to G4CK. *)

Lemma open_boxes_K_rule (Γ : env) φ :
  CKH_prv (fun γ => γ ∈ (⊗ Γ)) φ ->  CKH_prv (fun γ => γ ∈ Γ) (□ φ).
Proof.
intro H. remember (λ γ : form, γ ∈ (⊗ Γ)) as Γ'.
apply extCKH_comp with (λ x : form, ∃ B : form, (Ensembles.In form Γ' B ∧ x = (□ B))%type).
- apply K_rule. apply (extCKH_comp _ _ _ H) ; subst.
  intros. apply elem_of_open_boxes in H0 as [ψ [H1 H2]] ; subst.
  apply Id. unfold Ensembles.In ; cbn. 
  rewrite open_boxes_open_boxes'. apply elem_of_list_to_set_disj.
  apply in_l_open_boxes. apply gmultiset_elem_of_elements ; auto.
- intros ψ [χ [H0 H1]] ; subst ; apply Id. unfold Ensembles.In in *.
  apply elem_of_open_boxes in H0 as [ψ [H1 H2]] ; subst ; auto.
Qed.

Lemma open_boxes_Diam_rule (Γ : env) φ ψ : (◊ ψ) ∈ Γ ->
  CKH_prv (fun γ => γ ∈ ((⊗ Γ) • ψ)) φ ->  CKH_prv (fun γ => γ ∈ Γ) (◊ φ).
Proof.
intros Hin H. remember (λ γ : form, γ ∈ (⊗ Γ)) as Γ'.
apply extCKH_comp with (Ensembles.Union _ (λ x : form, ∃ B : form, (Ensembles.In form Γ' B ∧ x = (□ B))%type) (Ensembles.Singleton _ (◊ ψ))).
- apply Diam_rule. apply (extCKH_comp _ _ _ H) ; subst.
  intros. apply gmultiset_elem_of_disj_union in H0. destruct H0.
  + apply elem_of_open_boxes in H0 as [χ [H1 H2]] ; subst.
    apply Id. left ; unfold Ensembles.In ; cbn. 
    rewrite open_boxes_open_boxes'. apply elem_of_list_to_set_disj.
    apply in_l_open_boxes. apply gmultiset_elem_of_elements ; auto.
  + apply gmultiset_elem_of_singleton in H0 ; subst.
    apply Id ; right ; split.
- intros δ [χ [ρ [H0 H1]] | ] ; subst ; apply Id.
  + unfold Ensembles.In in *. apply elem_of_open_boxes in H0 as [γ [H1 H2]] ; subst ; auto.
  + inversion H0 ; subst. auto.
Qed.

Theorem G4CK_sound_CKH Γ φ : Γ ⊢ φ -> CKH_prv (fun γ => γ ∈ Γ) φ.
Proof.
induction 1.
- apply Id ; unfold Ensembles.In. ms.
- apply ND_BotE. apply Id ; unfold Ensembles.In ; ms.
- apply ND_AndI ; auto.
- apply extCKH_monot with (Γ:= Ensembles.Union _ (fun γ => γ ∈ Γ) (Ensembles.Singleton _ (φ ∧ ψ))).
  + apply extCKH_Detachment_Theorem. eapply MP ; [ apply Imp_And | ].
    do 2 (apply extCKH_Deduction_Theorem).
    apply (extCKH_monot _ _ _ IHProvable).
    intros χ Hχ. unfold Ensembles.In in *.
    apply gmultiset_elem_of_disj_union in Hχ ; destruct Hχ.
    * apply gmultiset_elem_of_disj_union in H0 ; destruct H0.
      -- do 2 left ; auto.
      -- left ; right. ms.
    * right ; ms.
  + intros χ Hχ. unfold Ensembles.In in *. inversion Hχ ; subst.
    * ms.
    * inversion H0 ; subst ; ms.
- apply ND_OrI1 ; auto.
- apply ND_OrI2 ; auto.
- apply ND_OrE with φ ψ.
  + apply Id. apply gmultiset_elem_of_disj_union ; right.
    apply gmultiset_elem_of_singleton ; auto.
  + apply extCKH_Deduction_Theorem. apply (extCKH_monot _ _ _ IHProvable1).
    intros χ Hχ. apply gmultiset_elem_of_disj_union in Hχ ; destruct Hχ.
    * left ; ms.
    * right ; ms.
  + apply extCKH_Deduction_Theorem. apply (extCKH_monot _ _ _ IHProvable2).
    intros χ Hχ. apply gmultiset_elem_of_disj_union in Hχ ; destruct Hχ.
    * left ; ms.
    * right ; ms.
- apply extCKH_Deduction_Theorem.
  apply (extCKH_monot _ _ _ IHProvable).
  intros χ Hχ. unfold Ensembles.In in *.
  apply gmultiset_elem_of_disj_union in Hχ ; destruct Hχ.
  + left ; ms.
  + right ; ms.
- apply (extCKH_comp _ _ _ IHProvable). intros χ Hin.
  apply gmultiset_elem_of_disj_union in Hin ; destruct Hin.
  + apply gmultiset_elem_of_disj_union in H0 ; destruct H0.
    * apply Id ; ms.
    * apply Id ; ms.
  + eapply MP ; apply Id.
    * apply gmultiset_elem_of_disj_union ; right.
      apply gmultiset_elem_of_singleton in H0 ; subst.
      apply gmultiset_elem_of_singleton ; auto.
    * ms.
- apply (extCKH_comp _ _ _ IHProvable). intros χ Hin.
  apply gmultiset_elem_of_disj_union in Hin ; destruct Hin.
  + apply Id ; ms.
  + apply gmultiset_elem_of_singleton in H0 ; subst.
    eapply MP ; [apply And_Imp | apply Id]. ms.
- apply (extCKH_comp _ _ _ IHProvable). intros χ Hin.
  apply gmultiset_elem_of_disj_union in Hin ; destruct Hin.
  + apply gmultiset_elem_of_disj_union in H0 ; destruct H0.
    * apply Id ; ms.
    * apply gmultiset_elem_of_singleton in H0 ; subst.
      apply extCKH_Deduction_Theorem.
      eapply MP ; [ apply Id ; left ; apply gmultiset_elem_of_disj_union ; right ; apply gmultiset_elem_of_singleton ; auto | ].
      apply ND_OrI1 ; apply Id ; right ; split.
  + apply gmultiset_elem_of_singleton in H0 ; subst.
    apply extCKH_Deduction_Theorem.
    eapply MP ; [ apply Id ; left ; apply gmultiset_elem_of_disj_union ; right ; apply gmultiset_elem_of_singleton ; auto | ].
    apply ND_OrI2 ; apply Id ; right ; split.
- apply (extCKH_comp _ _ _ IHProvable2). intros χ Hin.
  apply gmultiset_elem_of_disj_union in Hin ; destruct Hin.
  + apply Id ; ms.
  + apply gmultiset_elem_of_singleton in H1 ; subst.
    eapply MP ; [apply Id ; apply gmultiset_elem_of_disj_union ; right ; apply gmultiset_elem_of_singleton ; auto | ].
    apply extCKH_Deduction_Theorem. apply extCKH_Detachment_Theorem in IHProvable1.
    apply (extCKH_comp _ _ _ IHProvable1). intros χ Hin.
    inversion Hin ; subst.
    * apply gmultiset_elem_of_disj_union in H1 ; destruct H1.
      -- apply Id ; left ; ms.
      -- apply gmultiset_elem_of_singleton in H1 ; subst.
         apply extCKH_Deduction_Theorem.
         eapply MP ; [ apply Id ; left ; left ; apply gmultiset_elem_of_disj_union ; right ; apply gmultiset_elem_of_singleton ; auto | ].
         apply extCKH_Deduction_Theorem. apply Id ; left ; right ; split.
    * inversion H1 ; subst. apply Id ; right ; split.
- apply (extCKH_comp _ _ _ IHProvable2). intros χ Hin.
  apply gmultiset_elem_of_disj_union in Hin ; destruct Hin.
  + apply Id ; ms.
  + apply gmultiset_elem_of_singleton in H1 ; subst.
    eapply MP ; [apply Id ; apply gmultiset_elem_of_disj_union ; right ; apply gmultiset_elem_of_singleton ; auto | ].
    apply open_boxes_K_rule. rewrite open_boxes_add_f ; auto.
- apply (extCKH_comp _ _ _ IHProvable2). intros δ Hin.
  apply gmultiset_elem_of_disj_union in Hin ; destruct Hin.
  + apply gmultiset_elem_of_disj_union in H1 ; destruct H1.
    * apply Id ; ms.
    * apply gmultiset_elem_of_singleton in H1 ; subst. apply Id ; ms.
  + apply gmultiset_elem_of_singleton in H1 ; subst.
    eapply MP ; [apply Id ; apply gmultiset_elem_of_disj_union ; right ; apply gmultiset_elem_of_singleton ; auto | ].
    apply open_boxes_Diam_rule with χ.
    * apply gmultiset_elem_of_disj_union ; left ; apply gmultiset_elem_of_disj_union ; right ; 
      apply gmultiset_elem_of_singleton ; auto.
    * do 2 (rewrite open_boxes_add_f ; auto).
- apply open_boxes_K_rule ; auto.
- apply open_boxes_Diam_rule with ψ.
  + apply gmultiset_elem_of_disj_union ; right ; apply gmultiset_elem_of_singleton ; auto.
  + rewrite open_boxes_add_f ; auto.
Qed.

End Soundness.



Section Completeness.

(* Then we can show that if there is an axiomatic proof, then
   there exists (in Prop) a sequent proof. *)
  
Theorem G4CK_compl_CKH Γ φ : CKH_prv (fun γ => γ ∈ Γ) φ -> Γ ⊢ φ.
Proof.
enough (CKH_prv (fun γ => γ ∈ Γ) φ -> exists (P : Γ ⊢ φ), True).
{ intro D. apply H in D. destruct (Provable_dec (elements Γ) φ).
  + rewrite (proper_Provable _ (list_to_set_disj (elements Γ))) with (y:=φ) ; auto.
    rewrite <- elements_list_to_set_disj ; auto.
  + exfalso. destruct D as [D Vrai] ; auto. apply f.
    rewrite (proper_Provable _ Γ) with (y:=φ) ; auto. rewrite <- elements_list_to_set_disj ; auto. }
{ intro. remember (λ γ : form, γ ∈ Γ) as Γ'.
  revert Γ HeqΓ'. induction H ; intros ; subst.
  (* Id *)
  - assert (Γ0 ⊢CK A). exhibit H 0. apply generalised_axiom.
    exists H0 ; auto.
  (* Axiom *)
  - destruct H as [H | H] ; [ destruct H ; destruct H ; subst | contradiction].
    + assert (Γ0 ⊢CK (A0 → B → A0)). do 2 (apply ImpR). exch 0. apply generalised_axiom.
      exists H ; auto.
    + assert (Γ0 ⊢CK ((A0 → B → C) → (A0 → B) → A0 → C)). 
      { do 3 (apply ImpR). exch 0. apply weak_ImpL.
      * apply generalised_axiom.
      * exch 1 ; exch 0. apply weak_ImpL.
        -- exch 0 ; apply generalised_axiom.
        -- apply weak_ImpL ; apply generalised_axiom. }
      exists H ; auto.
    + assert (Γ0 ⊢CK (A0 → A0 ∨ B)). apply ImpR,OrR1 ; apply generalised_axiom.
      exists H ; auto.
    + assert (Γ0 ⊢CK (B → A0 ∨ B)). apply ImpR,OrR2 ; apply generalised_axiom.
      exists H ; auto.
    + assert (Γ0 ⊢CK ((A0 → C) → (B → C) → A0 ∨ B → C)).
      { do 3 (apply ImpR). apply OrL.
      * exch 1 ; exch 0. apply weak_ImpL ; apply generalised_axiom.
      * exch 0. apply weak_ImpL ; apply generalised_axiom. }
      exists H ; auto.
    + assert (Γ0 ⊢CK (A0 ∧ B → A0)). apply ImpR,AndL ; exch 0 ; apply generalised_axiom.
      exists H ; auto.
    + assert (Γ0 ⊢CK (A0 ∧ B → B)). apply ImpR,AndL ; apply generalised_axiom.
      exists H ; auto.
    + assert (Γ0 ⊢CK ((A0 → B) → (A0 → C) → A0 → B ∧ C)).
      { do 3 (apply ImpR). apply AndR.
      * exch 1 ; exch 0. apply weak_ImpL ; apply generalised_axiom.
      * exch 0. apply weak_ImpL ; apply generalised_axiom. }
      exists H ; auto.
    + assert (Γ0 ⊢CK (⊥ → A0)). apply ImpR,ExFalso. exists H ; auto.
    + assert (Γ0 ⊢CK (□ (A0 → B) → □ A0 → □ B)). do 2 (apply ImpR). apply BoxR. repeat rewrite open_boxes_add_t ; auto ; cbn.
      exch 0 ; apply weak_ImpL ; apply generalised_axiom.
      exists ; auto.
    + assert (Γ0 ⊢CK (□ (A0 → B) → ◊ A0 → ◊ B)). do 2 (apply ImpR). apply DiamL. repeat rewrite open_boxes_add_t ; auto ; cbn.
      exch 0 ; apply weak_ImpL ; apply generalised_axiom.
      exists H ; auto.
  (* MP *)
  - destruct (IHextCKH_prv2 Γ0) ; auto. destruct (IHextCKH_prv1 Γ0) ; auto.
    assert (Γ0 ⊢CK B).
    { apply additive_cut with A ; auto.
      apply additive_cut with (A → B) ; auto.
      + apply weakening ; auto.
      + apply weak_ImpL ; apply generalised_axiom. }
    exists H3 ; auto.
  (* Nec *)
  - destruct (IHextCKH_prv (⊗ ∅)) ; auto.
    + apply Extensionality_Ensembles ; split ; intros x Hx.
      * inversion Hx.
      * unfold Ensembles.In in Hx. apply elem_of_open_boxes in Hx as [ψ [H0 H1]] ; subst.
        inversion H1.
    + assert (Γ0 ⊢CK □ A). rewrite <- gmultiset_disj_union_right_id. apply generalised_weakeningL.
      apply BoxR ; auto.
      exists H1 ; auto. }
Qed.


End Completeness.
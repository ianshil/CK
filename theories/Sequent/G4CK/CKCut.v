
(** * Cut Admissibility *)
Require Import im_syntax syntax_facts CKOrder.
Require Import CKSequents CKSequentProps.
From Stdlib Require Import Program.Equality.


Local Hint Rewrite @elements_env_add : order.


(* From "A New Calculus for Intuitionistic Strong Löb Logic" *)
Theorem additive_cut Γ φ ψ :
  Γ ⊢ φ  -> Γ • φ ⊢ ψ ->
  Γ ⊢ ψ.
Proof.
remember (weight φ) as w. assert(Hw : weight φ ≤ w) by lia. clear Heqw.
revert φ Hw ψ Γ.
induction w; intros φ Hw; [pose (weight_pos φ); lia|].
intros ψ Γ.
remember (Γ, ψ) as pe.
replace Γ with pe.1 by now subst.
replace ψ with pe.2 by now subst. clear Heqpe Γ ψ. revert pe.
refine  (@well_founded_induction _ _ wf_pointed_env_ms_order _ _).
intros (Γ &ψ). simpl. intro IHW'. assert (IHW := fun Γ0 => fun ψ0 => IHW' (Γ0, ψ0)).
simpl in IHW. clear IHW'. intros HPφ HPψ.
Ltac otac Heq := subst; repeat rewrite env_replace in Heq by trivial; repeat rewrite env_add_remove by trivial; order_tac; rewrite Heq; order_tac.
destruct HPφ; simpl in Hw.
- now apply contraction.
- apply ExFalso.
- apply AndL_rev in HPψ. do 2 apply IHw in HPψ; trivial; try lia; apply weakening; assumption.
- apply AndL. apply IHW; auto with proof. otac Heq.
- apply OrL_rev in HPψ; apply (IHw φ); [lia| |]; tauto.
- apply OrL_rev in HPψ; apply (IHw ψ0); [lia| |]; tauto.
- apply OrL; apply IHW; auto with proof.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
  + otac Heq.
  + exch 0. eapply (OrL_rev _ φ ψ0). exch 0. exact HPψ.
- (* (V) *) (* hard:  *)
(* START *)
  remember (Γ • (φ → ψ0)) as Γ' eqn:HH.
  assert (Heq: Γ ≡ Γ' ∖ {[ φ → ψ0]}) by ms.
  assert(Hin : (φ → ψ0) ∈ Γ')by ms.
  rw Heq 0. destruct HPψ.
  + forward. auto with proof.
  + forward. auto with proof.
  + apply AndR.
     * rw (symmetry Heq) 0. apply IHW.
     -- unfold pointed_env_ms_order. otac Heq.
     -- now apply ImpR.
     -- peapply HPψ1.
     * rw (symmetry Heq) 0. apply IHW.
       -- otac Heq.
       -- apply ImpR. peapply HPφ.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * unfold pointed_env_ms_order. otac Heq.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * rewrite HH, env_add_remove. otac Heq.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * rewrite HH, env_add_remove. otac Heq.
    * rw (symmetry Heq) 0. apply ImpR, HPφ.
    * peapply HPψ.
  + forward. apply ImpR in HPφ.
       assert(Hin' : (φ0 ∨ ψ) ∈ ((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}))
            by (apply in_difference; [discriminate|ms]).
       assert(HPφ' : (((Γ0 • φ0 ∨ ψ) ∖ {[φ→ ψ0]}) ∖ {[φ0 ∨ ψ]} • φ0 ∨ ψ) ⊢ (φ → ψ0))
            by (rw (symmetry (difference_singleton _ (φ0 ∨ψ) Hin')) 0; peapply HPφ).
       assert (HP := (OrL_rev  _ φ0 ψ (φ → ψ0) HPφ')).
       apply OrL.
      * apply IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- otac Heq.
      -- apply weakening, ImpR,  HPφ.
      -- exch 0.  rewrite <- HH. exact HPψ.
  + case (decide ((Var p → φ0) = (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'.
         replace ((Γ0 • Var p • (#p → ψ0)) ∖ {[#p → ψ0]}) with (Γ0 • Var p) by ms.
         apply (IHw ψ0).
        -- lia.
        -- apply contraction. peapply HPφ.
        -- assumption.
      * intro Hneq. do 2 forward. exch 0. apply ImpLVar, IHW.
        -- repeat rewrite env_replace in Heq by trivial. otac Heq.
        -- apply imp_cut with (φ := Var p). exch 0. do 2 backward.
            rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + case (decide (((φ1 ∧ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'. rw (symmetry Heq) 0.
         apply (IHw (φ1 → φ2 → ψ0)).
        -- simpl in *. lia.
        -- apply ImpR, ImpR, AndL_rev, HPφ.
        -- peapply HPψ.
      * intro Hneq. forward. apply ImpLAnd, IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- apply ImpLAnd_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + case (decide (((φ1 ∨ φ2) → φ3)= (φ → ψ0))).
      * intro Heq'; dependent destruction Heq'. rw (symmetry Heq) 0. apply OrL_rev in HPφ.
         apply (IHw (φ1 → ψ0)).
        -- simpl in *. lia.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply ImpR, HPφ.
           ++ apply weakening, ImpR, HPφ.
        -- apply (IHw (φ2 → ψ0)).
           ++ simpl in *; lia.
           ++ apply weakening, ImpR, HPφ.
           ++ peapply HPψ.
      * intro Hneq. forward. apply ImpLOr, IHW.
        -- rewrite env_replace in Heq by trivial. otac Heq.
        -- apply ImpLOr_rev. backward. rw (symmetry Heq) 0. apply ImpR, HPφ.
        -- exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + case (decide (((φ1 → φ2) → φ3) = (φ → ψ0))).
     * intro Heq'. dependent destruction Heq'. rw (symmetry Heq) 0. apply (IHw ψ0).
      -- lia.
      -- apply (IHw(φ1 → φ2)).
        ++ lia.
        ++ apply (IHw (φ2 → ψ0)).
            ** simpl in *. lia.
            ** apply ImpR. eapply imp_cut, HPφ.
            ** peapply HPψ1.
        ++ exact HPφ.
    -- peapply HPψ2.
   *  (* (V-d) *)
       intro Hneq. forward. apply ImpLImp.
      -- apply ImpR, IHW.
        ++ otac Heq.
        ++ exch 0. apply contraction, ImpLImp_dup. backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0. apply ImpR_rev. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1.
                exact HPψ1.
      -- apply IHW.
        ++ otac Heq.
        ++ apply imp_cut with (φ1 → φ2). backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + case (decide ((□ φ1 → φ2) = (φ → ψ0))).
     * intro Heq'. dependent destruction Heq'. rw (symmetry Heq) 0.
        assert(Γ = Γ0) by ms. subst Γ0. clear Hin.
        apply (IHw(ψ0)) ; auto.
      -- lia.
      -- apply (IHw (□ φ1)) ; auto.
        ++ lia.
        ++ apply BoxR ; auto. 
    *  (* (V-g ) *)
       intro Hneq. forward. apply ImpBox.
       -- erewrite proper_Provable ; [ exact HPψ1 | rewrite open_boxes_remove_f ; cbn ; auto | auto].
       -- apply IHW.
        ++ otac Heq.
        ++ apply ImpLBox_prev with φ1. backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 0.  rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + case (decide ((◊ φ1 → φ2) = (φ → ψ0))).
     * intro Heq'. dependent destruction Heq'. rw (symmetry Heq) 0.
        assert(Γ = (Γ0 • (◊ χ))) by ms. subst Γ. clear Hin.
        apply (IHw(ψ0)) ; auto.
      -- lia.
      -- apply (IHw (◊ φ1)) ; auto.
        ++ lia.
        ++ apply DiamL ; auto. 
    *  (* (V-g ) *)
       intro Hneq. forward ; forward ; exch 0. apply ImpDiam.
       -- erewrite proper_Provable ; [ exact HPψ1 | rewrite open_boxes_remove_f ; cbn ; auto | auto].
       -- apply IHW.
        ++ otac Heq.
        ++ apply ImpLDiam_prev with φ1. exch 0 ; backward ; backward. rw (symmetry Heq) 0.
                apply ImpR, HPφ.
        ++ exch 1 ; exch 0. backward. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + subst. rw (symmetry Heq) 0. rewrite open_boxes_add_f in HPψ ; auto.
      apply BoxR ; auto.
  + subst. forward. apply DiamL. 
    erewrite proper_Provable ; [ exact HPψ | rewrite open_boxes_remove_f ; cbn ; auto | auto].
- apply ImpLVar. eapply IHW; eauto.
  + otac Heq.
  + exch 0. apply (imp_cut (Var p)). exch 0; exact HPψ.
- apply ImpLAnd. eapply IHW; eauto.
  + otac Heq.
  + exch 0. apply ImpLAnd_rev. exch 0. exact HPψ.
- apply ImpLOr. eapply IHW; eauto.
  + otac Heq.
  + exch 0. exch 1. apply ImpLOr_rev. exch 0. exact HPψ.
- apply ImpLImp; [assumption|].
  apply IHW.
  + otac Heq.
  + assumption.
  + exch 0. eapply ImpLImp_prev. exch 0. exact HPψ.
- apply ImpBox. trivial. apply IHW.
  * otac Heq.
  * assumption.
  * exch 0. eapply ImpLBox_prev. exch 0. exact HPψ.
(* (VII 1/2)*)
- apply ImpDiam ; auto. apply IHW.
  * otac Heq.
  * assumption.
  * exch 0 ; exch 1. eapply ImpLDiam_prev. exch 1 ; exch 0. exact HPψ.
(* (VIII) *)
- remember (Γ • □ φ) as Γ' eqn:HH.
  assert (Heq: Γ ≡ Γ' ∖ {[ □ φ ]}) by ms.
  assert(Hin : (□ φ) ∈ Γ')by ms.
  rw Heq 0. dependent destruction HPψ.
  + forward. auto with proof.
  + forward. auto with proof.
  + apply AndR.
     * apply IHW.
     -- otac Heq.
     -- rw (symmetry Heq) 0. now apply BoxR.
     -- peapply HPψ1.
     * peapply (IHW Γ).
       -- otac Heq.
       -- apply BoxR ; auto.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * otac Heq.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply BoxR, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * otac Heq.
    * rw (symmetry Heq) 0. apply BoxR, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * otac Heq.
    * rw (symmetry Heq) 0. apply BoxR, HPφ.
    * peapply HPψ.
  + forward. apply BoxR in HPφ.
       assert(Hin' : (φ0 ∨ ψ) ∈ ((Γ0 • φ0 ∨ ψ) ∖ {[□ φ]}))
            by (apply in_difference; [discriminate|ms]).
       assert(HPφ' : (((Γ0 • φ0 ∨ ψ) ∖ {[□ φ]}) ∖ {[φ0 ∨ ψ]} • φ0 ∨ ψ) ⊢ □ φ).
       { rw (symmetry (difference_singleton _ (φ0 ∨ ψ) Hin')) 0.
         rw (symmetry Heq) 0.
         exact HPφ. }
       assert (HP := (OrL_rev  _ φ0 ψ (□φ) HPφ')).
       apply OrL.
      * apply IHW.
        -- otac Heq.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- otac Heq.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- otac Heq.
      -- apply weakening, BoxR, HPφ.
      -- peapply HPψ.
  + do 2 forward. exch 0. apply ImpLVar, IHW.
      * otac Heq.
      * apply imp_cut with (φ := Var p). exch 0. do 2 backward.
         rewrite HH. apply BoxR in HPφ. peapply HPφ.
      * exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + forward. apply ImpLAnd, IHW.
      * otac Heq.
      * apply BoxR in HPφ. apply ImpLAnd_rev. backward. rewrite HH. peapply HPφ.
      * exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + forward. apply ImpLOr, IHW.
      * otac Heq.
      * apply BoxR in HPφ. apply ImpLOr_rev. backward. rewrite HH. peapply HPφ.
      * exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + forward. apply ImpLImp.
      -- apply ImpR, IHW.
        ++ otac Heq.
        ++ exch 0. apply contraction, ImpLImp_dup. backward. rw (symmetry Heq) 0.
                apply BoxR, HPφ.
        ++ exch 0. apply ImpR_rev. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1.
                exact HPψ1.
      -- apply IHW.
        ++ otac Heq.
        ++ apply imp_cut with (φ1 → φ2). backward. rw (symmetry Heq) 0.
                apply BoxR, HPφ.
        ++ exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* (VIII-b) *)
      forward. apply ImpBox.
     * (* π0 *)
       apply (IHw φ) ; auto.
      -- lia.
      -- peapply HPφ. rewrite Heq. rewrite open_boxes_remove_t ; auto ; cbn.
         rewrite open_boxes_remove_t ; auto ; cbn. rewrite open_boxes_add_f ; auto.
      -- peapply HPψ1. rewrite open_boxes_remove_t ; auto ; cbn.
         rewrite <- env_replace. ms. unfold open_boxes.
         apply elem_of_list_to_set_disj. apply elem_of_list_In.
         apply in_map_iff. exists (□ φ) ; cbn ; split ; auto.
         apply filter_In ; cbn ; split ; auto.
         apply elem_of_list_In. apply gmultiset_elem_of_elements ; auto.
     * apply IHW.
      -- otac Heq.
      -- apply weakening. apply BoxR.
         peapply HPφ. rewrite Heq. rewrite open_boxes_remove_t ; auto ; cbn.
         rewrite open_boxes_remove_t ; auto ; cbn. rewrite open_boxes_add_f ; auto.
      -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* (VIII-d) *)
      forward ; forward ; exch 0. apply ImpDiam.
     * (* π0 *)
       apply (IHw φ) ; auto.
      -- lia.
      -- apply weakening. peapply HPφ. rewrite Heq. rewrite open_boxes_remove_t ; auto ; cbn.
         rewrite open_boxes_remove_t ; auto ; cbn. rewrite open_boxes_add_f ; auto.
         rewrite open_boxes_add_f ; auto.
      -- exch 0. peapply HPψ1. rewrite open_boxes_remove_t ; auto ; cbn.
         rewrite <- env_replace. ms.
         unfold open_boxes.
         apply elem_of_list_to_set_disj. apply elem_of_list_In.
         apply in_map_iff. exists (□ φ) ; cbn ; split ; auto.
         apply filter_In ; cbn ; split ; auto.
         apply elem_of_list_In. apply gmultiset_elem_of_elements ; auto.
     * apply IHW.
      -- otac Heq.
      -- do 2 apply weakening. apply BoxR.
         peapply HPφ. rewrite Heq. rewrite open_boxes_remove_t ; auto ; cbn.
         rewrite open_boxes_remove_t ; auto ; cbn. rewrite open_boxes_add_f ; auto.
         rewrite open_boxes_add_f ; auto.
      -- exch 1 ; exch 0. backward. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* (VIII-c) *)
      subst. rw (symmetry Heq) 0. rewrite open_boxes_add_t in HPψ ; auto. simpl in HPψ.
      apply BoxR. apply (IHw φ) ; auto. lia.
  + (* (VIII-e) *)
      forward. apply DiamL. apply (IHw φ) ; auto.
      * lia.
      * apply weakening. peapply HPφ. rewrite Heq. rewrite open_boxes_remove_t ; auto ; cbn.
        rewrite open_boxes_remove_t ; auto ; cbn. rewrite open_boxes_add_f ; auto.
      * exch 0. peapply HPψ. rewrite open_boxes_remove_t ; auto ; cbn.
        rewrite <- env_replace. ms.
        apply elem_of_list_to_set_disj. apply elem_of_list_In.
        apply in_map_iff. exists (□ φ) ; cbn ; split ; auto.
        apply filter_In ; cbn ; split ; auto.
        apply elem_of_list_In. apply gmultiset_elem_of_elements ; auto.
(* IX *)
- remember (Γ • ◊ ψ0 • ◊ φ) as Γ' eqn:HH.
  assert (Heq: (Γ • ◊ ψ0) ≡ Γ' ∖ {[ ◊ φ ]}) by ms.
  assert(Hin : (◊ φ) ∈ Γ')by ms.
  rw Heq 0. dependent destruction HPψ.
  + forward. auto with proof.
  + forward. auto with proof.
  + apply AndR.
     * apply IHW.
     -- otac Heq.
     -- rw (symmetry Heq) 0. now apply DiamL.
     -- peapply HPψ1.
     * peapply (IHW (Γ • (◊ ψ0))).
       -- otac Heq.
       -- apply DiamL ; auto.
       -- peapply HPψ2.
  + forward. apply AndL. apply IHW.
     * repeat rewrite env_replace in Heq by trivial.
       assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} • φ0 ∧ ψ) ∖ {[ ◊ ψ0 ]})) by ms.
       otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
     * apply AndL_rev. backward. rw (symmetry Heq) 0. apply DiamL, HPφ.
     * backward. peapply HPψ.
  + apply OrR1, IHW.
    * otac Heq.
    * rw (symmetry Heq) 0. apply DiamL, HPφ.
    * peapply HPψ.
  + apply OrR2, IHW.
    * otac Heq.
    * rw (symmetry Heq) 0. apply DiamL, HPφ.
    * peapply HPψ.
  + forward. apply DiamL in HPφ.
       assert(Hin' : (φ0 ∨ ψ) ∈ ((Γ0 • φ0 ∨ ψ) ∖ {[◊ φ]}))
            by (apply in_difference; [discriminate|ms]).
       assert(HPφ' : (((Γ0 • φ0 ∨ ψ) ∖ {[◊ φ]}) ∖ {[φ0 ∨ ψ]} • φ0 ∨ ψ) ⊢ ◊ φ).
       { rw (symmetry (difference_singleton _ (φ0 ∨ ψ) Hin')) 0.
         rw (symmetry Heq) 0.
         exact HPφ. }
       assert (HP := (OrL_rev  _ φ0 ψ (◊φ) HPφ')).
       apply OrL.
      * apply IHW.
        -- repeat rewrite env_replace in Heq by trivial.
           assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} • φ0 ∨ ψ) ∖ {[ ◊ ψ0 ]})) by ms.
           otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
        -- peapply HP.1.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ1.
      * apply IHW.
        -- repeat rewrite env_replace in Heq by trivial.
           assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} • φ0 ∨ ψ) ∖ {[ ◊ ψ0 ]})) by ms.
           otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
        -- peapply HP.2.
        -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + rw (symmetry Heq) 0. apply ImpR, IHW.
      -- otac Heq.
      -- apply weakening, DiamL, HPφ.
      -- peapply HPψ.
  + do 2 forward. exch 0. apply ImpLVar, IHW.
      * repeat rewrite env_replace in Heq by trivial.
        assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} • # p • (# p → φ0)) ∖ {[ ◊ ψ0 ]})) by ms.
        otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
      * apply imp_cut with (φ := Var p). exch 0. do 2 backward.
         rewrite HH. apply DiamL in HPφ. peapply HPφ.
      * exch 0; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. exact HPψ.
  + forward. apply ImpLAnd, IHW.
      * repeat rewrite env_replace in Heq by trivial.
        assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} •(φ1 ∧ φ2 → φ3)) ∖ {[ ◊ ψ0 ]})) by ms.
        otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
      * apply DiamL in HPφ. apply ImpLAnd_rev. backward. rewrite HH. peapply HPφ.
      * exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ.
  + forward. apply ImpLOr, IHW.
      * repeat rewrite env_replace in Heq by trivial.
        assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} •(φ1 ∨ φ2 → φ3)) ∖ {[ ◊ ψ0 ]})) by ms.
        otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
      * apply DiamL in HPφ. apply ImpLOr_rev. backward. rewrite HH. peapply HPφ.
      * exch 0. exch 1. rw (symmetry (difference_singleton _ _ Hin0)) 2. exact HPψ.
  + forward. apply ImpLImp.
      -- apply ImpR, IHW.
        ++ repeat rewrite env_replace in Heq by trivial.
           assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} •((φ1 → φ2) → φ3)) ∖ {[ ◊ ψ0 ]})) by ms.
           otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
        ++ exch 0. apply contraction, ImpLImp_dup. backward. rw (symmetry Heq) 0.
                apply DiamL, HPφ.
        ++ exch 0. apply ImpR_rev. exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1.
                exact HPψ1.
      -- apply IHW.
        ++ repeat rewrite env_replace in Heq by trivial.
           assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} •((φ1 → φ2) → φ3)) ∖ {[ ◊ ψ0 ]})) by ms.
           otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
        ++ apply imp_cut with (φ1 → φ2). backward. rw (symmetry Heq) 0.
                apply DiamL, HPφ.
        ++ exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* (VIII-b) *)
      forward. apply ImpBox.
     * peapply HPψ1. apply open_boxes_remove_f ; auto.
     * apply IHW.
      -- repeat rewrite env_replace in Heq by trivial.
         assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} •(□ φ1 → φ2)) ∖ {[ ◊ ψ0 ]})) by ms.
         otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
      -- apply weakening.
         assert (◊ ψ0 ∈ (Γ0 ∖ {[◊ φ]})).
         { enough (◊ ψ0 ∈ ((Γ0 • (□ φ1 → φ2)) ∖ {[◊ φ]})).
            - rewrite union_difference_L in H ; auto. ms.
            - rewrite <- Heq. ms. }
         exhibit H 0. apply DiamL.
         do 2 (erewrite proper_Provable ; [ | (rewrite open_boxes_remove_f ; cbn ; auto) | auto]).
         peapply HPφ. enough ((⊗ (Γ • ◊ ψ0)) ≡ (⊗ ((Γ0 • (□ φ1 → φ2)) ∖ {[◊ φ]}))).
         ++ repeat rewrite open_boxes_disj_union in H0. rewrite open_boxes_singleton_f in H0 ; auto.
            rewrite open_boxes_remove_f in H0 ; auto.
            rewrite open_boxes_disj_union in H0. rewrite open_boxes_singleton_f in H0 ; auto. ms.
         ++ rewrite Heq. auto.
      -- exch 0. rw (symmetry (difference_singleton _ _ Hin0)) 1. exact HPψ2.
  + (* (VIII-d) *) 
      forward. case (decide (◊ χ = ◊ φ)).
      * intro Heq' ; dependent destruction Heq'.
        assert (◊ ψ0 ∈ ((Γ0 • ◊ φ) ∖ {[◊ φ]})).
        { enough (◊ ψ0 ∈ ((Γ0 • ◊ φ • (◊ φ1 → φ2)) ∖ {[◊ φ]})).
          - rewrite union_difference_L in H ; auto. ms.
          - rewrite <- Heq. ms. }
        exhibit H 1. apply ImpDiam.
        -- (* π0 *)
          apply (IHw φ) ; auto.
          ++ lia.
          ++ do 2 (erewrite proper_Provable ; [ | (rewrite open_boxes_remove_f ; cbn ; auto) | auto]).
            rewrite open_boxes_disj_union. rewrite open_boxes_singleton_f ; auto.
            peapply HPφ.
            enough ((⊗ Γ0) ≡ (⊗ Γ)).
            ** rewrite H0. ms.
            ** enough ((⊗ (Γ • ◊ ψ0)) ≡ (⊗ (Γ0 • ◊ φ • (◊ φ1 → φ2)) ∖ {[◊ φ]})).
               --- rewrite open_boxes_remove_f in H0 ; auto. repeat (rewrite open_boxes_add_f in H0 ; auto).
               --- rewrite Heq ; auto.
          ++ do 2 (erewrite proper_Provable ; [ | (rewrite open_boxes_remove_f ; cbn ; auto) | auto]).
             rewrite open_boxes_add_f ; auto. exch 0 ; apply weakening ; auto.
      -- apply IHW.
          ++ repeat rewrite env_replace in Heq by trivial. repeat rewrite env_add_remove by trivial.
             assert ((Γ0 ∖ {[◊ ψ0]} • ◊ ψ0) ≡ Γ0). rewrite <- difference_singleton ; auto. ms.
             assert ((Γ0 ∖ {[◊ ψ0]} • ◊ ψ0 • φ2) ≡ (Γ0 • φ2)) by ms.
             repeat rewrite env_add_remove in Heq by trivial.
             assert (Heq': Γ ≡ (((Γ0 • ◊ φ) ∖ {[◊ φ]} • (◊ φ1 → φ2))) ∖ {[ ◊ ψ0 ]}) by ms.
             otac Heq'. rewrite <- elements_elem_of. rewrite env_add_remove by trivial.
             assert ((elements (Γ0 ∖ {[◊ ψ0]}) • (◊ φ1 → φ2) • ◊ ψ0) ≡ₚ elements (((Γ0 ∖ {[◊ ψ0]}) • ◊ ψ0) • (◊ φ1 → φ2))).
             { pose (gmultiset_elements_disj_union (Γ0 ∖ {[◊ ψ0]} • ◊ ψ0 ) ({[+ ◊ φ1 → φ2 +]})). rewrite p.
               rewrite <- difference_singleton ; [ | ms].
               pose (gmultiset_elements_disj_union ((Γ0 ∖ {[◊ ψ0]}) • (◊ φ1 → φ2)) ({[+ ◊ ψ0 +]})).
               rewrite <- elements_env_add. rewrite <- elements_env_add. rewrite p0.
               pose (gmultiset_elements_disj_union (Γ0 ∖ {[◊ ψ0]}) ({[+ ◊ φ1 → φ2 +]})). rewrite p1.
               eapply perm_trans. rewrite <- app_assoc. apply Permutation_app_head,Permutation_app_comm. 
               rewrite app_assoc.
               pose (gmultiset_elements_disj_union (Γ0 ∖ {[◊ ψ0]}) ({[+ ◊ ψ0 +]})). rewrite <- p2.
               rewrite <- difference_singleton ; ms. }
             epose (@env_order_equiv_right_compat (elements Γ0 • φ2) _ _ H2). apply e.
             rewrite <- difference_singleton ; auto. order_tac.
             all: ms.
          ++ apply weakening. apply DiamL.
             peapply HPφ. repeat (rewrite open_boxes_remove_f ; auto).
             rewrite open_boxes_add_f ; auto. enough ((⊗ Γ0) ≡ (⊗ Γ)).
             ** rewrite H0. ms.
             ** enough ((⊗ (Γ • ◊ ψ0)) ≡ (⊗ (Γ0 • ◊ φ • (◊ φ1 → φ2)) ∖ {[◊ φ]})).
                --- rewrite open_boxes_remove_f in H0 ; auto. repeat (rewrite open_boxes_add_f in H0 ; auto).
                --- rewrite Heq ; auto.
          ++ rw (symmetry (difference_singleton _ _ H)) 2. exch 0.
             assert (◊φ ∈ (Γ0 • ◊ φ)) by ms. rw (symmetry (difference_singleton _ _ H0)) 1.
             exact HPψ2.
      * intro Hneq'. forward ; exch 0 ; apply ImpDiam.
      -- (* π0 *)
         erewrite proper_Provable ; [ | (rewrite open_boxes_remove_f ; cbn ; auto) | auto] ; auto.
      -- apply IHW.
          ++ repeat rewrite env_replace in Heq by trivial.
             assert (Heq': Γ ≡ ((Γ0 ∖ {[◊ φ]} • ◊ χ • (◊ φ1 → φ2)) ∖ {[ ◊ ψ0 ]})) by ms.
             otac Heq'. rewrite <- elements_elem_of. order_tac. rewrite <- Heq ; ms.
          ++ apply weakening.
             case (decide (◊χ = ◊ψ0)).
             ** intro Heq' ; dependent destruction Heq'.
                apply DiamL.
                peapply HPφ. rewrite open_boxes_remove_f ; auto.
                enough ((⊗ Γ0) ≡ (⊗ Γ)).
                --- rewrite H. ms.
                --- enough ((⊗ (Γ • ◊ ψ0)) ≡ (⊗ (Γ0 • ◊ ψ0 • (◊ φ1 → φ2)) ∖ {[◊ φ]})).
                    +++ rewrite open_boxes_remove_f in H ; auto. repeat (rewrite open_boxes_add_f in H ; auto).
                    +++ rewrite Heq ; auto.
              ** intro Hneq''. apply weakening.
                 assert (◊ψ0 ∈ (Γ0 ∖ {[◊ φ]})).
                 { enough (◊ψ0 ∈ (Γ0 • ◊ χ • (◊ φ1 → φ2)) ∖ {[◊ φ]}).
                   - repeat (rewrite union_difference_L in H ; auto).
                     apply gmultiset_elem_of_disj_union in H. destruct H.
                     + apply gmultiset_elem_of_disj_union in H. destruct H ; auto.
                       exfalso. ms.
                     + exfalso ; ms.
                   - rewrite <- Heq ; ms. }
                 exhibit H 0. apply DiamL.
                 do 2 (erewrite proper_Provable ; [ | rewrite open_boxes_remove_f ; cbn ; auto | auto]).
                 erewrite proper_Provable ; [ exact HPφ | | auto].
                 enough ((⊗ Γ0) ≡ (⊗ Γ)).
                  --- rewrite H0. ms.
                  --- enough ((⊗ (Γ • ◊ ψ0)) ≡ (⊗ (Γ0 • ◊ χ • (◊ φ1 → φ2)) ∖ {[◊ φ]})).
                      +++ rewrite open_boxes_remove_f in H0 ; auto. repeat (rewrite open_boxes_add_f in H0 ; auto).
                      +++ rewrite Heq ; auto.
          ++ exch 0 ; exch 1. rw (symmetry (difference_singleton _ _ Hin1)) 2. auto.
  + (* (VIII-c) *)
      subst. rw (symmetry Heq) 0. repeat (rewrite open_boxes_add_f in HPψ ; auto).
      apply weakening ; apply BoxR ; auto.
  + (* (VIII-e) *)
      case (decide (◊ ψ = ◊ φ)).
      * intro Heq' ; dependent destruction Heq'.
        rewrite env_add_remove.
        assert (◊ψ0 ∈ Γ0).
        { enough (◊ψ0 ∈ ((Γ0 • ◊ φ) ∖ {[◊ φ]})).
          - rewrite env_add_remove in H ; auto.
          - rewrite <- Heq ; ms. }
        exhibit H 0. apply DiamL.
        erewrite proper_Provable ; [ | rewrite open_boxes_remove_f ; cbn ; auto | auto].
        apply (IHw φ) ; auto.
        -- lia.
        -- peapply HPφ.
           enough ((⊗ Γ0) ≡ (⊗ Γ)).
            ++ rewrite H0. ms.
            ++ enough ((⊗ (Γ • ◊ ψ0)) ≡ (⊗ (Γ0 • ◊ φ) ∖ {[◊ φ]})).
              ** rewrite open_boxes_remove_f in H0 ; auto. repeat (rewrite open_boxes_add_f in H0 ; auto).
              ** rewrite Heq ; auto.
        -- exch 0 ; apply weakening ; auto.
      * intro Hneq'. forward. apply DiamL.
        erewrite proper_Provable ; [ | rewrite open_boxes_remove_f ; cbn ; auto | auto].
        auto.
Qed.

(* Multiplicative cut rule *)
Theorem cut Γ Γ' φ ψ :
  Γ ⊢ φ  -> Γ' • φ ⊢ ψ ->
  Γ ⊎ Γ' ⊢ ψ.
Proof.
intros π1 π2. apply additive_cut with φ.
- apply generalised_weakeningR, π1.
- replace (Γ ⊎ Γ' • φ) with (Γ ⊎ (Γ' • φ)) by ms. apply generalised_weakeningL, π2.
Qed.
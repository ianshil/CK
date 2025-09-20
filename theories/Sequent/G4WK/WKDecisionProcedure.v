(** * Decision Procedure *)
Require Import WKSequents WKSequentProps WKOrder.
From Stdlib Require Import Program.Equality.

(**
  This file implements a decision procedure for CK. There are two versions, with the same proof.
  `Proof_tree_dec` computes a proof tree for the sequent, while `Provable_dec` only decides the provability
  of the sequent.
*)

Global Instance proper_rm : Proper ((=) ==> (≡ₚ) ==> (≡ₚ)) rm.
Proof.
intros x y Heq. subst y.
induction 1; simpl; trivial.
- case form_eq_dec; auto with *.
- case form_eq_dec; auto with * ;
   case form_eq_dec; auto with *. intros. apply Permutation_swap.
- now rewrite IHPermutation1.
Qed.

Definition exists_dec {A : Type} (P : A -> bool) (l : list A): {x & (In x l) /\ P x} + {forall x, In x l -> ¬ P x}.
Proof.
induction l as [|x l].
- right. tauto.
- case_eq (P x); intro Heq.
  + left. exists x. split; auto with *.
  + destruct IHl as [(y & Hin & Hy)|Hf].
    * left. exists y. split; auto with *.
    * right. simpl. intros z [Hz|Hz]; subst; try rewrite Heq; auto with *.
Defined.

Ltac l_tac := repeat rewrite list_to_set_disj_open_boxes;
    rewrite (proper_Provable _ _ (list_to_set_disj_env_add _ _) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _))) _ _ eq_refl)
|| rewrite (proper_Provable _ _ (equiv_disj_union_compat_r(equiv_disj_union_compat_r (equiv_disj_union_compat_r (list_to_set_disj_env_add _ _)))) _ _ eq_refl).


Ltac eqt := match goal with | H : (_ • ?φ) = list_to_set_disj ?Γ |- _ =>
  let Heq := fresh "Heq" in assert(Heq := H);
  assert(Hinφ : φ ∈ Γ) by (apply elem_of_list_to_set_disj; setoid_rewrite <- H; ms);
  apply env_equiv_eq, env_add_inv', symmetry in Heq; rewrite list_to_set_disj_rm in Heq end.

(** The function [Provable_dec] decides whether a sequent is provable.
   The proof is essentially the same as the definition of [Proof_tree_dec].
   *)

Proposition Provable_dec  Γ φ :
  (list_to_set_disj Γ ⊢ φ) + (list_to_set_disj  Γ ⊢ φ -> False).
(* Proposition Provable_dec  Γ φ :
  (exists _ : list_to_set_disj Γ ⊢ φ, True) + (forall H : list_to_set_disj  Γ ⊢ φ, False). *)
Proof.
remember (Γ, φ) as pe.
replace Γ with pe.1 by now inversion Heqpe.
replace φ with pe.2 by now inversion Heqpe. clear Heqpe Γ φ.
revert pe.
refine  (@well_founded_induction _ _ wf_pointed_order _ _).
intros (Γ& φ) Hind; simpl.
assert(Hind' := λ Γ' φ', Hind(Γ', φ')). simpl in Hind'. clear Hind. rename Hind' into Hind.

case (decide (⊥ ∈ Γ)); intro Hbot.
{ left. apply elem_of_list_to_set_disj in Hbot. exhibit Hbot 0. apply ExFalso. }
assert(HAndR : {φ1 & {φ2 & φ = Some (And φ1 φ2)}} + {∀ φ1 φ2, φ ≠ Some (And φ1 φ2)}) by (destruct φ as [ φ | ] ; [ destruct φ ; eauto | eauto ]).
assert(Hvar : {p & φ = (Some (Var p)) & Var p ∈ Γ} + {∀ p, φ = (Some (Var p)) -> Var p ∈ Γ -> False}).
{ destruct φ as [ φ | ] ; [ destruct φ | right ; intros ; discriminate ].
  2-7: right; auto with *.
  case (decide (Var n ∈ Γ)); intro Hin.
  - left. exists n; trivial.
  - right; auto with *. }
destruct Hvar as [[p Heq Hp]|Hvar].
{ subst. left. apply elem_of_list_to_set_disj in Hp. exhibit Hp 0. apply Atom. }

assert(HAndL : {ψ1 & {ψ2 & (And ψ1 ψ2) ∈ Γ}} + {∀ ψ1 ψ2, (And ψ1 ψ2) ∈ Γ -> False}). {
  pose (fA := (fun θ => match θ with |And _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 3: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
}
destruct HAndL as [(ψ1 & ψ2 & Hin)|HAndL].
{ destruct (Hind (ψ1 :: ψ2 :: rm (And ψ1 ψ2) Γ) φ) as [Hp' | Hf]. destruct φ ; order_tac.
  - left. apply elem_of_list_to_set_disj in Hin.
    exhibit Hin 0.
    rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_rm Γ _)) _ _ eq_refl).
    apply AndL. peapply Hp'.
 - right. intro Hf'. apply Hf.
   rw (symmetry (list_to_set_disj_env_add (ψ2 :: rm (And ψ1 ψ2) Γ) ψ1)) 0.
   rw (symmetry (list_to_set_disj_env_add (rm (And ψ1 ψ2) Γ) ψ2)) 1.
   exch 0. apply AndL_rev.
   rw (symmetry (list_to_set_disj_rm Γ(And ψ1 ψ2))) 1.
   apply elem_of_list_to_set_disj in Hin.
   pose (difference_singleton (list_to_set_disj Γ) (And ψ1 ψ2)).
   peapply Hf'.
}
assert(HImpR : {φ1 & {φ2 & φ = Some (φ1 → φ2)}} + {∀ φ1 φ2, φ ≠ Some (φ1 → φ2)}) by (destruct φ as [ φ | ] ; [ destruct φ ; eauto | eauto ]).
destruct HImpR as [(φ1 & φ2 & Heq) | HImpR].
{ subst.
  destruct (Hind (φ1 :: Γ) (Some φ2)) as [Hp1| H1]. order_tac.
  - left. apply ImpR. peapply Hp1.
  - right. intro Hf. apply H1. apply ImpR_rev in Hf. peapply Hf.
}
assert(HImpLVar : {p & {ψ & Var p ∈ Γ /\ (Imp (Var p) ψ) ∈ Γ}} +
                                 {∀ p ψ, Var p ∈ Γ -> (Imp (Var p) ψ) ∈ Γ -> False}). {
  pose (fIp :=λ p θ, match θ with | Imp (Var q) _ => if decide (p = q) then true else false | _ => false end).
  pose (fp:= (fun θ => match θ with |Var p => if (exists_dec (fIp p) Γ) then true else false | _ => false end)).
  destruct (exists_dec fp Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fp. destruct θ. 2-7: auto with *.
    case exists_dec as [(ψ &Hinψ & Hψ)|] in Hθ; [|auto with *].
    unfold fIp in Hψ. destruct ψ.  1-4, 6-7: auto with *.
    destruct ψ1. 2-7: auto with *. case decide in Hψ; [|auto with *].
    subst. apply elem_of_list_In in Hinψ, Hin.
    do 2 eexists. split; eauto.
  - right. intros p ψ Hp Hψ. rewrite elem_of_list_In in Hp, Hψ. apply Hf in Hp. subst fp fIp.
    simpl in Hp. case exists_dec as [|Hf'] in Hp. auto with *.
    apply (Hf' _ Hψ). rewrite decide_True; trivial. auto with *.
}
destruct HImpLVar as [[p [ψ [Hinp Hinψ]]]|HImpLVar].
{ apply elem_of_list_to_set_disj in Hinp.
  apply elem_of_list_to_set_disj in Hinψ.
  assert(Hinp' : Var p ∈ (list_to_set_disj Γ ∖ {[Imp (# p) ψ]} : env))
    by (apply in_difference; [discriminate| assumption]).
  destruct (Hind (ψ :: rm (Imp (Var p) ψ) Γ) φ) as [Hp|Hf]. destruct φ ; order_tac.
  - left. exhibit Hinψ 0.
     exhibit Hinp' 1. apply ImpLVar.
     rw (symmetry (difference_singleton (list_to_set_disj Γ ∖ {[Imp (Var p) ψ]}) (Var p) Hinp')) 1.
     rw (list_to_set_disj_rm Γ(Imp (Var p) ψ)) 1. l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (rm (Imp (Var p) ψ) Γ) ψ)) 0.
     rw (symmetry (list_to_set_disj_rm Γ(Imp (Var p) ψ))) 1.
     exhibit Hinp' 1. apply ImpLVar_rev.
     rw (symmetry (difference_singleton _ _ Hinp')) 1.
     rw (symmetry (difference_singleton _ _ Hinψ)) 0.
     exact Hf'.
}
assert(HImpLAnd : {φ1 & {φ2 & {φ3 &  (Imp (And φ1 φ2) φ3) ∈ Γ}}} +
                                 {∀ φ1 φ2 φ3, (Imp (And φ1 φ2) φ3) ∈ Γ -> False}). {
    pose (fII := (fun θ => match θ with |Imp (And _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left.  subst fII. destruct θ. 1-4, 6,7: auto with *.
      destruct θ1. 1-2,4-7: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
}
destruct HImpLAnd as [(φ1&φ2&φ3&Hin)|HImpLAnd].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (Imp φ1 (Imp φ2 φ3) :: rm (Imp (And φ1 φ2) φ3) Γ) φ) as [Hp|Hf]. destruct φ ; order_tac.
  - left. exhibit Hin 0. apply ImpLAnd.
     rw (list_to_set_disj_rm Γ(Imp (And φ1 φ2) φ3)) 1. l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add (rm (Imp (And φ1 φ2) φ3) Γ) (Imp φ1 (Imp φ2 φ3)))) 0.
     rw (symmetry (list_to_set_disj_rm Γ(Imp (And φ1 φ2) φ3))) 1.
     apply ImpLAnd_rev.
     rw (symmetry (difference_singleton _ _ Hin)) 0. exact Hf'.
}
assert(HImpLOr : {φ1 & {φ2 & {φ3 &  (Imp (Or φ1 φ2) φ3) ∈ Γ}}} +
                                 {∀ φ1 φ2 φ3, (Imp (Or φ1 φ2) φ3) ∈ Γ -> False}). {
    pose (fII := (fun θ => match θ with |Imp (Or _ _) _ => true | _ => false end)).
   destruct (exists_dec fII Γ) as [(θ & Hin & Hθ) | Hf].
    - left. subst fII. destruct θ. 1-4, 6-7: auto with *.
      destruct θ1. 1-3, 5-7: auto with *. do 3 eexists; apply elem_of_list_In; eauto.
    - right. intros ψ1 ψ2 ψ3 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fII. simpl in Hψ. tauto.
}
destruct HImpLOr as [(φ1&φ2&φ3&Hin)|HImpLOr].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (Imp φ2 φ3 :: Imp φ1 φ3 :: rm (Imp (Or φ1 φ2) φ3) Γ) φ) as [Hp|Hf]. destruct φ ; order_tac.
  - left. exhibit Hin 0. apply ImpLOr.
     rw (list_to_set_disj_rm Γ(Imp (Or φ1 φ2) φ3)) 2. do 2 l_tac. exact Hp.
  - right. intro Hf'. apply Hf.
     rw (symmetry (list_to_set_disj_env_add ( Imp φ1 φ3 :: rm (Imp (Or φ1 φ2) φ3) Γ) (Imp φ2 φ3))) 0.
     rw (symmetry (list_to_set_disj_env_add (rm (Imp (Or φ1 φ2) φ3) Γ) (Imp φ1 φ3))) 1.
     rw (symmetry (list_to_set_disj_rm Γ(Imp (Or φ1 φ2) φ3))) 2.
     apply ImpLOr_rev.
     rw (symmetry (difference_singleton _ _ Hin)) 0. exact Hf'.
}
assert(HOrL : {ψ1 & {ψ2 & (Or ψ1 ψ2) ∈ Γ}} + {∀ ψ1 ψ2, (Or ψ1 ψ2) ∈ Γ -> False}). {
  pose (fA := (fun θ => match θ with |Or _ _ => true | _ => false end)).
  destruct (exists_dec fA Γ) as [(θ & Hin & Hθ) | Hf].
  - left. subst fA. destruct θ. 4: { eexists. eexists. apply elem_of_list_In. eauto. }
    all:  auto with *.
  - right. intros ψ1 ψ2 Hψ. rewrite elem_of_list_In in Hψ. apply Hf in Hψ. subst fA. simpl in Hψ. tauto.
}
destruct HAndR as [(φ1 & φ2 & Heq) | HAndR].
{ subst.
  destruct (Hind Γ (Some φ1)) as [Hp1| H1]. order_tac.
  - destruct (Hind Γ (Some φ2)) as [Hp2| H2]. order_tac.
    + left. apply AndR; assumption.
    + right. intro Hp. apply AndR_rev in Hp. tauto.
  - right. intro Hp. apply AndR_rev in Hp. tauto.
}
destruct HOrL as [(ψ1 & ψ2 & Hin)|HOrL].
{ apply elem_of_list_to_set_disj in Hin.
  destruct (Hind (ψ1 :: rm (Or ψ1 ψ2) Γ) φ) as [Hp1| Hf]. destruct φ ; order_tac.
  - destruct (Hind (ψ2 :: rm (Or ψ1 ψ2) Γ) φ) as [Hp2| Hf]. destruct φ ; order_tac.
    + left. exhibit Hin 0.
         rewrite (proper_Provable _ _ (equiv_disj_union_compat_r (list_to_set_disj_rm Γ _)) _ _ eq_refl).
         apply OrL. peapply Hp1. peapply Hp2.
    + right; intro Hf'. assert(Hf'' :list_to_set_disj (rm (Or ψ1 ψ2) Γ) • Or ψ1 ψ2 ⊢ φ). {
          rw (symmetry (list_to_set_disj_rm Γ(Or ψ1 ψ2))) 1.
          pose (difference_singleton (list_to_set_disj Γ) (Or ψ1 ψ2)). peapply Hf'.
         }
        apply OrL_rev in Hf''. apply Hf. peapply Hf''.
  - right; intro Hf'. assert(Hf'' :list_to_set_disj (rm (Or ψ1 ψ2) Γ) • Or ψ1 ψ2 ⊢ φ). {
          rw (symmetry (list_to_set_disj_rm Γ(Or ψ1 ψ2))) 1.
          pose (difference_singleton (list_to_set_disj Γ) (Or ψ1 ψ2)). peapply Hf'.
         }
        apply OrL_rev in Hf''. apply Hf. peapply Hf''.1.
}
(* non invertible right rules *)
assert(HOrR1 : {φ1 & {φ2 & {D : list_to_set_disj Γ ⊢ Some φ1 & φ = Some (Or φ1 φ2)}}} +
                       {∀ φ1 φ2, ∀ (H : list_to_set_disj Γ ⊢ Some φ1), φ = Some (Or φ1 φ2) -> False}).
{
  destruct φ as [ φ | ] ; [ destruct φ | right ; intros ; discriminate].
  4: { destruct (Hind Γ (Some φ1))as [Hp|Hf]. order_tac.
  - left. do 2 eexists. eauto.
  - right. intros ? ? Hp Heq. dependent destruction Heq. subst. tauto.
  }
  all: right; auto with *.
}
destruct HOrR1 as [(φ1 & φ2 & Hp)| HOrR1].
{ left. destruct Hp as (Hp & Heq). subst. apply OrR1, Hp. }
assert(HOrR2 : {φ1 & {φ2 & {D : list_to_set_disj Γ ⊢ Some φ2 & φ = Some (Or φ1 φ2)}}} +
                       {∀ φ1 φ2, ∀ (H : list_to_set_disj Γ ⊢ Some φ2), φ = Some (Or φ1 φ2) -> False}).
{
  destruct φ as [ φ | ] ; [ destruct φ | right ; intros ; discriminate].
  4: { destruct (Hind Γ (Some φ2))as [Hp|Hf]. order_tac.
  - left. do 2 eexists. eauto.
  - right. intros ? ? Hp Heq. dependent destruction Heq. subst. tauto.
  }
  all: right; auto with *.
}
destruct HOrR2 as [(φ1 & φ2 & Hp)| HOrR2 ].
{ left. destruct Hp as [Hp Heq]. subst. apply OrR2, Hp. }
assert(HBoxR : {φ1 & {D : (⊗ list_to_set_disj Γ) ⊢ Some φ1 & φ = Some (□ φ1)}} +
                       {∀ φ1, ∀ (H : (⊗ list_to_set_disj Γ) ⊢ Some φ1), φ = Some (□ φ1) -> False}).
{
  destruct φ as [ φ | ] ; [ destruct φ | right ; intros ; discriminate].
  6: { destruct (Hind ((map open_box (List.filter is_box Γ))) (Some φ)) as [Hp|Hf].
  order_tac ; rewrite <- l_open_boxes_open_boxes_perm ; order_tac.
  - left. eexists. eexists; eauto.
    rewrite <- list_to_set_disj_open_boxes in Hp ; exact Hp.
  - right. intros ? Hp Heq. dependent destruction Heq.
    rewrite <- list_to_set_disj_open_boxes in Hf ; tauto.
  }
  all: right; auto with *.
}
destruct HBoxR as [(φ' & Hp)| HBoxR ].
{ left. destruct Hp as [Hp Heq]. subst. apply BoxR, Hp. }
assert(Hempty: ∀ (Δ : env) φ,((Δ • φ) = ∅) -> False).
{
  intros Δ θ Heq. assert (Hm:= multiplicity_empty θ).
  unfold base.empty in *.
  rewrite <- Heq, union_mult in Hm.
  setoid_rewrite (singleton_mult_in θ θ) in Hm; trivial. lia.
}
(* non invertible left rules *)
assert(HImpLImp : ∀Γ2 Γ1, Γ1 ++ Γ2 = Γ -> {φ1 & {φ2 & {φ3 & {D0 : (list_to_set_disj (rm ((φ1 → φ2) → φ3) Γ) • (φ2 → φ3)) ⊢ Some (φ1 → φ2) &
                                          {D1 : list_to_set_disj (rm ((φ1 → φ2) → φ3) Γ) • φ3 ⊢ φ & ((φ1 → φ2) → φ3) ∈ Γ2}}}}} +
    {∀ φ1 φ2 φ3 (_ : (list_to_set_disj (rm ((φ1 → φ2) → φ3) Γ) • (φ2 → φ3)) ⊢ Some (φ1 → φ2))
                              (_: list_to_set_disj (rm ((φ1 → φ2) → φ3) Γ) • φ3 ⊢ φ),
                              ((φ1 → φ2) → φ3) ∈ Γ2 → False}).
{
  induction Γ2 as [|θ Γ2]; intros Γ1 Heq.
  - right. intros φ1 φ2 φ3 _ _ Hin. inversion Hin.
  - assert(Heq' : (Γ1 ++ [θ]) ++ Γ2 = Γ) by (subst; auto with *).
    destruct (IHΓ2 (Γ1 ++  [θ]) Heq') as [(φ1 & φ2 & φ3 & Hp)|Hf].
   + left. do 3 eexists. destruct Hp as ( Hp1 & Hp2 & Hin). do 2 (eexists; eauto). now right.
   + destruct θ.
        5: destruct θ1.
        9 : {
        destruct (Hind  (Imp θ1_2 θ2 :: rm (Imp (Imp θ1_1 θ1_2) θ2) Γ) (Some (Imp θ1_1 θ1_2)))
          as [Hp1| Hf'].
        - destruct φ ; order_tac ; [ rewrite <- Permutation_middle ; unfold rm ;
          destruct form_eq_dec; [|tauto] ; order_tac | rewrite <- Permutation_middle ; unfold rm ;
          destruct form_eq_dec; [|tauto] ; order_tac].
        - destruct (Hind  (θ2 :: rm (Imp (Imp θ1_1 θ1_2) θ2) Γ) φ) as [Hp2| Hf''].
          + destruct φ ; order_tac ; [ rewrite <- Permutation_middle ; unfold rm ;
            destruct form_eq_dec; [|tauto] ; order_tac | rewrite <- Permutation_middle ; unfold rm ;
            destruct form_eq_dec; [|tauto] ; order_tac].
          + left. do 3 eexists.
              eexists; try l_tac; eauto. eexists. ms. ms.
          + right; intros φ1 φ2 φ3 Hp1' Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               dependent destruction Heq''. apply Hf''. peapply Hp2.
      - right; intros φ1 φ2 φ3 Hp1 Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               dependent destruction Heq''. apply Hf'. peapply Hp1.
        }
        all: (right; intros φ1 φ2 φ3 Hp1 Hp2 He; apply elem_of_list_In in He; destruct He as [Heq''| Hin];
     [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
}
destruct (HImpLImp Γ [] (app_nil_l _)) as [(φ1 & φ2 & φ3 & Hp1)|HfImpl].
{ left. destruct Hp1 as (Hp1 & Hp2 & Hin). 
  apply elem_of_list_to_set_disj in Hin. exhibit Hin 0.
  rw (list_to_set_disj_rm Γ(Imp (Imp φ1 φ2) φ3)) 1.
  apply ImpLImp; assumption.
}
(* ImpBox *)
assert(HImpLBox :∀Γ2 Γ1, Γ1 ++ Γ2 = Γ -> {φ1 & {φ2 & {D0 : (⊗ (list_to_set_disj (rm ((□ φ1) → φ2) Γ))) ⊢ Some φ1 &
                                          {D1 : list_to_set_disj (rm ((□ φ1) → φ2) Γ) • φ2 ⊢ φ &  ((□ φ1) → φ2) ∈ Γ2}}}} +
    {∀ φ1 φ2 (_ : (⊗ (list_to_set_disj (rm ((□ φ1) → φ2) Γ))) ⊢ Some φ1)
                              (_: list_to_set_disj (rm ((□ φ1) → φ2) Γ) • φ2 ⊢ φ),
                               ((□ φ1) → φ2) ∈ Γ2 → False}).
{
  induction Γ2 as [|θ Γ2]; intros Γ1 Heq.
  - right. intros φ1 φ2 _ _ Hin. inversion Hin.
  - assert(Heq' : (Γ1 ++ [θ]) ++ Γ2 = Γ) by (subst; auto with *).
    destruct (IHΓ2 (Γ1 ++  [θ]) Heq') as [(φ1 & φ2 & Hp1)|Hf].
   + left. subst. do 2 eexists.
     destruct Hp1 as (Hp1 & Hp2 & Hin). do 2 (eexists; eauto). now right.
   + destruct θ.
        5: destruct θ1.
        10 : {
        destruct (Hind  ((map open_box (List.filter is_box (rm (Imp (Box θ1) θ2) Γ)))) (Some θ1))
          as [Hp1|Hf'].
        - destruct φ ; order_tac ; rewrite <- l_open_boxes_open_boxes_perm ; order_tac ;
          rewrite l_open_boxes_rm ; auto ; rewrite l_open_boxes_app ; cbn ;
          rewrite <- l_open_boxes_app.
          do 2 (apply env_order_0' ; apply env_order_env_order_refl).
          all: apply (@env_order_equiv_right_compat _ _ ((□ θ1 → θ2) :: (Γ1 ++ Γ2))) ;
          [ rewrite Permutation_middle ; auto | 
            apply env_order_2 ; cbn ; try lia ; apply l_open_boxes_env_order].
        - destruct (Hind  (θ2 :: rm (Imp (□ θ1) θ2) Γ) φ) as [Hp2| Hf''].
          + destruct φ ; order_tac ; rewrite <- Permutation_middle ; unfold rm.
              all: destruct form_eq_dec; [|tauto] ; order_tac.
          + left. do 2 eexists. 
               repeat eexists; repeat l_tac; eauto. 2: ms. 
               rewrite <- list_to_set_disj_open_boxes in Hp1 ; auto.
          + right; intros φ1 φ2 Hp1' Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               dependent destruction Heq''. apply Hf''. peapply Hp2.
      - right; intros φ1 φ2 Hp1 Hp2 He; apply elem_of_list_In in He;
               destruct He as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
               dependent destruction Heq''. apply Hf'.
             (erewrite proper_Provable;  [| |reflexivity]);  [eapply Hp1|].
             repeat rewrite <- ?list_to_set_disj_env_add, list_to_set_disj_open_boxes. trivial.
        }
        all: (right; trivial; intros φ1 φ2 Hp1 Hp2 He;
              apply elem_of_list_In in He; destruct He as [Heq''| Hin];
             [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
}
destruct (HImpLBox Γ [] (app_nil_l _)) as [(φ1 & φ2 & Hp1)|HfImpLBox].
{ left. destruct Hp1 as (Hp1 & Hp2 & Hin). 
  apply elem_of_list_to_set_disj in Hin. exhibit Hin 0.
  rw (list_to_set_disj_rm Γ(Imp (□ φ1) φ2)) 1.
  apply ImpBox; assumption.
}

assert(HImpLDiam :∀ Γ3 Γ2 Γ1, Γ1 ++ Γ2 ++ Γ3 ≡ₚ Γ -> {φ1 & {φ2 & {χ & {D0 : (⊗ (list_to_set_disj (rm (◊ χ) (rm ((◊ φ1) → φ2) Γ)))) • χ ⊢ Some φ1 &
                                          {D1 : (list_to_set_disj (rm ((◊ φ1) → φ2) Γ)) • φ2 ⊢ φ & ((◊ φ1) → φ2) ∈ Γ2 /\ (◊ χ) ∈ Γ3}}}}} +
    {∀ φ1 φ2 χ (_ : (⊗ (list_to_set_disj (rm (◊ χ) (rm ((◊ φ1) → φ2) Γ)))) • χ ⊢ Some φ1)
                              (_: (list_to_set_disj (rm ((◊ φ1) → φ2) Γ)) • φ2 ⊢ φ),
                               ((◊ φ1) → φ2) ∈ Γ2 → (◊ χ) ∈ Γ3 → False}).
{
induction Γ3 as [|θ Γ3].
  - intros Γ2 Γ1 perm. right. intros φ1 φ2 χ _ _ Hin1 Hin2. inversion Hin2.
  - induction Γ2 as [|γ Γ2] ; intros Γ1 Heq.
    + right. intros φ1 φ2 χ _ _ Hin1 Hin2. inversion Hin1.
    + assert(perm' : (Γ1 ++ [θ]) ++ (Γ2 • γ) ++ Γ3 ≡ₚ Γ).
      { rewrite <- Heq. repeat rewrite <- app_assoc. cbn. repeat rewrite Permutation_middle. rewrite Permutation_swap ; auto. }
      destruct (IHΓ3 (γ :: Γ2) (Γ1 ++ [θ]) perm') as [(φ1 & φ2 & χ & Hp1 & Hp2 & Hin1 & Hin2)|Hf].
      * left. do 3 eexists. do 2 (eexists; eauto). split ; ms.
      * destruct θ.
        1-6: (right; trivial; intros φ1 φ2 χ Hp1 Hp2 Hin1 Hin2;
              apply elem_of_list_In in Hin2; destruct Hin2 as [Heq''| Hin] ;
             [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
        assert (perm'' : (Γ1 ++ [γ]) ++ Γ2 ++ (Γ3 • ◊ θ) ≡ₚ Γ).
        { rewrite <- Heq. repeat rewrite <- app_assoc. cbn. repeat rewrite Permutation_middle. auto. }
        destruct (IHΓ2 (Γ1 ++ [γ]) perm'') as [(φ1 & φ2 & χ & Hp1 & Hp2 & Hin1 & Hin2)|Hf0].
        -- left. do 3 eexists. do 2 (eexists; eauto). split ; ms.
        -- destruct γ.
           5: destruct γ1.
           1-10,12-13: (right; trivial; intros φ1 φ2 χ Hp1 Hp2 Hin1 Hin2;
                apply elem_of_list_In in Hin1; destruct Hin1 as [Heq''| Hin] ;
                [discriminate|apply elem_of_list_In in Hin; eapply Hf0; eauto]).
           destruct (Hind (θ :: (map open_box (List.filter is_box (rm (◊ θ) (rm ((◊ γ1) → γ2) Γ))))) (Some γ1))
           as [Hp1|Hf'].
           ++ assert (H: (◊ γ1 → γ2) :: ◊ θ :: (Γ1 ++ Γ2 ++ Γ3) ≡ₚ Γ).
              { rewrite <- Heq. cbn. repeat rewrite Permutation_middle. auto. }
              destruct φ ; order_tac ; rewrite <- l_open_boxes_open_boxes_perm ; order_tac.
              do 2 (apply env_order_0' ; apply env_order_env_order_refl).
              all: symmetry in H ; apply (env_order_equiv_right_compat H) ;
              apply env_order_2 ; cbn ; try lia ; apply env_order_env_order_refl ; apply env_order_1' ; cbn ; try lia ;
              apply env_order_refl_trans with (l_open_boxes (Γ1 ++ Γ2 ++ Γ3)) ; [ | apply l_open_boxes_env_order] ;
              do 2 (rewrite l_open_boxes_rm ; auto).
              all: enough (Permutation (l_open_boxes (Γ1 ++ Γ2 ++ Γ3)) (l_open_boxes Γ)) by (rewrite H0 ; left ; auto) ;
              assert (l_open_boxes (Γ1 ++ Γ2 ++ Γ3) = l_open_boxes ((◊ γ1 → γ2) :: ◊ θ :: Γ1 ++ Γ2 ++ Γ3)) ;
              cbn ; auto ; rewrite H0 ; apply l_open_boxes_perm ; symmetry in H ; auto.
           ++ destruct (Hind  (γ2 :: ◊ θ :: rm (◊ θ) (rm ((◊ γ1) → γ2) Γ)) φ) as [Hp2| Hf''].
              ** destruct φ ; order_tac ; apply env_order_lt_le_trans with ((◊ γ1 → γ2) :: ◊ θ :: rm (◊ θ) (rm (◊ γ1 → γ2) Γ)).
                 1,3: apply env_order_1' ; cbn ; try lia ; apply env_order_refl_add ; left ; auto.
                 1-2: enough (Γ ≡ₚ (◊ γ1 → γ2) :: ◊ θ :: rm (◊ θ) (rm (◊ γ1 → γ2) Γ)) by (rewrite <- H ; left ; auto) ;
                     rewrite <- rm_add ; [ rewrite <- rm_add ; [auto | ] | ].
                     1,3: apply (Permutation_in _ Heq) ; apply in_or_app ; right ; apply in_or_app ; left ; cbn ; auto.
                     1-2: apply in_in_rm ; [ intro K ; discriminate | ] ; apply (Permutation_in _ Heq) ;
                          apply in_or_app ; right ; apply in_or_app ; right ; cbn ; auto.
              ** left. do 3 eexists. eexists.
                 --- rewrite (proper_Provable _ (list_to_set_disj (map open_box (List.filter is_box (rm (◊ θ) (rm (◊ γ1 → γ2) Γ))) • θ))) with (y:=Some γ1) ; auto.
                     rewrite list_to_set_disj_open_boxes. rewrite <- l_open_boxes_open_boxes_perm.
                     rewrite list_to_set_disj_env_add ; auto.
                 --- eexists.
                     +++ rewrite (proper_Provable _ (list_to_set_disj (rm (◊ θ) (rm (◊ γ1 → γ2) Γ) • ◊ θ • γ2))) with (y:=φ) ; auto.
                         rewrite <- rm_add ; [ rewrite list_to_set_disj_env_add ; auto | ]. 
                         apply in_in_rm ; [ intro K ; discriminate | ]. apply (Permutation_in _ Heq).
                         apply in_or_app ; right ; apply in_or_app ; right ; cbn ; auto.
                     +++ split ; ms.
              ** right. intros φ1 φ2 χ Hp1' Hp2 Hin1 Hin2. apply elem_of_list_In in Hin2; destruct Hin2 as [Heq''| Hin].
                 --- inversion Heq'' ; subst. apply elem_of_list_In in Hin1; destruct Hin1 as [Heq'''| Hin'].
                     +++ inversion Heq''' ; subst. apply Hf''.
                         rewrite (proper_Provable _ (list_to_set_disj (rm (◊ φ1 → φ2) Γ) • φ2)) with (y:=φ) ; auto.
                         rewrite <- rm_add ; [ rewrite list_to_set_disj_env_add ; auto | ]. 
                         apply in_in_rm ; [ intro K ; discriminate | ]. apply (Permutation_in _ Heq).
                         apply in_or_app ; right ; apply in_or_app ; right ; cbn ; auto.
                     +++ apply (Hf0 _ _ _ Hp1' Hp2) ; [ apply elem_of_list_In ; auto | ms].
                 --- apply (Hf _ _ _ Hp1' Hp2) ; auto. apply elem_of_list_In ; auto.
           ++ right. intros φ1 φ2 χ Hp1' Hp2 Hin1 Hin2. apply elem_of_list_In in Hin2; destruct Hin2 as [Heq''| Hin].
              ** inversion Heq'' ; subst. apply elem_of_list_In in Hin1; destruct Hin1 as [Heq'''| Hin'].
                 --- inversion Heq''' ; subst. apply Hf'.
                     rewrite (proper_Provable _ (⊗ list_to_set_disj (rm (◊ χ) (rm (◊ φ1 → φ2) Γ)) • χ)) with (y:=Some φ1) ; auto.
                     rewrite <- l_open_boxes_open_boxes_perm. do 2 (rewrite l_open_boxes_rm ; auto).
                     rewrite list_to_set_disj_open_boxes. rewrite <- l_open_boxes_open_boxes_perm. do 2 (rewrite l_open_boxes_rm ; auto).
                     rewrite list_to_set_disj_env_add ; auto.
                 --- apply (Hf0 _ _ _ Hp1' Hp2) ; [ apply elem_of_list_In ; auto | ms].
              ** apply elem_of_list_In in Hin1; destruct Hin1 as [Heq'''| Hin'].
                 --- inversion Heq''' ; subst. apply (Hf _ _ _ Hp1' Hp2) ; [ ms | apply elem_of_list_In ; auto ].
                 --- apply (Hf _ _ _ Hp1' Hp2) ; [ | apply elem_of_list_In ; auto ].
                     right ; apply elem_of_list_In ; auto.
}
assert(HImpLDiam' : {φ1 & {φ2 & {χ & {D0 : (⊗ (list_to_set_disj (rm (◊ χ) (rm ((◊ φ1) → φ2) Γ)))) • χ ⊢ Some φ1 &
                                          {D1 : (list_to_set_disj (rm ((◊ φ1) → φ2) Γ)) • φ2 ⊢ φ & ((◊ φ1) → φ2) ∈ Γ /\ (◊ χ) ∈ Γ}}}}} +
    {∀ φ1 φ2 χ (_ : (⊗ (list_to_set_disj (rm (◊ χ) (rm ((◊ φ1) → φ2) Γ)))) • χ ⊢ Some φ1)
                              (_: (list_to_set_disj (rm ((◊ φ1) → φ2) Γ)) • φ2 ⊢ φ),
                               ((◊ φ1) → φ2) ∈ Γ → (◊ χ) ∈ Γ → False}).
{ 
  destruct (HImpLDiam (List.filter (fun φ => negb (is_diam_implication_b φ)) Γ) (List.filter is_diam_implication_b Γ) []).
  - cbn. apply diamimp_partition. 
  - left. destruct s as [φ1 [φ2 [χ [Hp1 [Hp2 [Hin1 Hin2]]]]]]. do 4 eexists ; eauto.
    eexists ; auto. split.
    + apply elem_of_list_In,filter_In in Hin1. destruct Hin1. apply elem_of_list_In ; auto. 
    + apply elem_of_list_In,filter_In in Hin2. destruct Hin2. apply elem_of_list_In ; auto.
  - right. intros φ1 φ2 χ Hp1 Hp2 Hin1 Hin2. apply (f φ1 φ2 χ) ; auto ;
    apply elem_of_list_In ; apply filter_In ; split ; auto ; apply elem_of_list_In ; auto.
}
destruct (HImpLDiam') as [(φ1 & φ2 & χ & Hp1)|HfImpLDiam].
{left. destruct Hp1 as (Hp1 & Hp2 & Hin1 & Hin2).
  apply elem_of_list_to_set_disj in Hin1,Hin2. exhibit Hin1 0.
  apply in_difference with (ψ:= ◊ φ1 → φ2) in Hin2 ; auto.
  exhibit Hin2 1. apply ImpDiam.
  - rewrite (proper_Provable _ (⊗ list_to_set_disj (rm (◊ χ) (rm (◊ φ1 → φ2) Γ)) • χ)) with (y:=Some φ1) ; auto.
    rewrite list_to_set_disj_open_boxes. rewrite <- l_open_boxes_open_boxes_perm.
    do 2 (rewrite l_open_boxes_rm ; auto). rewrite l_open_boxes_open_boxes_perm.
    rewrite <- list_to_set_disj_open_boxes. do 2 (rewrite open_boxes_remove_f ; auto).
  - rewrite (proper_Provable _ (list_to_set_disj (rm (◊ φ1 → φ2) Γ) • φ2)) with (y:=φ) ; auto.
    rewrite <- difference_singleton ; auto. rewrite list_to_set_disj_rm ; auto. 
}
assert(HDiamL : ∀Γ2 Γ1, Γ1 ++ Γ2 = Γ -> {φ2 & {D : (⊗ list_to_set_disj Γ) • φ2 ⊢ oud φ & (◊ φ2) ∈ Γ2}} +
                       {∀ φ2, ∀ (H : (⊗ list_to_set_disj Γ) • φ2 ⊢ oud φ), (◊ φ2) ∈ Γ2 → False}).
{
  induction Γ2 as [|θ Γ2]; intros Γ1 Heq.
  - right. intros φ1 φ2 Hin. inversion Hin.
  - assert(Heq' : (Γ1 ++ [θ]) ++ Γ2 = Γ) by (subst; auto with *).
    destruct (IHΓ2 (Γ1 ++  [θ]) Heq') as [(φ1 & Hp1)|Hf].
   + left. subst. eexists.
     destruct Hp1 as (Hp1 & Hin). eexists; eauto. ms.
   + destruct θ.
        1-6: (right; trivial; intros φ1 Hp1 He;
              apply elem_of_list_In in He; destruct He as [Heq''| Hin];
             [discriminate|apply elem_of_list_In in Hin; eapply Hf; eauto]).
        destruct (Hind  (θ :: (map open_box (List.filter is_box (rm (◊ θ) Γ)))) (oud φ)) as [Hp1|Hf'].
        * destruct φ as [φ | ] ; [destruct φ ; cbn | cbn ] ; order_tac ; rewrite <- l_open_boxes_open_boxes_perm ; order_tac.
          all : rewrite l_open_boxes_rm ; cbn ; auto ; rewrite l_open_boxes_app ; cbn ; rewrite <- l_open_boxes_app.
          1-6 : eapply env_order_lt_le_trans with (_ :: _ :: ◊ θ :: (Γ1 ++ Γ2)) ;
          [ do 2 (apply env_order_0' ; apply env_order_env_order_refl) ; apply env_order_1' ; cbn ; auto ; try
            apply l_open_boxes_env_order | 
            eapply Proper_env_order_refl ; [ reflexivity | | left ; reflexivity] ;
            do 2 (repeat rewrite Permutation_middle ; repeat rewrite <- app_assoc ; cbn) ; reflexivity].
          apply env_order_2 ; cbn ; try lia. apply env_order_env_order_refl.
          apply env_order_0'. apply env_order_env_order_refl. 
          all : eapply env_order_lt_le_trans with (◊ θ :: (Γ1 ++ Γ2)) ;
          [ apply env_order_1' ; cbn ; auto ;
            apply l_open_boxes_env_order | 
            eapply Proper_env_order_refl ; [ reflexivity | | left ; reflexivity] ;
            rewrite Permutation_middle ; auto ].
        * left. exists θ. repeat eexists; repeat l_tac; eauto. 2: ms.
          rewrite (proper_Provable _ (list_to_set_disj (map open_box (List.filter is_box (rm (◊ θ) Γ)) • θ))) with (y:=oud φ) ; auto.
          do 2 rewrite <- l_open_boxes_open_boxes_perm. rewrite l_open_boxes_rm ; auto. 
        * right; intros φ1 Hp1' He1 ; apply elem_of_list_In in He1 ;
          destruct He1 as [Heq''| Hin]; [|apply elem_of_list_In in Hin; eapply Hf; eauto].
          dependent destruction Heq''. apply Hf'.
          rewrite (proper_Provable _ (⊗ list_to_set_disj (Γ1 ++ (Γ2 • ◊ φ1)) • φ1)) with (y:=oud φ) ; auto.
          rewrite <- list_to_set_disj_env_add. apply equiv_disj_union_compat_r.
          rewrite list_to_set_disj_open_boxes. apply env_equiv_eq. apply list_to_set_disj_perm.
          do 2 (rewrite <- l_open_boxes_open_boxes_perm). rewrite l_open_boxes_rm ; auto.
}
destruct (HDiamL Γ [] (app_nil_l _)) as [(φ1 & Hp1)|HfDiamL].
{ left. destruct Hp1 as (Hp1 & Hin) ; subst.
  apply elem_of_list_to_set_disj in Hin. exhibit Hin 0.
  apply DiamL.
  rewrite (proper_Provable _ (⊗ list_to_set_disj Γ • φ1)) with (y:=oud φ) ; auto.
  rewrite open_boxes_remove_f ; auto.
}
clear Hind HImpLImp HImpLBox HImpLDiam HDiamL.
right.
intro Hp. dependent destruction Hp; try eqt; eauto 2.
- eapply HAndR; eauto.
- eapply HImpR; eauto.
- eapply HImpLVar; eauto. apply elem_of_list_to_set_disj.
  match goal with H : _ = list_to_set_disj Γ |- _ => setoid_rewrite <- H end. ms.
- eapply HfImpl; eauto.
  + now rw Heq 1.
  + now rw Heq 1.
- eapply HfImpLBox; eauto.
  + rw (proper_open_boxes _ _ Heq) 0 ; auto.
  + now rw Heq 1.
- apply (HfImpLDiam φ1 φ2 χ) ; eauto.
  + rewrite (proper_Provable _ (⊗ Γ0 • χ)) with (y:=Some φ1) ; auto.
    rewrite list_to_set_disj_open_boxes. rewrite <- l_open_boxes_open_boxes_perm.
    rewrite l_open_boxes_rm ; auto. rewrite l_open_boxes_open_boxes_perm.
    rewrite <- list_to_set_disj_open_boxes. rewrite Heq.
    rewrite open_boxes_add_f ; auto.
  + rewrite (proper_Provable _ (Γ0 • ◊ χ • φ2)) with (y:=oψ) ; auto.
    rewrite Heq ; auto.
  + apply remove_include with (◊ φ1 → φ2) ; auto. apply elem_of_list_to_set_disj.
    rewrite Heq. ms.
- eapply HfDiamL ; eauto.
  rewrite (proper_Provable _ (⊗ Γ0 • ψ)) with (y:=oud oφ) ; auto.
  rewrite <- Heq. do 2 rewrite list_to_set_disj_open_boxes. do 2 rewrite <- l_open_boxes_open_boxes_perm.
  rewrite l_open_boxes_rm ; auto.
Defined.

Global Infix "⊢?" := Provable_dec (at level 80).

Lemma Provable_dec_of_Prop  Γ φ: (∃ _ : list_to_set_disj Γ ⊢ φ, True) -> (list_to_set_disj Γ ⊢ φ).
Proof.
destruct (Provable_dec Γ φ) as [Hφ1' | Hf']. tauto.
intros Hf. exfalso. destruct Hf as [Hf _]. tauto.
Qed.

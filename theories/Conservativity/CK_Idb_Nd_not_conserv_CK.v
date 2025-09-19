From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Ensembles.
From Stdlib Require Import Bool.
From Stdlib Require Import Btauto.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_soundness.
Require Import CK_Idb_Nd_soundness.
Require Import CK_Idb_Nd_segP_completeness.



Section CKIdbNd_not_conserv_CK.

(* The diamond free fragment of CK + Idb + Nd extends the one of CK. *)

Theorem diam_free_ext_CKIdbNd_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ -> CKIdbNdH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (fun x => False) ; auto. intros A F ; contradiction.
Qed.

(* We proceed to show that this extension is strict, by proving that the formula
    (¬ ¬ □ ⊥) → □ ⊥ is not validated in the class of all frames. We thus
    need to provide a countermodel for it, which we define next. *)

(* Intuitionistic relation *)

Definition bireach (b0 b1 : bool * bool) : Prop :=
  if eqb (fst b0) (fst b1) then (if eqb (snd b0) (snd b1) then True else False) else
    if fst b1 then (if eqb (snd b0) (snd b1) then True else False) else False.

Lemma bireach_refl b : bireach b b.
Proof.
unfold bireach ; destruct b ; repeat rewrite eqb_reflx ; cbn ; auto.
Qed.

Lemma bireach_trans u v w: bireach u v -> bireach v w -> bireach u w.
Proof.
intros ; unfold bireach in *. destruct w ; destruct v ; destruct u ; cbn in * ; auto.
destruct (eqb b3 b1) eqn:E0; destruct (eqb b4 b2) eqn:E1; destruct (eqb b1 b) eqn:E2;
destruct (eqb b2 b0) eqn:E3; destruct (eqb b3 b) eqn:E4; destruct (eqb b4 b0) eqn:E5;
cbn in * ; try apply eqb_prop in E0 ; try apply eqb_prop in E1 ; try apply eqb_prop in E2 ;
try apply eqb_prop in E3 ; try apply eqb_prop in E4 ; try apply eqb_prop in E5 ; subst ;
firstorder. 1,3,4,5,9,10,11: destruct b0 ; cbn in E5 ; discriminate.
destruct b ; cbn in E4 ; discriminate. destruct b ; cbn in E2 ; discriminate.
1,4:destruct b0 ; cbn in E3 ; discriminate. destruct b0 ; cbn in E5 ; discriminate.
1,4,5,6,7:destruct b,b1 ; cbn in * ; auto. destruct b ; cbn in E0 ; discriminate.
destruct b0 ; cbn in E1 ; discriminate.
Qed.

Lemma bireach_expl u : bireach (true,true) u -> u = (true,true).
Proof.
intros. unfold bireach in H ; destruct u ; cbn in * ; auto.
destruct b,b0; try rewrite eqb_iff in H ; firstorder.
Qed.

(* Modal relation *)

Definition bmreach (b0 b1 : bool * bool) : Prop :=
  if fst b1 then (if snd b1 then (if fst b0 then True else False) else False) else
    if negb (fst b0) then (if negb (snd b0) then (if negb (fst b1) then (if snd b1 then True else False) else False) else False) else False.

Lemma bmreach_expl u : bmreach (true,true) u <-> u = (true,true).
Proof.
split ; unfold bmreach ; intro ; destruct u ; cbn in * ; subst ; destruct b ; destruct b0 ; inversion H ; subst ; firstorder.
Qed.

(* We can define a frame. *)

Instance bF : frame :=
      {|
        nodes := bool * bool ;
        expl:= (true,true) ;

        ireachable := bireach ;
        ireach_refl := bireach_refl ;
        ireach_tran := bireach_trans ;
        ireach_expl := bireach_expl  ;

        mreachable := bmreach  ;
        mreach_expl := bmreach_expl  ;
      |}.

(* We define a valuation. *)

Definition bval (b : bool * bool) (p : nat) := if fst b then (if snd b then True else False) else False.

Lemma bval_persist : forall u v, bireach u v -> forall (p : nat), bval u p -> bval v p.
Proof.
intros. unfold bval in *. destruct u ; destruct v ; destruct b ; destruct b0 ; destruct b1 ; destruct b2 ; cbn in * ; auto.
Qed.

Lemma bval_expl  : forall p, bval expl p.
Proof.
intros. unfold bval. destruct expl eqn:E; destruct b ; destruct b0 ; cbn ; auto. all: inversion E.
Qed.

(* Finally we can define a model. *)

Instance bM : model :=
      {|
        fra := bF ;

        val := bval  ;
        persist :=  bval_persist ;
        val_expl :=  bval_expl
      |}.

(* We use this model to show that the extension is strict. *)

Theorem diam_free_strict_ext_CKIdbNd_CK : CKIdbNdH_prv (Empty_set _) ((¬ ¬ □ ⊥) → □ ⊥) /\
                                                                     ~ CKH_prv (Empty_set _) ((¬ ¬ □ ⊥) → □ ⊥).
Proof.
split.
- eapply MP. eapply MP. apply Imp_trans.
  apply negneg_box_prv.
  eapply MP. apply Ax ; left ; right ; eapply Kb ; reflexivity.
  apply Nec. apply extCKH_Deduction_Theorem. eapply MP.
  apply Id ; right ; split. apply imp_Id_gen.
- intro. apply extCKH_Detachment_Theorem in H. apply CK_Soundness in H.
  assert (forces bM (false,false) ((¬ (¬ (□ ⊥))))).
  { intros b ifb Hb. destruct b ; cbn in * ; unfold bireach in ifb ; cbn in ifb.
    destruct b ; cbn in *.
    - destruct b0 ; cbn in * ; auto. apply Hb. unfold bireach ; cbn ; auto.
      intros. destruct v. unfold bireach in H0 ; cbn in *. destruct b. destruct b0.
      contradiction. destruct u. unfold bmreach in H1 ; destruct b ; destruct b0 ; cbn in * ; firstorder.
      contradiction.
    - destruct b0. contradiction. enough ((true,false) = (true,true)). inversion H0.
      apply Hb. unfold bireach ; cbn ; auto. intros. destruct v. unfold bireach in H0 ; cbn in *. destruct b. destruct b0.
      contradiction. destruct u. unfold bmreach in H1 ; destruct b ; destruct b0 ; cbn in * ; firstorder.
      contradiction. }
  assert (~ forces bM (false,false) (□ ⊥)).
  { intro. cbn in H1. enough ((false,true) = (true,true)). inversion H2.
    apply H1 with (false,false). unfold bireach ; cbn ; auto. unfold bmreach ; cbn ; auto. }
  apply H1. apply H ; auto.
  intros. inversion H2 ; subst ; auto. inversion H3. inversion H3 ; auto.
Qed.

End CKIdbNd_not_conserv_CK.






Section IK_not_conserv_CK.

(* We can also show that the diamond free fragment of IK extends the one of CK. *)

Theorem diam_free_ext_IK_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ -> IKH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (fun x => False) ; auto. intros A F ; contradiction.
Qed.

(* Using the previous model, we show that this extension is also strict. *)

Theorem diam_free_strict_ext_IK_CK : IKH_prv (Empty_set _) ((¬ ¬ □ ⊥) → □ ⊥) /\
                                                                     ~ CKH_prv (Empty_set _) ((¬ ¬ □ ⊥) → □ ⊥).
Proof.
split.
- apply more_AdAx_more_prv with (fun x => (exists A B, Idb A B = x) \/ Nd = x).
  intros A HA ; firstorder.
  apply diam_free_strict_ext_CKIdbNd_CK.
- apply diam_free_strict_ext_CKIdbNd_CK.
Qed.

End IK_not_conserv_CK.





Section IK_not_conserv_CKIdbNd.

  (* Intuitionistic relation *)

Definition tbireach (tb0 tb1 : bool * bool * bool) : Prop :=
  match tb0 with
  | (true,true,true) => match tb1 with
                            | (true,true,true) => True
                            | _ => False
                            end
  | (false,false,false) => match tb1 with
                            | (false,false,false) => True
                            | (false,true,false) => True
                            | (true,true,false) => True
                            | (true,false,true) => True
                            | _ => False
                            end
  | (false,false,true) => match tb1 with
                            | (false,false,true) => True
                            | (false,true,true) => True
                            | (true,false,false) => True
                            | _ => False
                            end
  | (false,true,false) => match tb1 with
                            | (false,true,false) => True
                            | (true,true,false) => True
                            | (true,false,true) => True
                            | _ => False
                            end
  | (true,false,true) => match tb1 with
                            | (true,false,true) => True
                            | _ => False
                            end
  | (true,true,false) => match tb1 with
                            | (true,true,false) => True
                            | _ => False
                            end
  | (true,false,false) => match tb1 with
                            | (true,false,false) => True
                            | _ => False
                            end
  | (false,true,true) => match tb1 with
                            | (false,true,true) => True
                            | _ => False
                            end
  end.

Lemma tbireach_refl t : tbireach t t.
Proof.
unfold tbireach ; destruct t as [[b0 b1] b2] ; destruct b0,b1,b2 ; repeat rewrite eqb_reflx ; cbn ; auto.
Qed.

Lemma tbireach_trans u v w: tbireach u v -> tbireach v w -> tbireach u w.
Proof.
intros ; unfold tbireach in *.
destruct w as [[b0 b1] b2]; destruct v as [[b3 b4] b5]; destruct u as [[b6 b7] b8]; 
destruct b0,b1,b2,b3,b4,b5,b6,b7,b8 ; cbn in * ; auto ; try contradiction.
Qed.

Lemma tbireach_expl u : tbireach (true,true,true) u -> u = (true,true,true).
Proof.
intros. unfold tbireach in H ; destruct u as [[b0 b1] b2]; destruct b0,b1,b2 ; cbn in * ; auto ; try contradiction.
Qed.

(* Modal relation *)

Definition tbmreach (tb0 tb1 : bool * bool * bool) : Prop :=
  match tb0 with
  | (true,true,true) => match tb1 with
                            | (true,true,true) => True
                            | _ => False
                            end
  | (false,false,false) => match tb1 with
                            | (false,false,true) => True
                            | _ => False
                            end
  | (false,false,true) => False
  | (false,true,false) => match tb1 with
                            | (false,true,true) => True
                            | (true,false,false) => True
                            | _ => False
                            end
  | (true,false,true) => match tb1 with
                            | (false,true,true) => True
                            | _ => False
                            end
  | (true,true,false) => match tb1 with
                            | (true,false,false) => True
                            | _ => False
                            end
  | (true,false,false) => False
  | (false,true,true) => False
  end.

Lemma tbmreach_expl u : tbmreach (true,true,true) u <-> u = (true,true,true).
Proof.
split ; unfold tbmreach ; intro ; destruct u as [[b0 b1] b2] ; destruct b0,b1,b2; 
cbn in * ; subst ; auto ; try contradiction ; try inversion H.
Qed.

(* We can define a frame. *)

Instance tbF : frame :=
      {|
        nodes := bool * bool * bool ;
        expl:= (true,true,true) ;

        ireachable := tbireach ;
        ireach_refl := tbireach_refl ;
        ireach_tran := tbireach_trans ;
        ireach_expl := tbireach_expl  ;

        mreachable := tbmreach  ;
        mreach_expl := tbmreach_expl  ;
      |}.


(* This frame is a CK_Idb_Nd frame *)

Lemma tbF_Idb_Nd : suff_Idb_frame tbF /\ suff_Nd_frame tbF.
Proof.
split.
(* suff_Idb *)
- intros x y z mxy iyz ; cbn in *. unfold tbmreach in * ; unfold tbireach in *.
  destruct x as [[b0 b1] b2] ; destruct y as [[b3 b4] b5] ; destruct z as [[b6 b7] b8] ; 
  destruct b0,b1,b2,b3,b4,b5,b6,b7,b8 ; cbn in * ; subst ; auto ; try contradiction ; cbn.
  + exists (true,true,true) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    exists (true,true,true) ; cbn. cbn in *. destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction.
  + exists (true,true,false) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    exists (true,false,false) ; cbn. cbn in *. destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction. split ; auto. exists (true,false,false) ; cbn ; split ; auto ; split.
  + exists (true,false,true) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    exists (false,true,true) ; cbn. cbn in *. destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction. split ; auto. exists (false,true,true) ; cbn ; split ; auto ; split.
  + exists (true,true,false) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    exists (true,false,false) ; cbn. cbn in *. destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction. split ; auto. exists (true,false,false) ; cbn ; split ; auto ; split.
  + exists (true,false,true) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    exists (false,true,true) ; cbn. cbn in *. destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction. split ; auto. exists (false,true,true) ; cbn ; split ; auto ; split.
  + exists (true,true,false) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    exists (true,false,false) ; cbn. cbn in *. destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction. split ; auto. exists (true,false,false) ; cbn ; split ; auto ; split.
  + exists (true,false,true) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    exists (false,true,true) ; cbn. cbn in *. destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction. split ; auto. exists (false,true,true) ; cbn ; split ; auto ; split.
  + exists (false,false,false) ; cbn. repeat split ; auto. intros z Hz ; inversion Hz. destruct H. inversion H ; subst.
    destruct z as [[b6 b7] b8] ; destruct b6,b7,b8 ; cbn in * ; subst ; auto ;
    try contradiction.
    * exists (true,false,false) ; cbn. split ; auto. exists (false,false,true) ; cbn ; split ; auto ; split.
    * exists (false,true,true) ; cbn. split ; auto. exists (false,false,true) ; cbn ; split ; auto ; split.
    * exists (false,true,true) ; cbn. split ; auto. exists (false,false,true) ; cbn ; split ; auto ; split.
    * exists (false,false,true) ; cbn. split ; auto. exists (false,false,true) ; cbn ; split ; auto ; split.
(* suff_Nd *)
- intros x mxexpl ; cbn in *. destruct x as [[b0 b1] b2] ; destruct b0,b1,b2 ; cbn in * ; auto ; try contradiction.
Qed.

(* We define a valuation. *)

Definition tbval (tb : bool * bool * bool) (p : nat) := 
  match tb with
  | (true,true,true) => True
  | (true,false,false) => p = 0 \/ p = 1
  | (false,true,true) => p = 0 \/ p = 2
  | _ => False
  end.

Lemma tbval_persist : forall u v, tbireach u v -> forall (p : nat), tbval u p -> tbval v p.
Proof.
intros. unfold tbval in *.
destruct u as [[b0 b1] b2]; destruct v as [[b3 b4] b5]; destruct b0,b1,b2,b3,b4,b5 ; cbn in * ; auto ; try contradiction.
Qed.

Lemma tbval_expl  : forall p, tbval expl p.
Proof.
intros. unfold tbval. destruct expl as [[b0 b1] b2] eqn:E ; auto.
unfold expl in E. inversion E ; subst ; cbn ; auto.
Qed.

(* Finally we can define a model. *)

Instance tbM : model :=
      {|
        fra := tbF ;

        val := tbval  ;
        persist :=  tbval_persist ;
        val_expl :=  tbval_expl
      |}.




Theorem diam_free_strict_ext_IK_CKIdbNd : 
        IKH_prv (Empty_set _) (((□ ((# 1) ∨ (# 2)) → ((¬ □ ¬ # 1) ∨ (¬ □ ¬ # 2))) → □ # 0) → □ # 0) /\
        ~ CKIdbNdH_prv (Empty_set _) (((□ ((# 1) ∨ (# 2)) → ((¬ □ ¬ # 1) ∨ (¬ □ ¬ # 2))) → □ # 0) → □ # 0).
Proof.
split ; [ | intro H].
- eapply MP.
  + remember (□ (# 1 ∨ # 2) → ¬ □ ¬ # 1 ∨ ¬ □ ¬ # 2) as φ.
    do 2 (apply extCKH_Deduction_Theorem).
    eapply MP.
    * apply extCKH_Deduction_Theorem.
      eapply MP.
      -- eapply MP ; [apply Ax ; left ; right ; eapply Kb ; reflexivity | ].
         apply extCKH_monot with (Empty_set _) ; [ | intros A HA ; inversion HA ].
         apply Nec. apply extCKH_Deduction_Theorem.
         apply MP with ⊤.
         ++ apply Id ; right ; apply In_singleton.
         ++ apply prv_Top.
      -- eapply MP ;  [apply Ax ; right ; left ; eexists ; eexists ; right ; reflexivity | ].
         apply Id ; right ; apply In_singleton.
    * eapply MP ; [ eapply MP ; [ apply Imp_trans | apply Id ; left ; right ; subst ; apply In_singleton ]| apply Id ; right ; apply In_singleton].
  + do 2 (apply extCKH_Deduction_Theorem). eapply MP ; [ apply extCKH_Deduction_Theorem | ].
    * apply extCKH_monot with  (Singleton form (◊ (# 1 ∨ # 2))).
      -- eapply MP ; [ | eapply MP ; [ apply Ax ; right ; left ; eexists ; eexists ; left ; reflexivity | apply Id ; apply In_singleton ] ].
         apply extCKH_Deduction_Theorem.
         eapply ND_OrE ; [ apply Id ; right ; apply In_singleton | apply extCKH_Deduction_Theorem | apply extCKH_Deduction_Theorem ].
         ++ apply ND_OrI1. apply extCKH_Deduction_Theorem.
            eapply MP ; [ apply Ax ; right ; right ; reflexivity | ].
            apply extCKH_monot with (Union _  (fun x => (exists B, In _ (Singleton _ (¬ # 1)) B /\ x = Box B)) (Singleton _ (◊ # 1))).
            ** apply Diam_rule. eapply MP ; [ apply Id ; left ; apply In_singleton | apply Id ; right ; apply In_singleton].
            ** intros A HA ; inversion HA ; subst.
               --- inversion H ; subst. destruct H0 ; subst. inversion H0 ; subst. right ; split.
               --- left ; right ; auto.
         ++ apply ND_OrI2. apply extCKH_Deduction_Theorem.
            eapply MP ; [ apply Ax ; right ; right ; reflexivity | ].
            apply extCKH_monot with (Union _  (fun x => (exists B, In _ (Singleton _ (¬ # 2)) B /\ x = Box B)) (Singleton _ (◊ # 2))).
            ** apply Diam_rule. eapply MP ; [ apply Id ; left ; apply In_singleton | apply Id ; right ; apply In_singleton].
            ** intros A HA ; inversion HA ; subst.
               --- inversion H ; subst. destruct H0 ; subst. inversion H0 ; subst. right ; split.
               --- left ; right ; auto.
      -- intros A HA ; inversion HA ; subst. right ; split.
    * apply extCKH_monot with (Union _  (fun x => (exists B, In _ (Singleton _ (# 1 ∨ # 2)) B /\ x = Box B)) (Singleton _ (◊ ⊤))).
      -- apply Diam_rule. apply Id ; left ; split.
      -- intros A HA ; inversion HA ; subst.
        ++ inversion H. destruct H0 ; subst. inversion H0 ; subst. right ; split.
        ++ left ; right ; auto.
- apply extCKH_Detachment_Theorem in H. apply CKIdbNd_Soundness in H.
  assert (~ forces tbM (false,false,false) (□ # 0)).
  { intro H0. cbn in H0. pose (H0 (false,false,false) I (false,false,true) I) as p ; cbn in p ; auto. }
  apply H0. apply H ; auto.
  split ; [apply suff_impl_Idb ; apply tbF_Idb_Nd | apply suff_impl_Nd ; apply tbF_Idb_Nd].
  intros ψ H1 ; cbn in *. inversion H1 ; subst.
  + inversion H2.
  + inversion H2 ; subst. clear H1 H2. intros w iw Hw v iwv u mvu ; cbn.
    destruct w as [[b0 b1] b2] eqn:E0 ; destruct v as [[b3 b4] b5] eqn:E1 ; destruct u as [[b6 b7] b8] eqn:E2;
    destruct b0,b1,b2,b3,b4,b5,b6,b7,b8 ; cbn ; cbn in iw,iwv,mvu ; auto ; try contradiction.
    assert (forces tbM (false, true, false) (¬ □ ¬ # 1 ∨ ¬ □ ¬ # 2)).
    { apply Hw ; auto. intros. destruct v0 as [[b9 b10] b11] eqn:E3 ; destruct u0 as [[b12 b13] b14] eqn:E4 ;
    destruct b9,b10,b11,b12,b13,b14 ; cbn ; cbn in * ; auto ; try contradiction. }
    destruct H1.
    * pose (H1 (true,false,true) I) ; cbn in f.
      enough ((true, false, true) = (true, true, true)) ; [discriminate | apply f].
      intros [[b0 b1] b2] H2 [[b3 b4] b5] H3 [[b6 b7] b8] H4 H5.
      destruct b0,b1,b2,b3,b4,b5,b6,b7,b8 ; cbn in H2,H3,H4,H5 ; auto ; try contradiction.
      destruct H5 ; discriminate.
    * pose (H1 (true,true,false) I) ; cbn in f.
      enough ((true, true, false) = (true, true, true)) ; [discriminate | apply f].
      intros [[b0 b1] b2] H2 [[b3 b4] b5] H3 [[b6 b7] b8] H4 H5.
      destruct b0,b1,b2,b3,b4,b5,b6,b7,b8 ; cbn in H2,H3,H4,H5 ; auto ; try contradiction.
      destruct H5 ; discriminate.
Qed.

End IK_not_conserv_CKIdbNd.



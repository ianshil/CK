Require Import List.
Export ListNotations.
Require Import Arith.
Require Import Ensembles.
Require Import Bool.
Require Import Btauto.

Require Import im_syntax.
Require Import CKH_export.
Require Import kripke_export.
Require Import CK_soundness.

Section negboxbot_negneg_box.

(* The logic CK + Idb + Ndb proves the following formula. *)

Lemma negboxbot_negneg_box_prv : forall Γ φ, CKIdbNdbH_prv Γ ((¬ □ ⊥) → (¬ ¬ □ φ) → □ ¬ ¬ φ).
Proof.
intros.
assert (CKIdbNdbH_prv Γ ((□ φ) → ((◊ ¬ φ) → (□ ⊥)))).
{ eapply MP. eapply MP. apply Imp_trans.
  - Unshelve. 2: exact (□ ¬ ¬ φ). eapply MP. apply Ax ; left ; right ; eapply Kb ; reflexivity.
    apply Nec. apply extCKH_Deduction_Theorem. apply extCKH_Deduction_Theorem.
    eapply MP. apply Id. right ; apply In_singleton. apply Id ; left ; right ; apply In_singleton.
  - eapply MP. eapply MP. apply Imp_trans. Unshelve. 3: exact ((◊ (¬ φ)) → (◊ ⊥)).
    + apply Ax ; left ; right ; eapply Kd ; reflexivity.
    + apply extCKH_Deduction_Theorem. eapply MP. eapply MP. apply Imp_trans.
       apply Id ; right ; apply In_singleton.
       apply Ax ; right ; right ; auto. }
assert (CKIdbNdbH_prv Γ ((¬ (¬ (□ φ))) → ((¬ □ ⊥) → (¬ ◊ ¬ φ)))).
repeat apply extCKH_Deduction_Theorem. eapply MP. apply Id ; left ; left ; right ; apply In_singleton.
apply extCKH_Deduction_Theorem. eapply MP. apply Id ; left ; left ; right ; apply In_singleton.
repeat apply extCKH_Detachment_Theorem in H.
apply (extCKH_monot _ _ _ H). intros A HA. inversion HA ; subst.
inversion H0 ; subst. left ; left ; left ; left ; auto. right ; auto.
left ; right ; auto.
apply extCKH_Deduction_Theorem. apply extCKH_Deduction_Theorem.
eapply MP. apply Ax ; right ; left ; eexists ; eexists ; reflexivity.
repeat  apply extCKH_Deduction_Theorem. eapply MP.
apply EFQ. apply extCKH_Detachment_Theorem.
apply extCKH_Detachment_Theorem in H0.
apply extCKH_Detachment_Theorem in H0.
apply (extCKH_monot _ _ _ H0). intros A HA. inversion HA ; subst.
inversion H1 ; subst. left ; left ; auto. right ; auto.
left ; right ; auto.
Qed.

End negboxbot_negneg_box.





Section CKIdbNdb_not_conserv_CK.

(* The diamond free fragment of CK + Idb + Ndb extends the one of CK. *)

Theorem diam_free_ext_CKIdbNdb_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ -> CKIdbNdbH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (fun x => False) ; auto. intros A F ; contradiction.
Qed.

(* We proceed to show that this extension is strict, by proving that the formula
    in the section negboxbot_negneg_box is not validated in the class of all frames.
    We thus need to provide a countermodel for it. *)

(* Intuitionistic relation *)

Definition obireach (ob0 ob1 : option (bool * bool)) : Prop :=
  match ob0 with
  | None => match ob1 with
                   | None => True
                   | _ => False
                   end
  | Some b0 => match ob1 with
                   | None => False
                   | Some b1 => if eqb (fst b0) (fst b1) then (if eqb (snd b0) (snd b1) then True else False) else
                                            if fst b1 then (if snd b1 then False else if eqb (snd b0) (snd b1) then True else False) else False
                   end
  end.

Lemma obireach_refl b : obireach b b.
Proof.
unfold obireach ; destruct b ; repeat rewrite eqb_reflx ; cbn ; auto.
Qed.

Lemma obireach_trans u v w: obireach u v -> obireach v w -> obireach u w.
Proof.
intros ; unfold obireach in *. destruct w ; destruct v ; destruct u ; cbn in * ; auto ; try contradiction.
destruct p ; destruct p0 ; destruct p1 ; cbn in * ; auto.
destruct (eqb b3 b1) eqn:E0; destruct (eqb b4 b2) eqn:E1; destruct (eqb b1 b) eqn:E2;
destruct (eqb b2 b0) eqn:E3; destruct (eqb b3 b) eqn:E4; destruct (eqb b4 b0) eqn:E5;
cbn in * ; try apply eqb_prop in E0 ; try apply eqb_prop in E1 ; try apply eqb_prop in E2 ;
try apply eqb_prop in E3 ; try apply eqb_prop in E4 ; try apply eqb_prop in E5 ; subst ;
firstorder. 1,3,4,5,9,10,11: destruct b0 ; cbn in E5 ; discriminate.
destruct b ; cbn in E4 ; discriminate. destruct b ; cbn in E2 ; discriminate.
1,4:destruct b0 ; cbn in E3 ; discriminate. destruct b0 ; cbn in E5 ; discriminate.
1,4,5,6,7:destruct b,b1 ; cbn in * ; auto.
1,4,5: destruct b2 ; cbn in E0 ; discriminate.
1,5: destruct b0 ; cbn in E1 ; discriminate. destruct b0 ; auto.
contradiction. destruct b ; cbn in E0 ; discriminate.
Qed.

Lemma obireach_expl u : obireach None u -> u = None.
Proof.
intros. unfold obireach in H ; destruct u ; cbn in * ; auto ; try contradiction.
Qed.

(* Modal relation *)

Definition obmreach (ob0 ob1 : option (bool * bool)) : Prop :=
  match ob0 with
  | None => match ob1 with
                   | None => True
                   | _ => False
                   end
  | Some b0 => match ob1 with
                   | None => False
                   | Some b1 => if fst b1 then (if snd b1 then (if fst b0 then (if snd b0 then False else True) else False) else False) else
                                            if negb (fst b0) then (if negb (snd b0) then (if negb (fst b1) then (if snd b1 then True else False) else False) else False) else False
                   end
  end.

Lemma obmreach_expl u : obmreach None u <-> u = None.
Proof.
split ; unfold obmreach ; intro ; destruct u ; cbn in * ; subst ; auto ; try contradiction.
inversion H.
Qed.

(* We can define a frame. *)

Instance obF : frame :=
      {|
        nodes := option (bool * bool) ;
        expl:= (@None (bool * bool)) ;

        ireachable := obireach ;
        ireach_refl := obireach_refl ;
        ireach_tran := obireach_trans ;
        ireach_expl := obireach_expl  ;

        mreachable := obmreach  ;
        mreach_expl := obmreach_expl  ;
      |}.

(* We define a valuation. *)

Definition obval (ob : option (bool * bool)) (p : nat) := 
  match ob with
  | None => True
  | Some b => if fst b then (if snd b then True else False) else False
  end.

Lemma obval_persist : forall u v, obireach u v -> forall (p : nat), obval u p -> obval v p.
Proof.
intros. unfold obval in *.
destruct u ; destruct v ; cbn in * ; auto ; try contradiction.
destruct p0 ; destruct p1 ; destruct b ; destruct b0 ; destruct b1 ; destruct b2 ; cbn in * ; auto.
Qed.

Lemma obval_expl  : forall p, obval expl p.
Proof.
intros. unfold obval. destruct expl eqn:E ; auto.
unfold expl in E. inversion E.
Qed.

(* Finally we can define a model. *)

Instance obM : model :=
      {|
        fra := obF ;

        val := obval  ;
        persist :=  obval_persist ;
        val_expl :=  obval_expl
      |}.

(* We use this model to show that the extension is strict. *)

Theorem diam_free_strict_ext_CKIdbNdb_CK : 
               CKIdbNdbH_prv (Empty_set _) ((¬ □ ⊥) → (¬ ¬ □ (#0)) → □ ¬ ¬ (#0)) /\
                ~ CKH_prv (Empty_set _) ((¬ □ ⊥) → (¬ ¬ □ (#0)) → □ ¬ ¬ (#0)).
Proof.
split.
- apply negboxbot_negneg_box_prv.
- intro. repeat apply extCKH_Detachment_Theorem in H. apply CK_Soundness in H.
  assert (forces obM (Some (false,false)) ((¬ (□ ⊥)))).
  { intros b ifb Hb. destruct b ; cbn in * ; unfold obireach in ifb ; cbn in ifb ; auto.
    destruct p ; cbn in *. destruct b ; cbn in *.
    - destruct b0 ; cbn in * ; auto ; try contradiction.
      assert (obmreach (Some (true, false)) (Some (true, true))) ; cbn ; auto.
      pose (Hb (Some (true,false)) I (Some (true,true)) H0). inversion e.
    - destruct b0 ; cbn in * ; auto ; try contradiction.
      assert (obmreach (Some (false, false)) (Some (false, true))) ; cbn ; auto.
      pose (Hb (Some (false,false)) I (Some (false,true)) H0). inversion e. }
  assert (forces obM (Some (false,false)) (¬ (¬ (□ (#0))))).
  { intros b ifb Hb. exfalso. destruct b ; cbn in * ; unfold obireach in ifb ; cbn in ifb ; auto.
    destruct p ; cbn in *. destruct b ; cbn in *.
    - destruct b0 ; cbn in * ; auto ; try contradiction.
      assert (obmreach (Some (true, false)) (Some (true, true))) ; cbn ; auto.
      assert (forall v : option (bool * bool), obireach (Some (true, false)) v ->
      forall u : option (bool * bool), obmreach v u -> forces obM u (#0)).
      { intros. destruct v ; cbn in * ; try contradiction.
        destruct p ; cbn in * ; try contradiction.
        destruct b ; destruct b0 ; cbn in * ; auto ; try contradiction.
        destruct u ; cbn in * ; auto ; try contradiction. }
      pose (Hb (Some (true,false)) I H2). inversion e.
    - destruct b0 ; cbn in * ; auto ; try contradiction.
      assert (obmreach (Some (true, false)) (Some (true, true))) ; cbn ; auto.
      assert (forall v : option (bool * bool), obireach (Some (true, false)) v ->
      forall u : option (bool * bool), obmreach v u -> forces obM u (#0)).
      { intros. destruct v ; cbn in * ; try contradiction.
        destruct p ; cbn in * ; try contradiction.
        destruct b ; destruct b0 ; cbn in * ; auto ; try contradiction.
        destruct u ; cbn in * ; auto ; try contradiction. }
      pose (Hb (Some (true,false)) I H2). inversion e. }
  assert (~ forces obM (Some (false,false)) (□ ¬ ¬ (#0))).
  { intro.
    assert ((forall v : option (bool * bool),
    match v with
    | Some b1 =>
        if if fst b1 then false else true
        then if if snd b1 then true else false then True else False
        else
         if fst b1
         then
          if snd b1
          then False
          else if if snd b1 then true else false then True else False
         else False
    | None => False
    end -> obval v 0 -> v = None)).
    { intros. destruct v ; cbn in * ; auto. destruct p ; cbn in * ; try contradiction.
      destruct b ; destruct b0 ; cbn in * ; auto ; try contradiction. }
    pose (H2 (Some (false,false)) I (Some (false,true)) I (Some (false,true)) I H3) ; cbn in f. inversion f. }
  apply H2. apply H ; auto. intros. inversion H3 ; subst. inversion H4 ; subst.
  inversion H5. inversion H5 ; subst ; auto. inversion H4 ; subst ; auto.
Qed.

End CKIdbNdb_not_conserv_CK.






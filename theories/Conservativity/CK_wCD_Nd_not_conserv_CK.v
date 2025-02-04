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
Require Import CK_Idb_Ndb_not_conserv_CK.

Section wCDb_prv.

(* The logic CK + wCD + Nd proves the following formula. *)

Lemma CKwCDNd_prv_wCDb : forall Γ φ ψ, CKwCDNdH_prv Γ ((☐(φ ∨ ψ)) --> ((¬ ☐¬ φ) --> (☐ψ)) -->  ☐ψ).
Proof.
intros.
repeat apply extCKH_Deduction_Theorem.
eapply MP. eapply MP.
apply Ax ; right ; left ; eexists ; eexists ; reflexivity.
apply Id ; left ; right ; split.
apply extCKH_Deduction_Theorem.
eapply MP. apply Id ; left ; right ; split.
apply extCKH_Deduction_Theorem.
eapply MP. apply Ax ; right ; right ; reflexivity.
eapply MP. eapply MP.
apply Ax ; left ; right ; eapply Kd ; reflexivity.
apply Id ; right ; split.
apply Id ; left ; right ; split.
Qed.

End wCDb_prv.





Section CKwCDNd_not_conserv_CK.

(* The diamond free fragment of CK + wCD + Nd extends the one of CK. *)

Theorem diam_free_ext_CKwCDNd_CK : forall Γ φ, (forall ψ, (Γ ψ \/ φ = ψ) -> diam_free ψ) ->
              CKH_prv Γ φ -> CKwCDNdH_prv Γ φ.
Proof.
intros. apply more_AdAx_more_prv with (fun x => False) ; auto. intros A F ; contradiction.
Qed.

(* We proceed to show that this extension is strict, by proving that the formula
    in the section wCDb_prv is not validated in the class of all frames. We thus
    need to provide a countermodel for it. The frame of the model is the one from
    the file CK_Idb_Ndb_not_conserv_CK. Then, we simply need to define a valuation. *)

Definition obval' (ob : option (bool * bool)) (p : nat) :=
  match ob with
  | None => True
  | Some b => match p with
                      | 0 => if fst b then False else (if snd b then True else False)
                      | S n => if fst b then (if snd b then True else False) else False
                      end
  end.

Lemma obval_persist' : forall u v, obireach u v -> forall (p : nat), obval' u p -> obval' v p.
Proof.
intros. unfold obval' in *.
destruct u ; destruct v ; cbn in * ; auto ; try contradiction.
destruct p0 ; destruct p1 ; destruct b ; destruct b0 ; destruct b1 ; destruct b2 ; destruct p ; cbn in * ; auto.
Qed.

Lemma obval_expl'  : forall p, obval' (@expl obF) p.
Proof.
intros. unfold obval'. destruct expl eqn:E ; auto.
inversion E.
Qed.

(* Finally we can define the model. *)

Instance obM' : model :=
      {|
        fra := obF ;

        val := obval'  ;
        persist :=  obval_persist' ;
        val_expl :=  obval_expl'
      |}.

(* We use this model to show that the extension is strict. *)

Theorem diam_free_strict_ext_CKwCDNd_CK :
                  CKwCDNdH_prv (Empty_set _) ((☐((#0) ∨ (#1))) --> ((¬ ☐¬ (#0)) --> (☐(#1))) -->  ☐(#1)) /\
                  ~ CKH_prv (Empty_set _) ((☐((#0) ∨ (#1))) --> ((¬ ☐¬ (#0)) --> (☐(#1))) -->  ☐(#1)).
Proof.
split.
- apply CKwCDNd_prv_wCDb.
- intro. repeat apply extCKH_Detachment_Theorem in H. apply CK_Soundness in H.
  assert (forces obM' (Some (false,false)) (☐ # 0 ∨ # 1)).
  { intros ob0 ifob0 ob1 mfob1.
    destruct ob0 eqn:E0; unfold obireach in ifob0 ; cbn in ifob0 ; auto ; try contradiction.
    destruct ob1 eqn:E1; unfold obmreach in mfob1 ; cbn in mfob1 ; auto ; try contradiction.
    destruct p,p0 ; cbn in *. destruct b1 ; cbn in * ; auto. destruct b2 ; cbn in * ; auto.
    left. destruct b ; cbn in * ; auto ; try contradiction. destruct b0 ; cbn in * ; auto ; try contradiction. }
  assert (forces obM' (Some (false,false)) ((¬ (☐ (¬ # 0))) --> (☐ # 1))).
  { intros ob0 ifob0 Hob0 ob1 iob0ob1 ob2 mob1ob2.
    destruct ob0 eqn:E0; unfold obireach in ifob0 ; cbn in ifob0 ; auto ; try contradiction.
    destruct ob1 eqn:E1; unfold obireach in iob0ob1 ; cbn in iob0ob1 ; auto ; try contradiction.
    destruct ob2 eqn:E2; unfold obmreach in mob1ob2 ; cbn in mob1ob2 ; auto ; try contradiction.
    destruct p,p0,p1 ; cbn ; cbn in mob1ob2, iob0ob1, ifob0.
    destruct b3 ; cbn in * ; auto ; try contradiction. destruct b4 ; cbn in * ; auto ; try contradiction.
    destruct b1 ; cbn in * ; auto ; try contradiction. destruct b2 ; cbn in * ; auto ; try contradiction.
    destruct b4 ; cbn in * ; auto ; try contradiction. destruct b ; cbn in * ; auto ; try contradiction.
    destruct b0 ; cbn in * ; auto ; try contradiction.
    assert (J: (forall v : option (bool * bool),
    match v with
    | Some b1 =>
        if if fst b1 then true else false
        then if if snd b1 then false else true then True else False
        else
         if fst b1
         then
          if snd b1 then False else if if snd b1 then false else true then True else False
         else False
    | None => False
    end ->
    forall u : option (bool * bool),
    obmreach v u ->
    forall v0 : option (bool * bool), obireach u v0 -> obval' v0 0 -> v0 = None)).
    { intros.
      destruct u eqn:E3 ; unfold obireach in H3 ; cbn in H3 ; auto ; try contradiction.
      destruct v0 eqn:E4 ; unfold obmreach in H2 ; cbn in H2 ; auto ; try contradiction.
      destruct v eqn:E5 ; unfold obmreach in H2 ; cbn in H2 ; auto ; try contradiction.
      destruct p,p0,p1 ; cbn in *.
      destruct b1 ; cbn in * ; auto ; try contradiction. destruct b ; cbn in * ; auto ; try contradiction.
      destruct b2 ; cbn in * ; auto ; try contradiction. destruct b3 ; cbn in * ; auto ; try contradiction.
      destruct v0 eqn:E4 ; unfold obmreach in H2 ; cbn in H2 ; auto ; try contradiction. }
    pose (Hob0 (Some (true,false)) I J) ; cbn in e. inversion e. }
  assert (~ forces obM' (Some (false,false)) (☐ # 1)).
  { intro. pose (H2 (Some (false,false)) I (Some (false,true)) I) ; contradiction. }
  apply H2. apply H ; auto. intros. inversion H3 ; subst. inversion H4 ; subst.
  inversion H5. inversion H5 ; subst ; auto. inversion H4 ; subst ; auto.
Qed.

End CKwCDNd_not_conserv_CK.






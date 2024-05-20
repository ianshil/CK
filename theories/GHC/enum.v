Require Import Lia.
Require Import Coq.Arith.Cantor.
Require Import Coq.Logic.ConstructiveEpsilon.

Require Import im_syntax.
Require Import CKH logic.

Require Import List.
Import ListNotations.

Fixpoint L_enum n :=
  match n with
  | 0 => [Bot]
  | S n => let LL := list_prod (L_enum n) (L_enum n)
          in L_enum n ++ [Var n]
                    ++ map (fun p => And (fst p) (snd p)) LL
                    ++ map (fun p => Or (fst p) (snd p)) LL
                    ++ map (fun p => Imp (fst p) (snd p)) LL
                    ++ map (fun p => Box (fst p)) LL
                    ++ map (fun p => Diam (fst p)) LL
  end.

Lemma L_enum_cumulative n m :
  n <= m -> incl (L_enum n) (L_enum m).
Proof.
  induction 1.
  - apply incl_refl.
  - eapply incl_tran; try apply IHle. cbn. apply incl_appl. apply incl_refl.
Qed.

Lemma L_enum_exhaustive A :
  exists n, In A (L_enum n).
Proof.
  induction A.
  - exists (S n). cbn. apply in_app_iff. right. now left.
  - exists 0. cbn. tauto.
  - destruct IHA1 as [n Hn], IHA2 as [m Hm]. exists (S (n + m)). cbn. apply in_app_iff.
    right. right. apply in_app_iff. left.
    apply in_map_iff. exists (A1, A2). cbn. split; trivial. apply in_prod.
    + eapply L_enum_cumulative; try apply Hn. lia.
    + eapply L_enum_cumulative; try apply Hm. lia.
  - destruct IHA1 as [n Hn], IHA2 as [m Hm]. exists (S (n + m)). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists (A1, A2). cbn. split; trivial. apply in_prod.
    + eapply L_enum_cumulative; try apply Hn. lia.
    + eapply L_enum_cumulative; try apply Hm. lia.
  - destruct IHA1 as [n Hn], IHA2 as [m Hm]. exists (S (n + m)). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. left.
    apply in_map_iff. exists (A1, A2). cbn. split; trivial. apply in_prod.
    + eapply L_enum_cumulative; try apply Hn. lia.
    + eapply L_enum_cumulative; try apply Hm. lia.
  - destruct IHA as [n Hn]. exists (S n). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
     apply in_app_iff. left. apply in_map_iff. exists (A,A). cbn. split; trivial. apply in_prod ; auto.
  - destruct IHA as [n Hn]. exists (S n). cbn. apply in_app_iff.
    right. right. apply in_app_iff. right. apply in_app_iff. right. apply in_app_iff. right.
     apply in_app_iff. right. apply in_map_iff. exists (A,A). cbn. split; trivial. apply in_prod ; auto.
Qed.

Definition form_enum n :=
  let (k, l) := of_nat n in nth k (L_enum l) Bot.

Lemma form_enum_sur A :
  exists n, form_enum n = A.
Proof.
  destruct (L_enum_exhaustive A) as [l Hl].
  destruct (In_nth (L_enum l) A Bot Hl) as [k Hk].
  exists (to_nat (k, l)). unfold form_enum. rewrite cancel_of_to. apply Hk.
Qed.

Definition form_index' A :
  { n | form_enum n = A }.
Proof.
  apply constructive_indefinite_ground_description_nat.
  - decide equality. decide equality.
  - apply form_enum_sur.
Defined.

Definition form_index A :=
  proj1_sig (form_index' A).

Lemma form_enum_index A :
  form_enum (form_index A) = A.
Proof.
  unfold form_index. apply proj2_sig.
Qed.

Lemma form_index_inj A B :
  form_index A = form_index B -> A = B.
Proof.
  intros H. rewrite <- (form_enum_index A), <- (form_enum_index B). now rewrite H.
Qed.


(* Enumerability of proofs *)

Fixpoint L_ded (f : nat -> option form) n : list form :=
  match n with 
  | 0 => []
  | S n => let LL := list_prod (L_enum n) (L_enum n)
          in let LLL := list_prod (list_prod (L_enum n) (L_enum n)) (L_enum n)
          in L_ded f n ++ match f n with Some phi => [phi] | None => [] end
                   ++ map (fun a => fst a --> snd a --> fst a) LL
                   ++ map (fun a => ((fst (fst a)) --> ((snd (fst a)) --> (snd a))) --> (((fst (fst a)) --> (snd (fst a))) --> ((fst (fst a)) --> (snd a)))) LLL
                   ++ map (fun a => (fst a) --> (Or (fst a) (snd a))) LL
                   ++ map (fun a => (snd a) --> (Or (fst a) (snd a))) LL
                   ++ map (fun a => ((fst (fst a)) --> (snd a)) --> (((snd (fst a)) --> (snd a)) --> ((Or (fst (fst a)) (snd (fst a))) --> (snd a)))) LLL
                   ++ map (fun a => (And (fst a) (snd a)) --> (fst a)) LL 
                   ++ map (fun a => (And (fst a) (snd a)) --> (snd a)) LL 
                   ++ map (fun a => ((fst (fst a)) --> (snd (fst a))) --> (((fst (fst a)) --> (snd a)) --> ((fst (fst a)) --> (And (snd (fst a)) (snd a))))) LLL
                   ++ map (fun a => Bot --> a) (L_enum n)
                   ++ map (fun a => Box ((fst a) --> (snd a)) --> (Box (fst a) --> Box (snd a))) LL
                   ++ map (fun a => Box ((fst a) --> (snd a)) --> (Diam (fst a) --> Diam (snd a))) LL
                   ++ map (fun a => (Box a)) (L_ded (fun _ => None) n)
                   ++ map (fun a => match a with Imp phi psi => if existsb (fun b => if eq_dec_form b phi then true else false) (L_ded f n) then psi else a | _ => a end) (L_ded f n)
  end.

Lemma L_ded_cumulative A n m :
  n <= m -> incl (L_ded A n) (L_ded A m).
Proof.
  induction 1.
  - apply incl_refl.
  - eapply incl_tran; try apply IHle. cbn. apply incl_appl. apply incl_refl.
Qed.

Lemma L_ded1 f phi :
  CKH_prv (fun psi => exists n, f n = Some psi) phi -> exists n, In phi (L_ded f n).
Proof.
  enough (forall X A, CKH_prv X A -> forall phi f, phi = A -> (forall psi, (exists n, f n = Some psi) <-> X psi) -> exists n, In phi (L_ded f n)).
  { intros H'. apply (H (fun psi : form => exists n, f n = Some psi) phi); cbn; tauto. }
  clear f phi. intros X A. induction 1; intros phi f -> HG.
  - apply HG in H. destruct H ; subst. exists (S x). cbn.
    apply in_app_iff. right. apply in_app_iff. left. rewrite H. now left.
  - inversion H; subst.
    { destruct H0 ; subst.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive A0) as [n2 H2].
      exists (S (n1 + n2)). cbn. do 2 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive C) as [n2 H2].
      destruct (L_enum_exhaustive A0) as [n3 H3].
      exists (S (n1 + n2 + n3)). cbn. do 3 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B, C). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive A0) as [n2 H2].
      exists (S (n1 + n2)). cbn. do 4 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive A0) as [n2 H2].
      exists (S (n1 + n2)). cbn. do 5 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive C) as [n2 H2].
      destruct (L_enum_exhaustive A0) as [n3 H3].
      exists (S (n1 + n2 + n3)). cbn. do 6 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B, C). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive A0) as [n2 H2].
      exists (S (n1 + n2)). cbn. do 7 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive A0) as [n2 H2].
      exists (S (n1 + n2)). cbn. do 8 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive C) as [n2 H2].
      destruct (L_enum_exhaustive A0) as [n3 H3].
      exists (S (n1 + n2 + n3)). cbn. do 9 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B, C). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive A0) as [n1 H1].
      exists (S n1). cbn. do 10 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists A0. now split. }
    { destruct H0 ; subst.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive A0) as [n2 H2].
      exists (S (n1 + n2)). cbn. do 11 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia.
    + destruct (L_enum_exhaustive B) as [n1 H1].
      destruct (L_enum_exhaustive A0) as [n2 H2].
      exists (S (n1 + n2)). cbn. do 12 (apply in_app_iff; right). apply in_app_iff. left.
      apply in_map_iff. exists (A0, B). split; trivial. repeat rewrite in_prod_iff.
      repeat split; eapply L_enum_cumulative; try eassumption; lia. }
  - destruct (IHCKH_prv1 (A --> B) f) ; auto. destruct (IHCKH_prv2 A f) ; auto.
    exists (S (x + x0)). cbn. do 13 (apply in_app_iff; right). apply in_app_iff ; right.
        apply in_map_iff. exists (A --> B).
        assert (existsb (fun b : form => if eq_dec_form b A then true else false) (L_ded f (x + x0)) = true) as ->.
        { apply existsb_exists. exists A. destruct eq_dec_form; try tauto.
          split; trivial. eapply L_ded_cumulative; try apply H2. lia. }
        split; trivial. apply L_ded_cumulative with x ; auto ; try apply H3. lia.
  - destruct (IHCKH_prv A (fun _ : nat => @None form)) ; auto.
    + intros psi; split; intros []. discriminate.
    + exists (S x). cbn. do 13 (apply in_app_iff; right).
      apply in_app_iff. left. apply in_map_iff. exists A ; subst;  auto.
Qed.

Lemma L_ded2 f phi n :
  In phi (L_ded f n) -> CKH_prv (fun psi => exists n, f n = Some psi) phi.
Proof.
  induction n in phi, f |- *.
  - intros [].
  - cbn. rewrite !in_app_iff. intros [|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]].
    + now apply IHn.
    + destruct f eqn : Hf; try now destruct H. destruct H as [<-|[]] ; subst.
      constructor 1. now exists n.
    + apply in_map_iff in H as [[B C][<- HP]].
      constructor 2. left. cbn. econstructor 1. eauto.
    + apply in_map_iff in H as [[[B C]D][<- HP]].
      constructor 2. left. cbn. econstructor 2. eauto.
    + apply in_map_iff in H as [[B C][<- HP]].
      constructor 2. left. cbn. econstructor 3. eauto.
    + apply in_map_iff in H as [[B C][<- HP]].
      constructor 2. left. cbn. econstructor 4. eauto.
    + apply in_map_iff in H as [[B C][<- HP]].
      constructor 2. cbn. left. econstructor 5. eauto.
    + apply in_map_iff in H as [[B C][<- HP]].
      constructor 2. left. cbn. econstructor 6. eauto.
    + apply in_map_iff in H as [[B C][<- HP]].
      constructor 2. left. cbn. econstructor 7. eauto.
    + apply in_map_iff in H as [[[B C]D][<- HP]].
      constructor 2. left. cbn. econstructor 8. eauto.
    + apply in_map_iff in H as [B [<- HP]].
      constructor 2. left. cbn. econstructor 9. eauto.
    + apply in_map_iff in H as [B [<- HP]].
      constructor 2. right. cbn. econstructor 1. eauto.
    + apply in_map_iff in H as [B [<- HP]].
      constructor 2. right. cbn. econstructor 2. eauto.
    + apply in_map_iff in H as [A [<- HA]].
      econstructor 4.
      * apply IHn in HA. eapply CKH_comp in HA; try apply HA. intros B []. discriminate.
    + apply in_map_iff in H as [A [<- HA]]. destruct A; try now apply IHn.
      destruct existsb eqn : He; try now apply IHn.
      apply existsb_exists in He as [A' [H1 H2]].
      destruct eq_dec_form; try discriminate; subst.
      econstructor 3.
      * apply IHn in HA. exact HA.
      * apply IHn in H1. exact H1.
Qed.

Definition form_enum_ded n f :=
  let (k, l) := of_nat n in nth_error (L_ded f l) k.

Lemma form_enum_ded_spec f :
  forall phi, CKH_prv (fun psi => exists n, f n = Some psi) phi <-> exists n, form_enum_ded n f = Some phi.
Proof.
  intros phi. split; intros H.
  - apply L_ded1 in H as [l Hl]. apply In_nth_error in Hl as [k Hk].
    exists (to_nat (k, l)). unfold form_enum_ded. rewrite cancel_of_to. apply Hk.
  - destruct H as [n Hn]. unfold form_enum_ded in Hn. destruct of_nat.
    apply nth_error_In in Hn. eapply L_ded2. apply Hn.
Qed.







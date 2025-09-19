From Stdlib Require Import List.
Export ListNotations.
From Stdlib Require Import Arith.
From Stdlib Require Import Ensembles.

Require Import im_syntax.

(* We define here the intuitionistic axioms. *)

Inductive IAxioms (F : form) : Prop :=
 | IA1 A B : F = (A → (B → A)) -> IAxioms F
 | IA2 A B C : F = ((A → (B → C)) → ((A → B) → (A → C))) -> IAxioms F
 | IA3 A B : F = (A → (A ∨ B)) -> IAxioms F
 | IA4 A B : F = (B → (A ∨ B)) -> IAxioms F
 | IA5 A B C : F = ((A → C) → ((B → C) → ((A ∨ B) → C))) -> IAxioms F
 | IA6 A B : F = ((A ∧ B) → A) -> IAxioms F
 | IA7 A B : F = ((A ∧ B) → B) -> IAxioms F
 | IA8 A B C : F = ((A → B) → ((A → C) → (A → (B ∧ C)))) -> IAxioms F
 | IA9 A : F = (⊥ → A) -> IAxioms F.

(* We then define the modal axioms. *)

Inductive MAxioms (F : form) : Prop :=
 | Kb A B : F = ((□ (A → B)) → ((□ A) → □ B)) -> MAxioms F
 | Kd A B : F = ((□ (A → B)) → ((◊A) → ◊B)) -> MAxioms F.

(* And join both set of axioms. *)

Definition Axioms (A : form) : Prop := IAxioms A \/ MAxioms A.

(* Here are additional specific axioms. *)

Definition Cd A B := (◊(A ∨ B))→  (◊A) ∨ (◊B).
Definition Idb A B := ((◊A) → (□B)) →  □(A → B).
Definition Nd := (◊⊥) → ⊥.
Definition Ndb := (◊⊥) → (□⊥).
Definition wCD A B := (□(A ∨ B)) → ((◊A) → (□B)) →  □ B.

(* We can then define the generalised Hilbert system for CK parametrised
    in a set of additional axioms. *)

Inductive extCKH_prv (AdAx: form -> Prop) : (form -> Prop) -> form -> Prop :=
  | Id Γ A : In _ Γ A -> extCKH_prv AdAx Γ A
  | Ax Γ A : (Axioms A \/ AdAx A) -> extCKH_prv AdAx Γ A
  | MP Γ A B : extCKH_prv AdAx Γ (A → B) ->  extCKH_prv AdAx Γ A -> extCKH_prv AdAx Γ B
  | Nec Γ A : extCKH_prv AdAx (Empty_set _) A -> extCKH_prv AdAx Γ (□ A).

(* We give names to some instances of the general definition above. *)

Definition CKH_prv := extCKH_prv (fun x => False).
(* One axiom. *)
Definition CKCdH_prv := extCKH_prv (fun x => exists A B, Cd A B = x).
Definition CKIdbH_prv := extCKH_prv (fun x => exists A B, Idb A B = x).
Definition WKH_prv := extCKH_prv (fun x => Nd = x).
Definition CKNdbH_prv := extCKH_prv (fun x => Ndb = x).
Definition CKwCDH_prv := extCKH_prv (fun x => exists A B, wCD A B = x).
(* Two axioms. *)
Definition CKCdIdbH_prv := extCKH_prv (fun x => exists A B, Cd A B = x \/ Idb A B = x).
Definition CKCdNdH_prv := extCKH_prv (fun x => (exists A B, Cd A B = x) \/ Nd = x).
Definition CKIdbNdH_prv := extCKH_prv (fun x => (exists A B, Idb A B = x) \/ Nd = x).
Definition CKCdNdbH_prv := extCKH_prv (fun x => (exists A B, Cd A B = x) \/ Ndb = x).
Definition CKIdbNdbH_prv := extCKH_prv (fun x => (exists A B, Idb A B = x) \/ Ndb = x).
Definition CKCdwCDH_prv := extCKH_prv (fun x => exists A B, Cd A B = x \/ wCD A B = x).
Definition CKwCDNdH_prv := extCKH_prv (fun x => (exists A B, wCD A B = x) \/ Nd = x).
(* Three axioms. *)
Definition CKCdIdbNdbH_prv := extCKH_prv (fun x => (exists A B, Cd A B = x \/ Idb A B = x) \/ Ndb = x).
Definition FIKH_prv := extCKH_prv (fun x => (exists A B, Cd A B = x \/ wCD A B = x) \/ Nd = x).
Definition IKH_prv := extCKH_prv (fun x => (exists A B, Cd A B = x \/ Idb A B = x) \/ Nd = x).


(* Require Import Logic.FunctionalExtensionality. *)

Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import ListSet.

From LMNTAL Require Export Util.

Definition AtomId := nat.
Definition ArgPos := nat.
Definition AtomNum := nat.
Definition Port: Type := AtomId * ArgPos.
Definition Edge := set Port.
Definition Graph: Type := AtomNum * (set Edge) * (list string).

(* Definition injective {A B} (f: A->B) :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.
Definition surjective {A B} (f: A->B) :=
  forall b, exists a, f a = b.
Definition bijective {A B} (f: A->B) :=
  injective f /\ surjective f. *)

Definition Geq_dec: forall x y : Graph, {x=y} +{x<>y}.
Proof.
  intros [[v1 e1] l1] [[v2 e2] l2].
  repeat decide equality.
Defined.

Definition Peq_dec: forall x y : Port, {x=y} +{x<>y}.
Proof.
  repeat decide equality.
Defined.

Definition Eeq_dec: forall x y : Edge, {x=y} +{x<>y}.
Proof.
  repeat decide equality.
Defined.

Definition swap_atomid_port (i1 i2: nat) (p: Port) := 
  match p with
  | (atomid, argpos) =>
    (if PeanoNat.Nat.eq_dec i1 atomid
      then i2 else atomid, argpos)
  end.

Definition swap_atomid_edge (i1 i2: nat) (e: Edge) :=
  set_map Peq_dec (swap_atomid_port i1 i2) e.

Definition swap_atomid_edges (i1 i2: nat) (e: set Edge) :=
  set_map Eeq_dec (swap_atomid_edge i1 i2) e.

Definition swap_atomid_labels (i1 i2: nat) (l: list string) :=
  swap i1 i2 l.

Definition swap_atomid (i1 i2: nat) (g: Graph) :=
  match g with (v, e, l) =>
    (v, swap_atomid_edges i1 i2 e, swap_atomid_labels i1 i2 l)
  end.

Definition swap_atomid_list l (G:Graph) :=
  fold_right (fun x g => match x with
                          | (i1, i2) => swap_atomid i1 i2 g
                          end) G l.

Definition isomorphic G G' := exists l, swap_atomid_list l G = G'.

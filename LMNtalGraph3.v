(* Require Import Logic.FunctionalExtensionality. *)

Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.
Import PeanoNat.Nat.
Open Scope nat_scope.

Require Import ListSet.

Require Import Logic.ProofIrrelevance.
Require Import Logic.FinFun.

From LMNTAL Require Export Util.

Definition AtomId (n:nat) :=  Fin.t n.
Definition ArgPos := nat.
Definition AtomNum := nat.
Definition Port (n:nat): Type := AtomId n * ArgPos.
(* Inductive Port := local (atomid: AtomId) (argpos: ArgPos) | free (name: string). *)
Definition Edge (n:nat) := set (Port n).
(* Inductive Edge := local (ps: set Port) | free (name: string) (p: Port). *)
Inductive Graph: Type := 
  graph (n:nat) (es:set (Edge n)) (l:list string).

(* Definition injective {A B} (f: A->B) :=
  forall a1 a2, f a1 = f a2 -> a1 = a2.
Definition surjective {A B} (f: A->B) :=
  forall b, exists a, f a = b.
Definition bijective {A B} (f: A->B) :=
  injective f /\ surjective f. *)

Definition Aeq_dec (n:nat): forall (x y : AtomId n), {x=y}+{x<>y}.
Proof.
  apply Vectors.Fin.eq_dec.
Defined. 

Definition Peq_dec (n:nat): forall (x y : Port n), {x=y} + {x<>y}.
Proof.
  repeat decide equality.
  apply Aeq_dec.
Defined.

Definition Eeq_dec (n:nat): forall (x y : Edge n), {x=y} + {x<>y}.
Proof.
  repeat decide equality.
  apply Aeq_dec.
Defined.

Definition Geq_dec: forall x y : Graph, {x=y} + {x<>y}.
Proof.
  intros [v1 e1 l1] [v2 e2 l2].
  destruct (eq_dec v1 v2).
  2: { right. unfold "<>". intros. inversion H. auto. }
  (* destruct (Eeq_dec e1 e2). *)
Admitted.

Check @set_map.

Definition iso_e (n:nat) (f:AtomId n -> AtomId n) (e:Edge n): Edge n := set_map (Peq_dec n) (fun a => match a with (i,j) => (f i, j) end) e.

Definition iso_es (n:nat) f es := set_map (Eeq_dec n) (iso_e n f) es.

Definition iso_l n f l: nth 

Definition iso_g f (G:Graph) := match G with
  (v, e, l) => (v, (iso_es n f e), (iso_l n (inverse f) l))
  end.

Definition isomorphic G G' := exists f, iso_g f G = G'.

(* Definition swap_atomid_port (i1 i2: nat) (p: Port) := 
  match p with
  | (atomid, argpos) =>
    (if PeanoNat.Nat.eq_dec i1 atomid
      then i2
      else if PeanoNat.Nat.eq_dec i2 atomid
      then i1
      else atomid, argpos)
  end.

Definition swap_atomid_edge (i1 i2: nat) (e: Edge) :=
  set_map Peq_dec (swap_atomid_port i1 i2) e.

Definition swap_atomid_edges (i1 i2: nat) (e: set Edge) :=
  set_map Eeq_dec (swap_atomid_edge i1 i2) e.

Definition swap_atomid_labels (i1 i2: nat) (l: list string) :=
  swap i1 i2 l.

Definition swap_atomid (i1 i2: nat) (g: Graph) :=
  match g with (v, e, l) =>
    if andb (i1 <? v) (i2 <? v) then
      (v, swap_atomid_edges i1 i2 e, swap_atomid_labels i1 i2 l)
    else g
  end.

Definition swap_atomid_list l (G:Graph) :=
  fold_right (fun x g => match x with
                          | (i1, i2) => swap_atomid i1 i2 g
                          end) G l.

Definition isomorphic G G' := exists l, swap_atomid_list l G = G'. *)


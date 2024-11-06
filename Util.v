Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Inductive seq := Empty | Seq (h:nat) (t : seq).

Fixpoint append l1 l2 :=
  match l1 with
  | Seq h t => Seq h (append t l2)
  | Empty => l2
  end.

Theorem seq_empty: forall xs, append xs Empty = xs.
Proof.
  intro xs. induction xs as [|h t IH].
  - auto.
  - simpl. f_equal. auto.
    (* rewrite IH. auto. *)
Qed.


Fixpoint subst_nth {A} n (x:A) l :=
  match l with 
  | h :: t => if PeanoNat.Nat.eq_dec n 0
              then x :: t
              else h :: (subst_nth (n-1) x t)
  | [] => []
  end.

(* Fixpoint swap l i j :=
  match l with
  | h :: t => if PeanoNat.Nat.eq_dec i 0
              then (nth (j-1) t 0) :: subst_nth (j-1) h t
              else h :: swap t (i-1) (j-1)
  | [] => []
  end. *)

Definition swap {A} i j (l: list A) :=
  let xi := nth_error l i in 
  let xj := nth_error l j in
  match xi, xj with
  | Some yi, Some yj => subst_nth i yj (subst_nth j yi l)
  | _, _ => l
  end.

Definition swap_list {A} (l: list (nat * nat)) (ls: list A) :=
  fold_right (fun x ls' => match x with
                           | (i1, i2) => swap i1 i2 ls'
                           end) ls l.

Require Import Coq.Logic.Eqdep_dec.
Lemma string_dec_refl x : string_dec x x = left eq_refl.
Proof.
  destruct (string_dec x x); [ apply f_equal | congruence ].
  apply UIP_dec, string_dec.
Qed.

Lemma nat_eq_dec_refl x : PeanoNat.Nat.eq_dec x x = left eq_refl.
Proof.
  destruct (PeanoNat.Nat.eq_dec x x).
  - f_equal. apply UIP_dec, PeanoNat.Nat.eq_dec.
  - congruence.
Qed.

Import PeanoNat.Nat.
Open Scope nat_scope.

(* https://stackoverflow.com/questions/62464821/how-to-make-an-inverse-function-in-coq *)
(* Require Import Coq.Logic.Description.
Require Import Coq.Logic.FunctionalExtensionality.

Definition injective {X Y : Set} (f : X -> Y) := forall x y, f x = f y -> x = y.
Definition surjective {X Y : Set} (f : X -> Y) := forall y, exists x, f x = y.
Definition bijective {X Y : Set} (f : X -> Y) := injective f /\ surjective f.

Lemma inverse {X Y : Set} (f : X -> Y) :
  bijective f -> {g : Y -> X | (forall x, g (f x) = x) /\
                               (forall y, f (g y) = y) }.
Proof.
intros [inj sur].
apply constructive_definite_description.
assert (H : forall y, exists! x, f x = y).
{ intros y.
  destruct (sur y) as [x xP].
  exists x; split; trivial.
  intros x' x'P.
  now apply inj; rewrite xP, x'P. }
exists (fun y => proj1_sig (constructive_definite_description _ (H y))).
split.
- split.
  + intros x.
    destruct (constructive_definite_description _ _).
    simpl.
    now apply inj.
  + intros y.
    now destruct (constructive_definite_description _ _).
- intros g' [H1 H2].
  apply functional_extensionality.
  intros y.
  destruct (constructive_definite_description _ _) as [x e].
  simpl.
  now rewrite <- e, H1.
Qed. *)

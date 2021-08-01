Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

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

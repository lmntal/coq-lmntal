Require Import Logic.FunctionalExtensionality.

Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import ListSet.

From LMNTAL Require Export Util.

(* From LMNTAL Require Export LMNtalSyntax.
Open Scope lmntal_scope. *)

(* Module LMNtalGraph. *)
Inductive Port := link (atomid argpos : nat) | null.
Record Atom := { name: string; args : list Port }.
Definition Graph := nat -> option Atom.
Definition empty : Graph := fun _ => None.

Definition eq_port : forall x y : Port, { x = y } + { x <> y }.
Proof. repeat decide equality. Defined.
Definition is_null p := eq_port p null.

Definition bind {A B} a (f : A -> option B) :=
  match a with
  | Some x => f x
  | None => None
  end.

Notation " x >>= y " := (bind x y) (at level 65, left associativity).
Notation " v <- M ; F " := (M >>= (fun v => F)) (at level 64, right associativity).

Fixpoint subst {X} l n (x : X) : option (list X) :=
  match l with
  | h :: t =>
    match n with
    | O => Some (x :: t)
    | S k => match subst t k x with
             | Some t' => Some (h :: t')
             | _ => None
             end
    end
  | _ => None
  end.

Definition arity (a : Atom) := length (args a).

Fixpoint seq {X} n (x : X) :=
  match n with
  | O => []
  | S k => x :: seq k x
  end.

Definition make_atom name n : Atom := {| name := name; args := seq n null |}.

Definition getarg (a : Atom) i : option Port := nth_error (args a) i.
Definition setarg (a : Atom) i (p : Port) : option Atom :=
  args' <- subst (args a) i p ;
  Some {| name := name a; args := args' |}.

Definition upd_graph (G : Graph) r opta : Graph :=
  fun r' => if PeanoNat.Nat.eq_dec r r' then opta else G r'.

Definition setatom (G : Graph) r a : Graph :=
  upd_graph G r (Some a).

Definition getport (G : Graph) (p : Port) : option Port :=
  match p with
  | link atomid argpos => atom <- G atomid ; getarg atom argpos
  | null => None
  end.

Definition setport (G : Graph) (p q : Port) : option Graph :=
  match p with
  | link atomid argpos =>
      a <- G atomid ;
      a' <- setarg a argpos q ;
      Some (setatom G atomid a')
  | _ => None
  end.

Definition setport_force (G : Graph) (p q : Port) : Graph :=
  match setport G p q with
  | Some G' => G'
  | None => G
  end.

Definition newatom G id name n := upd_graph G id (Some (make_atom name n)).

Definition removeatom G id := upd_graph G id None.

Definition newlink p1 p2 G := G' <- setport G  p1 p2 ;
                                    setport G' p2 p1.

Definition newlink_force (p q : Port) (G : Graph) : Graph :=
  match newlink p q G with
  | Some G' => G'
  | None => G
  end.

Definition Refers G p q := getport G p = Some q.

(* Definition RefEquivP G G' p := forall q, Refers G p q <-> Refers G' p q.
Definition RefEquiv G G' := forall p, RefEquivP G G' p. *)

Definition equiv (G G' : Graph) := forall n, G n = G' n.

Lemma equiv_refl :
  forall G, equiv G G.
Proof.
  intros G.
  unfold equiv. reflexivity.
Qed.

Lemma equiv_trans : 
  forall G1 G2 G3,
    equiv G1 G2 -> equiv G2 G3 -> equiv G1 G3.
Proof.
  intros G1 G2 G3 H12 H23.
  unfold equiv. intros n.
  unfold equiv in H12.
  unfold equiv in H23.
  rewrite H12.
  apply H23.
Qed.

Lemma equiv_sym :
  forall G G',
    equiv G G' -> equiv G' G.
Proof.
  intros G G'.
  unfold equiv. intros H n.
  rewrite H. reflexivity.
Qed.

Definition swap_atomid_port i1 i2 (p : Port) :=
  match p with
  | link atomid argpos => if PeanoNat.Nat.eq_dec atomid i1 then link i2 argpos
                          else if PeanoNat.Nat.eq_dec atomid i2 then link i1 argpos
                          else link atomid argpos
  | null => null
  end.

Definition swap_atomid_atom i1 i2 (a : Atom) :=
  {| name := name a; args := map (swap_atomid_port i1 i2) (args a) |}.

Definition swap_atomid i1 i2 (G : Graph) : Graph :=
  fun id => A <- (if PeanoNat.Nat.eq_dec id i1 then G i2
            else if PeanoNat.Nat.eq_dec id i2 then G i1
            else G id);
            Some (swap_atomid_atom i1 i2 A).

Definition swap_atomid_list l (G:Graph) :=
  fold_right (fun x g => match x with
                          | (i1, i2) => swap_atomid i1 i2 g
                         end) G l.

Definition isomorphic G G' := exists l, equiv (swap_atomid_list l G) G'.

Lemma isomorphic_refl :
  forall G, isomorphic G G.
Proof.
  intros G. unfold isomorphic.
  exists []. simpl. apply equiv_refl.
Qed.

Lemma swap_atomid_list_app :
  forall l1 l2 G,
    swap_atomid_list (l1++l2) G
    = swap_atomid_list l1 (swap_atomid_list l2 G).
Proof.
  intros l1 l2 G.
  induction l1.
  - auto.
  - destruct a as [i1 i2].
    simpl. f_equal. apply IHl1.
Qed.

Lemma isomorphic_trans :
  forall G1 G2 G3,
    isomorphic G1 G2 -> isomorphic G2 G3 ->
      isomorphic G1 G3.
Proof.
  intros G1 G2 G3.
  unfold isomorphic.
  unfold equiv.
  intros H12 H23.
  destruct H12 as [l12 H12].
  destruct H23 as [l23 H23].
  exists (l23++l12).
  rewrite swap_atomid_list_app.
  intros n.
  rewrite <- H23.
  f_equal.
  extensionality k.
  apply H12.
Qed.

Lemma equiv_swap_atomid_list :
  forall G G' l,
    equiv G G' ->
    equiv (swap_atomid_list l G) (swap_atomid_list l G').
Proof.
  intros G G' l H.
  (* generalize dependent G'. *)
  induction l.
  - auto.
  - destruct a as [i1 i2].
    simpl. unfold equiv. intros n.
    f_equal.
    extensionality x.
    apply IHl.
Qed.

Lemma swap_atomid_port_n_n :
  forall p n,
    swap_atomid_port n n p = p.
Proof.
  intros p n.
  unfold swap_atomid_port.
  destruct p; auto.
  destruct (PeanoNat.Nat.eq_dec atomid n); auto.
Qed.

Lemma swap_atomid_atom_n_n :
  forall a n,
    swap_atomid_atom n n a = a.
Proof.
  intros a n.
  unfold swap_atomid_atom.
  destruct a. f_equal.
  simpl. induction args0; auto.
  simpl. rewrite IHargs0.
  rewrite swap_atomid_port_n_n. reflexivity.
Qed.

Lemma swap_atomid_n_n :
  forall G n,
    swap_atomid n n G = G.
Proof.
  intros G n.
  extensionality x.
  unfold swap_atomid.
  unfold bind.
  destruct (PeanoNat.Nat.eq_dec x n).
  - rewrite e. destruct (G n); auto.
    f_equal. apply swap_atomid_atom_n_n.
  - destruct (G x); auto.
    f_equal. apply swap_atomid_atom_n_n.
Qed.

Lemma swap_atomid_port_twice :
  forall p i1 i2,
    swap_atomid_port i1 i2 (swap_atomid_port i1 i2 p)
    = p.
Proof.
  intros p i1 i2.
  unfold swap_atomid_port.
  destruct p; auto.
  destruct (PeanoNat.Nat.eq_dec atomid i1).
  - destruct (PeanoNat.Nat.eq_dec i2 i1).
    + rewrite e. rewrite e0. reflexivity.
    + rewrite nat_eq_dec_refl. f_equal.
      symmetry. apply e.
  - destruct (PeanoNat.Nat.eq_dec atomid i2).
    + rewrite nat_eq_dec_refl. f_equal.
      symmetry. apply e.
    + destruct (PeanoNat.Nat.eq_dec atomid i1);
      destruct (PeanoNat.Nat.eq_dec atomid i2); congruence.
Qed.

Lemma swap_atomid_atom_twice :
  forall a i1 i2,
    swap_atomid_atom i1 i2 (swap_atomid_atom i1 i2 a)
    = a.
Proof.
  intros a i1 i2.
  unfold swap_atomid_atom.
  destruct a.
  f_equal. simpl.
  induction args0; auto.
  simpl. f_equal; auto.
  apply swap_atomid_port_twice.
Qed.

Lemma swap_atomid_twice :
  forall G i1 i2,
    swap_atomid i1 i2 (swap_atomid i1 i2 G)
    = G.
Proof.
  intros G i1 i2.
  unfold swap_atomid.
  unfold bind.
  extensionality n.
  destruct (PeanoNat.Nat.eq_dec n i1).
  - destruct (PeanoNat.Nat.eq_dec i2 i1).
    + rewrite e. rewrite e0.
      destruct (G i1); auto.
      f_equal. repeat rewrite swap_atomid_atom_n_n.
      reflexivity.
    + rewrite nat_eq_dec_refl.
      rewrite e.
      destruct (G i1); auto.
      f_equal. apply swap_atomid_atom_twice.
  - destruct (PeanoNat.Nat.eq_dec n i2).
    + rewrite nat_eq_dec_refl.
      rewrite e. destruct (G i2); auto.
      f_equal. apply swap_atomid_atom_twice.
    + destruct (G n); auto. f_equal.
      apply swap_atomid_atom_twice.
Qed. 

Lemma isomorphic_sym :
  forall G G',
    isomorphic G G' -> isomorphic G' G.
Proof.
  intros G G'.
  unfold isomorphic.
  intros H.
  destruct H as [l H].
  exists (rev l).
  generalize dependent G'.
  generalize dependent G.
  induction l.
  - simpl.
    unfold equiv.
    intros G G' H n. rewrite H.
    reflexivity.
  - intros G G'. unfold equiv.
    destruct a as [i1 i2]. simpl.
    rewrite swap_atomid_list_app.
    intros H.
    unfold equiv in H.
    unfold equiv in IHl.
    apply IHl.
    simpl.
    extensionality in H.
    rewrite <- H.
    rewrite swap_atomid_twice.
    reflexivity.
Qed.
    


(* End LMNtalGraph. *)

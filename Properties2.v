Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import ListSet.

From LMNTAL Require Export LMNtalSyntax.
From LMNTAL Require Export LMNtalGraph2.
From LMNTAL Require Export Util.

Definition edges_of_edge (atomid: AtomId) (argpos: ArgPos) (link: Link) :=
  (link, (atomid, argpos)).

Fixpoint mapi_sub {A B} (i: nat) (f: nat -> A -> B) (l: list A): list B :=
  match l with
  | [] => []
  | h::t => (f i h) :: mapi_sub (S i) f t
  end.

Definition mapi {A B} (f: nat -> A -> B) (l: list A): list B :=
  mapi_sub O f l.

Definition edges_of_atom (atomid: AtomId) (l: Atom) :=
  match l with
    AAtom _ links => mapi (edges_of_edge atomid) links
  end.

Definition edges_of_atoms (atoms: list Atom) :=
  mapi edges_of_atom atoms.

Fixpoint add_edge (edge: (Link * Port)) (ls: list (Link * set Port)) :=
  match edge with (name, port) =>
    match ls with
    | [] => [(name, set_add Peq_dec port (empty_set Port))]
    | (name', ps)::t => if string_dec name name'
                        then (name, set_add Peq_dec port ps) :: t
                        else (name', ps) :: (add_edge edge t)
    end
  end.

Definition collect_edges (edges: list (list (Link * Port))): list (Link * set Port) :=
  fold_right (fun l a => fold_right (fun edge => add_edge edge) a l) [] edges.

Definition remove_links (l: list (Link * set Port)): set Edge :=
  fold_right (fun lp a => match lp with (_, ps) => set_add Eeq_dec ps a end) (empty_set Edge) l.

Definition get_edges (atoms: list Atom): set Edge :=
  remove_links (collect_edges (edges_of_atoms atoms)).

Definition get_labeling (atoms: list Atom) :=
  map (fun a => match a with (AAtom name _) => name end) atoms.

Definition get_atomnum (atoms: list Atom): AtomNum := length atoms.

Definition term_to_graph (term: LMNtalSyntax.Graph): LMNtalGraph2.Graph :=
  let atoms := term_to_atom_list term in
    (get_atomnum atoms, get_edges atoms, get_labeling atoms).

(* Compute (term_to_graph {{"p" ("X", "Y"), "q" ("Y", "X")}}). *)

Example ex_iso1: isomorphic
  (term_to_graph {{"p" ("X", "Y"), "q" ("Y", "X")}})
  (term_to_graph {{"q" ("A", "B"), "p" ("B", "A")}}).
Proof.
  exists [(0,1)]. simpl.
  unfold term_to_graph. simpl.
  unfold get_edges. simpl.
  unfold swap_atomid_labels, swap. reflexivity.
Qed.

Definition swap_atomid_al i1 i2 (al: list Atom) :=
  map (swap_atomid_atom i1 i2) al.

Definition swap_atomid_list_al l (al: list (string * list (nat * nat))) :=
  fold_right (fun x g => match x with
                          | (i1, i2) => swap_atomid_al i1 i2 g
                          end) G l.

Definition strong_iso G G' :=
  exists l, swap_atomid_list_al l (term_to_port_list G) = term_to_port_list G'.

Lemma strong_iso_isomorphic:
  forall G G', strong_iso G G' => isomorphic G G'.

(* Fixpoint make_swap :  *)

Lemma term_to_graph_swap :
  forall P Q, exists l,
    swap_atomid_list l (term_to_graph {{ P, Q }}) =
    term_to_graph {{ Q, P }}.
Proof.
  intro P. induction P; intro Q.
  - exists []. simpl.
    unfold term_to_graph. simpl.
    rewrite app_nil_r. reflexivity.
  
Admitted.

Lemma get_atomnum_app:
  forall l1 l2,
    get_atomnum (l1 ++ l2)
    = get_atomnum l1 + get_atomnum l2.
Proof.
  intros. induction l1; auto.
  simpl. auto.
Qed.

Lemma swap_atomid_mol:
  forall P P' Q,
    (exists l, swap_atomid_list l (term_to_graph P) = term_to_graph P')
    -> exists l, swap_atomid_list l (term_to_graph {{P,Q}}) = (term_to_graph {{P',Q}}).
Proof.
  intros.
Admitted.

Theorem cong_to_iso :
  forall t1 t2,
    cong t1 t2 -> isomorphic (term_to_graph t1) (term_to_graph t2).
Proof.
  intros.
  unfold isomorphic.
  rewrite congm_cong_iff in H.
  induction H.
  - exists []. simpl.
    unfold term_to_graph. reflexivity.
  - apply term_to_graph_swap.
  - exists []. simpl.
    unfold term_to_graph. simpl.
    rewrite app_assoc. reflexivity.
  - destruct IHcongm. exists x.
    unfold term_to_graph. simpl.
    unfold term_to_graph in H2.
    repeat rewrite get_atomnum_app.

  (* - exists []. simpl. *)
    (* unfold term_to_graph. f_equal. f_equal.
    + induction P; auto; simpl.
      { destruct atom. reflexivity. }
      repeat rewrite get_atomnum_app.
      rewrite <- IHP1. *)





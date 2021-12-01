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

Compute (term_to_graph {{"p" ("X", "Y"), "q" ("Y", "X")}}).

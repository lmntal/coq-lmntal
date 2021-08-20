Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import ListSet.

From LMNTAL Require Export LMNtalSyntax.
Open Scope lmntal_scope.

Inductive ShapeType : Type :=
  | defshape (S: LMNtalSyntax.Functor) (P: LMNtalSyntax.RuleSet) (N: list LMNtalSyntax.Functor).

(* Notation "'defshape' S '{' P '} 'nonterminal' {' N }" := (ty S P N)
  (at level 40, P custom lmntal at level 99, N custom lmntal at level 99) : lmntal_scope. *)

Check {{ "p"("X","Y") }}.

Definition skiplist_type :=
  defshape ("skiplist"/2) {{ 
    "skiplist"("L1","L2") :- "nil"("L1","L2");
    "skiplist"("L1","L2") :- "node1"("X1","L1"), "skiplist"("X1","L2");
    "skiplist"("L1","L2") :- "node2"("X1","X2","L1","L2"), "skiplist"("X1","X2")
  }} ["skiplist"/2].

Definition prel (t:ShapeType) (g:Graph) : Prop := 
  match t with
  | defshape (s/n) P _ => exists (args:list Link),
      length args = n /\ (AAtom s args) =[ P ]=>* g
  end.
Notation "g <| t" := (prel t g) (at level 40).

Lemma Feq_dec : forall x y : Functor, {x=y} +{x<>y}.
Proof.
  intros [a n] [b m].
  decide equality.
  - apply PeanoNat.Nat.eq_dec.
  - apply string_dec.
Qed.

Fixpoint fold_graph {T} f g u G : T :=
  match G with
  | GZero => u
  | GAtom a => f a
  | {{ G1, G2 }} => g (fold_graph f g u G1) (fold_graph f g u G2)
  end.

Definition funct (g:Graph) : set Functor :=
  fold_graph (fun a => [get_functor a]) (set_union Feq_dec) [] g.

Definition trel (t:ShapeType) (g:Graph) : Prop :=
  match t with
  | defshape _ _ N => g <| t /\ set_inter Feq_dec (funct g) N = empty_set Functor
  end.

Example prel_example:
  let t := defshape ("t"/2) {{ "t"("X","Y") :- "a"("X","Y") }} ["t"/2] in
  {{"a" ("X","Y")}} <| t .
Proof.
  simpl. exists ["X";"Y"].
  split. { reflexivity. }
  apply rrel_ruleset_rep_step with {{"t"("X","Y")}}.
  - apply rrel_ruleset_rep_refl.
    apply cong_refl. unfold wellformed_g. reflexivity.
  - unfold rrel_ruleset.
    apply rrel_R6.
    + unfold wellformed_g. auto.
    + unfold wellformed_g. auto.
    + unfold wellformed_r. unfold freelinks. simpl.
      unfold link_list_eq. apply Multiset.meq_refl.
Qed.

Definition is_connector (a:Atom) : Prop :=
  get_functor a = "="/2.

Definition CFp (p:Rule) : Prop :=
  match p with
  | {{ lhs :- rhs }} =>
    match lhs with
    | GAtom a => ~ (is_connector a) /\
        exists b,
          In b (term_to_atom_list rhs)
          /\ ~ (is_connector b)
    | _ => False
    end
  end.

Definition CF (t:ShapeType) : Prop :=
  match t with
  | defshape s P N =>
    forall p, In p (ruleset_to_list P) -> CFp p
  end.

Definition is_weighting g w :=
  forall f,
    In f (funct g) ->
    f = "="/2 /\ w f = 0 \/
    f <> "="/2 /\ 1 <= w f.
  
Definition weight w g :=
  fold_right (fun a s => w (get_functor a) + s) 0 (term_to_atom_list g).

Lemma assoc_fold_right:
  forall A B f g u (la:list A) (b:B), 
    (forall a, g a u = a) ->
    (forall a, g u a = a) ->
    (forall a b c, g (g a b) c = g a (g b c)) ->
    g (fold_right (fun a s => g (f a) s) u la) b
    = fold_right (fun a s => g (f a) s) b la.
Proof.
  intros A B f g u la b H1 H2 H3.
  generalize dependent b.
  induction la; simpl; auto.
  intros b.
  rewrite <- IHla.
  rewrite H1, H3.
  f_equal. apply IHla.
Qed.

Lemma assoc_fold_graph:
  forall A f g u P,
    (forall a, g a u = a) ->
    (forall a, g u a = a) ->
    (forall a b c, g (g a b) c = g a (g b c)) ->
    @fold_graph A f g u P =
    @fold_right A _ (fun a s => g (f a) s) u (term_to_atom_list P).
Proof.
  intros A f g u P H1 H2 H3.
  induction P; simpl; auto.
  rewrite fold_right_app. rewrite IHP1, IHP2. simpl.
  remember (fold_right (fun a s => g (f a) s) u (term_to_atom_list P2)) as a2.
  apply assoc_fold_right; auto.
Qed.

Lemma weight_fold:
  forall w g, weight w g =
    fold_graph (fun a => w (get_functor a)) plus 0 g.
Proof.
  intros w g. unfold weight.
  symmetry.
  assert (A:= PeanoNat.Nat.add_assoc).
  apply assoc_fold_graph; auto.
Qed.




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

Fixpoint funct (g:Graph) : set Functor :=
  match g with
  | GZero => []
  | GAtom a => [get_functor a]
  | {{ P,Q }} => set_union Feq_dec (funct P) (funct Q)
  end.

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

(* Definition weight w g := Admitted. *)
  

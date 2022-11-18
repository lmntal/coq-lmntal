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

Definition skiplist_example
  := {{ "node1"("X11","List1"),"node2"("X12","X21","X11","List2"),"nil"("X12","X21")}}.
  (* := {{ "node2"("L0","X","F0","F1"),"node2"("L1","Y","L0","X"),"nil"("L1","Y") }}. *)

Example prel_skiplist:
  skiplist_example <| skiplist_type.
Proof.
  simpl. exists ["List1";"List2"].
  simpl. split; auto.
  apply rrel_ruleset_rep_step
    with {{"node1"("X11","List1"),"node2"("X12","X21","X11","List2"),"skiplist"("X12","X21")}}.
  {
    apply rrel_ruleset_rep_step
      with {{"node1"("X11","List1"),"skiplist"("X11","List2")}}.
    {
      apply rrel_ruleset_rep_step
        with {{"skiplist"("List1","List2")}}.
      { apply rrel_ruleset_rep_refl. apply cong_refl.
        unfold wellformed_g. auto. }
      simpl. left. right.
      apply rrel_R3 with
        (G1:={{"skiplist"("L1","L2"),("L1"="List1","L2"="List2")}})
        (G1':={{"node1" ("X1", "L1"), "skiplist" ("X1", "L2"), ("L1"="List1","L2"="List2")}}); simpl.
      - solve_refl. unfold link_list_eq. apply Multiset.meq_refl.
      - Abort.

    }

  }

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

Example cf_example:
  CF skiplist_type.
Proof.
  simpl. intros.
  unfold CFp. simpl.
  destruct p. destruct lhs; destruct H as [H|[H|[H|H]]];
  try discriminate; auto; try injection H as H1 H2;
  try rewrite <- H1, <- H2; simpl; unfold is_connector; split; auto; try discriminate.
  - exists {{"nil" ("L1", "L2")}}.
    split; simpl; auto; discriminate.
  - exists {{"node1" ("X1", "L1")}}.
    split; simpl; auto; discriminate.
  - exists {{"node2" ("X1", "X2", "L1", "L2")}}.
    split; simpl; auto; discriminate.
  - exfalso. auto.
Qed.

Definition is_weighting w :=
  forall f,
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

Definition MTp w (p:Rule) : Prop :=
  match p with
  | {{ lhs :- rhs }} =>
    weight w lhs <= weight w rhs
  end.

Definition MT_weight w t : Prop :=
  is_weighting w /\
  match t with
  | defshape s P N =>
    forall p, In p (ruleset_to_list P) -> MTp w p
  end.

Definition MT (t:ShapeType) : Prop :=
  exists w, MT_weight w t.
  

Example mt_example:
  MT skiplist_type.
Proof.
  unfold MT. simpl.
  exists (fun f =>
    if Feq_dec f ("="/2)
      then 0 else 1).
  split.
  - unfold is_weighting. intros.
    case (Feq_dec f ("="/2)); auto.
  - unfold skiplist_type. intros. destruct H as [H|[H|[H|H]]];
    try rewrite <- H; simpl; unfold weight; simpl.
    + destruct (Feq_dec ("skiplist" / 2) ("=" / 2)); 
      destruct (Feq_dec ("nil" / 2) ("=" / 2)); simpl; auto.
      discriminate e.
    + destruct (Feq_dec ("skiplist" / 2) ("=" / 2)); 
      destruct (Feq_dec ("node1" / 2) ("=" / 2)); simpl; auto.
    + destruct (Feq_dec ("skiplist" / 2) ("=" / 2)); 
      destruct (Feq_dec ("node2" / 4) ("=" / 2)); simpl; auto.
    + destruct H.
Qed.

Lemma weight_mol:
  forall P Q w,
    weight w {{P,Q}} = weight w P + weight w Q.
Proof.
  intros.
  unfold weight. simpl.
  rewrite fold_right_app.
  rewrite assoc_fold_right; auto.
  symmetry.
  apply PeanoNat.Nat.add_assoc.
Qed.

Theorem CF_MT :
  forall t, CF t -> MT t.
Proof.
  intros. unfold MT. unfold CF in H.
  destruct t.
  exists (fun f => if Feq_dec f ("="/2) then 0 else 1).
  split.
  { unfold is_weighting. intros.
    destruct (Feq_dec f ("=" / 2));
    [left | right]; auto. }
  induction (ruleset_to_list P); intros.
  { destruct H0. }
  simpl in H.
  simpl in H0. destruct H0 eqn:E; auto.
  rewrite <- e. destruct E.
  apply H in H0. destruct a. simpl.
  rewrite <- e in H0.
  simpl in H0.
  destruct lhs; destruct H0.
  unfold weight. simpl.
  assert (A: CFp p).
  { apply H. left. apply e. }
  destruct (Feq_dec (get_functor atom)).
  { apply H0 in e0. destruct e0. }
  simpl. 
  induction (term_to_atom_list rhs).
  { repeat destruct H1. }
  simpl.
  destruct (Feq_dec (get_functor a) ("=" / 2)); simpl.
  - apply IHl0.
    destruct H1; destruct H1.
    destruct H1.
    + rewrite H1 in e0.
      apply H2 in e0. destruct e0.
    + exists x. split; [ apply H1 | apply H2 ].
  - apply PeanoNat.Nat.add_le_mono with (n:=1) (m:=1); auto.
    apply le_0_n.
Qed.

Lemma weight_replace:
  forall G X Y w, weight w {{G[Y/X]}} = weight w G.
Proof.
  intros. induction G; auto; simpl.
  - unfold weight. simpl.
    destruct atom. simpl.
    rewrite map_length. auto.
  - rewrite 2 weight_mol.
    rewrite IHG1, IHG2. auto.
Qed.

Lemma weight_connector:
  forall w X Y, is_weighting w ->
    weight w {{X=Y}} = 0.
Proof.
  intros.
  unfold is_weighting in H.
  unfold weight. simpl.
  destruct (H ("="/2)).
  + destruct H0. rewrite H1. auto.
  + destruct H0. exfalso. apply H0. auto.
Qed.

Lemma weight_cong:
  forall w P Q, P == Q -> is_weighting w ->
    weight w P = weight w Q.
Proof.
  intros.
  apply congm_cong_iff in H.
  induction H; auto; repeat rewrite weight_mol; auto.
  - apply PeanoNat.Nat.add_comm.
  - apply PeanoNat.Nat.add_assoc.
  - rewrite weight_connector; auto.
  - rewrite weight_replace.
    rewrite weight_connector; auto.
  - rewrite IHcongm1. apply IHcongm2.
Qed.

Lemma MT_dec :
  forall w S P N, MT_weight w (defshape S P N) ->
    forall G G', G' =[ P ]=> G -> weight w G' <= weight w G.
Proof.
  intros.
  rewrite rrel_ruleset_In in H0.
  destruct H0 as [p].
  destruct H0. unfold MT_weight in H.
  destruct H.
  induction H1.
  - rewrite 2 weight_mol.
    apply PeanoNat.Nat.add_le_mono; auto.
  - destruct weight_cong with (w:=w) (P:=G2) (Q:=G1); auto.
    destruct weight_cong with (w:=w) (P:=G1') (Q:=G2'); auto.
  - apply H2 in H0. unfold MTp in H0. auto.
Qed.



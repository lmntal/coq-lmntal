Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Multiset.

Definition Link := string.

Inductive Atom : Type :=
  | AAtom (name:string) (links:list Link).

Inductive Functor : Type :=
  | FFunctor (name:string) (arity:nat).
Notation "p / n" := (FFunctor p n).

Definition get_functor (a:Atom) : Functor :=
  match a with
  | AAtom p ls => p / length ls
  end.

Inductive Graph : Type :=
  | GZero 
  | GAtom (atom:Atom)
  | GMol (g1 g2:Graph).

Inductive Rule : Type :=
  | React (lhs rhs:Graph).

Inductive RuleSet : Type :=
  | RZero
  | RRule (rule:Rule)
  | RMol (r1 r2:RuleSet).

Coercion RRule : Rule >-> RuleSet.
Coercion GAtom : Atom >-> Graph.

Declare Custom Entry lmntal.
Declare Scope lmntal_scope.
Notation "{{ e }}" := e (at level 0, e custom lmntal at level 99) : lmntal_scope.
Notation "( x )" := x (in custom lmntal, x at level 99) : lmntal_scope.
Notation "x" := x (in custom lmntal at level 0, x constr at level 0) : lmntal_scope.
Notation "p ( x , .. , y )" := (AAtom p (cons x .. (cons y nil) .. ))
                  (in custom lmntal at level 0,
                  p constr at level 0, x constr at level 9,
                  y constr at level 9) : lmntal_scope.
Notation "p ()" := (AAtom p nil) (in custom lmntal at level 0,
                                  p constr at level 0) : lmntal_scope.
Notation "x = y" := (AAtom "=" [x;y]) (in custom lmntal at level 40, left associativity) : lmntal_scope.
Notation "x , y" := (GMol x y) (in custom lmntal at level 90, left associativity) : lmntal_scope.
Notation "x ':-' y" := (React x y) (in custom lmntal at level 91, no associativity) : lmntal_scope.
Notation "x ';' y" := (RMol x y) (in custom lmntal at level 92, left associativity) : lmntal_scope.
Open Scope lmntal_scope.

Check {{ "Y" }} : Link.
Check {{ "p"("X","Y"),"q"("Y","X") }} : Graph.
Check {{ "p"("X","Y"),"q"("Y","X") :- GZero }} : Rule.
Check {{ "p"("X","Y"),"q"("Y","X") :- GZero; RZero }} : RuleSet.

Example get_functor_example: get_functor (AAtom "p" ["L";"L";"M";"M"]) = "p"/4.
Proof. reflexivity. Qed.

Fixpoint remove_one (x: Link) (l: list Link) : bool * list Link :=
  match l with
  | [] => (false, [])
  | h::t => if h =? x then (true, t)
    else match (remove_one x t) with
    | (b, ls) => (b, h::ls)
    end
  end.

Fixpoint links (g: Graph) : list Link := 
  match g with
  | GZero => []
  | GAtom (AAtom p args) => args
  | {{P,Q}} => links P ++ links Q
  end.

Definition Leq_dec : forall x y : Link, {x=y} + {x<>y} := string_dec.

Definition unique_links (g: Graph): list Link := nodup Leq_dec (links g).

Definition list_to_multiset (l:list Link) : multiset Link :=
  fold_right (fun x a => munion (SingletonBag eq Leq_dec x) a) (EmptyBag Link) l.

Definition link_multiset (g: Graph) : multiset Link :=
  list_to_multiset (links g).

Definition freelinks (g: Graph) : list Link := filter 
  (fun x => Nat.eqb (multiplicity (link_multiset g) x) 1) (unique_links g).

Definition locallinks (g: Graph) : list Link := filter
  (fun x => Nat.eqb (multiplicity (link_multiset g) x) 2) (unique_links g).

Compute freelinks {{ "p"("X","Y"),"q"("Y","X","F") }}.
Compute locallinks {{ "p"("X","Y"),"q"("Y","X","F") }}.

Lemma in_unique_links:
  forall g x, In x (unique_links g) <-> In x (links g).
Proof.
  intros g x.
  unfold unique_links.
  apply nodup_In.
Qed.

Require Import Coq.Logic.Eqdep_dec.
Lemma Leq_dec_refl: 
  forall X, Leq_dec X X = left eq_refl.
Proof.
  intros X. destruct (Leq_dec X X).
  - apply f_equal, UIP_dec, Leq_dec.
  - congruence.
Qed.

(* A graph is well-formed if each link name occurs at most twice in it *)
Definition wellformed_g (g:Graph) : Prop :=
  forallb (fun x => Nat.leb (multiplicity (link_multiset g) x) 2) (unique_links g) = true.

Lemma wellformed_g_forall: forall g, wellformed_g g <->
  forall x, In x (links g) -> (multiplicity (link_multiset g) x) <= 2.
Proof.
  intros g.
  split.
  - intros H1 x H2.
    unfold wellformed_g in H1. rewrite forallb_forall in H1.
    apply in_unique_links in H2.
    apply H1 in H2. rewrite PeanoNat.Nat.leb_le in H2.
    apply H2.
  - intros H1. unfold wellformed_g. rewrite forallb_forall.
    intros x H2. rewrite PeanoNat.Nat.leb_le.
    apply H1. apply in_unique_links. apply H2.
Qed.

Fixpoint link_list_eqb (l1 l2 : list Link) : bool :=
  match l1,l2 with
  | [],[] => true
  | [],_ => false
  | h1::t1,_ => match (remove_one h1 l2) with
                | (true, l) => link_list_eqb t1 l
                | (false, _) => false
                end
  end.

Definition link_list_eq (l1 l2 : list Link) : Prop :=
  meq (list_to_multiset l1) (list_to_multiset l2).

Definition wellformed_r (r:Rule) : Prop :=
  match r with
  | {{lhs :- rhs}} => link_list_eq (freelinks lhs) (freelinks rhs)
  end.

(* P[Y/X] *)
Fixpoint substitute (Y X:Link) (P:Graph) : Graph :=
  match P with
  | GZero => GZero
  | GAtom (AAtom p args) => GAtom (AAtom p (map (fun L => if L =? X then Y else L) args))
  | {{P,Q}} => GMol (substitute Y X P) (substitute Y X Q)
  end.
Notation "P [ Y / X ]" := (substitute Y X P) (in custom lmntal at level 40, left associativity) : lmntal_scope.

Example substitute_example :
  {{ ( "p"("X", "Y"), "q"("Y", "X") ) [ "L" / "X" ] }} = {{ "p"("L", "Y"), "q"("Y", "L") }}.
Proof. reflexivity. Qed.

Reserved Notation "p == q" (at level 40).
Inductive cong : Graph -> Graph -> Prop :=
  | cong_E1 : forall P, wellformed_g P ->
              {{GZero, P}} == P
  | cong_E2 : forall P Q, wellformed_g {{P, Q}} -> 
              {{P, Q}} == {{Q, P}}
  | cong_E3 : forall P Q R, wellformed_g {{P, (Q, R)}} -> 
              {{P, (Q, R)}} == {{(P, Q), R}}
  | cong_E4 : forall P X Y, wellformed_g P -> wellformed_g {{ P[Y/X] }} ->
              In X (locallinks P) -> P == {{ P[Y/X] }}
  | cong_E5 : forall P P' Q, wellformed_g {{ P,Q }} -> wellformed_g {{ P',Q }} ->
              P == P' -> {{ P,Q }} == {{ P',Q }}
  | cong_E7 : forall X, {{ X = X }} == GZero
  | cong_E8 : forall X Y, {{ X = Y }} == {{ Y = X }}
  | cong_E9 : forall X Y (A:Atom),
              wellformed_g {{ X = Y, A }} -> wellformed_g {{ A[Y/X] }} ->
              In X (freelinks A) ->
              {{ X = Y, A }} == {{ A[Y/X] }}
  | cong_refl : forall P, wellformed_g P ->
                  P == P
  | cong_trans : forall P Q R, wellformed_g P -> wellformed_g Q -> wellformed_g R ->
                  P == Q -> Q == R -> P == R
  | cong_sym : forall P Q, wellformed_g P -> wellformed_g Q -> 
                  P == Q -> Q == P
  where "p '==' q" := (cong p q).

Example cong_example : {{ "p"("X","X") }} == {{ "p"("Y","Y") }}.
Proof.
  replace ({{ "p"("Y","Y") }}:Graph) with {{ "p"("X","X")["Y"/"X"] }}; auto.
  apply cong_E4; unfold wellformed_g; auto.
  simpl. auto.
Qed.

Ltac solve_refl := 
      repeat 
        unfold wellformed_g, wellformed_r,
                freelinks, locallinks,
                unique_links; simpl;
      repeat (
        (rewrite Leq_dec_refl 
      || rewrite eqb_refl);
        simpl); auto.

Example cong_example_var : forall p X Y, {{ p(X,X) }} == {{ p(Y,Y) }}.
Proof.
  intros p X Y.
  replace ({{ p(Y,Y) }}:Graph) with {{ p(X,X)[Y/X] }}.
  - apply cong_E4; solve_refl.
  - solve_refl.
Qed.

Reserved Notation "p '-[' r ']->' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Inductive rrel : Rule -> Graph -> Graph -> Prop :=
  | rrel_R1 : forall G1 G1' G2 r,
                wellformed_g {{G1,G2}} -> wellformed_g {{G1',G2}} ->
                wellformed_r r ->
                G1 -[ r ]-> G1' -> {{G1,G2}} -[ r ]-> {{G1',G2}}
  | rrel_R3 : forall G1 G1' G2 G2' r,
                wellformed_r r ->
                G2 == G1 -> G1' == G2' ->
                G1 -[ r ]-> G1' -> G2 -[ r ]-> G2'
  | rrel_R6 : forall T U,
                wellformed_g T -> wellformed_g U ->
                wellformed_r {{ T :- U }} ->
                T -[ T :- U ]-> U
  where "p '-[' r ']->' q" := (rrel r p q).

Reserved Notation "p '-[' r ']->*' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Inductive rrel_rep : Rule -> Graph -> Graph -> Prop :=
  | rrel_rep_refl : forall r a b, a == b -> a -[ r ]->* b
  | rrel_rep_step : forall r a b c, a -[ r ]->* b -> b -[ r ]-> c -> a -[ r ]->* c
  where "p '-[' r ']->*' q" := (rrel_rep r p q).

Reserved Notation "p '=[' r ']=>' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Fixpoint rrel_ruleset (rs : RuleSet) (p q : Graph) : Prop :=
  match rs with
  | RZero => False
  | RRule r => p -[ r ]-> q
  | RMol a b => p =[ a ]=> q \/ p =[ b ]=> q
  end
  where "p '=[' rs ']=>' q" := (rrel_ruleset rs p q).

Reserved Notation "p '=[' r ']=>*' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Inductive rrel_ruleset_rep : RuleSet -> Graph -> Graph -> Prop :=
  | rrel_ruleset_rep_refl : forall rs a b, a == b -> a =[ rs ]=>* b
  | rrel_ruleset_rep_step : forall rs a b c, a =[ rs ]=>* b -> b =[ rs ]=> c -> a =[ rs ]=>* c
  where "p '=[' r ']=>*' q" := (rrel_ruleset_rep r p q).

Example rrel_example :
  {{ "a"(), "b"("Z"), "c"("Z") }}
  -[ "b"("X"),"c"("X") :- "d"() ]->
  {{ "a"(), "d"() }}.
Proof.
  apply rrel_R3 with (G1:={{"b" ("X"), "c" ("X"), "a" ()}}) (G1':={{"d" (), "a" ()}}).
  - unfold wellformed_r. unfold link_list_eq. simpl. apply meq_refl.
  - apply cong_trans with (Q:={{"a"(),("b"("Z"),"c"("Z"))}}); unfold wellformed_g; auto.
    + apply cong_sym; unfold wellformed_g; auto.
      apply cong_E3; unfold wellformed_g; auto.
    + apply cong_trans with (Q:={{"b" ("Z"), "c" ("Z"), "a" ()}}); unfold wellformed_g; auto.
      * apply cong_E2; unfold wellformed_g; auto.
      * assert (H1: {{"b"("X"), "c"("X"), "a"()}}={{("b"("Z"), "c"("Z"),"a"())["X"/"Z"] }}).
        { reflexivity. }
        rewrite H1.
        apply cong_E4; unfold wellformed_g; auto.
        simpl. auto.
  - apply cong_E2; unfold wellformed_g; auto.
  - apply rrel_R1; unfold wellformed_g; auto.
    + unfold wellformed_r. unfold link_list_eq. simpl. apply meq_refl.
    + apply rrel_R6; unfold wellformed_g; auto.
      unfold wellformed_r. unfold link_list_eq. simpl. apply meq_refl.
Qed.

Example rrel_example_var : forall a b c d X Z,
  {{ a(), b(Z), c(Z) }}
  -[ b(X), c(X) :- d() ]->
  {{ a(), d() }}.
Proof.
  intros a b c d X Z.
  apply rrel_R3 with (G1:={{b(X), c(X), a()}}) (G1':={{d(), a()}}).
  - unfold wellformed_r. unfold link_list_eq. simpl.
    solve_refl.
    apply meq_refl.
  - apply cong_trans with (Q:={{a(),(b(Z),c(Z))}}); solve_refl.
    + apply cong_sym; solve_refl.
      apply cong_E3; solve_refl.
    + apply cong_trans with (Q:={{b(Z), c(Z), a()}}); solve_refl.
      * apply cong_E2; solve_refl.
      * assert (H1: {{b(X), c(X), a()}}={{(b(Z), c(Z), a())[X/Z] }}); solve_refl.
        rewrite H1.
        apply cong_E4; solve_refl.
  - apply cong_E2; solve_refl.
  - apply rrel_R1; solve_refl.
    + unfold link_list_eq. simpl. apply meq_refl.
    + apply rrel_R6; solve_refl. unfold link_list_eq. simpl. apply meq_refl.
Qed.

Definition inv (r:Rule) : Rule :=
  match r with
  | {{ lhs:-rhs }} => {{ rhs :- lhs }}
  end.

Lemma link_list_eq_commut : forall l1 l2,
  link_list_eq l1 l2 <-> link_list_eq l2 l1.
Proof.
  intros l1 l2.
  unfold link_list_eq.
  split.
  - apply meq_sym.
  - apply meq_sym.
Qed.

Lemma list_to_multiset_app:
  forall l1 l2, meq (list_to_multiset (l1 ++ l2)) (munion (list_to_multiset l1) (list_to_multiset l2)).
Proof.
  intros l1 l2.
  induction l1.
  - simpl. apply munion_empty_left.
  - simpl. apply meq_trans
      with (munion (SingletonBag eq Leq_dec a) (munion (list_to_multiset l1) (list_to_multiset l2))).
    + apply meq_right. apply IHl1.
    + apply meq_sym. apply munion_ass.
Qed.

Lemma link_multiset_mol:
  forall G1 G2, meq (link_multiset {{G1,G2}}) (munion (link_multiset G1) (link_multiset G2)).
Proof.
  intros G1. destruct G1.
  - intros G2. unfold link_multiset.
    replace (links GZero) with ([]:list Link).
    + simpl. apply munion_empty_left.
    + reflexivity.
  - intros G2. unfold link_multiset. destruct atom. simpl.
    apply list_to_multiset_app.
  - intros G2. unfold link_multiset.
    replace (links {{G1_1, G1_2}}) with (links {{G1_1}} ++ links {{G1_2}}).
    + apply list_to_multiset_app.
    + reflexivity.
Qed.

Lemma multiplicity_munionL: forall {X:Type} (m m1 m2:multiset X) (x:X),
  meq m (munion m1 m2) -> multiplicity m1 x <= multiplicity m x.
Proof.
  intros X m m1 m2 x H.
  unfold meq in H.
  rewrite H.
  unfold munion. simpl.
  apply PeanoNat.Nat.le_add_r.
Qed.

Lemma multiplicity_munionR: forall {X:Type} (m m1 m2:multiset X) (x:X),
  meq m (munion m1 m2) -> multiplicity m2 x <= multiplicity m x.
Proof.
  intros X m m1 m2 x H.
  unfold meq in H.
  rewrite H.
  unfold munion. simpl. rewrite PeanoNat.Nat.add_comm.
  apply PeanoNat.Nat.le_add_r.
Qed.

Lemma links_mol:
  forall G1 G2 x, In x (links {{G1,G2}}) <-> In x (links G1) \/ In x (links G2).
Proof.
  intros G1 G2 x.
  replace (links {{G1,G2}}) with (links G1 ++ links G2).
  - apply in_app_iff.
  - reflexivity.
Qed.

Lemma wellformed_g_inj:
  forall G1 G2, wellformed_g {{G1,G2}} -> wellformed_g G1 /\ wellformed_g G2.
Proof.
  intros G1 G2 H.
  rewrite wellformed_g_forall in H.
  split.
  - rewrite wellformed_g_forall. intros x H1.
    apply PeanoNat.Nat.le_trans with (multiplicity (link_multiset {{G1, G2}}) x).
    + apply multiplicity_munionL with (link_multiset G2).
      apply link_multiset_mol.
    + apply H. rewrite links_mol. left. apply H1.
  - rewrite wellformed_g_forall. intros x H1.
    apply PeanoNat.Nat.le_trans with (multiplicity (link_multiset {{G1, G2}}) x).
    + apply multiplicity_munionR with (link_multiset G1).
      apply link_multiset_mol.
    + apply H. rewrite links_mol. right. apply H1.
Qed.

Lemma connector_wellformed_g :
  forall X Y, wellformed_g {{ X = Y }}.
Proof.
  intros X Y.
  unfold wellformed_g.
  unfold unique_links.
  unfold nodup.
  simpl.
  destruct (Leq_dec Y X) eqn:EYX; simpl.
  - rewrite e. rewrite Leq_dec_refl. auto.
  - destruct (Leq_dec X Y) eqn:EXY; simpl.
    + rewrite Leq_dec_refl. auto.
    + rewrite Leq_dec_refl. rewrite EYX.
      rewrite Leq_dec_refl. auto.
Qed.

Lemma in_links_link_multiset:
  forall P x, In x (links P) <-> 1 <= multiplicity (link_multiset P) x.
Proof.
  intros P x.
  unfold link_multiset.
  induction (links P).
  - simpl. split.
    + intros C. destruct C.
    + intros C. apply Compare_dec.nat_compare_ge in C.
      simpl in C. destruct C. reflexivity.
  - simpl. split; intros H.
    + destruct H.
      * rewrite H. rewrite Leq_dec_refl.
        apply le_n_S.
        apply le_0_n.
      * apply IHl in H.
        rewrite PeanoNat.Nat.add_comm.
        apply Plus.le_plus_trans.
        apply H.
    + destruct (Leq_dec a x).
      * left. auto.
      * right. simpl in H. apply IHl.
        apply H.
Qed.

Lemma wellformed_g_link_multiset:
  forall P Q,
    meq (link_multiset P) (link_multiset Q) ->
    wellformed_g P -> wellformed_g Q.
Proof.
  intros P Q H.
  rewrite wellformed_g_forall.
  rewrite wellformed_g_forall.
  intros HP x Hx.
  unfold meq in H. rewrite <- H.
  apply HP.
  apply in_links_link_multiset.
  rewrite H.
  apply in_links_link_multiset.
  apply Hx.
Qed.

Lemma link_multiset_swap :
  forall P Q, meq (link_multiset {{P, Q}}) (link_multiset {{Q, P}}).
Proof.
  intros P Q.
  apply meq_trans with (munion (link_multiset P) (link_multiset Q)).
  { apply link_multiset_mol. }
  apply meq_trans with (munion (link_multiset Q) (link_multiset P)).
  { apply munion_comm. }
  apply meq_sym.
  apply link_multiset_mol.
Qed.

Lemma link_multiset_assoc:
  forall P Q R,
    meq (link_multiset {{P, (Q, R)}}) (link_multiset {{P, Q, R}}).
Proof.
  intros P Q R.
  apply meq_trans with (munion (link_multiset P) (link_multiset {{Q,R}})).
  { apply link_multiset_mol. }
  apply meq_trans with (munion (link_multiset P) (munion (link_multiset Q) (link_multiset R))).
  { apply meq_right. apply link_multiset_mol. }
  apply meq_trans with (munion (munion (link_multiset P) (link_multiset Q)) (link_multiset R)).
  { apply meq_sym. apply munion_ass. }
  apply meq_trans with (munion (link_multiset {{P,Q}}) (link_multiset R)).
  { apply meq_left. apply meq_sym. apply link_multiset_mol. }
  apply meq_sym. apply link_multiset_mol.
Qed.

Lemma cong_wellformed_g :
  forall P Q, P == Q -> wellformed_g P /\ wellformed_g Q.
Proof.
  intros P Q H.
  induction H; auto; split; auto.
  - apply wellformed_g_link_multiset with {{P,Q}}; auto.
    apply link_multiset_swap.
  - apply wellformed_g_link_multiset with {{P,(Q,R)}}; auto.
    apply link_multiset_assoc.
  - apply connector_wellformed_g.
  - unfold wellformed_g.
    simpl. auto.
  - apply connector_wellformed_g.
  - apply connector_wellformed_g.
Qed.

Lemma rrel_wellformed :
  forall P Q r, P -[ r ]-> Q ->
    wellformed_g P /\ wellformed_g Q /\ wellformed_r r.
Proof.
  intros P Q r H.
  induction H; auto.
  apply cong_wellformed_g in H0.
  apply cong_wellformed_g in H1.
  destruct H0. destruct H1.
  auto.
Qed.

Theorem inv_rrel: forall r G G', G' -[r]-> G
  -> let inv_r := inv r in G -[ inv_r ]-> G'.
Proof.
  intros r G G' H. simpl.
  assert (A: wellformed_r r -> wellformed_r (inv r)).
  { simpl. destruct r. apply link_list_eq_commut. }
  induction H.
  - apply rrel_R1; auto.
  - apply rrel_R3 with (G1') (G1); auto.
    + apply cong_sym; auto; apply cong_wellformed_g in H1; destruct H1; auto.
    + apply cong_sym; auto; apply cong_wellformed_g in H0; destruct H0; auto.
  - apply rrel_R6; auto.
Qed.

Lemma inv_inv : forall r, inv (inv r) = r.
Proof.
  intros [lhs rhs]. reflexivity.
Qed.

Corollary inv_rrel_iff: forall r G G', G' -[r]-> G
  <-> let inv_r := inv r in G -[ inv_r ]-> G'.
Proof.
  intros r G G'.
  split.
  - apply inv_rrel.
  - simpl. intros H. apply inv_rrel in H.
    rewrite inv_inv in H.
    apply H.
Qed.

Reserved Notation "p '==m' q" (at level 40).
Inductive congm : Graph -> Graph -> Prop :=
  | congm_E1 : forall P, wellformed_g P ->
                {{GZero, P}} ==m P
  | congm_E2 : forall P Q, wellformed_g {{P, Q}} ->
                {{P, Q}} ==m {{Q, P}}
  | congm_E3 : forall P Q R, wellformed_g {{P, (Q, R)}} -> 
                {{P, (Q, R)}} ==m {{(P, Q), R}}
  | congm_E5 : forall P P' Q, wellformed_g {{ P,Q }} -> wellformed_g {{ P',Q }} ->
                P ==m P' -> {{ P,Q }} ==m {{ P',Q }}
  | congm_E7 : forall X, {{ X = X }} ==m GZero
  | congm_E9 : forall X Y (A:Atom), 
                wellformed_g {{ X = Y, A }} -> wellformed_g {{ A[Y/X] }} ->
                In X (freelinks A) ->
                {{ X = Y, A }} ==m {{ A[Y/X] }}
  | congm_refl : forall P, wellformed_g P ->
                  P ==m P
  | congm_trans : forall P Q R, wellformed_g P -> wellformed_g Q -> wellformed_g R ->
    P ==m Q -> Q ==m R -> P ==m R
  | congm_sym : forall P Q, wellformed_g P -> wellformed_g Q -> 
    P ==m Q -> Q ==m P
  where "p '==m' q" := (congm p q).

Lemma in_freelinks:
  forall X P, In X (freelinks P) <-> multiplicity (link_multiset P) X = 1.
Proof.
  intros X P. unfold freelinks.
  rewrite filter_In. split.
  - intros [H1 H2].
    apply PeanoNat.Nat.eqb_eq.
    auto.
  - intros H. split.
    + apply in_unique_links.
      apply in_links_link_multiset.
      rewrite H. auto.
    + apply PeanoNat.Nat.eqb_eq. auto.
Qed.

Lemma in_freelinks_inj:
  forall X P Q, In X (freelinks {{P,Q}}) ->
    In X (freelinks P) \/ In X (freelinks Q).
Proof.
  intros X P Q H.
  rewrite in_freelinks. rewrite in_freelinks.
  rewrite in_freelinks in H.
  assert (A: multiplicity (link_multiset {{P, Q}}) X
    = multiplicity (link_multiset P) X + multiplicity (link_multiset Q) X).
  { apply link_multiset_mol. }
  rewrite A in H. apply PeanoNat.Nat.eq_add_1 in H.
  destruct H as [[H1 H2]|[H1 H2]]; auto.
Qed.

Lemma congm_E9ex :
  forall X Y P, 
    wellformed_g {{ X = Y, P }} -> wellformed_g {{ P[Y/X] }} ->
    In X (freelinks P) ->
    {{ X = Y, P }} ==m {{ P[Y/X] }}.
Proof.
  intros X Y P H1 H2 H3.
  induction P.
  - simpl. simpl in H3. destruct H3.
  - apply congm_E9; auto.
  - simpl in H2. apply wellformed_g_inj in H2.
    destruct H2 as [H21 H22].
    apply in_freelinks_inj in H3.
    destruct H3.
    + apply wellformed_g_link_multiset with (Q:={{X=Y,P1,P2}}) in H1.
      apply wellformed_g_inj in H1.
      destruct H1. apply IHP1 in H0; auto.
Abort.

Lemma congm_E4 :
  forall P X Y,
    wellformed_g P -> wellformed_g {{P [Y / X]}} ->
    In X (locallinks P) -> P ==m {{ P[Y/X] }}.
Proof.
  intros P X Y H.
Admitted.

Lemma congm_E8_sub :
  forall X Y Z, X <> Z -> Y <> Z ->
    wellformed_g {{ Z=X, Z=Y }} ->
    {{ Z=X, Z=Y }} ==m {{ X=Y }}.
Proof.
  intros X Y Z Hxz Hyz H.
  destruct (Leq_dec Y Z) eqn:EYZ.
  { congruence. }
  apply congm_trans with {{ (Z=Y)[X/Z] }}; auto.
  - apply connector_wellformed_g.
  - apply connector_wellformed_g.
  - apply congm_E9; auto.
    { simpl. apply connector_wellformed_g. }
    unfold freelinks.
    simpl. unfold unique_links.
    simpl. rewrite EYZ.
    simpl. repeat rewrite Leq_dec_refl.
    rewrite EYZ. simpl. auto.
  - simpl.
    rewrite eqb_refl.
    replace (Y =? Z) with false.
    + apply congm_refl.
      apply connector_wellformed_g.
    + symmetry. apply eqb_neq. apply n.
Qed.

Lemma get_fresh_link_X_Y:
  forall (X Y: Link), exists Z, X <> Z /\ Y <> Z.
Proof.
  intros X Y.
  destruct (Leq_dec X "X").
  - destruct (Leq_dec Y "X").
    + rewrite e, e0. exists "Y".
      rewrite <- eqb_neq. auto.
    + rewrite e. destruct (Leq_dec Y "Y").
      * rewrite e0. exists "Z".
        repeat rewrite <- eqb_neq. auto.
      * exists "Y". 
        rewrite <- eqb_neq. auto.
  - destruct (Leq_dec Y "X").
    + rewrite e. destruct (Leq_dec X "Y").
      * rewrite e0. exists "Z".
        repeat rewrite <- eqb_neq. auto.
      * exists "Y".
        split; auto.
        rewrite <- eqb_neq. auto.
    + exists "X". auto.
Qed.

Lemma wellformed_g_swap :
  forall P Q, wellformed_g {{P,Q}} -> wellformed_g {{Q,P}}.
Proof.
  intros P Q H.
  apply wellformed_g_link_multiset with {{P,Q}}.
  - apply link_multiset_swap.
  - auto.
Qed.

Lemma wellformed_g_zx_zy:
  forall X Y Z,
    X <> Z -> Y <> Z -> wellformed_g {{Z = X, Z = Y}}.
Proof.
  intros X Y Z Hxz Hyz.
  apply wellformed_g_forall.
  intros L H1. simpl in H1. simpl.
  destruct H1 as [H1|[H1|[H1|[H1|[]]]]]; rewrite <- H1;
  rewrite Leq_dec_refl.
  - destruct (Leq_dec X Z); 
    destruct (Leq_dec Y Z);
    try congruence; auto.
  - destruct (Leq_dec Z X); 
    destruct (Leq_dec Y X);
    try congruence; auto.
  - destruct (Leq_dec X Z); 
    destruct (Leq_dec Y Z);
    try congruence; auto.
  - destruct (Leq_dec Z Y); 
    destruct (Leq_dec X Y);
    try congruence; auto.
Qed.

Lemma congm_E8 :
  forall X Y, {{X = Y}} ==m {{Y = X}}.
Proof.
  intros X Y.
  assert (AZ: exists Z, X <> Z /\ Y <> Z).
  { apply get_fresh_link_X_Y. }
  destruct AZ as [Z].
  destruct H.
  assert (WF: wellformed_g {{Z = X, Z = Y}}).
  { apply wellformed_g_zx_zy; auto. }
  apply congm_trans with {{ Z=X, Z=Y }}.
  - apply connector_wellformed_g.
  - apply WF. 
  - apply connector_wellformed_g.
  - apply congm_sym; auto.
    + apply connector_wellformed_g.
    + apply congm_E8_sub; auto.
  - apply congm_trans with {{ Z=Y,Z=X }}; auto.
    + apply wellformed_g_swap. auto.
    + apply connector_wellformed_g.
    + apply congm_E2. auto.
    + apply congm_E8_sub; auto.
      apply wellformed_g_swap. auto.
Qed.

Theorem congm_cong_iff :
  forall P Q, P == Q <-> P ==m Q.
Proof.
  intros P Q.
  split.
  - intros H. induction H.
    + apply congm_E1; auto.
    + apply congm_E2; auto.
    + apply congm_E3; auto.
    + apply congm_E4; auto.
    + apply congm_E5; auto.
    + apply congm_E7; auto.
    + apply congm_E8; auto.
    + apply congm_E9; auto.
    + apply congm_refl; auto.
    + apply congm_trans with Q; auto.
    + apply congm_sym; auto.
  - intros H. induction H.
    + apply cong_E1; auto.
    + apply cong_E2; auto.
    + apply cong_E3; auto.
    + apply cong_E5; auto.
    + apply cong_E7; auto.
    + apply cong_E9; auto.
    + apply cong_refl; auto.
    + apply cong_trans with Q; auto.
    + apply cong_sym; auto.
Qed.

Fixpoint term_to_atom_list (t: Graph) : list Atom :=
  match t with
  | GZero => []
  | GAtom atom => [atom]
  | GMol g1 g2 => (term_to_atom_list g1)++(term_to_atom_list g2)
  end.

Fixpoint add_indices {X} (n : nat) (l : list X) : list (nat * X) := 
  match l with
  | h :: t => (n,h) :: add_indices (S n) t
  | [] => []
  end.

Fixpoint add_to_port_list (name : string) (atomid argpos : nat) (l : list (string * list (nat * nat))) :=
  match l with
  | (name', list) :: t => if string_dec name name'
                          then (name, (atomid, argpos) :: list) :: t
                          else (name, list) :: 
                               (add_to_port_list name atomid argpos t)
  | [] => [(name, [(atomid, argpos)])]
  end.

Definition add_atom_to_port_list (atomid : nat) (links : list Link) (pl : list (string * list (nat * nat))) :=
  fold_right (fun x a => match x with
              | (argpos,link) => add_to_port_list link atomid argpos a
              end) pl (add_indices O links).

Definition atom_list_to_port_list (atoms: list Atom) :=
  fold_right (fun x a => match x with
              | (atomid, AAtom _ links) => add_atom_to_port_list atomid links a
              end) [] (add_indices O atoms).

(* Definition term_to_port_list (t: Graph) := atom_list_to_port_list (term_to_atom_list t). *)

Definition count_atoms (t: Graph) := length (term_to_atom_list t).

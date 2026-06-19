Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Multiset.

Require Import Stdlib.Logic.Eqdep_dec.
Require Import Stdlib.Logic.ClassicalDescription.
Require Import Stdlib.Sorting.Permutation.

Definition Link := string.

Inductive Atom : Type :=
  | AAtom (name:string) (links:list Link)
  | AConn (X: Link) (Y: Link).

Inductive Functor : Type :=
  | FFunctor (name:string) (arity:nat).
Notation "p / n" := (FFunctor p n).

Definition Feq_dec: forall x y : Functor, {x=y} + {x<>y}.
Proof. repeat decide equality. Defined.

Definition get_functor (a:Atom) : Functor :=
  match a with
  | AAtom p ls => p / length ls
  | AConn x y => "=" / 2
  end.

Inductive Term : Type :=
  | TZero 
  | TAtom (atom:Atom)
  | TMol (g1 g2:Term).

Inductive Rule : Type :=
  | React (lhs rhs:Term).

Inductive RuleSet : Type :=
  | RZero
  | RRule (rule:Rule)
  | RMol (r1 r2:RuleSet).

Coercion RRule : Rule >-> RuleSet.
Coercion TAtom : Atom >-> Term.

Declare Custom Entry lmntal.
Declare Scope lmntal_scope.
Notation "{{ e }}" := e (at level 0, e custom lmntal at level 99) : lmntal_scope.
Notation "( x )" := x (in custom lmntal, x at level 2) : lmntal_scope.
Notation "x" := x (in custom lmntal at level 0, x constr at level 0) : lmntal_scope.
Notation "p ( x , .. , y )" := (AAtom p (cons x .. (cons y nil) .. ))
                  (in custom lmntal at level 0,
                  p constr at level 0, x constr at level 9,
                  y constr at level 9) : lmntal_scope.
Notation "p ()" := (AAtom p nil) (in custom lmntal at level 0,
                                  p constr at level 0) : lmntal_scope.
Notation "x = y" := (AConn x y) (in custom lmntal at level 40, left associativity) : lmntal_scope.
Notation "x , y" := (TMol x y) (in custom lmntal at level 90, left associativity) : lmntal_scope.
Notation "x ':-' y" := (React x y) (in custom lmntal at level 91, no associativity) : lmntal_scope.
Notation "x ';' y" := (RMol x y) (in custom lmntal at level 92, left associativity) : lmntal_scope.
Open Scope lmntal_scope.

Check {{ "Y" }} : Link.
Check {{ "p"("X","Y"),"q"("Y","X") }} : Term.
Check {{ "p"("X","Y"),"q"("Y","X") :- TZero }} : Rule.
Check {{ "p"("X","Y"),"q"("Y","X") :- TZero; RZero }} : RuleSet.

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

Fixpoint links (g: Term) : list Link := 
  match g with
  | TZero => []
  | TAtom a => match a with
    | AAtom p args => args
    | AConn x y => [x;y]
    end
  | {{P,Q}} => links P ++ links Q
  end.

Definition Leq_dec : forall x y : Link, {x=y} + {x<>y} := string_dec.

Definition unique_links (g: Term): list Link := nodup Leq_dec (links g).

Definition list_to_multiset (l:list Link) : multiset Link :=
  fold_right (fun x a => munion (SingletonBag eq Leq_dec x) a) (EmptyBag Link) l.

Definition link_multiset (g: Term) : multiset Link :=
  list_to_multiset (links g).

Definition freelinks (g: Term) : list Link := filter 
  (fun x => Nat.eqb (multiplicity (link_multiset g) x) 1) (unique_links g).

Definition locallinks (g: Term) : list Link := filter
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

Lemma Leq_dec_refl: 
  forall X, Leq_dec X X = left eq_refl.
Proof.
  intros X. destruct (Leq_dec X X).
  - apply f_equal, UIP_dec, Leq_dec.
  - congruence.
Qed.

Lemma Leq_dec_eq:
  forall X Y, X = Y <-> exists p, Leq_dec X Y = left p.
Proof.
  intros. destruct (Leq_dec X Y); split; intro H.
  - exists e. auto.
  - auto.
  - congruence.
  - destruct H. congruence.
Qed.

Lemma Leq_dec_neq:
  forall X Y, X <> Y <-> exists p, Leq_dec X Y = right p.
Proof.
  intros. destruct (Leq_dec X Y); split; intro H.
  - congruence.
  - destruct H. congruence.
  - exists n. auto.
  - auto.
Qed.

(* A graph is well-formed if each link name occurs at most twice in it *)
Definition wellformed_t (g:Term) : Prop :=
  forallb (fun x => Nat.leb (multiplicity (link_multiset g) x) 2) (unique_links g) = true.

Lemma wellformed_t_forall: forall g, wellformed_t g <->
  forall x, In x (links g) -> (multiplicity (link_multiset g) x) <= 2.
Proof.
  intros g.
  split.
  - intros H1 x H2.
    unfold wellformed_t in H1. rewrite forallb_forall in H1.
    apply in_unique_links in H2.
    apply H1 in H2. rewrite PeanoNat.Nat.leb_le in H2.
    apply H2.
  - intros H1. unfold wellformed_t. rewrite forallb_forall.
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

Definition substitute_link (Y X L : Link) :=
  if L =? X then Y else L.

(* P[Y/X] *)
Fixpoint substitute (Y X:Link) (P:Term) : Term :=
  match P with
  | TZero => TZero
  | TAtom a => TAtom (match a with
    | AAtom p args => AAtom p (map (substitute_link Y X) args)
    | AConn a b => AConn (substitute_link Y X a) (substitute_link Y X b)
    end)
  | {{P,Q}} => TMol (substitute Y X P) (substitute Y X Q)
  end.
Notation "P [ Y / X ]" := (substitute Y X P) (in custom lmntal at level 40, left associativity) : lmntal_scope.

Example substitute_example :
  {{ ( "p"("X", "Y"), "q"("Y", "X") ) [ "L" / "X" ] }} = {{ "p"("L", "Y"), "q"("Y", "L") }}.
Proof. reflexivity. Qed.

Reserved Notation "p == q" (at level 40).
Inductive cong : Term -> Term -> Prop :=
  | cong_E1 : forall P, wellformed_t P ->
              {{TZero, P}} == P
  | cong_E2 : forall P Q, wellformed_t {{P, Q}} -> 
              {{P, Q}} == {{Q, P}}
  | cong_E3 : forall P Q R, wellformed_t {{P, (Q, R)}} -> 
              {{P, (Q, R)}} == {{(P, Q), R}}
  | cong_E4 : forall P X Y, wellformed_t P -> wellformed_t {{ P[Y/X] }} ->
              In X (locallinks P) -> P == {{ P[Y/X] }}
  | cong_E5 : forall P P' Q, wellformed_t {{ P,Q }} -> wellformed_t {{ P',Q }} ->
              P == P' -> {{ P,Q }} == {{ P',Q }}
  | cong_E7 : forall X, {{ X = X }} == TZero
  | cong_E8 : forall X Y, {{ X = Y }} == {{ Y = X }}
  | cong_E9 : forall X Y (A:Atom),
              wellformed_t {{ X = Y, A }} -> wellformed_t {{ A[Y/X] }} ->
              In X (freelinks A) ->
              {{ X = Y, A }} == {{ A[Y/X] }}
  | cong_refl : forall P, wellformed_t P ->
                  P == P
  | cong_trans : forall P Q R, wellformed_t P -> wellformed_t Q -> wellformed_t R ->
                  P == Q -> Q == R -> P == R
  | cong_sym : forall P Q, wellformed_t P -> wellformed_t Q -> 
                  P == Q -> Q == P
  where "p '==' q" := (cong p q).

Example cong_example : {{ "p"("X","X") }} == {{ "p"("Y","Y") }}.
Proof.
  replace ({{ "p"("Y","Y") }}:Term) with {{ "p"("X","X")["Y"/"X"] }}; auto.
  apply cong_E4; unfold wellformed_t; auto.
  simpl. auto.
Qed.

Ltac solve_refl :=
  repeat (
    unfold wellformed_t, wellformed_r,
            freelinks, locallinks,
            unique_links, substitute_link
  || rewrite Leq_dec_refl
  || rewrite eqb_refl
  || simpl); auto.

Example cong_example_var : forall p X Y, {{ p(X,X) }} == {{ p(Y,Y) }}.
Proof.
  intros p X Y.
  replace ({{ p(Y,Y) }}:Term) with {{ p(X,X)[Y/X] }}.
  - apply cong_E4; solve_refl.
  - solve_refl.
Qed.

Reserved Notation "p '-[' r ']->' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Inductive rrel : Rule -> Term -> Term -> Prop :=
  | rrel_R1 : forall G1 G1' G2 r,
                wellformed_t {{G1,G2}} -> wellformed_t {{G1',G2}} ->
                wellformed_r r ->
                G1 -[ r ]-> G1' -> {{G1,G2}} -[ r ]-> {{G1',G2}}
  | rrel_R3 : forall G1 G1' G2 G2' r,
                wellformed_r r ->
                G2 == G1 -> G1' == G2' ->
                G1 -[ r ]-> G1' -> G2 -[ r ]-> G2'
  | rrel_R6 : forall T U,
                wellformed_t T -> wellformed_t U ->
                wellformed_r {{ T :- U }} ->
                T -[ T :- U ]-> U
  where "p '-[' r ']->' q" := (rrel r p q).

Reserved Notation "p '-[' r ']->*' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Inductive rrel_rep : Rule -> Term -> Term -> Prop :=
  | rrel_rep_refl : forall r a b, a == b -> a -[ r ]->* b
  | rrel_rep_step : forall r a b c, a -[ r ]->* b -> b -[ r ]-> c -> a -[ r ]->* c
  where "p '-[' r ']->*' q" := (rrel_rep r p q).

Reserved Notation "p '=[' r ']=>' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Fixpoint rrel_ruleset (rs : RuleSet) (p q : Term) : Prop :=
  match rs with
  | RZero => False
  | RRule r => p -[ r ]-> q
  | RMol a b => p =[ a ]=> q \/ p =[ b ]=> q
  end
  where "p '=[' rs ']=>' q" := (rrel_ruleset rs p q).

Reserved Notation "p '=[' r ']=>*' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Inductive rrel_ruleset_rep : RuleSet -> Term -> Term -> Prop :=
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
  - apply cong_trans with (Q:={{"a"(),("b"("Z"),"c"("Z"))}}); unfold wellformed_t; auto.
    + apply cong_sym; unfold wellformed_t; auto.
      apply cong_E3; unfold wellformed_t; auto.
    + apply cong_trans with (Q:={{"b" ("Z"), "c" ("Z"), "a" ()}}); unfold wellformed_t; auto.
      * apply cong_E2; unfold wellformed_t; auto.
      * assert (H1: {{"b"("X"), "c"("X"), "a"()}}={{("b"("Z"), "c"("Z"),"a"())["X"/"Z"] }}).
        { reflexivity. }
        rewrite H1.
        apply cong_E4; unfold wellformed_t; auto.
        simpl. auto.
  - apply cong_E2; unfold wellformed_t; auto.
  - apply rrel_R1; unfold wellformed_t; auto.
    + unfold wellformed_r. unfold link_list_eq. simpl. apply meq_refl.
    + apply rrel_R6; unfold wellformed_t; auto.
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

Fixpoint ruleset_to_list rs :=
  match rs with
  | RZero => []
  | RRule r => [r]
  | RMol a b => (ruleset_to_list a) ++ (ruleset_to_list b)
  end.

Lemma rrel_ruleset_In :
  forall p q rs, p =[ rs ]=> q <->
    (exists r, In r (ruleset_to_list rs)
      /\ p -[ r ]-> q).
Proof.
  intros p q rs.
  generalize dependent q.
  generalize dependent p.
  induction rs; split; intros H.
  - simpl in H. destruct H.
  - simpl in H. destruct H.
    destruct H as [[] _].
  - simpl in H. exists rule.
    simpl. auto.
  - simpl in H. destruct H.
    destruct H as [[H1|[]] H2].
    simpl. rewrite H1. auto.
  - destruct H;
    [ rewrite IHrs1 in H | rewrite IHrs2 in H ];
    destruct H; destruct H as [H1 H2];
    exists x; simpl;
    rewrite in_app_iff; auto.
  - destruct H. simpl.
    simpl in H. rewrite in_app_iff in H.
    destruct H as [[H1|H1] H2];
    [ left | right ];
    [ rewrite IHrs1 | rewrite IHrs2 ];
    exists x; auto.
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
    replace (links TZero) with ([]:list Link).
    + simpl. apply munion_empty_left.
    + reflexivity.
  - intros G2. unfold link_multiset. destruct atom; simpl.
    { apply list_to_multiset_app. }
    apply meq_trans with (munion
    (munion (SingletonBag eq Leq_dec X)
       (SingletonBag eq Leq_dec Y))
    (list_to_multiset (links G2))).
    { apply meq_sym, munion_ass. }
    apply meq_left, meq_right, munion_empty_right.
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

Lemma wellformed_t_inj:
  forall G1 G2, wellformed_t {{G1,G2}} -> wellformed_t G1 /\ wellformed_t G2.
Proof.
  intros G1 G2 H.
  rewrite wellformed_t_forall in H.
  split.
  - rewrite wellformed_t_forall. intros x H1.
    apply PeanoNat.Nat.le_trans with (multiplicity (link_multiset {{G1, G2}}) x).
    + apply multiplicity_munionL with (link_multiset G2).
      apply link_multiset_mol.
    + apply H. rewrite links_mol. left. apply H1.
  - rewrite wellformed_t_forall. intros x H1.
    apply PeanoNat.Nat.le_trans with (multiplicity (link_multiset {{G1, G2}}) x).
    + apply multiplicity_munionR with (link_multiset G1).
      apply link_multiset_mol.
    + apply H. rewrite links_mol. right. apply H1.
Qed.

Lemma connector_wellformed_t :
  forall X Y, wellformed_t {{ X = Y }}.
Proof.
  intros X Y.
  unfold wellformed_t.
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
        apply Arith_base.le_plus_trans_stt.
        (* apply Plus.le_plus_trans. *)
        apply H.
    + destruct (Leq_dec a x).
      * left. auto.
      * right. simpl in H. apply IHl.
        apply H.
Qed.

Lemma wellformed_t_link_multiset:
  forall P Q,
    meq (link_multiset P) (link_multiset Q) ->
    wellformed_t P -> wellformed_t Q.
Proof.
  intros P Q H.
  rewrite wellformed_t_forall.
  rewrite wellformed_t_forall.
  intros HP x Hx.
  unfold meq in H. rewrite <- H.
  apply HP.
  apply in_links_link_multiset.
  rewrite H.
  apply in_links_link_multiset.
  apply Hx.
Qed.

Lemma link_multiset_inj :
  forall P1 Q1 P2 Q2,
    meq (link_multiset P1) (link_multiset P2) ->
    meq (link_multiset Q1) (link_multiset Q2) ->
    meq (link_multiset {{P1, Q1}}) (link_multiset {{P2, Q2}}).
Proof.
  intros P1 Q1 P2 Q2 H1 H2.
  apply meq_trans with (munion (link_multiset P1) (link_multiset Q1)).
  { apply link_multiset_mol. }
  apply meq_trans with (munion (link_multiset P2) (link_multiset Q2)).
  { apply meq_congr; auto. }
  apply meq_sym. apply link_multiset_mol.
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

Lemma cong_wellformed_t :
  forall P Q, P == Q -> wellformed_t P /\ wellformed_t Q.
Proof.
  intros P Q H.
  induction H; auto; split; auto.
  - apply wellformed_t_link_multiset with {{P,Q}}; auto.
    apply link_multiset_swap.
  - apply wellformed_t_link_multiset with {{P,(Q,R)}}; auto.
    apply link_multiset_assoc.
  - apply connector_wellformed_t.
  - unfold wellformed_t.
    simpl. auto.
  - apply connector_wellformed_t.
  - apply connector_wellformed_t.
Qed.

Lemma rrel_wellformed :
  forall P Q r, P -[ r ]-> Q ->
    wellformed_t P /\ wellformed_t Q /\ wellformed_r r.
Proof.
  intros P Q r H.
  induction H; auto.
  apply cong_wellformed_t in H0.
  apply cong_wellformed_t in H1.
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
    + apply cong_sym; auto; apply cong_wellformed_t in H1; destruct H1; auto.
    + apply cong_sym; auto; apply cong_wellformed_t in H0; destruct H0; auto.
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
Inductive congm : Term -> Term -> Prop :=
  | congm_E1 : forall P, wellformed_t P ->
                {{TZero, P}} ==m P
  | congm_E2 : forall P Q, wellformed_t {{P, Q}} ->
                {{P, Q}} ==m {{Q, P}}
  | congm_E3 : forall P Q R, wellformed_t {{P, (Q, R)}} -> 
                {{P, (Q, R)}} ==m {{(P, Q), R}}
  | congm_E5 : forall P P' Q, wellformed_t {{ P,Q }} -> wellformed_t {{ P',Q }} ->
                P ==m P' -> {{ P,Q }} ==m {{ P',Q }}
  | congm_E7 : forall X, {{ X = X }} ==m TZero
  | congm_E9 : forall X Y (A:Atom), 
                wellformed_t {{ X = Y, A }} -> wellformed_t {{ A[Y/X] }} ->
                In X (freelinks A) ->
                {{ X = Y, A }} ==m {{ A[Y/X] }}
  | congm_refl : forall P, wellformed_t P ->
                  P ==m P
  | congm_trans : forall P Q R, wellformed_t P -> wellformed_t Q -> wellformed_t R ->
    P ==m Q -> Q ==m R -> P ==m R
  | congm_sym : forall P Q, wellformed_t P -> wellformed_t Q -> 
    P ==m Q -> Q ==m P
  where "p '==m' q" := (congm p q).

Lemma in_freelinks:
  forall X P, In X (freelinks P) <-> multiplicity (link_multiset P) X = 1.
Proof.
  intros X P. unfold freelinks.
  rewrite filter_In.
  rewrite PeanoNat.Nat.eqb_eq.
  split.
  - intros [H1 H2]. auto.
  - intros H. split; auto.
    apply in_unique_links.
    apply in_links_link_multiset.
    rewrite H. auto.
Qed.

Lemma multiplicity_mol:
  forall P Q X,
    multiplicity (link_multiset {{P, Q}}) X
    = multiplicity (link_multiset P) X + multiplicity (link_multiset Q) X.
Proof.
  apply link_multiset_mol.
Qed.

Lemma multiplicity_not_in:
  forall P X,
    multiplicity (link_multiset P) X = 0
    <-> ~ In X (links P).
Proof.
  intros P X.
  split; intros H.
  - unfold not. intros H1.
    apply in_links_link_multiset in H1.
    rewrite H in H1.
    apply Compare_dec.nat_compare_ge in H1.
    auto.
  - unfold link_multiset.
    induction (links P); auto.
    simpl. simpl in H.
    destruct (Leq_dec a X); auto.
    exfalso. auto.
Qed.

Lemma in_freelinks_mol:
  forall X P Q, In X (freelinks {{P,Q}}) <->
    In X (freelinks P) /\ ~ In X (links Q) \/
    In X (freelinks Q) /\ ~ In X (links P).
Proof.
  intros X P Q.
  repeat rewrite in_freelinks.
  rewrite multiplicity_mol.
  split; intros H.
  - apply PeanoNat.Nat.eq_add_1 in H.
    destruct H as [[H1 H2]|[H1 H2]]; [left | right]; split; auto;
    apply multiplicity_not_in; auto.
  - destruct H as [[H1 H2]|[H1 H2]]; apply multiplicity_not_in in H2;
    rewrite H1, H2; auto.
Qed.

Lemma in_locallinks:
  forall X P, In X (locallinks P) <-> multiplicity (link_multiset P) X = 2.
Proof.
  intros X P. unfold locallinks.
  rewrite filter_In.
  rewrite PeanoNat.Nat.eqb_eq.
  split.
  - intros [H1 H2]. auto.
  - intros H. split; auto.
    apply in_unique_links.
    apply in_links_link_multiset.
    rewrite H. auto.
Qed.

Lemma congm_E8_sub :
  forall X Y Z, X <> Z -> Y <> Z ->
    wellformed_t {{ Z=X, Z=Y }} ->
    {{ Z=X, Z=Y }} ==m {{ X=Y }}.
Proof.
  intros X Y Z Hxz Hyz H.
  destruct (Leq_dec Y Z) eqn:EYZ.
  { congruence. }
  apply congm_trans with {{ (Z=Y)[X/Z] }}; auto.
  - apply connector_wellformed_t.
  - apply connector_wellformed_t.
  - apply congm_E9; auto.
    { simpl. apply connector_wellformed_t. }
    unfold freelinks.
    simpl. unfold unique_links.
    simpl. rewrite EYZ.
    simpl. repeat rewrite Leq_dec_refl.
    rewrite EYZ. simpl. auto.
  - simpl. solve_refl.
    replace (Y =? Z) with false.
    + apply congm_refl.
      apply connector_wellformed_t.
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

Lemma wellformed_t_swap :
  forall P Q, wellformed_t {{P,Q}} -> wellformed_t {{Q,P}}.
Proof.
  intros P Q H.
  apply wellformed_t_link_multiset with {{P,Q}}.
  - apply link_multiset_swap.
  - auto.
Qed.

Lemma wellformed_t_zx_zy:
  forall X Y Z,
    X <> Z -> Y <> Z -> wellformed_t {{Z = X, Z = Y}}.
Proof.
  intros X Y Z Hxz Hyz.
  apply wellformed_t_forall.
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
  assert (WF: wellformed_t {{Z = X, Z = Y}}).
  { apply wellformed_t_zx_zy; auto. }
  apply congm_trans with {{ Z=X, Z=Y }}.
  - apply connector_wellformed_t.
  - apply WF. 
  - apply connector_wellformed_t.
  - apply congm_sym; auto.
    + apply connector_wellformed_t.
    + apply congm_E8_sub; auto.
  - apply congm_trans with {{ Z=Y,Z=X }}; auto.
    + apply wellformed_t_swap. auto.
    + apply connector_wellformed_t.
    + apply congm_E2. auto.
    + apply congm_E8_sub; auto.
      apply wellformed_t_swap. auto.
Qed.

Lemma sum_2 :
  forall a b,
    a + b = 2 <->
      a = 2 /\ b = 0 \/
      a = 1 /\ b = 1 \/
      a = 0 /\ b = 2.
Proof.
  intros a b.
  split.
  - intros H.
    destruct a; auto.
    destruct a; auto.
    simpl in H. left.
    inversion H.
    apply PeanoNat.Nat.eq_add_0 in H1.
    destruct H1.
    rewrite !H0, !H1.
    auto.
  - intros [[H1 H2]|[[H1 H2]|[H1 H2]]];
    rewrite H1,H2; auto.
Qed.

Lemma in_locallinks_mol :
  forall P Q X,
    In X (locallinks {{P,Q}}) <->
      In X (locallinks P) /\ ~ In X (links Q)  \/
      In X (locallinks Q) /\ ~ In X (links P) \/
      In X (freelinks P) /\ In X (freelinks Q).
Proof.
  intros P Q X.
  repeat rewrite in_locallinks.
  repeat rewrite in_freelinks.
  repeat rewrite <- multiplicity_not_in.
  rewrite multiplicity_mol.
  rewrite sum_2.
  split; intros [[H1 H2]|[[H1 H2]|[H1 H2]]];
  rewrite !H1,!H2; auto.
Qed.

Lemma subst_mol:
  forall P Q X Y,
    {{(P,Q)[Y/X]}} = {{P[Y/X],Q[Y/X]}}.
Proof.
  intros P Q X Y.
  induction P; auto.
Qed.

Lemma subst_multiplicity_X:
  forall P X Y,
    X <> Y ->
    multiplicity (link_multiset {{P[Y/X]}}) X = 0.
Proof.
  intros P.
  induction P; intros X Y H; auto.
  - destruct atom as [n ls|a b]; simpl. 
    { induction ls as [|h t IH]; auto.
    simpl. unfold link_multiset in IH.
    simpl in IH. rewrite IH. solve_refl.
    destruct (h =? X) eqn:E1.
    + destruct (Leq_dec Y X); auto.
      destruct H. auto.
    + destruct (Leq_dec h X); auto.
      apply eqb_neq in E1. destruct E1.
      auto. }
    solve_refl. destruct (a =? X) eqn:e1.
    + destruct (Leq_dec Y X).
      * destruct H. auto.
      * destruct (b =? X) eqn:e2.
        { destruct (Leq_dec Y X); auto. destruct n. auto. }
        destruct (Leq_dec b X); auto.
        apply eqb_neq in e2. destruct e2.
        auto.
    + destruct (Leq_dec a X).
      { apply eqb_neq in e1. destruct e1. auto. }
      destruct (b =? X) eqn:e2.
      { destruct (Leq_dec Y X); auto.
        destruct H. auto. }
      destruct (Leq_dec b X); auto.
      apply eqb_neq in e2. destruct e2. auto.
  - rewrite subst_mol.
    rewrite link_multiset_mol. simpl.
    apply PeanoNat.Nat.eq_add_0.
    auto.
Qed.

Lemma subst_multiplicity_Y:
  forall P X Y, X <> Y ->
    multiplicity (link_multiset {{P[Y/X]}}) Y =
    multiplicity (link_multiset P) X + multiplicity (link_multiset P) Y.
Proof.
  intros P X Y H.
  induction P; auto.
  - destruct atom as [n ls|x y].
    { simpl. induction ls as [|h t IH]; auto.
    unfold link_multiset in IH.
    simpl in IH.
    simpl. destruct (Leq_dec h X).
    + rewrite e. solve_refl.
      unfold substitute_link in IH.
      f_equal. rewrite IH.
      f_equal. destruct (Leq_dec X Y); auto.
      destruct H. auto.
    + solve_refl. unfold substitute_link in IH.
      apply eqb_neq in n0.
      rewrite n0. simpl.
      destruct (Leq_dec h Y); auto.
      simpl. rewrite IH. auto. }
    simpl. solve_refl.
    destruct (x =? X) eqn:e1.
    + apply eqb_eq in e1. rewrite e1. solve_refl.
      destruct (y =? X) eqn:e2.
      * apply eqb_eq in e2. rewrite e2. solve_refl.
        repeat f_equal.
        apply Leq_dec_neq in H.
        destruct H. rewrite H. auto.
      * apply eqb_neq in e2. apply Leq_dec_neq in e2.
        destruct e2. rewrite H0.
        apply Leq_dec_neq in H.
        destruct H. rewrite H. simpl. auto.
    + apply eqb_neq in e1.
      apply Leq_dec_neq in e1. destruct e1.
      rewrite H0. destruct (y =? X) eqn:e2.
      * apply eqb_eq in e2. rewrite e2. solve_refl.
        apply Leq_dec_neq in H. destruct H.
        rewrite H. auto.
      * apply eqb_neq in e2. apply Leq_dec_neq in e2.
        destruct e2. rewrite H1. auto.
  - rewrite subst_mol, !multiplicity_mol.
    rewrite IHP1, IHP2.
    apply PeanoNat.Nat.add_shuffle1.
Qed.

Lemma subst_id :
  forall P X, {{P[X/X]}} = P.
Proof.
  intros P X.
  induction P; auto.
  - destruct atom as [n ls|x y].
    { simpl. induction ls as [|h t IH]; auto.
    simpl. replace (map (substitute_link X X) t) with t.
    + solve_refl. destruct (h =? X) eqn:E; auto.
      apply eqb_eq in E.
      rewrite E. auto.
    + inversion IH. repeat rewrite H0. auto. }
    simpl. solve_refl.
    destruct (x =? X) eqn:E1; destruct (y =? X) eqn:E2.
    + apply eqb_eq in E1,E2. rewrite E1,E2. auto.
    + apply eqb_eq in E1. rewrite E1. auto.
    + apply eqb_eq in E2. rewrite E2. auto.
    + auto.
  - rewrite subst_mol.
    f_equal; auto.
Qed.

Lemma subst_none :
  forall P X Y,
    P = {{ P[Y/X] }} <-> X = Y \/ ~ In X (links P).
Proof.
  intros P X Y.
  split; intros H.
  - destruct (Leq_dec X Y); auto.
    right. induction P; auto.
    + destruct atom as [name ls|x y].
      { simpl in H. simpl. inversion H.
      rewrite <- H1. induction ls as [|h t IH]; auto.
      simpl in H1. inversion H1. solve_refl.
      unfold substitute_link in H1,IH,H2,H3.
      destruct (h =? X) eqn:E.
      { apply eqb_eq in E. congruence. }
      rewrite <- H3. simpl.
      intros C.
      destruct C.
      { apply eqb_neq in E. congruence. }
      apply IH; auto.
      rewrite <- H3.
      reflexivity. }
      simpl. simpl in H. inversion H.
      rewrite <- H1, <- H2. simpl.
      intro C. destruct C as [C|[C|C]]; auto.
      * rewrite C in H1.
        unfold substitute_link in H1.
        rewrite eqb_refl in H1. congruence.
      * rewrite C in H2.
        unfold substitute_link in H2.
        rewrite eqb_refl in H2. congruence.
    + rewrite links_mol.
      rewrite subst_mol in H.
      inversion H. intros [H0|H0];
      rewrite in_links_link_multiset in H0;
      rewrite subst_multiplicity_X in H0; auto;
      apply Compare_dec.nat_compare_ge in H0; auto.
  - destruct (Leq_dec X Y).
    { rewrite e. rewrite subst_id. reflexivity. }
    destruct H.
    { rewrite H. rewrite subst_id. reflexivity. }
    induction P; auto.
    + destruct atom as [name ls|x y].
      { simpl. induction ls as [|h t IH]; auto.
      simpl. destruct (h =? X) eqn:E.
      * simpl in H. simpl in IH.
        apply eqb_eq in E.
        rewrite E in H.
        destruct H. auto.
      * simpl in H.
        apply eqb_neq in E. simpl in IH.
        apply Decidable.not_or in H.
        destruct H as [H1 H2].
        apply IH in H2.
        inversion H2.
        repeat rewrite <- H0. solve_refl.
        apply eqb_neq in E. rewrite E. auto. }
      solve_refl.
      destruct (x =? X) eqn:e1; destruct (y =? X) eqn:e2.
      * apply eqb_eq in e1. rewrite e1 in H.
        destruct H. simpl. left. auto.
      * apply eqb_eq in e1. rewrite e1 in H.
        destruct H. simpl. left. auto.
      * apply eqb_eq in e2. rewrite e2 in H.
        destruct H. simpl. right. left. auto.
      * auto. 
    + rewrite subst_mol.
      rewrite links_mol in H.
      apply Decidable.not_or in H.
      destruct H. f_equal; auto.
Qed.

Lemma subst_multiplicity_other:
  forall P X Y Z, X <> Z -> Y <> Z ->
    multiplicity (link_multiset {{P[Y/X]}}) Z =
    multiplicity (link_multiset P) Z.
Proof.
  intros P X Y Z HX HY.
  induction P; auto.
  - destruct atom as [name ls|x y].
    { induction ls as [|h t IH]; auto.
    simpl in IH.
    unfold link_multiset in IH.
    simpl in IH. simpl.
    solve_refl.
    destruct (h =? X) eqn:E.
    + destruct (Leq_dec Y Z); simpl.
      { congruence. }
      apply eqb_eq in E. rewrite E.
      destruct (Leq_dec X Z); simpl.
      { congruence. }
      unfold substitute_link in IH.
      apply IH.
    + destruct (Leq_dec h Z); simpl.
      unfold substitute_link in IH.
      { congruence. }
      apply IH. }
    solve_refl.
    apply Leq_dec_neq in HX,HY.
    destruct HX as [HX eX], HY as [HY eY].
    destruct (x =? X) eqn:e1; destruct (y =? X) eqn:e2.
    + apply eqb_eq in e1,e2. rewrite e1,e2.
      rewrite eX,eY. auto.
    + apply eqb_eq in e1. rewrite e1.
      rewrite eX,eY. auto.
    + apply eqb_eq in e2. rewrite e2. 
      rewrite eX,eY. auto.
    + auto.
  - rewrite subst_mol, !multiplicity_mol.
    rewrite IHP1, IHP2. reflexivity.
Qed.

Lemma subst_wellformed_t :
  forall X Y P,
    wellformed_t P ->
    multiplicity (link_multiset P) X + multiplicity (link_multiset P) Y <= 2 ->
    wellformed_t {{ P[Y/X] }}.
Proof.
  intros X Y P.
  rewrite !wellformed_t_forall.
  intros H1 H2 L H3.
  destruct (Leq_dec X Y).
  { rewrite e, subst_id.
    rewrite e, subst_id in H3.
    auto. }
  destruct (Leq_dec X L).
  { rewrite <- e.
    rewrite subst_multiplicity_X; auto. }
  destruct (Leq_dec Y L).
  { rewrite <- e.
    rewrite subst_multiplicity_Y; auto. }
  rewrite subst_multiplicity_other; auto.
  apply H1.
  rewrite in_links_link_multiset.
  rewrite in_links_link_multiset in H3.
  rewrite subst_multiplicity_other in H3; auto.
Qed.

Lemma congm_E5r :
  forall P Q Q', wellformed_t {{ P,Q }} -> wellformed_t {{ P,Q' }} ->
    Q ==m Q' -> {{ P,Q }} ==m {{ P,Q' }}.
Proof.
  intros P Q Q' H1 H2 H3.
  apply congm_trans with {{Q,P}}; auto.
  { apply wellformed_t_swap. auto. }
  { apply congm_E2. auto. }
  apply congm_trans with {{Q',P}}; auto.
  { apply wellformed_t_swap. auto. }
  { apply wellformed_t_swap. auto. }
  { apply congm_E5; auto; apply wellformed_t_swap; auto. }
  apply congm_E2.
  apply wellformed_t_swap. auto.
Qed.

Lemma congm_E9ex :
  forall X Y P, 
    wellformed_t {{ X = Y, P }} -> wellformed_t {{ P[Y/X] }} ->
    In X (freelinks P) ->
    {{ X = Y, P }} ==m {{ P[Y/X] }}.
Proof.
  intros X Y P H1 H2 H3.
  destruct (Leq_dec X Y).
  { rewrite e, subst_id.
    rewrite e in H1.
    assert (A: wellformed_t P).
    { rewrite e, subst_id in H2. auto. }
    apply congm_trans with {{TZero, P}}; auto.
    { apply congm_E5; auto. apply congm_E7. }
    apply congm_E1; auto. }
  induction P.
  { simpl. simpl in H3. destruct H3. }
  { apply congm_E9; auto. }
  simpl in H2. apply wellformed_t_inj in H2.
  destruct H2 as [H21 H22].
  assert (WF1: wellformed_t {{P1 [Y / X], P2 [Y / X]}}).
  { rewrite <- subst_mol.
    apply subst_wellformed_t.
    apply wellformed_t_inj in H1;
    destruct H1; auto.
    rewrite !multiplicity_mol.
    rewrite wellformed_t_forall in H1.
    assert (AX: In X (links {{X=Y,(P1,P2)}})).
    { apply in_links_link_multiset. simpl.
      rewrite Leq_dec_refl. simpl.
      apply le_n_S. apply le_0_n. }
    assert (AY: In Y (links {{X=Y,(P1,P2)}})).
    { apply in_links_link_multiset. simpl.
      rewrite Leq_dec_refl. simpl.
      rewrite PeanoNat.Nat.add_succ_r.
      apply le_n_S. apply le_0_n. }
    apply H1 in AX, AY.
    rewrite !multiplicity_mol in AX, AY.
    simpl in AX, AY.
    rewrite Leq_dec_refl in AX, AY.
    destruct (Leq_dec X Y).
    { congruence. }
    destruct (Leq_dec Y X).
    { congruence. }
    simpl in AX, AY.
    apply le_S_n in AX, AY.
    replace 2 with (1+1); auto.
    apply PeanoNat.Nat.add_le_mono; auto. }
  apply in_freelinks_mol in H3.
  destruct H3.
  - rewrite subst_mol.
    destruct H.
    assert (A: {{P2[Y/X]}}=P2).
    { symmetry. apply subst_none. auto. }
    apply congm_trans with {{(X=Y,P1),P2}}; auto.
    { apply congm_E3; auto. }
    rewrite A.
    apply congm_E5; auto.
    { rewrite <- A. auto. }
    apply IHP1; auto.
    apply wellformed_t_link_multiset with (Q:={{X=Y,P1,P2}}) in H1.
    + apply wellformed_t_inj in H1. destruct H1. auto.
    + apply link_multiset_assoc.
  - rewrite subst_mol.
    destruct H.
    assert (A: {{P1[Y/X]}}=P1).
    { symmetry. apply subst_none. auto. }
    assert (A1: wellformed_t {{X = Y, (P2, P1)}}).
    { apply wellformed_t_link_multiset with {{X=Y,(P1,P2)}}; auto.
      apply link_multiset_inj.
      - apply meq_refl.
      - apply link_multiset_swap. }
    apply congm_trans with {{X=Y,(P2,P1)}}; auto.
    { apply congm_E5r; auto. apply congm_E2.
      apply wellformed_t_inj in H1. destruct H1. auto. }
    apply congm_trans with {{(X=Y,P2),P1}}; auto.
    { apply congm_E3; auto. }
    rewrite A. rewrite A in WF1.
    apply congm_trans with {{P2 [Y / X], P1}}; auto.
    { apply wellformed_t_swap. auto. }
    { apply congm_E5; auto.
      { apply wellformed_t_swap. auto. }
      apply IHP2; auto.
      apply wellformed_t_link_multiset with (Q:={{X=Y,P2,P1}}) in H1.
      { apply wellformed_t_inj in H1. destruct H1. auto. }
      apply meq_trans with (link_multiset {{X=Y,(P2,P1)}}).
      { apply link_multiset_inj.
        - apply meq_refl.
        - apply link_multiset_swap. }
      apply link_multiset_assoc. }
    apply congm_E2.
    apply wellformed_t_swap. auto.
Qed.

Fixpoint subst_once_list (Y X:Link) (ls:list Link) : option (list Link) :=
  match ls with
  | [] => None
  | h::t => if h =? X then Some (Y::t)
            else 
              match subst_once_list Y X t with
              | Some t' => Some (h::t')
              | None => None
              end
  end.

Fixpoint subst_once (Y X:Link) (P:Term) : option Term :=
  match P with
  | TZero => None
  | TAtom a => match a with 
    | AConn x y => if x =? X then Some (TAtom (AConn Y y))
                   else if y =? X then Some (TAtom (AConn x Y))
                   else None
    | AAtom p args => match subst_once_list Y X args with
                      | Some ls => Some (TAtom (AAtom p ls))
                      | None => None
                      end
    end
  | {{P,Q}} => 
            match subst_once Y X P with
            | Some P' => Some {{P',Q}}
            | None =>
              match subst_once Y X Q with
              | Some Q' => Some {{P,Q'}}
              | None => None
              end
            end
  end.

Lemma subst_once_Some:
  forall P X Y,
    (exists G, subst_once Y X P = Some G) <->
    In X (links P).
Proof.
  intros P X Y.
  induction P.
  - simpl.
    split; intros H.
    + destruct H. inversion H.
    + destruct H.
  - simpl.
    destruct atom as [name ls|x y].
    { induction ls as [|h t IH].
    + split; simpl; intros H.
      * destruct H. inversion H.
      * destruct H.
    + split; simpl; intros H.
      * destruct (h =? X) eqn:E.
        { left. apply eqb_eq. auto. }
        right. apply IH.
        destruct H as [G0 H].
        destruct (subst_once_list Y X t).
        { exists (AAtom name l). auto. }
        inversion H.
      * destruct H.
        { rewrite H. rewrite eqb_refl.
          exists ((AAtom name (Y :: t))). auto. }
        apply IH in H.
        destruct H as [G0 H].
        destruct (h =? X) eqn:E.
        { exists (AAtom name (Y :: t)). auto. }
        destruct (subst_once_list Y X t).
        { exists (AAtom name (h :: l)). auto. }
        inversion H. }
    simpl. destruct (x =? X) eqn:e1.
    { split; intro H. 
      { destruct H. left. apply eqb_eq. auto. }
      exists {{Y=y}}. auto.
    }
    destruct (y=?X) eqn:e2.
    { split; intro H.
      { destruct H. right. left. apply eqb_eq. auto. }
      exists {{x=Y}}. auto. }
    split; intro H.
    { destruct H. inversion H. }
    destruct H as [H|[H|[]]]; apply eqb_neq in e1,e2; congruence.
  - simpl. rewrite in_app_iff.
    destruct (subst_once Y X P1) eqn:E1.
    + split; intros H.
      * left. apply IHP1. exists t. auto.
      * exists {{t, P2}}. auto.
    + destruct (subst_once Y X P2) eqn:E2;
      split; intros H.
      * right. apply IHP2. exists t. auto.
      * exists {{P1, t}}. auto.
      * destruct H. inversion H.
      * destruct H;
        [ apply IHP1 in H | apply IHP2 in H ];
        destruct H; inversion H.
Qed.

Lemma subst_once_None:
  forall P X Y,
    subst_once Y X P = None <->
    ~ In X (links P).
Proof.
  intros P X Y.
  destruct (subst_once Y X P) eqn:E.
  - split; try congruence.
    intros H. rewrite <- subst_once_Some in H.
    exfalso. apply H.
    exists t. apply E.
  - split; try congruence.
    intros H C.
    rewrite <- subst_once_Some in C.
    destruct C as [G C].
    rewrite E in C.
    inversion C.
Qed. 

Lemma subst_once_list_multiplicity_X:
  forall l1 l2 X Y,
    Y <> X ->
    subst_once_list Y X l1 = Some l2 ->
    multiplicity (list_to_multiset l2) X =
    multiplicity (list_to_multiset l1) X - 1.
Proof.
  intros l1.
  induction l1.
  - intros l2 X Y H1 H2.
    simpl in H2. inversion H2.
  - intros l2 X Y H1 H2.
    simpl in H2.
    destruct (a=?X) eqn:E.
    + inversion H2.
      simpl.
      destruct (Leq_dec Y X).
      { congruence. }
      destruct (Leq_dec a X).
      * simpl. rewrite PeanoNat.Nat.sub_0_r.
        auto.
      * rewrite eqb_eq in E. congruence.
    + destruct (subst_once_list Y X l1) eqn:E1.
      * inversion H2. simpl.
        destruct (Leq_dec a X).
        { rewrite eqb_neq in E. congruence. }
        simpl. apply IHl1 with (Y:=Y); auto.
      * inversion H2.
Qed.

Lemma subst_once_list_multiplicity_Y:
  forall l1 l2 X Y,
    Y <> X ->
    subst_once_list Y X l1 = Some l2 ->
    multiplicity (list_to_multiset l2) Y =
    multiplicity (list_to_multiset l1) Y + 1.
Proof.
  intros l1.
  induction l1.
  - intros l2 X Y H1 H2.
    simpl in H2. inversion H2.
  - intros l2 X Y H1 H2.
    simpl. simpl in H2.
    destruct (a =? X) eqn:E.
    + inversion H2.
      simpl. rewrite Leq_dec_refl.
      apply eqb_eq in E.
      rewrite E.
      destruct (Leq_dec X Y).
      { congruence. }
      simpl. rewrite PeanoNat.Nat.add_1_r.
      auto.
    + destruct (subst_once_list Y X l1) eqn:E1.
      * inversion H2. simpl.
        replace (multiplicity (list_to_multiset l) Y)
          with (multiplicity (list_to_multiset l1) Y + 1).
        { apply PeanoNat.Nat.add_assoc. }
        symmetry. apply IHl1 with X; auto.
      * inversion H2.
Qed.

Lemma subst_once_multiplicity_X:
  forall P P' X Y,
    Y <> X ->
    subst_once Y X P = Some P' ->
    multiplicity (link_multiset P') X 
    = multiplicity (link_multiset P) X - 1.
Proof.
  intros P.
  induction P; intros P' X Y NE H; 
  generalize dependent P'; simpl.
  - intros P' H. simpl in H. inversion H.
  - destruct atom as [name ls|x y].
    { induction ls.
    + intros P' H. simpl in H. inversion H.
    + intros P' H. simpl in H.
      destruct (a =? X) eqn:EaX.
      * inversion H.
        simpl. apply eqb_eq in EaX.
        rewrite EaX. rewrite Leq_dec_refl.
        destruct (Leq_dec Y X).
        { congruence. }
        simpl. rewrite PeanoNat.Nat.sub_0_r.
        reflexivity.
      * simpl. apply eqb_neq in EaX.
        destruct (Leq_dec a X) eqn:E.
        { congruence. }
        destruct (subst_once_list Y X ls) eqn:E1; auto.
        simpl. inversion H.
        simpl. rewrite E. simpl.
        apply subst_once_list_multiplicity_X with (Y:=Y); auto. }
    simpl. destruct (x =? X) eqn:e1.
    { intros P' H. inversion H.
      simpl. apply Leq_dec_neq in NE. destruct NE.
      rewrite H0. apply eqb_eq in e1.
      rewrite e1. solve_refl. rewrite PeanoNat.Nat.sub_0_r. auto. }
    destruct (y =? X) eqn:e2.
    { intros P' H. inversion H.
      apply eqb_neq in e1. apply Leq_dec_neq in e1.
      destruct e1. rewrite H0.
      apply eqb_eq in e2. rewrite e2. solve_refl.
      apply Leq_dec_neq in NE. destruct NE.
      rewrite H0,H2. auto. }
    intros P' H. inversion H.
  - intros P' H.
    destruct (subst_once Y X P1) eqn:E1.
    + inversion H. rewrite !multiplicity_mol.
      replace (multiplicity (link_multiset t) X)
        with (multiplicity (link_multiset P1) X - 1).
      { symmetry. apply PeanoNat.Nat.add_sub_swap.
        rewrite <- in_links_link_multiset.
        rewrite <- subst_once_Some.
        exists t. apply E1. }
      symmetry. apply IHP1 with (Y:=Y); auto.
    + destruct (subst_once Y X P2) eqn:E2.
      * inversion H. rewrite !multiplicity_mol.
        replace (multiplicity (link_multiset t) X)
        with (multiplicity (link_multiset P2) X - 1).
        { apply PeanoNat.Nat.add_sub_assoc.
          rewrite <- in_links_link_multiset.
          rewrite <- subst_once_Some.
          exists t. apply E2. }
        symmetry. apply IHP2 with (Y:=Y); auto.
      * inversion H.
Qed.

Lemma subst_once_multiplicity_Y:
  forall P P' X Y,
    Y <> X ->
    subst_once Y X P = Some P' ->
    multiplicity (link_multiset P') Y
    = multiplicity (link_multiset P) Y + 1.
Proof.
  intros P. induction P.
  - intros P' X Y H1 H2.
    simpl in H2. inversion H2.
  - destruct atom as [name ls|x y].
    {induction ls as [|h t IH].
    + intros P' X Y H1 H2.
      inversion H2.
    + intros P' X Y H1 H2.
      simpl in H2.
      destruct (h =? X) eqn:E.
      * inversion H2.
        simpl. rewrite Leq_dec_refl.
        apply eqb_eq in E.
        rewrite E.
        destruct (Leq_dec X Y).
        { congruence. }
        simpl. rewrite PeanoNat.Nat.add_1_r.
        auto.
      * simpl.
        destruct (subst_once_list Y X t) eqn:E1.
        { simpl in IH. inversion H2. simpl.
          replace (multiplicity (list_to_multiset l) Y)
            with (multiplicity (list_to_multiset t) Y + 1).
          { apply PeanoNat.Nat.add_assoc. }
          symmetry. apply subst_once_list_multiplicity_Y with X; auto. }
        inversion H2. }
    simpl. intros P' X Y H1 H2.
    destruct (x=?X) eqn:e1.
    { inversion H2. simpl. apply eqb_eq in e1.
      rewrite e1. solve_refl. apply not_eq_sym in H1.
      apply Leq_dec_neq in H1.
      destruct H1. rewrite H. simpl.
      destruct (Leq_dec y Y); auto. }
    destruct (y=?X) eqn:e2.
    { inversion H2. simpl. apply eqb_eq in e2.
      rewrite e2. solve_refl. apply not_eq_sym in H1.
      apply Leq_dec_neq in H1.
      destruct H1. rewrite H. auto. }
    inversion H2.
  - intros P' X Y H1 H2. simpl in H2.
    destruct (subst_once Y X P1) eqn:E1.
    { inversion H2. rewrite !multiplicity_mol.
      replace (multiplicity (link_multiset t) Y)
        with (multiplicity (link_multiset P1) Y + 1).
      { apply PeanoNat.Nat.add_shuffle0. }
      symmetry. apply IHP1 with X; auto. }
    destruct (subst_once Y X P2) eqn:E2.
    { inversion H2. rewrite !multiplicity_mol.
      replace (multiplicity (link_multiset t) Y)
        with (multiplicity (link_multiset P2) Y + 1).
      { apply PeanoNat.Nat.add_assoc. }
      symmetry. apply IHP2 with X; auto. }
    inversion H2.
Qed.

Lemma substitute_link_multiplicity:
  forall ls X Y,
    multiplicity (list_to_multiset ls) X = 0
    -> ls = map (substitute_link Y X) ls.
Proof.
  intros ls X Y H.
  induction ls; auto.
  simpl. simpl in H.
  destruct (Leq_dec a X).
  { simpl in H. inversion H. }
  simpl in H.
  apply IHls in H.
  rewrite <- H.
  f_equal.
  unfold substitute_link.
  apply eqb_neq in n.
  rewrite n. auto.
Qed.

Lemma not_in_multiplicity:
  forall l X, ~ In X l <-> multiplicity (list_to_multiset l) X = 0.
Proof.
  intros l X.
  induction l; split; simpl; intros H; auto.
  - destruct (Leq_dec a X).
    + destruct H. left. auto.
    + simpl. apply IHl.
      intros C. destruct H.
      right. auto.
  - destruct (Leq_dec a X).
    + intros C.
      simpl in H. inversion H.
    + intros C.
      destruct C.
      * destruct n. auto.
      * simpl in H.
        apply IHl in H.
        destruct H. auto.
Qed. 

Lemma subst_once_list_subst:
  forall X Y l1 l2,
    ~ In Y l1 ->
    subst_once_list Y X l1 = Some l2 ->
    l1 = map (substitute_link X Y) l2.
Proof.
  intros X Y l1.
  induction l1.
  - intros l2 H1 H2. simpl in H2.
    inversion H2.
  - intros l2 H1 H2. simpl in H2.
    destruct (a =? X) eqn:E.
    + inversion H2. simpl.
      solve_refl. apply eqb_eq in E.
      rewrite E. f_equal.
      apply substitute_link_multiplicity.
      apply not_in_cons in H1.
      destruct H1.
      apply not_in_multiplicity.
      auto.
    + destruct (subst_once_list Y X l1) eqn:E1;
      inversion H2.
      simpl. f_equal.
      * apply not_in_cons in H1.
        destruct H1.
        unfold substitute_link.
        apply not_eq_sym in H.
        apply eqb_neq in H.
        rewrite H. auto.
      * apply IHl1; auto.
        apply not_in_cons in H1.
        destruct H1.
        auto.
Qed.

Lemma subst_one_locallink :
  forall P X Y,
    In X (locallinks P) ->
    ~ In Y (links P) ->
  exists Q,
    subst_once Y X P = Some Q /\
    In X (freelinks Q) /\
    In Y (freelinks Q).
Proof.
  intros P X Y HX HY.
  rewrite <- multiplicity_not_in in HY.
  rewrite in_locallinks in HX.
  destruct (Leq_dec Y X) eqn:EYX.
  { rewrite e in HY.
    rewrite HX in HY.
    inversion HY. }
  destruct (Leq_dec X Y) eqn:EXY.
  { rewrite <- e in HY.
    rewrite HX in HY.
    inversion HY. }
  destruct (subst_once Y X P) eqn:E0.
  - exists t. repeat (split; auto).
    + apply in_freelinks.
      rewrite subst_once_multiplicity_X
        with (P:=P) (Y:=Y); auto.
      rewrite HX. auto.
    + apply in_freelinks.
      rewrite subst_once_multiplicity_Y
        with (P:=P) (X:=X); auto.
      rewrite HY. auto.
  - apply subst_once_None in E0.
    apply multiplicity_not_in in E0.
    rewrite E0 in HX. inversion HX.
Qed.

Lemma subst_once_subst :
  forall P Q X Y,
    subst_once Y X P = Some Q ->
    ~ In Y (links P) ->
    P = {{Q [X / Y]}}.
Proof.
  intros P.
  induction P.
  - intros Q X Y H1 H2. simpl in H1. inversion H1.
  - intros Q X Y H1 H2.
    destruct atom as [name ls|x y].
    { simpl in H1.
    destruct (subst_once_list Y X ls) eqn:E.
    + inversion H1. simpl.
      rewrite <- subst_once_list_subst with (l1:=ls); auto.
    + inversion H1. }
    simpl in H1. destruct (x =? X) eqn:e1.
    { apply eqb_eq in e1. inversion H1.
      simpl. solve_refl. rewrite e1.
      destruct (y =? Y) eqn:e2; auto.
      apply eqb_eq in e2.
      destruct H2. rewrite e2.
      simpl. auto. }
    destruct (y =? X) eqn:e2.
    { apply eqb_eq in e2.
      rewrite e2. inversion H1.
      solve_refl.
      destruct (x =? Y) eqn:e3; auto.
      apply eqb_eq in e3.
      destruct H2. rewrite e3.
      simpl. auto. }
    inversion H1.
  - intros Q X Y H1 H2.
    simpl in H1,H2.
    rewrite in_app_iff in H2.
    destruct (subst_once Y X P1) eqn:E1.
    { inversion H1. rewrite subst_mol.
      f_equal.
      - apply IHP1; auto.
      - apply subst_none. auto. }
    destruct (subst_once Y X P2) eqn:E2.
    { inversion H1. rewrite subst_mol.
      f_equal.
      - apply subst_none. auto.
      - apply IHP2; auto. }
    inversion H1.
Qed.

Lemma subst_once_subst_both :
  forall P Q X Y,
    subst_once Y X P = Some Q ->
    {{Q [Y / X]}} = {{P [Y / X]}}.
Proof.
  intros P Q X Y H.
  generalize dependent Q.
  induction P.
  - intros Q H. simpl in H. inversion H.
  - destruct atom as [name ls|x y].
    { induction ls as [|h t IH].
      { simpl. intros Q H. inversion H. }
      simpl. intros Q H.
      destruct (h =? X) eqn:E1.
      + inversion H. simpl.
        f_equal. f_equal. f_equal.
        unfold substitute_link.
        rewrite E1. destruct (Y =? X); auto.
      + simpl in IH.
        destruct (subst_once_list Y X t) eqn:E2.
        * assert (A:=IH (AAtom name l)).
          simpl in A.
          inversion H. simpl.
          f_equal. f_equal. f_equal.
          assert (A1: Some (TAtom (AAtom name l)) = Some (TAtom (AAtom name l))); auto.
          apply A in A1.
          inversion A1. auto.
        * inversion H. }
    intros Q H. simpl in H.
    destruct (x =? X) eqn:e1.
    { inversion H. simpl. apply eqb_eq in e1.
      rewrite e1. solve_refl.
      destruct (Y =? X); auto. }
    destruct (y =? X) eqn:e2.
    { inversion H. simpl. apply eqb_eq in e2.
      rewrite e2. solve_refl.
      destruct (Y =? X); auto. }
    inversion H.
  - intros Q H. simpl in H.
    destruct (subst_once Y X P1) eqn:E1.
    { inversion H.
      rewrite !subst_mol.
      f_equal.
      apply IHP1. auto. }
    destruct (subst_once Y X P2) eqn:E2.
    { inversion H.
      rewrite !subst_mol.
      f_equal.
      apply IHP2. auto. }
    inversion H.
Qed.

Lemma locallink_subst:
  forall P X Y,
    X <> Y ->
    wellformed_t P -> wellformed_t {{P [Y / X]}} ->
    In X (locallinks P) ->
    ~ In Y (links P) /\ In Y (locallinks {{P [Y / X]}}).
Proof.
  intros P X Y NE WFX WFY LX.
  rewrite in_locallinks in LX.
  rewrite <- multiplicity_not_in.
  rewrite in_locallinks.
  assert (A1: multiplicity (link_multiset {{P[Y/X]}}) Y <= 2).
  { apply wellformed_t_forall; auto.
    rewrite in_links_link_multiset.
    rewrite subst_multiplicity_Y; auto.
    rewrite LX. apply le_n_S.
    apply PeanoNat.Nat.le_0_l. }
  assert (A2: multiplicity (link_multiset P) Y = 0).
  { rewrite subst_multiplicity_Y in A1; auto.
    rewrite LX in A1.
    repeat apply le_S_n in A1.
    apply PeanoNat.Nat.le_0_r.
    auto. }
  split; auto.
  rewrite subst_multiplicity_Y; auto.
  rewrite LX, A2. auto.
Qed.

Lemma congm_wellformed_t:
  forall P Q, P ==m Q -> wellformed_t P /\ wellformed_t Q.
Proof.
  intros P Q H.
  induction H; auto; split; auto.
  - apply wellformed_t_link_multiset with {{P,Q}}; auto.
    apply link_multiset_swap.
  - apply wellformed_t_link_multiset with {{P,(Q,R)}}; auto.
    apply link_multiset_assoc.
  - apply connector_wellformed_t.
  - unfold wellformed_t.
    simpl. auto.
Qed.

Lemma subst_inv:
  forall P X Y,
    ~ In Y (links P) ->
    {{(P[Y/X])[X/Y]}} = P.
Proof.
  intros P X Y HY.
  induction P; auto.
  - destruct atom as [name ls|x y].
    { simpl.
      replace (map (substitute_link X Y) (map (substitute_link Y X) ls)) with ls; auto.
      induction ls; auto. simpl.
      f_equal.
      + unfold substitute_link.
        destruct (a =? X) eqn:E1.
        { solve_refl. apply eqb_eq. auto. }
        destruct (a =? Y) eqn:E2; auto.
        apply eqb_neq in E1. simpl in HY.
        destruct HY. left. apply eqb_eq. auto.
      + apply IHls.
        apply multiplicity_not_in in HY.
        apply multiplicity_not_in.
        simpl in HY.
        apply PeanoNat.Nat.eq_add_0 in HY.
        destruct HY. auto. }
    solve_refl.
    destruct (x =? X) eqn:e1.
    { apply eqb_eq in e1. rewrite e1.
      solve_refl. destruct (y =? X) eqn:e2.
      { solve_refl. apply eqb_eq in e2. rewrite e2. auto. }
      destruct (y =? Y) eqn:e3; auto.
      apply eqb_eq in e3. destruct HY.
      rewrite e3. simpl. auto. }
    destruct (y =? X) eqn:e2.
    { apply eqb_eq in e2.
      rewrite e2. solve_refl.
      destruct (x =? Y) eqn:e3; auto.
      apply eqb_eq in e3. destruct HY.
      rewrite e3. simpl. auto. }
    destruct (x =? Y) eqn:e3.
    { apply eqb_eq in e3. destruct HY.
      rewrite e3. simpl. auto. }
    destruct (y =? Y) eqn:e4.
    { apply eqb_eq in e4. destruct HY.
      rewrite e4. simpl. auto. }
    auto.
  - rewrite !subst_mol.
    simpl in HY. rewrite in_app_iff in HY.
    f_equal.
    + apply IHP1. intros C. destruct HY. auto.
    + apply IHP2. intros C. destruct HY. auto.
Qed.

Lemma subst_once_multiplicity_other:
  forall P Q X Y Z,
    X <> Z -> Y <> Z ->
    subst_once Y X P = Some Q ->
    multiplicity (link_multiset P) Z
    = multiplicity (link_multiset Q) Z.
Proof.
  intros P Q X Y Z H1 H2.
  generalize dependent Q.
  induction P.
  - intros Q H. simpl in H. inversion H.
  - destruct atom as [name ls|x y].
    { induction ls; intros Q H; simpl in H.
      { inversion H. }
      destruct (a =? X) eqn:E1.
      + simpl. destruct (Leq_dec a Z).
        { apply eqb_eq in E1.
          rewrite <- E1,e in H1.
          destruct H1. auto. }
        inversion H.
        simpl.
        destruct (Leq_dec Y Z).
        { congruence. }
        auto.
      + simpl. destruct (Leq_dec a Z) eqn:E2.
        * destruct (subst_once_list Y X ls) eqn:E3; inversion H.
          simpl. rewrite E2.
          simpl. f_equal.
          assert (A:= IHls (AAtom name l)).
          unfold link_multiset in A.
          simpl in A. apply A.
          rewrite E3. auto.
        * destruct (subst_once_list Y X ls) eqn:E3; inversion H.
          simpl. rewrite E2. simpl.
          assert (A:= IHls (AAtom name l)).
          simpl in A. apply A.
          rewrite E3. auto. }
    intros Q H. simpl in H.
    destruct (x =? X) eqn:e1.
    { apply eqb_eq in e1. inversion H. simpl.
      rewrite e1. f_equal.
      apply Leq_dec_neq in H1,H2.
      destruct H1,H2. rewrite H0,H1. auto. }
    destruct (y =? X) eqn:e2.
    { apply eqb_eq in e2. inversion H.
      simpl. f_equal. f_equal.
      rewrite e2.
      apply Leq_dec_neq in H1,H2.
      destruct H1,H2. rewrite H0,H1. auto. }
    inversion H.
  - intros Q H.
    simpl in H.
    destruct (subst_once Y X P1) eqn:E1.
    { inversion H. rewrite !multiplicity_mol.
      rewrite IHP1 with t; auto. }
    destruct (subst_once Y X P2) eqn:E2.
    { inversion H. rewrite !multiplicity_mol.
      rewrite IHP2 with t; auto. }
    inversion H.
Qed.

Lemma congm_E4 :
  forall P X Y,
    wellformed_t P -> wellformed_t {{P [Y / X]}} ->
    In X (locallinks P) -> P ==m {{ P[Y/X] }}.
Proof.
  intros P X Y WFP WFP' HX.
  destruct (Leq_dec X Y).
  { rewrite e. rewrite subst_id.
    apply congm_refl. auto. }
  assert (A1: ~ In Y (links P) /\ In Y (locallinks {{P [Y / X]}})).
  { apply locallink_subst; auto. }
  destruct A1 as [A1 A2].
  assert (A3:= subst_one_locallink P X Y).
  assert (H:=HX).
  apply A3 in H; auto.
  destruct H as [Q [H1 [H2 H3]]].
  assert (A6: P = {{Q [X / Y]}}).
  { apply subst_once_subst; auto. }
  assert (A4: wellformed_t {{X=Y,Q}}).
  { apply wellformed_t_forall.
    intros L H.
    rewrite multiplicity_mol.
    simpl.
    destruct (Leq_dec X L);
    destruct (Leq_dec Y L); simpl.
    - rewrite e,e0 in n. congruence.
    - apply le_n_S. rewrite e in H2.
      apply in_freelinks in H2. rewrite H2. auto.
    - apply le_n_S. rewrite e in H3.
      apply in_freelinks in H3. rewrite H3. auto.
    - rewrite <- subst_once_multiplicity_other 
        with P Q X Y L; auto.
      rewrite wellformed_t_forall in WFP.
      apply WFP. rewrite A6.
      apply in_links_link_multiset.
      rewrite subst_multiplicity_other; auto.
      simpl in H. destruct H as [H|[H|H]]; try congruence.
      apply in_links_link_multiset. auto. }
  assert (A5: wellformed_t {{Y=X,Q}}).
  { apply wellformed_t_link_multiset with ({{X=Y,Q}}); auto.
    apply meq_trans with (munion (link_multiset {{X=Y}}) (link_multiset Q)).
    { apply link_multiset_mol. }
    apply meq_trans with (munion (link_multiset {{Y=X}}) (link_multiset Q)).
    { apply meq_left. unfold link_multiset.
      simpl. unfold meq.
      unfold munion. simpl. intros a.
      destruct (Leq_dec X a);
      destruct (Leq_dec Y a); auto. }
    apply meq_sym, link_multiset_mol. }
  assert (A7: {{Q[Y/X]}}={{P[Y/X]}}).
  { apply subst_once_subst_both. auto. }
  apply congm_trans with {{Y=X,Q}}; auto.
  { rewrite A6. apply congm_sym; auto.
    { rewrite <- A6. auto. }
    apply congm_E9ex; auto.
    rewrite <- A6. auto. }
  apply congm_trans with {{X=Y,Q}}; auto.
  { apply congm_E5; auto. apply congm_E8. }
  rewrite <- A7.
  apply congm_E9ex; auto.
  rewrite A7. auto.
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

(* For SC-GI Correspondence *)

Inductive Path : Type :=
  | PHere
  | PLeft (p : Path)
  | PRight (p : Path).

Record Port := {
  node : Path;
  arg : nat;
}.

Record PortGraph := {
  nodes : list (string * Path);
  frees : list (Link * Port);
  locals : list (Port * Port)
}.

Fixpoint add_indices {X} (n : nat) (l : list X) : list (nat * X) := 
  match l with
  | h :: t => (n,h) :: add_indices (S n) t
  | [] => []
  end.

Fixpoint find_link (p : Link) (l : list (Link * Port)) : option (Link * Port) :=
  match l with
  | (l', port) :: t => if l' =? p then Some (l', port) else find_link p t
  | [] => None
  end.

Definition add_free_link (lp : Link * Port) (g : PortGraph) : PortGraph :=
  let (l, p) := lp in
  match find_link l (frees g) with
  | Some (l', p') => 
    {| nodes := nodes g;
       frees := filter (fun '(l'', _) => negb (l'' =? l)) (frees g);
       locals := (p, p') :: locals g |}
  | None => 
    {| nodes := nodes g;
       frees := lp :: frees g;
       locals := locals g |}
  end.

(* Definition empty_graph : PortGraph :=
  {| nodes := []; frees := []; locals := [] |}. *)

Definition atom_to_graph (name : string) (links : list Link) : PortGraph :=
  fold_right add_free_link
    {| nodes := [(name, PHere)]; frees := []; locals := [] |}
    (map
      (fun '(n, l) => (l, {| node := PHere; arg := n |}))
      (add_indices 0 links)).

Definition graph_mol (g1 g2 : PortGraph) : PortGraph :=
  fold_right add_free_link
    {| nodes := map (fun '(n, p) => (n, PLeft p)) (nodes g1) ++
                        map (fun '(n, p) => (n, PRight p)) (nodes g2);
      frees := map (fun '(l, p) => (l, {| node := PRight (node p); arg := arg p |})) (frees g2);
      locals := map (fun '(p1, p2) =>
                      ({| node := PLeft (node p1); arg := arg p1 |},
                        {| node := PLeft (node p2); arg := arg p2 |})) (locals g1) ++
                map (fun '(p1, p2) =>
                      ({| node := PRight (node p1); arg := arg p1 |},
                        {| node := PRight (node p2); arg := arg p2 |})) (locals g2) |}
    (map (fun '(l, p) => (l, {| node := PLeft (node p); arg := arg p |})) (frees g1)).

Fixpoint term_to_graph (t : Term) : PortGraph := 
  match t with
  | TZero => {| nodes := []; frees := []; locals := [] |}
  | TAtom a => 
    match a with
    | AAtom name links => atom_to_graph name links
    | AConn X Y => atom_to_graph "=" [X; Y]
    end
  | TMol t1 t2 => graph_mol (term_to_graph t1) (term_to_graph t2)
  end.

Compute term_to_graph {{ "a"("X"), "b"("X"), "c"("Y") }}.

Definition bijection (xs ys : list Path) (f : Path -> Path) : Prop :=
  NoDup xs /\ NoDup ys /\ Permutation ys (map f xs).

Record isomorphism (g1 g2 : PortGraph) := {
  iso_map : Path -> Path;
  iso_map_bij : bijection (map snd (nodes g1)) (map snd (nodes g2)) iso_map;
  locals_preserve : forall p1 p2,
    In (p1, p2) (locals g1) \/ In (p2, p1) (locals g1) <->
    In ({| node := iso_map (node p1); arg := arg p1 |},
        {| node := iso_map (node p2); arg := arg p2 |}) (locals g2)
    \/
    In ({| node := iso_map (node p2); arg := arg p2 |},
        {| node := iso_map (node p1); arg := arg p1 |}) (locals g2);
  frees_preserve : forall l p,
    In (l, p) (frees g1) <->
    In (l, {| node := iso_map (node p); arg := arg p |}) (frees g2);
}.

Definition iso (g1 g2 : PortGraph) : Prop := 
  exists (i : isomorphism g1 g2), True.
Notation "p '~=' q" := (iso p q) (at level 40).

Tactic Notation "solve_iso" constr(f) :=
  eexists; auto; refine {| iso_map := f |}; simpl.

Lemma iso_refl :
  forall g, g ~= g.
Proof.
  intros g.
  solve_iso (fun (p:Path) => p).
  (* - unfold bijection.
    set (map snd (nodes g)) as xs.
    rewrite map_id.
  - intros. split; intros H; destruct H, p1, p2;
    simpl in *; auto.
  - intros. split; intros H; destruct p; simpl; auto. *)
Admitted.

Lemma iso_sym :
  forall g1 g2, g1 ~= g2 -> g2 ~= g1.
Proof.
  intros. destruct H as [H _].
  destruct H as [m0 m0_bij m0_lp m0_fp].
Admitted.

Example iso_example :
  let g1 := term_to_graph {{ "a"("X"), "b"("X"), "c"("Y") }} in
  let g2 := term_to_graph {{ "b"("X"), "a"("X"), "c"("Y") }} in
  g1 ~= g2.
Proof. Admitted.

Reserved Notation "p '==nc' q" (at level 40).
Inductive congnc : Term -> Term -> Prop :=
  | congnc_E1 : forall P, wellformed_t P ->
                {{TZero, P}} ==nc P
  | congnc_E2 : forall P Q, wellformed_t {{P, Q}} ->
                {{P, Q}} ==nc {{Q, P}}
  | congnc_E3 : forall P Q R, wellformed_t {{P, (Q, R)}} -> 
                {{P, (Q, R)}} ==nc {{(P, Q), R}}
  | congnc_E5 : forall P P' Q, wellformed_t {{ P, Q }} -> wellformed_t {{ P',Q }} ->
                P ==nc P' -> {{ P,Q }} ==nc {{ P',Q }}
  | congnc_refl : forall P, wellformed_t P ->
                  P ==nc P
  | congnc_trans : forall P Q R, wellformed_t P -> wellformed_t Q -> wellformed_t R ->
    P ==nc Q -> Q ==nc R -> P ==nc R
  | congnc_sym : forall P Q, wellformed_t P -> wellformed_t Q -> 
    P ==nc Q -> Q ==nc P
  where "p '==nc' q" := (congnc p q).

Theorem congnc_iso :
  forall P Q, P ==nc Q -> exists (i : iso (term_to_graph P) (term_to_graph Q)), True.
Proof. Admitted.

Theorem iso_congnc :
  forall P Q (i : iso (term_to_graph P) (term_to_graph Q)), P ==nc Q.
Proof. Admitted.

Corollary congnc_iso_iff :
  forall P Q, P ==nc Q <-> exists (i : iso (term_to_graph P) (term_to_graph Q)), True.
Proof.
  intros P Q. split.
  - apply congnc_iso.
  - intros [i _]. apply iso_congnc. auto.
Qed.


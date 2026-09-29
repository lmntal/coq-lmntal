Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Multiset.
Require Import Lia.

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

(* ------------------------------------------------------------------ *)
(*  A modular presentation of structural congruence (cf. Fig. 4 of the  *)
(*  design note): the base rewrite rules (E1)-(E3),(E7),(E9) live in    *)
(*  [congm_step]; the two admissible rules (E4),(E8) live separately in *)
(*  [cong_extra]; both [cong] (==) and [congm] (==m, defined further    *)
(*  below) are obtained by applying the SAME generic closure operator   *)
(*  [cclose] to a step relation.  [cclose] adds reflexivity, symmetry,  *)
(*  transitivity, and the (E5) molecule-congruence rule -- each of      *)
(*  these four (and (E1)-(E3),(E7),(E9)) is guarded by well-formedness  *)
(*  of both sides, exactly as in the informal rules, and exactly once.  *)
(*  The individual named rules ([cong_E1] .. [cong_sym]; [congm_E1] ..  *)
(*  [congm_sym]) are recovered as short lemmas below, so every site     *)
(*  that used to [apply cong_E4] (etc.) is unaffected by this           *)
(*  refactoring.                                                        *)
(* ------------------------------------------------------------------ *)

Inductive congm_step : Term -> Term -> Prop :=
  | ms_E1 : forall P, congm_step {{ TZero, P }} P
  | ms_E2 : forall P Q, congm_step {{ P, Q }} {{ Q, P }}
  | ms_E3 : forall P Q R, congm_step {{ P, (Q, R) }} {{ (P, Q), R }}
  | ms_E7 : forall X, congm_step {{ X = X }} TZero
  | ms_E9 : forall X Y (A:Atom),
              In X (freelinks A) -> congm_step {{ X = Y, A }} {{ A[Y/X] }}.

Inductive cong_extra : Term -> Term -> Prop :=
  | es_E4 : forall P X Y, In X (locallinks P) -> cong_extra P {{ P[Y/X] }}
  | es_E8 : forall X Y, cong_extra {{ X = Y }} {{ Y = X }}.

Inductive cclose (step : Term -> Term -> Prop) : Term -> Term -> Prop :=
  | cc_step  : forall P Q,
                 wellformed_t P -> wellformed_t Q -> step P Q -> cclose step P Q
  | cc_ctxt  : forall P P' Q, wellformed_t {{ P,Q }} -> wellformed_t {{ P',Q }} ->
                 cclose step P P' -> cclose step {{ P,Q }} {{ P',Q }}
  | cc_refl  : forall P, wellformed_t P -> cclose step P P
  | cc_trans : forall P Q R, cclose step P Q -> cclose step Q R -> cclose step P R
  | cc_sym   : forall P Q, cclose step P Q -> cclose step Q P.

Lemma cclose_mono : forall (s1 s2 : Term -> Term -> Prop),
  (forall P Q, s1 P Q -> s2 P Q) ->
  forall P Q, cclose s1 P Q -> cclose s2 P Q.
Proof.
  intros s1 s2 Hs P Q H. induction H.
  - apply cc_step; auto.
  - apply cc_ctxt; auto.
  - apply cc_refl; auto.
  - apply cc_trans with Q; auto.
  - apply cc_sym; auto.
Qed.

(* A handful of self-contained well-formedness facts, proved directly
   from [links]/[list_to_multiset] (available this early in the file),
   just enough to recover the individual step rules below without
   depending on the general well-formedness lemmas proved later. *)

Lemma mult_cons : forall a l x,
  multiplicity (list_to_multiset (a :: l)) x
  = (if Leq_dec a x then 1 else 0) + multiplicity (list_to_multiset l) x.
Proof. reflexivity. Qed.

Lemma mult_app : forall l1 l2 x,
  multiplicity (list_to_multiset (l1 ++ l2)) x
  = multiplicity (list_to_multiset l1) x + multiplicity (list_to_multiset l2) x.
Proof.
  induction l1 as [|a l1 IH]; intros l2 x.
  - reflexivity.
  - simpl app. rewrite !mult_cons, IH. destruct (Leq_dec a x); lia.
Qed.

Lemma wf_TZero : wellformed_t TZero.
Proof. reflexivity. Qed.

Lemma wf_mol_TZero_l : forall P, wellformed_t P -> wellformed_t {{ TZero, P }}.
Proof. intros P H. exact H. Qed.

Lemma wf_mol_comm : forall P Q, wellformed_t {{P,Q}} -> wellformed_t {{Q,P}}.
Proof.
  intros P Q H. rewrite wellformed_t_forall in *. intros x Hx.
  assert (Hx' : In x (links {{P,Q}}))
    by (simpl in Hx |- *; apply in_app_or in Hx; apply in_or_app; tauto).
  specialize (H x Hx'). unfold link_multiset in H |- *. simpl links.
  simpl links in H. rewrite mult_app in H |- *. lia.
Qed.

Lemma wf_mol_assoc : forall P Q R, wellformed_t {{P,(Q,R)}} -> wellformed_t {{(P,Q),R}}.
Proof.
  intros P Q R H. rewrite wellformed_t_forall in *. intros x Hx.
  assert (Hx' : In x (links {{P,(Q,R)}}))
    by (simpl in Hx |- *; rewrite <- app_assoc in Hx; exact Hx).
  specialize (H x Hx'). unfold link_multiset in H |- *. simpl links.
  simpl links in H. rewrite <- app_assoc. exact H.
Qed.

Lemma wf_selfconn : forall X, wellformed_t (TAtom (AConn X X)).
Proof.
  intros X. rewrite wellformed_t_forall. intros x Hx.
  simpl in Hx. destruct Hx as [E|[E|[]]]; subst x;
    (unfold link_multiset; simpl links; rewrite !mult_cons, Leq_dec_refl; simpl; lia).
Qed.

Lemma wf_conn : forall X Y, wellformed_t (TAtom (AConn X Y)).
Proof.
  intros X Y. rewrite wellformed_t_forall. intros x Hx.
  unfold link_multiset. simpl links. rewrite !mult_cons.
  destruct (Leq_dec X x); destruct (Leq_dec Y x); simpl; lia.
Qed.

Definition cong (P Q : Term) : Prop :=
  cclose (fun P Q => congm_step P Q \/ cong_extra P Q) P Q.
Notation "p == q" := (cong p q) (at level 40).

Lemma cong_E1 : forall P, wellformed_t P -> {{TZero, P}} == P.
Proof. intros P H. apply cc_step; [ apply wf_mol_TZero_l | | left; apply ms_E1 ]; auto. Qed.

Lemma cong_E2 : forall P Q, wellformed_t {{P, Q}} -> {{P, Q}} == {{Q, P}}.
Proof. intros P Q H. apply cc_step; [ | apply wf_mol_comm | left; apply ms_E2 ]; auto. Qed.

Lemma cong_E3 : forall P Q R, wellformed_t {{P, (Q, R)}} -> {{P, (Q, R)}} == {{(P, Q), R}}.
Proof. intros P Q R H. apply cc_step; [ | apply wf_mol_assoc | left; apply ms_E3 ]; auto. Qed.

Lemma cong_E4 : forall P X Y, wellformed_t P -> wellformed_t {{ P[Y/X] }} ->
                In X (locallinks P) -> P == {{ P[Y/X] }}.
Proof. intros P X Y H1 H2 H3. apply cc_step; auto. right. apply es_E4; auto. Qed.

Lemma cong_E5 : forall P P' Q, wellformed_t {{ P,Q }} -> wellformed_t {{ P',Q }} ->
                P == P' -> {{ P,Q }} == {{ P',Q }}.
Proof. intros P P' Q H1 H2 H3. apply cc_ctxt; auto. Qed.

Lemma cong_E7 : forall X, {{ X = X }} == TZero.
Proof. intros X. apply cc_step; [ apply wf_selfconn | apply wf_TZero | left; apply ms_E7 ]. Qed.

Lemma cong_E8 : forall X Y, {{ X = Y }} == {{ Y = X }}.
Proof. intros X Y. apply cc_step; [ apply wf_conn | apply wf_conn | right; apply es_E8 ]. Qed.

Lemma cong_E9 : forall X Y (A:Atom),
                wellformed_t {{ X = Y, A }} -> wellformed_t {{ A[Y/X] }} ->
                In X (freelinks A) -> {{ X = Y, A }} == {{ A[Y/X] }}.
Proof. intros X Y A H1 H2 H3. apply cc_step; auto. left. apply ms_E9; auto. Qed.

Lemma cong_refl : forall P, wellformed_t P -> P == P.
Proof. intros P H. apply cc_refl; auto. Qed.

Lemma cong_trans : forall P Q R, wellformed_t P -> wellformed_t Q -> wellformed_t R ->
                P == Q -> Q == R -> P == R.
Proof. intros P Q R _ _ _ H1 H2. apply cc_trans with Q; auto. Qed.

Lemma cong_sym : forall P Q, wellformed_t P -> wellformed_t Q ->
                P == Q -> Q == P.
Proof. intros P Q _ _ H. apply cc_sym; auto. Qed.

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
        eapply PeanoNat.Nat.le_trans.
        { exact H. }
        apply PeanoNat.Nat.le_add_r.
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
  induction H as
    [ P Q HwP HwQ Hstep
    | P P' Q Hw1 Hw2 H IH
    | P Hw
    | P Q R H1 IH1 H2 IH2
    | P Q H IH ].
  - split; assumption.
  - split; assumption.
  - split; assumption.
  - destruct IH1 as [HP HQ]. destruct IH2 as [_ HR]. split; assumption.
  - destruct IH as [HP HQ]. split; assumption.
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
  - intros H. induction H as
      [ P Q HwP HwQ Hstep
      | P P' Q Hw1 Hw2 H IH
      | P Hw
      | P Q R H1 IH1 H2 IH2
      | P Q H IH ].
    { destruct Hstep as [Hs | He].
      { destruct Hs as [ P0 | P0 Q0 | P0 Q0 R0 | X0 | X0 Y0 A0 Hfr ].
        { apply congm_E1; auto. }
        { apply congm_E2; auto. }
        { apply congm_E3; auto. }
        { apply congm_E7; auto. }
        { apply congm_E9; auto. } }
      (* (E4),(E8) are admissible in congm *)
      { destruct He as [ P0 X0 Y0 Hloc | X0 Y0 ].
        { apply congm_E4; auto. }
        { apply congm_E8. } } }
    { apply congm_E5; auto. }
    { apply congm_refl; auto. }
    { destruct (cong_wellformed_t _ _ H1) as [HwfP HwfQ].
      destruct (cong_wellformed_t _ _ H2) as [_ HwfR].
      apply congm_trans with Q; auto. }
    { destruct (cong_wellformed_t _ _ H) as [HwfP HwfQ].
      apply congm_sym; auto. }
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

(* Record AtomOcc := {
  occ_name : string;
  occ_links : list Link;
}.
Inductive AtomOcc :=
  | OccAtom (name:string) (links:list Link)
  | OccConn (X Y:Link).

Record PortGraph := {
  pg_atoms : list AtomOcc;
}. *)

Definition AtomOcc := Atom.
Definition OccId := nat.
Definition PortGraph := list (OccId * AtomOcc).

(* 
Definition OccId := nat.
Definition AtomOcc := (OccId * Atom).
Definition PortGraph := list AtomOcc.
 *)

Fixpoint flatten_atoms t :=
  match t with
  | TZero => []
  | TAtom a => [a]
  | TMol t1 t2 =>
      flatten_atoms t1 ++ flatten_atoms t2
  end.

Lemma flatten_atoms_E1: forall t,
  flatten_atoms (TMol TZero t) = flatten_atoms t.
Proof.
  intros. auto.
Qed.

Lemma flatten_atoms_mol: forall t1 t2,
  flatten_atoms (TMol t1 t2) = flatten_atoms t1 ++ flatten_atoms t2.
Proof.
  intros. auto.
Qed.

Fixpoint enumerate_from (n : nat) (l : list Atom) : PortGraph :=
  match l with
  | nil => nil
  | a :: tl =>
      (n, a) :: enumerate_from (S n) tl
  end.

Definition enumerate (l : list Atom) : PortGraph :=
  enumerate_from 0 l.

Lemma enumerate_from_app :
  forall n l1 l2,
    enumerate_from n (l1 ++ l2)
    =
    enumerate_from n l1 ++
    enumerate_from (n + length l1) l2.
Proof.
  intros. generalize dependent n. induction l1; simpl.
  - intros. rewrite PeanoNat.Nat.add_0_r. auto.
  - intros. f_equal. rewrite IHl1. f_equal. f_equal.
    auto.
Qed.

Lemma enumerate_app :
  forall l1 l2,
    enumerate (l1 ++ l2)
    =
    enumerate l1 ++
    enumerate_from (length l1) l2.
Proof.
  intros. unfold enumerate.
  apply enumerate_from_app.
Qed.

Definition graph_of (t : Term) : PortGraph :=
  enumerate (flatten_atoms t).

Lemma graph_of_E1: 
  forall t, graph_of (TMol TZero t) = graph_of t.
Proof.
  intros. unfold graph_of. auto.
Qed.

Lemma graph_of_mol:
  forall t1 t2,
    graph_of (TMol t1 t2)
    = graph_of t1 ++ 
      enumerate_from (length (flatten_atoms t1)) (flatten_atoms t2).
Proof.
  intros. unfold graph_of.
  rewrite flatten_atoms_mol.
  apply enumerate_app.
Qed.

Record Port := {
  port_occ: OccId;
  port_idx: nat;
}.

Fixpoint atom_of (G : PortGraph) (i : OccId) : option Atom :=
  match G with
  | [] => None
  | (j, a) :: tl =>
    if Nat.eqb i j then
      Some a
    else
      atom_of tl i
  end.

Definition link_of_atom (a : Atom) (k : nat) : option Link :=
  match a with
  | AAtom _ links =>
      nth_error links k
  | AConn X Y =>
      nth_error [X;Y] k
  end.

Definition port_link (G : PortGraph) (p : Port) : option Link :=
  match atom_of G (port_occ p) with
  | None => None
  | Some a =>
      link_of_atom a (port_idx p)
  end.

(* self-loop?? *)
Definition adjacent (G : PortGraph) (p1 p2 : Port) : Prop :=
  exists l,
    port_link G p1 = Some l /\ port_link G p2 = Some l.

Lemma atom_of_enumerate_from :
  forall n l k a,
    nth_error l k = Some a ->
    atom_of (enumerate_from n l) (n+k)
      = Some a.
Proof.
  intros. generalize dependent n.
  generalize dependent k.
  induction l.
  - intros. rewrite nth_error_nil in H. discriminate H.
  - intros. destruct k.
    + simpl in H. destruct H. simpl.
      assert (A: forall n, Nat.eqb (n+0) n = true).
      { induction n0; auto. }
      rewrite A. auto.
    + simpl in H. simpl.
      assert (A: forall n k, Nat.eqb (n + S k) n = false).
      { intros. induction n0; auto. }
      rewrite A.
      apply IHl with (n:=S n) in H.
      rewrite <- H. f_equal.
      rewrite PeanoNat.Nat.add_succ_comm. auto.
Qed.

Definition occs (G : PortGraph) : list OccId :=
  map fst G.

Lemma occs_enumerate_from :
  forall n l,
    occs (enumerate_from n l) = seq n (length l).
Proof.
  intros n l. unfold occs.
  generalize dependent n.
  induction l; intros; simpl; auto.
  f_equal. apply IHl.
Qed.

Fixpoint ports_of_atom_from
    (i : OccId) (k len : nat)
    : list Port :=
  match len with
  | 0 => []
  | S len' =>
      {| port_occ := i;
         port_idx := k |}
      :: ports_of_atom_from i (S k) len'
  end.

Definition ports_of_atom (i : OccId) (a : Atom)
  : list Port :=
  match a with
  | AAtom _ links =>
      ports_of_atom_from i 0 (length links)
  | AConn _ _ =>
      ports_of_atom_from i 0 2
  end.

Fixpoint ports (G : PortGraph) : list Port :=
  match G with
  | [] => []
  | (i,a)::tl =>
      ports_of_atom i a ++ ports tl
  end.

Definition links_of_atom (a : Atom) : list Link :=
  match a with
  | AAtom _ ls => ls
  | AConn X Y => [X;Y]
  end.

Fixpoint links_pg (G : PortGraph) : list Link :=
  match G with
  | [] => []
  | (_,a)::tl =>
      links_of_atom a ++ links_pg tl
  end.

Definition OccMap := OccId -> OccId.
Definition LinkMap := Link -> Link.

Definition map_port (fo : OccMap) (p : Port) : Port := {|
  port_occ := fo (port_occ p);
  port_idx := port_idx p;
|}.

Definition map_atom (fl : LinkMap) (a : Atom) : Atom :=
  match a with
  | AAtom name ls =>
      AAtom name (map fl ls)
  | AConn X Y =>
      AConn (fl X) (fl Y)
  end.

Definition map_graph (fo : OccMap) (fl : LinkMap)
    (G : PortGraph) : PortGraph :=
  map (fun '(i,a) => (fo i, map_atom fl a)) G.

Lemma link_of_atom_map :
  forall (fl : LinkMap) a k,
    link_of_atom (map_atom fl a) k =
    option_map fl (link_of_atom a k).
Proof.
  intros. destruct a; simpl; rewrite <- nth_error_map; auto.
Qed.

Definition Injective {A B} (f : A -> B) : Prop :=
  forall x y, f x = f y -> x = y.

Definition Surjective {A B} (f : A -> B) : Prop :=
  forall y, exists x, f x = y.

Definition Bijective {A B} (f : A -> B) : Prop :=
  Injective f /\ Surjective f.

Lemma map_graph_cons :
  forall fo fl i a G,
    map_graph fo fl ((i,a)::G)
    =
    (fo i, map_atom fl a)
      :: map_graph fo fl G.
Proof. auto. Qed.

Lemma atom_of_map_graph_Some :
  forall (fo : OccMap) (fl : LinkMap)
         (G : PortGraph) i a,
    Injective fo ->
    atom_of G i = Some a ->
    atom_of (map_graph fo fl G) (fo i)
      = Some (map_atom fl a).
Proof.
  intros. generalize dependent a.
  induction G as [| [o a0] G IH]; intros; simpl.
  - simpl in H0. discriminate H0.
  - destruct (Nat.eqb i o) eqn:E.
    + replace o with i 
        by (apply PeanoNat.Nat.eqb_eq; auto).
      replace (Nat.eqb (fo i) (fo i)) with true
        by (rewrite PeanoNat.Nat.eqb_refl; auto).
      f_equal.
      simpl in H0. rewrite E in H0.
      injection H0 as H0. rewrite H0. auto.
    + assert (Nat.eqb (fo i) (fo o) = false) as Hneq.
      {
        apply PeanoNat.Nat.eqb_neq.
        apply PeanoNat.Nat.eqb_neq in E.
        auto.
      }
      rewrite Hneq.
      simpl in H0. rewrite E in H0.
      apply IH. auto.
Qed.

Lemma atom_of_map_graph_None:
  forall (fo : OccMap) (fl : LinkMap)
         (G : PortGraph) i,
    Injective fo ->
    atom_of G i = None ->
    atom_of (map_graph fo fl G) (fo i)
      = None.
Proof.
  intros.
  induction G; simpl; auto.
  destruct a.
  destruct (PeanoNat.Nat.eq_dec i o).
  - rewrite e.
    replace (Nat.eqb (fo o) (fo o)) with true
      by (symmetry; apply PeanoNat.Nat.eqb_refl).
    simpl in H0.
    exfalso.
    replace (Nat.eqb i o) with true in H0.
    { discriminate H0. }
    rewrite e. symmetry.
    apply PeanoNat.Nat.eqb_refl.
  - assert (Nat.eqb (fo i) (fo o) = false).
    { apply PeanoNat.Nat.eqb_neq. auto. }
    assert (Nat.eqb i o = false).
    { apply PeanoNat.Nat.eqb_neq. auto. }
    rewrite H1. apply IHG.
    simpl in H0.
    rewrite H2 in H0. auto.
Qed.  

Lemma port_link_map :
  forall fo fl G p,
    Injective fo ->
    port_link (map_graph fo fl G) (map_port fo p)
      =
    option_map fl (port_link G p).
Proof.
  intros. unfold port_link. simpl.
  destruct (atom_of G (port_occ p)) eqn:E.
  - rewrite atom_of_map_graph_Some with (a:=a); auto.
    apply link_of_atom_map.
  - simpl.
    rewrite atom_of_map_graph_None; auto.
Qed.

(* Definition link_occurs (G : PortGraph) (X : Link) : nat :=
  multiplicity (list_to_multiset (links_pg G)) X.

Definition free_link (G : PortGraph) (X : Link) : Prop :=
  link_occurs G X = 1.

Definition local_link (G : PortGraph) (X : Link) : Prop :=
  link_occurs G X = 2. *)

Definition conn_step (G : PortGraph) (X Y : Link) : Prop :=
  exists i,
    atom_of G i = Some (AConn X Y).

Record GraphIso (G H : PortGraph) := {
  occ_map : OccMap;
  link_map : LinkMap;

  occ_bij : Bijective occ_map;
  link_bij : Bijective link_map;

  atom_ok :
    forall i,
      option_map (map_atom link_map) (atom_of G i)
      = atom_of H (occ_map i)
}.



(* Inductive Path : Type :=
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
 *)

(* ================================================================== *)
(*  SC-GI correspondence, take 2 : closed-term normalization           *)
(*                                                                    *)
(*  Plan (cf. the design note "LMNtal 項上の構造合同関係とその          *)
(*  グラフ表現上の同型との対応関係"):                                    *)
(*                                                                    *)
(*   Layer 1  normalize : Term -> Term  fuses every connector at the   *)
(*            term level via (E9ex)/(E7), producing a connector-free,  *)
(*            0-free normal form.  Key facts:                          *)
(*              - Thm 1 : Normal (normalize G)         (for closed WF) *)
(*              - Lem A : G ==m normalize G            (for closed WF) *)
(*   Layer 2  cong  ==>  graph_iso (denote P) (denote Q)               *)
(*   Layer 3  the converse.                                            *)
(*                                                                    *)
(*  The connectors are fused by an *incremental union-find*: when the  *)
(*  connector (x,y) is eliminated we rename x |-> y everywhere,        *)
(*  including in the connectors not yet processed.  This makes the     *)
(*  result independent of the order in which connectors are taken     *)
(*  (a plain fold over the connector list is NOT order independent,    *)
(*  e.g. on  {{X=Y, Y=Z, p(X,Z)}}  vs  {{p(X,Z), Y=Z, X=Y}}).         *)
(* ================================================================== *)

Require Import Lia.
Require Import Relation_Operators.

(* --- Def 3 : closed / normal terms -------------------------------- *)

Definition Closed (t : Term) : Prop := freelinks t = [].

Fixpoint connector_free (t : Term) : Prop :=
  match t with
  | TZero => True
  | TAtom (AAtom _ _) => True
  | TAtom (AConn _ _) => False
  | TMol t1 t2 => connector_free t1 /\ connector_free t2
  end.

(* [make_mol] below leaves a single trailing [TZero]; a term is "normal" in the
   sense of the design note (no connectors, no interior 0) once that trailing 0
   is dropped by (E1).  For the SC-GI development what matters is
   [connector_free] together with the atom list, so we work with those. *)

(* --- Def 4/5 : flattening, connector extraction, normalization ---- *)

(* split an atom list into (connector pairs, ordinary atoms) *)
Fixpoint get_connectors (l : list Atom) : list (Link * Link) * list Atom :=
  match l with
  | [] => ([], [])
  | h :: t =>
    let (conns, atoms) := get_connectors t in
    match h with
    | AConn x y => ((x, y) :: conns, atoms)
    | AAtom _ _ => (conns, h :: atoms)
    end
  end.

(* rebuild a molecule from an atom list (with a single trailing 0) *)
Definition make_mol (l : list Atom) : Term :=
  fold_right (fun a t => TMol (TAtom a) t) TZero l.

Lemma make_mol_nil : make_mol [] = TZero.
Proof. reflexivity. Qed.

Lemma make_mol_cons_eq : forall a l,
  make_mol (a :: l) = TMol (TAtom a) (make_mol l).
Proof. reflexivity. Qed.

Definition subst_conn (Y X : Link) (c : Link * Link) : Link * Link :=
  (substitute_link Y X (fst c), substitute_link Y X (snd c)).

Definition subst_atoms (Y X : Link) (l : list Atom) : list Atom :=
  map (map_atom (substitute_link Y X)) l.

(* eliminate connectors one by one; [fuel] is meant to be [length conns] *)
Fixpoint fuse_atoms (fuel : nat) (conns : list (Link * Link)) (atoms : list Atom)
  : list Atom :=
  match fuel with
  | 0 => atoms
  | S fuel' =>
    match conns with
    | [] => atoms
    | (x, y) :: rest =>
        if x =? y
        then fuse_atoms fuel' rest atoms
        else fuse_atoms fuel' (map (subst_conn y x) rest) (subst_atoms y x atoms)
    end
  end.

Definition nf_atoms (t : Term) : list Atom :=
  let (conns, atoms) := get_connectors (flatten_atoms t) in
  fuse_atoms (length conns) conns atoms.

Definition normalize (t : Term) : Term := make_mol (nf_atoms t).

(* graph denotation : the normalized atom list, seen up to
   [graph_iso] (permutation of atoms + a bijective renaming of links) *)
Definition denote (t : Term) : list Atom := nf_atoms t.

Definition graph_iso (l1 l2 : list Atom) : Prop :=
  exists fl : Link -> Link,
    Bijective fl /\ Permutation (map (map_atom fl) l1) l2.

(* --- sanity checks ---------------------------------------------- *)

Example denote_ex1 :
  denote {{ "X"="Y", "p"("X","Y") }} = [AAtom "p" ["Y"; "Y"]].
Proof. reflexivity. Qed.

Example denote_ex2 :
  denote {{ "X"="Y", ("Y"="Z", "p"("X","Z")) }} = [AAtom "p" ["Z"; "Z"]].
Proof. reflexivity. Qed.

Example denote_ex3 :
  denote {{ "p"("X","Z"), ("Y"="Z", "X"="Y") }} = [AAtom "p" ["Z"; "Z"]].
Proof. reflexivity. Qed.

Example denote_ex4 :
  denote {{ TZero, "a"() }} = [AAtom "a" []].
Proof. reflexivity. Qed.

Example denote_ex5 :
  denote {{ "X"="X", "a"() }} = [AAtom "a" []].
Proof. reflexivity. Qed.

Example flatten_make_mol_ex :
  flatten_atoms (make_mol [AAtom "p" ["X"]; AAtom "q" ["X"]])
  = [AAtom "p" ["X"]; AAtom "q" ["X"]].
Proof. reflexivity. Qed.

(* --- Thm 1 : normalize is connector-free ----------------------- *)
(*  (needs neither [Closed] nor [wellformed_t]: the fused atom list  *)
(*   only ever contains [AAtom]s.)                                   *)

Definition is_aatom (a : Atom) : Prop :=
  match a with AAtom _ _ => True | AConn _ _ => False end.

Lemma map_atom_is_aatom : forall fl a, is_aatom a -> is_aatom (map_atom fl a).
Proof. intros fl [p ls|x y]; simpl; auto. Qed.

Lemma get_connectors_atoms_aatom : forall l,
  Forall is_aatom (snd (get_connectors l)).
Proof.
  induction l as [|h t IH]; simpl.
  - constructor.
  - destruct (get_connectors t) as [c a]. simpl in IH.
    destruct h as [p ls|x y]; simpl.
    + constructor; [exact I | exact IH].
    + exact IH.
Qed.

Lemma fuse_atoms_aatom : forall fuel conns atoms,
  Forall is_aatom atoms -> Forall is_aatom (fuse_atoms fuel conns atoms).
Proof.
  induction fuel as [|fuel IH]; intros conns atoms H; simpl; auto.
  destruct conns as [|[x y] rest]; auto.
  destruct (x =? y); auto.
  apply IH. unfold subst_atoms.
  apply Forall_forall. intros a Hin.
  apply in_map_iff in Hin. destruct Hin as [b [Hb Hbin]].
  subst a. apply map_atom_is_aatom.
  rewrite Forall_forall in H. auto.
Qed.

Lemma nf_atoms_aatom : forall t, Forall is_aatom (nf_atoms t).
Proof.
  intros t. unfold nf_atoms.
  destruct (get_connectors (flatten_atoms t)) as [conns atoms] eqn:E.
  apply fuse_atoms_aatom.
  assert (A := get_connectors_atoms_aatom (flatten_atoms t)).
  rewrite E in A. simpl in A. exact A.
Qed.

Lemma connector_free_make_mol : forall l,
  Forall is_aatom l -> connector_free (make_mol l).
Proof.
  induction l as [|a l' IH]; intros H.
  - exact I.
  - inversion H as [|? ? Ha Hl']; subst.
    rewrite make_mol_cons_eq. simpl. split.
    + destruct a as [p ls|x y]; [ exact I | destruct Ha ].
    + apply IH, Hl'.
Qed.

Theorem normalize_connector_free : forall t, connector_free (normalize t).
Proof. intros t. apply connector_free_make_mol, nf_atoms_aatom. Qed.

Lemma flatten_make_mol : forall l, flatten_atoms (make_mol l) = l.
Proof.
  induction l as [|a l' IH]; auto.
  rewrite make_mol_cons_eq. simpl. rewrite IH. reflexivity.
Qed.

Corollary flatten_normalize : forall t, flatten_atoms (normalize t) = denote t.
Proof. intros t. unfold normalize, denote. apply flatten_make_mol. Qed.

(* --- Lemma A : G ==m normalize G  (closed, well-formed G) -------- *)
(*  Building blocks first.                                           *)

Definition conns_as_atoms (cs : list (Link * Link)) : list Atom :=
  map (fun c => AConn (fst c) (snd c)) cs.

Lemma links_TAtom : forall a, links (TAtom a) = links_of_atom a.
Proof. intros [p ls|x y]; reflexivity. Qed.

Lemma links_of_atom_map_atom : forall fl a,
  links_of_atom (map_atom fl a) = map fl (links_of_atom a).
Proof. intros fl [p ls|x y]; reflexivity. Qed.

Lemma links_flatten : forall t,
  links t = flat_map links_of_atom (flatten_atoms t).
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; simpl.
  - reflexivity.
  - destruct a; simpl; rewrite ?app_nil_r; reflexivity.
  - rewrite flat_map_app, IH1, IH2. reflexivity.
Qed.

Lemma links_make_mol : forall l,
  links (make_mol l) = flat_map links_of_atom l.
Proof.
  induction l as [|a l' IH]; auto.
  change (links (make_mol (a :: l')))
    with (links (TAtom a) ++ links (make_mol l')).
  rewrite links_TAtom, IH. reflexivity.
Qed.

Lemma link_multiset_flatten_make_mol : forall G,
  link_multiset G = link_multiset (make_mol (flatten_atoms G)).
Proof.
  intros G. unfold link_multiset.
  rewrite links_flatten, links_make_mol. reflexivity.
Qed.

Lemma wellformed_t_flatten_make_mol : forall G,
  wellformed_t G -> wellformed_t (make_mol (flatten_atoms G)).
Proof.
  intros G H.
  apply wellformed_t_link_multiset with G; auto.
  rewrite link_multiset_flatten_make_mol at 1. apply meq_refl.
Qed.

Lemma list_to_multiset_perm : forall (l1 l2 : list Link),
  Permutation l1 l2 -> meq (list_to_multiset l1) (list_to_multiset l2).
Proof.
  intros l1 l2 H. induction H; simpl.
  - apply meq_refl.
  - apply meq_right. auto.
  - unfold meq. intros a. unfold munion. simpl.
    rewrite !PeanoNat.Nat.add_assoc.
    f_equal. apply PeanoNat.Nat.add_comm.
  - apply meq_trans with (list_to_multiset l'); auto.
Qed.

Lemma Permutation_flat_map :
  forall {A B} (f : A -> list B) l1 l2,
    Permutation l1 l2 -> Permutation (flat_map f l1) (flat_map f l2).
Proof.
  intros A B f l1 l2 H. induction H; simpl; auto.
  - apply Permutation_app_head. auto.
  - rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - eapply Permutation_trans; eauto.
Qed.

Lemma wf_lm_eq : forall P Q,
  link_multiset P = link_multiset Q -> wellformed_t P -> wellformed_t Q.
Proof.
  intros P Q E. apply wellformed_t_link_multiset. rewrite E. apply meq_refl.
Qed.

Lemma wf_lm_meq : forall P Q,
  meq (link_multiset P) (link_multiset Q) -> wellformed_t P -> wellformed_t Q.
Proof. exact wellformed_t_link_multiset. Qed.

Lemma link_multiset_TZero_l : forall t,
  link_multiset (TMol TZero t) = link_multiset t.
Proof. intros t. unfold link_multiset. reflexivity. Qed.

Lemma link_multiset_TZero_r : forall t,
  link_multiset (TMol t TZero) = link_multiset t.
Proof. intros t. unfold link_multiset. simpl. rewrite app_nil_r. reflexivity. Qed.

Lemma wellformed_t_TZero_l : forall t,
  wellformed_t t -> wellformed_t (TMol TZero t).
Proof. intros t. apply wf_lm_eq. rewrite link_multiset_TZero_l. reflexivity. Qed.

Lemma wellformed_t_TZero_r : forall t,
  wellformed_t t -> wellformed_t (TMol t TZero).
Proof. intros t. apply wf_lm_eq. rewrite link_multiset_TZero_r. reflexivity. Qed.

Lemma link_multiset_mol_make_mol : forall l1 l2,
  meq (link_multiset (TMol (make_mol l1) (make_mol l2)))
      (link_multiset (make_mol (l1 ++ l2))).
Proof.
  intros l1 l2.
  eapply meq_trans; [ apply link_multiset_mol |].
  unfold link_multiset. rewrite !links_make_mol, flat_map_app.
  apply meq_sym, list_to_multiset_app.
Qed.

Lemma wellformed_t_mol_make_mol : forall l1 l2,
  wellformed_t (make_mol (l1 ++ l2)) ->
  wellformed_t (TMol (make_mol l1) (make_mol l2)).
Proof.
  intros l1 l2. apply wf_lm_meq.
  apply meq_sym, link_multiset_mol_make_mol.
Qed.

Lemma wellformed_t_make_mol_app : forall l1 l2,
  wellformed_t (make_mol (l1 ++ l2)) -> wellformed_t (make_mol l1).
Proof.
  intros l1 l2 H.
  apply wellformed_t_mol_make_mol in H.
  apply wellformed_t_inj in H. tauto.
Qed.

(* [make_mol (a :: l)] is definitionally [TMol (TAtom a) (make_mol l)] *)
Lemma make_mol_cons : forall a l,
  wellformed_t (make_mol (a :: l)) ->
  make_mol (a :: l) ==m TMol (TAtom a) (make_mol l).
Proof. intros a l H. apply congm_refl. exact H. Qed.

Lemma make_mol_app : forall l1 l2,
  wellformed_t (make_mol (l1 ++ l2)) ->
  make_mol (l1 ++ l2) ==m TMol (make_mol l1) (make_mol l2).
Proof.
  induction l1 as [|a l1 IH]; intros l2 H.
  - apply congm_sym.
    + apply wellformed_t_TZero_l. exact H.
    + exact H.
    + apply congm_E1. exact H.
  - (* wf of the various rearrangements *)
    assert (Hcons := make_mol_cons a (l1 ++ l2) H).
    assert (WF1 : wellformed_t (TMol (TAtom a) (make_mol (l1 ++ l2)))).
    { apply (proj2 (congm_wellformed_t _ _ Hcons)). }
    assert (WFapp : wellformed_t (make_mol (l1 ++ l2))).
    { apply wellformed_t_inj in WF1. tauto. }
    assert (WFa : wellformed_t (TAtom a)).
    { apply wellformed_t_inj in WF1. tauto. }
    assert (IHapp := IH l2 WFapp).
    assert (WF2 : wellformed_t (TMol (TAtom a) (TMol (make_mol l1) (make_mol l2)))).
    { apply wf_lm_meq with (TMol (TAtom a) (make_mol (l1 ++ l2))); auto.
      apply link_multiset_inj; [ apply meq_refl |].
      apply meq_sym, link_multiset_mol_make_mol. }
    assert (WF3 : wellformed_t (TMol (TMol (TAtom a) (make_mol l1)) (make_mol l2))).
    { apply wf_lm_meq with (TMol (TAtom a) (TMol (make_mol l1) (make_mol l2))); auto.
      apply link_multiset_assoc. }
    assert (WFgoalR : wellformed_t (TMol (make_mol (a :: l1)) (make_mol l2))).
    { apply wf_lm_meq with (make_mol ((a :: l1) ++ l2)); [| exact H].
      apply meq_sym, link_multiset_mol_make_mol. }
    assert (WFa1 : wellformed_t (make_mol (a :: l1))).
    { apply wellformed_t_inj in WFgoalR. tauto. }
    assert (WFa1' : wellformed_t (TMol (TAtom a) (make_mol l1))).
    { apply wellformed_t_inj in WF3. tauto. }
    (* the chain *)
    apply congm_trans with (TMol (TAtom a) (make_mol (l1 ++ l2))); auto.
    apply congm_trans with (TMol (TAtom a) (TMol (make_mol l1) (make_mol l2))); auto.
    { apply congm_E5r; auto. }
    apply congm_trans with (TMol (TMol (TAtom a) (make_mol l1)) (make_mol l2)); auto.
    { apply congm_E3. exact WF2. }
    apply congm_E5; auto.
    apply congm_sym; auto.
    apply make_mol_cons. exact WFa1.
Qed.

Lemma link_multiset_cons_mol : forall a l,
  link_multiset (make_mol (a :: l)) = link_multiset (TMol (TAtom a) (make_mol l)).
Proof. reflexivity. Qed.

Lemma wellformed_t_cons_mol : forall a l,
  wellformed_t (make_mol (a :: l)) <-> wellformed_t (TMol (TAtom a) (make_mol l)).
Proof. intros a l. split; intro H; exact H. Qed.

Lemma make_mol_perm : forall l1 l2,
  Permutation l1 l2 ->
  wellformed_t (make_mol l1) ->
  make_mol l1 ==m make_mol l2.
Proof.
  intros l1 l2 HP.
  induction HP as [ | x l l' HP IH | x y l | l l' l'' HP1 IH1 HP2 IH2 ];
    intros W.
  - apply congm_refl. exact W.
  - (* perm_skip :  x :: l  ~  x :: l'   (cons is definitional) *)
    change (wellformed_t (TMol (TAtom x) (make_mol l))) in W.
    assert (Wl : wellformed_t (make_mol l)) by (apply wellformed_t_inj in W; tauto).
    assert (Hmeq : meq (link_multiset (make_mol l)) (link_multiset (make_mol l'))).
    { unfold link_multiset. rewrite !links_make_mol.
      apply list_to_multiset_perm, Permutation_flat_map, HP. }
    assert (Wr' : wellformed_t (TMol (TAtom x) (make_mol l'))).
    { apply wf_lm_meq with (TMol (TAtom x) (make_mol l)); auto.
      apply link_multiset_inj; [ apply meq_refl | exact Hmeq ]. }
    change (make_mol (x :: l) ==m make_mol (x :: l')).
    change (TMol (TAtom x) (make_mol l) ==m TMol (TAtom x) (make_mol l')).
    apply congm_E5r; [ exact W | exact Wr' | apply IH; exact Wl ].
  - (* perm_swap :  y :: x :: l  ~  x :: y :: l   (cons is definitional) *)
    change (wellformed_t (TMol (TAtom y) (TMol (TAtom x) (make_mol l)))) in W.
    assert (Wx  : wellformed_t (TAtom x)).
    { apply wellformed_t_inj in W. destruct W as [_ W].
      apply wellformed_t_inj in W. tauto. }
    assert (Wy  : wellformed_t (TAtom y)) by (apply wellformed_t_inj in W; tauto).
    assert (WM  : wellformed_t (make_mol l)).
    { apply wellformed_t_inj in W. destruct W as [_ W].
      apply wellformed_t_inj in W. tauto. }
    assert (Wyx2 : wellformed_t (TMol (TMol (TAtom y) (TAtom x)) (make_mol l))).
    { apply wf_lm_meq with (TMol (TAtom y) (TMol (TAtom x) (make_mol l))); auto.
      apply link_multiset_assoc. }
    assert (Wxy2 : wellformed_t (TMol (TMol (TAtom x) (TAtom y)) (make_mol l))).
    { apply wf_lm_meq with (TMol (TMol (TAtom y) (TAtom x)) (make_mol l)); auto.
      apply link_multiset_inj; [ apply link_multiset_swap | apply meq_refl ]. }
    assert (Wxy1 : wellformed_t (TMol (TAtom x) (TMol (TAtom y) (make_mol l)))).
    { apply wf_lm_meq with (TMol (TMol (TAtom x) (TAtom y)) (make_mol l)); auto.
      apply meq_sym, link_multiset_assoc. }
    assert (Wyx0 : wellformed_t (TMol (TAtom y) (TAtom x))).
    { apply wellformed_t_inj in Wyx2. tauto. }
    change (TMol (TAtom y) (TMol (TAtom x) (make_mol l))
            ==m TMol (TAtom x) (TMol (TAtom y) (make_mol l))).
    apply congm_trans with (TMol (TMol (TAtom y) (TAtom x)) (make_mol l)); auto.
    { apply congm_E3, W. }
    apply congm_trans with (TMol (TMol (TAtom x) (TAtom y)) (make_mol l)); auto.
    { apply congm_E5; [ exact Wyx2 | exact Wxy2 | apply congm_E2, Wyx0 ]. }
    apply congm_sym; auto.
    apply congm_E3, Wxy1.
  - (* perm_trans *)
    assert (Wl' : wellformed_t (make_mol l')).
    { apply wf_lm_meq with (make_mol l); auto.
      unfold link_multiset. rewrite !links_make_mol.
      apply list_to_multiset_perm, Permutation_flat_map, HP1. }
    apply congm_trans with (make_mol l'); auto.
    { apply wf_lm_meq with (make_mol l); auto.
      unfold link_multiset. rewrite !links_make_mol.
      apply list_to_multiset_perm, Permutation_flat_map.
      eapply Permutation_trans; [ apply HP1 | apply HP2 ]. }
Qed.

Lemma cong_flatten : forall t,
  wellformed_t t -> t ==m make_mol (flatten_atoms t).
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; intros W.
  - apply congm_refl. exact W.
  - (* TAtom a :  make_mol [a] = TMol (TAtom a) TZero *)
    change (make_mol (flatten_atoms (TAtom a))) with (TMol (TAtom a) TZero).
    apply congm_sym.
    + apply wellformed_t_TZero_r, W.
    + exact W.
    + apply congm_trans with (TMol TZero (TAtom a)).
      * apply wellformed_t_TZero_r, W.
      * apply wellformed_t_TZero_l, W.
      * exact W.
      * apply congm_E2, (wellformed_t_TZero_r _ W).
      * apply congm_E1, W.
  - simpl.
    assert (WF1 : wellformed_t t1) by (apply wellformed_t_inj in W; tauto).
    assert (WF2 : wellformed_t t2) by (apply wellformed_t_inj in W; tauto).
    assert (WFapp : wellformed_t (make_mol (flatten_atoms t1 ++ flatten_atoms t2))).
    { apply wf_lm_eq with (TMol t1 t2); [| exact W].
      apply (link_multiset_flatten_make_mol (TMol t1 t2)). }
    assert (WFmm : wellformed_t (TMol (make_mol (flatten_atoms t1))
                                      (make_mol (flatten_atoms t2)))).
    { apply wellformed_t_mol_make_mol. exact WFapp. }
    assert (WFmid : wellformed_t (TMol (make_mol (flatten_atoms t1)) t2)).
    { apply wf_lm_meq with (TMol t1 t2); [| exact W].
      apply link_multiset_inj; [ | apply meq_refl ].
      rewrite (link_multiset_flatten_make_mol t1) at 1. apply meq_refl. }
    apply congm_trans with (TMol (make_mol (flatten_atoms t1)) (make_mol (flatten_atoms t2))).
    + exact W.
    + exact WFmm.
    + exact WFapp.
    + apply congm_trans with (TMol (make_mol (flatten_atoms t1)) t2).
      * exact W.
      * exact WFmid.
      * exact WFmm.
      * apply congm_E5; [ exact W | exact WFmid | apply IH1; exact WF1 ].
      * apply congm_E5r; [ exact WFmid | exact WFmm | apply IH2; exact WF2 ].
    + apply congm_sym; [ exact WFapp | exact WFmm |].
      apply make_mol_app. exact WFapp.
Qed.

(* --- get_connectors : move all connectors to the front ---------- *)

Lemma get_connectors_perm : forall l conns atoms,
  get_connectors l = (conns, atoms) ->
  Permutation l (conns_as_atoms conns ++ atoms).
Proof.
  induction l as [|h t IH]; intros conns atoms H; simpl in H.
  - inversion H. apply perm_nil.
  - destruct (get_connectors t) as [c a] eqn:E.
    specialize (IH c a eq_refl).
    destruct h as [p ls|x y].
    + (* AAtom *)
      injection H as Hc Ha. subst conns atoms.
      apply Permutation_trans with (AAtom p ls :: (conns_as_atoms c ++ a)).
      * apply perm_skip, IH.
      * apply Permutation_middle.
    + (* AConn *)
      injection H as Hc Ha. subst conns atoms.
      change (conns_as_atoms ((x, y) :: c))
        with (AConn x y :: conns_as_atoms c).
      apply perm_skip, IH.
Qed.

(* --- substitution / make_mol algebra --------------------------- *)

Lemma subst_atoms_app : forall Y X l1 l2,
  subst_atoms Y X (l1 ++ l2) = subst_atoms Y X l1 ++ subst_atoms Y X l2.
Proof. intros. unfold subst_atoms. apply map_app. Qed.

Lemma subst_atoms_conns_as_atoms : forall Y X cs,
  subst_atoms Y X (conns_as_atoms cs) = conns_as_atoms (map (subst_conn Y X) cs).
Proof.
  intros Y X cs. unfold subst_atoms, conns_as_atoms, subst_conn.
  rewrite !map_map. apply map_ext. intros [a b]. reflexivity.
Qed.

Lemma substitute_make_mol : forall Y X l,
  substitute Y X (make_mol l) = make_mol (subst_atoms Y X l).
Proof.
  intros Y X l. induction l as [|a l' IH]; auto.
  change (substitute Y X (make_mol (a :: l')))
    with (TMol (TAtom (map_atom (substitute_link Y X) a))
              (substitute Y X (make_mol l'))).
  rewrite IH.
  change (make_mol (subst_atoms Y X (a :: l')))
    with (TMol (TAtom (map_atom (substitute_link Y X) a))
              (make_mol (subst_atoms Y X l'))).
  reflexivity.
Qed.

(* --- Closed is preserved by ==m  (needed for connector peeling) --- *)

Lemma nil_iff_forall_not_in : forall {A} (l : list A),
  l = [] <-> forall x, ~ In x l.
Proof.
  intros A [|h t]; split; intros H.
  - intros x [].
  - reflexivity.
  - discriminate.
  - exfalso. apply (H h). left. reflexivity.
Qed.

Lemma Closed_iff : forall t,
  Closed t <-> forall X, multiplicity (link_multiset t) X <> 1.
Proof.
  intros t. unfold Closed. rewrite nil_iff_forall_not_in.
  split; intros H X; specialize (H X).
  - rewrite in_freelinks in H. exact H.
  - rewrite in_freelinks. exact H.
Qed.

Lemma multiplicity_TAtom_AConn : forall X Y L,
  multiplicity (link_multiset (TAtom (AConn X Y))) L
  = (if Leq_dec X L then 1 else 0) + (if Leq_dec Y L then 1 else 0).
Proof.
  intros X Y L. unfold link_multiset. simpl.
  destruct (Leq_dec X L); destruct (Leq_dec Y L); simpl; lia.
Qed.

Lemma multiplicity_TZero : forall L,
  multiplicity (link_multiset TZero) L = 0.
Proof. reflexivity. Qed.

Lemma wellformed_t_mult_le : forall g X,
  wellformed_t g -> multiplicity (link_multiset g) X <= 2.
Proof.
  intros g X W.
  destruct (PeanoNat.Nat.le_gt_cases (multiplicity (link_multiset g) X) 2)
    as [Hle|G]; auto.
  rewrite wellformed_t_forall in W.
  assert (In X (links g)) by (apply in_links_link_multiset; lia).
  specialize (W X H). lia.
Qed.

Lemma sum1_iff : forall a b a',
  a + b <= 2 -> a' + b <= 2 -> (a = 1 <-> a' = 1) ->
  (a + b = 1 <-> a' + b = 1).
Proof.
  intros a b a' H1 H2 [F B]. split; intros K.
  - destruct (PeanoNat.Nat.eq_dec a 1) as [e|e].
    + apply F in e. lia.
    + assert (a' <> 1) by (intro C; apply B in C; lia). lia.
  - destruct (PeanoNat.Nat.eq_dec a' 1) as [e|e].
    + apply B in e. lia.
    + assert (a <> 1) by (intro C; apply F in C; lia). lia.
Qed.

Lemma congm_mult1_iff : forall P Q,
  P ==m Q ->
  forall L, multiplicity (link_multiset P) L = 1
        <-> multiplicity (link_multiset Q) L = 1.
Proof.
  intros P Q H. induction H; intros L.
  - (* E1 *) rewrite link_multiset_TZero_l. reflexivity.
  - (* E2 *) rewrite (link_multiset_swap P Q L). reflexivity.
  - (* E3 *) rewrite (link_multiset_assoc P Q R L). reflexivity.
  - (* E5 : {{P,Q}} ==m {{P',Q}} from P ==m P' *)
    rewrite !multiplicity_mol.
    apply sum1_iff.
    + assert (Hle := wellformed_t_mult_le _ L H).
      rewrite multiplicity_mol in Hle. exact Hle.
    + assert (Hle := wellformed_t_mult_le _ L H0).
      rewrite multiplicity_mol in Hle. exact Hle.
    + apply IHcongm.
  - (* E7 : {{X=X}} ==m TZero *)
    rewrite multiplicity_TZero, multiplicity_TAtom_AConn.
    destruct (Leq_dec X L); simpl; split; intros K; lia.
  - (* E9 : {{X=Y,A}} ==m {{A[Y/X]}} *)
    rename H into WF1. rename H0 into WF2. rename H1 into HXA.
    assert (Hm1 : multiplicity (link_multiset (TAtom A)) X = 1)
      by (apply in_freelinks; exact HXA).
    assert (Hxy : X <> Y).
    { intro E. subst Y.
      assert (Hle := wellformed_t_mult_le _ X WF1).
      rewrite multiplicity_mol, multiplicity_TAtom_AConn, Leq_dec_refl in Hle.
      simpl in Hle. lia. }
    rewrite multiplicity_mol, multiplicity_TAtom_AConn.
    destruct (Leq_dec X L) as [EX|EX].
    + subst L. rewrite (subst_multiplicity_X (TAtom A) X Y Hxy).
      destruct (Leq_dec Y X); [ congruence |].
      simpl. rewrite Hm1. split; intros K; lia.
    + destruct (Leq_dec Y L) as [EY|EY].
      * subst L. rewrite (subst_multiplicity_Y (TAtom A) X Y Hxy).
        rewrite Hm1. simpl. split; intros K; lia.
      * rewrite (subst_multiplicity_other (TAtom A) X Y L EX EY).
        simpl. reflexivity.
  - (* refl *) reflexivity.
  - (* trans *) rewrite IHcongm1. apply IHcongm2.
  - (* sym *) symmetry. apply IHcongm.
Qed.

Lemma congm_Closed : forall P Q, P ==m Q -> (Closed P <-> Closed Q).
Proof.
  intros P Q H. rewrite !Closed_iff.
  split; intros C L; specialize (C L);
  [ rewrite <- (congm_mult1_iff _ _ H L) | rewrite (congm_mult1_iff _ _ H L) ];
  exact C.
Qed.

Lemma congm_trans' : forall P Q R, P ==m Q -> Q ==m R -> P ==m R.
Proof.
  intros P Q R H1 H2.
  apply congm_trans with Q.
  - exact (proj1 (congm_wellformed_t _ _ H1)).
  - exact (proj2 (congm_wellformed_t _ _ H1)).
  - exact (proj2 (congm_wellformed_t _ _ H2)).
  - exact H1.
  - exact H2.
Qed.

Lemma congm_sym' : forall P Q, P ==m Q -> Q ==m P.
Proof.
  intros P Q H. apply congm_sym.
  - exact (proj1 (congm_wellformed_t _ _ H)).
  - exact (proj2 (congm_wellformed_t _ _ H)).
  - exact H.
Qed.

(* --- Lemma A : G ==m normalize G  for closed well-formed G ------- *)

Lemma fuse_atoms_cong : forall n conns atoms,
  length conns <= n ->
  wellformed_t (make_mol (conns_as_atoms conns ++ atoms)) ->
  Closed (make_mol (conns_as_atoms conns ++ atoms)) ->
  make_mol (conns_as_atoms conns ++ atoms)
    ==m make_mol (fuse_atoms n conns atoms).
Proof.
  induction n as [|n IH]; intros conns atoms Hn WF HC.
  - destruct conns as [|c rest]; [ apply congm_refl; exact WF | simpl in Hn; lia ].
  - destruct conns as [|[x y] rest].
    + apply congm_refl; exact WF.
    + simpl in Hn. apply le_S_n in Hn.
      change (conns_as_atoms ((x, y) :: rest) ++ atoms)
        with (AConn x y :: (conns_as_atoms rest ++ atoms)) in WF, HC |- *.
      change (make_mol (AConn x y :: (conns_as_atoms rest ++ atoms)))
        with (TMol (TAtom (AConn x y)) (make_mol (conns_as_atoms rest ++ atoms)))
        in WF, HC |- *.
      set (R := conns_as_atoms rest ++ atoms) in *.
      assert (WFR : wellformed_t (make_mol R))
        by (apply wellformed_t_inj in WF; tauto).
      change (make_mol (fuse_atoms (S n) ((x, y) :: rest) atoms))
        with (make_mol (if x =? y
                        then fuse_atoms n rest atoms
                        else fuse_atoms n (map (subst_conn y x) rest)
                                          (subst_atoms y x atoms))).
      destruct (x =? y) eqn:Exy.
      * (* x = y : drop the connector via (E7)+(E1) *)
        assert (Exy2 : x = y) by (apply eqb_eq, Exy).
        assert (Hstep : TMol (TAtom (AConn x y)) (make_mol R) ==m make_mol R).
        { apply congm_trans' with (TMol TZero (make_mol R)).
          - apply congm_E5.
            + exact WF.
            + apply wellformed_t_TZero_l, WFR.
            + rewrite Exy2. apply congm_E7.
          - apply congm_E1, WFR. }
        apply congm_trans' with (make_mol R).
        -- exact Hstep.
        -- apply IH; [ exact Hn | exact WFR |].
           apply (proj1 (congm_Closed _ _ Hstep)), HC.
      * (* x <> y : eliminate the connector via (E9ex) *)
        assert (Exy2 : x <> y) by (apply eqb_neq, Exy).
        assert (Hnyx : y <> x) by (intro; apply Exy2; congruence).
        assert (Hlex : multiplicity (link_multiset (make_mol R)) x <= 1).
        { assert (Hle := wellformed_t_mult_le _ x WF).
          rewrite multiplicity_mol, multiplicity_TAtom_AConn, Leq_dec_refl in Hle.
          destruct (Leq_dec y x); [ congruence |]. simpl in Hle. lia. }
        assert (Hley : multiplicity (link_multiset (make_mol R)) y <= 1).
        { assert (Hle := wellformed_t_mult_le _ y WF).
          rewrite multiplicity_mol, multiplicity_TAtom_AConn, Leq_dec_refl in Hle.
          destruct (Leq_dec x y); [ congruence |]. simpl in Hle. lia. }
        assert (Hmx : multiplicity (link_multiset (make_mol R)) x = 1).
        { rewrite Closed_iff in HC. specialize (HC x).
          rewrite multiplicity_mol, multiplicity_TAtom_AConn, Leq_dec_refl in HC.
          destruct (Leq_dec y x); [ congruence |]. simpl in HC. lia. }
        assert (WFsub : wellformed_t (substitute y x (make_mol R))).
        { apply subst_wellformed_t; [ exact WFR | lia ]. }
        assert (HA : TMol (TAtom (AConn x y)) (make_mol R)
                     ==m substitute y x (make_mol R)).
        { apply (congm_E9ex x y (make_mol R)).
          - exact WF.
          - exact WFsub.
          - apply in_freelinks, Hmx. }
        rewrite substitute_make_mol in HA, WFsub.
        unfold R in HA, WFsub.
        rewrite subst_atoms_app, subst_atoms_conns_as_atoms in HA, WFsub.
        apply congm_trans' with
          (make_mol (conns_as_atoms (map (subst_conn y x) rest)
                     ++ subst_atoms y x atoms)).
        -- exact HA.
        -- apply IH.
           ++ rewrite length_map. exact Hn.
           ++ exact WFsub.
           ++ apply (proj1 (congm_Closed _ _ HA)), HC.
Qed.

Theorem normalize_cong : forall G,
  wellformed_t G -> Closed G -> G ==m normalize G.
Proof.
  intros G WF HC.
  unfold normalize, nf_atoms.
  destruct (get_connectors (flatten_atoms G)) as [conns atoms] eqn:E.
  assert (Hperm : Permutation (flatten_atoms G) (conns_as_atoms conns ++ atoms))
    by (apply get_connectors_perm; exact E).
  assert (Hf : G ==m make_mol (flatten_atoms G)) by (apply cong_flatten; exact WF).
  assert (WFf : wellformed_t (make_mol (flatten_atoms G)))
    by (apply wellformed_t_flatten_make_mol; exact WF).
  assert (Hp : make_mol (flatten_atoms G) ==m make_mol (conns_as_atoms conns ++ atoms))
    by (apply make_mol_perm; [ exact Hperm | exact WFf ]).
  assert (Hcong : G ==m make_mol (conns_as_atoms conns ++ atoms))
    by (apply congm_trans' with (make_mol (flatten_atoms G)); [ exact Hf | exact Hp ]).
  apply congm_trans' with (make_mol (conns_as_atoms conns ++ atoms)).
  - exact Hcong.
  - apply fuse_atoms_cong.
    + reflexivity.
    + exact (proj2 (congm_wellformed_t _ _ Hcong)).
    + apply (proj1 (congm_Closed _ _ Hcong)), HC.
Qed.

(* ================================================================== *)
(*  Layer 2 : graph_iso is an equivalence; easy cases of  cong => iso  *)
(* ================================================================== *)

Lemma map_atom_id : forall a, map_atom (fun x => x) a = a.
Proof. intros [p ls|x y]; simpl; [ rewrite map_id | ]; reflexivity. Qed.

Lemma map_atom_comp : forall (f g : Link -> Link) a,
  map_atom f (map_atom g a) = map_atom (fun x => f (g x)) a.
Proof. intros f g [p ls|x y]; simpl; [ rewrite map_map | ]; reflexivity. Qed.

Lemma map_map_atom_id : forall l, map (map_atom (fun x => x)) l = l.
Proof.
  induction l as [|a l IH]; simpl; auto.
  rewrite map_atom_id, IH. reflexivity.
Qed.

Lemma graph_iso_refl : forall l, graph_iso l l.
Proof.
  intros l. exists (fun x => x). split.
  - split; [ intros x y H; exact H | intros y; exists y; reflexivity ].
  - rewrite map_map_atom_id. apply Permutation_refl.
Qed.

Lemma graph_iso_trans : forall l1 l2 l3,
  graph_iso l1 l2 -> graph_iso l2 l3 -> graph_iso l1 l3.
Proof.
  intros l1 l2 l3 [f [[Fi Fs] Pf]] [g [[Gi Gs] Pg]].
  exists (fun x => g (f x)). split.
  - split.
    + intros x y H. apply Fi, Gi, H.
    + intros y. destruct (Gs y) as [z Hz]. destruct (Fs z) as [w Hw].
      exists w. rewrite Hw. exact Hz.
  - assert (E : map (map_atom g) (map (map_atom f) l1)
              = map (map_atom (fun x => g (f x))) l1).
    { rewrite map_map. apply map_ext. intros a. apply map_atom_comp. }
    rewrite <- E.
    apply Permutation_trans with (map (map_atom g) l2).
    + apply Permutation_map. exact Pf.
    + exact Pg.
Qed.

Lemma bij_unique_preimage : forall (f : Link -> Link),
  Bijective f -> forall y, exists ! x, f x = y.
Proof.
  intros f [Fi Fs] y. destruct (Fs y) as [x Hx].
  exists x. split; [ exact Hx |].
  intros x' Hx'. apply Fi. rewrite Hx, Hx'. reflexivity.
Qed.

Definition finv (f : Link -> Link) (Hf : Bijective f) (y : Link) : Link :=
  proj1_sig (constructive_definite_description _ (bij_unique_preimage f Hf y)).

Lemma finv_f : forall f Hf x, finv f Hf (f x) = x.
Proof.
  intros f Hf x. unfold finv.
  destruct (constructive_definite_description _ _) as [z Hz]. simpl.
  destruct Hf as [Fi _]. apply Fi. exact Hz.
Qed.

Lemma f_finv : forall f Hf y, f (finv f Hf y) = y.
Proof.
  intros f Hf y. unfold finv.
  destruct (constructive_definite_description _ _) as [z Hz]. simpl. exact Hz.
Qed.

Lemma map_atom_ext : forall (f g : Link -> Link) a,
  (forall x, f x = g x) -> map_atom f a = map_atom g a.
Proof.
  intros f g [p ls|x y] H; simpl; f_equal; auto.
  apply map_ext. exact H.
Qed.

Lemma graph_iso_sym : forall l1 l2, graph_iso l1 l2 -> graph_iso l2 l1.
Proof.
  intros l1 l2 [f [Hf Pf]].
  exists (finv f Hf). split.
  - split.
    + intros x y H.
      rewrite <- (f_finv f Hf x), <- (f_finv f Hf y), H. reflexivity.
    + intros y. exists (f y). apply finv_f.
  - apply Permutation_sym.
    assert (E : map (map_atom (finv f Hf)) (map (map_atom f) l1) = l1).
    { rewrite map_map. rewrite <- (map_map_atom_id l1) at 2.
      apply map_ext. intros a. rewrite map_atom_comp.
      apply map_atom_ext. intros x. apply finv_f. }
    rewrite <- E.
    apply Permutation_map. exact Pf.
Qed.

(* --- easy cases of  cong => graph_iso -------------------------- *)

Lemma nf_atoms_flatten_eq : forall t1 t2,
  flatten_atoms t1 = flatten_atoms t2 -> nf_atoms t1 = nf_atoms t2.
Proof. intros t1 t2 H. unfold nf_atoms. rewrite H. reflexivity. Qed.

Lemma nf_atoms_E1 : forall P, nf_atoms (TMol TZero P) = nf_atoms P.
Proof. intro P. apply nf_atoms_flatten_eq. reflexivity. Qed.

Lemma nf_atoms_E3 : forall P Q R,
  nf_atoms (TMol P (TMol Q R)) = nf_atoms (TMol (TMol P Q) R).
Proof.
  intros P Q R. apply nf_atoms_flatten_eq. simpl.
  rewrite app_assoc. reflexivity.
Qed.

Lemma nf_atoms_E7 : forall X, nf_atoms (TAtom (AConn X X)) = nf_atoms TZero.
Proof.
  intro X. unfold nf_atoms. simpl. rewrite eqb_refl. reflexivity.
Qed.

Lemma E9_neq : forall X Y (A : Atom),
  wellformed_t (TMol (TAtom (AConn X Y)) (TAtom A)) ->
  In X (freelinks (TAtom A)) -> X <> Y.
Proof.
  intros X Y A WF HXA E. subst Y.
  assert (Hle := wellformed_t_mult_le _ X WF).
  rewrite multiplicity_mol, multiplicity_TAtom_AConn, Leq_dec_refl in Hle.
  simpl in Hle. apply in_freelinks in HXA. lia.
Qed.

Lemma nf_atoms_E9 : forall X Y (A : Atom),
  wellformed_t (TMol (TAtom (AConn X Y)) (TAtom A)) ->
  In X (freelinks (TAtom A)) ->
  nf_atoms (TMol (TAtom (AConn X Y)) (TAtom A))
  = nf_atoms (substitute Y X (TAtom A)).
Proof.
  intros X Y A WF HXA.
  assert (Hxy : X <> Y) by (apply (E9_neq X Y A); assumption).
  apply eqb_neq in Hxy.
  unfold nf_atoms.
  destruct A as [p ls | u v]; simpl; rewrite Hxy; reflexivity.
Qed.

Lemma get_connectors_aatom_all : forall l,
  Forall is_aatom l -> get_connectors l = ([], l).
Proof.
  induction l as [|a l IH]; intros H; simpl; auto.
  inversion H as [|? ? Ha Hl]; subst.
  rewrite (IH Hl).
  destruct a as [p ls|x y]; [ reflexivity | destruct Ha ].
Qed.

Lemma nf_atoms_connector_free : forall l,
  Forall is_aatom l -> nf_atoms (make_mol l) = l.
Proof.
  intros l H. unfold nf_atoms.
  rewrite flatten_make_mol, (get_connectors_aatom_all l H). reflexivity.
Qed.

Lemma nf_atoms_normalize : forall t, nf_atoms (normalize t) = nf_atoms t.
Proof.
  intro t. unfold normalize.
  apply nf_atoms_connector_free, nf_atoms_aatom.
Qed.

Lemma denote_normalize : forall t, denote (normalize t) = denote t.
Proof. intro t. unfold denote. apply nf_atoms_normalize. Qed.

(* [fuse_atoms] applies one global renaming [uf conns] to [atoms].
   [uf] is (provably, TODO) invariant under permutation of [conns];
   that is what the (E2) case of the correspondence reduces to. *)
Fixpoint uf (fuel : nat) (conns : list (Link * Link)) : Link -> Link :=
  match fuel with
  | 0 => fun z => z
  | S fuel' =>
    match conns with
    | [] => fun z => z
    | (x, y) :: rest =>
        if x =? y then uf fuel' rest
        else fun z => uf fuel' (map (subst_conn y x) rest) (substitute_link y x z)
    end
  end.

Lemma fuse_atoms_uf : forall n conns atoms,
  length conns <= n ->
  fuse_atoms n conns atoms = map (map_atom (uf n conns)) atoms.
Proof.
  induction n as [|n IH]; intros conns atoms Hn.
  - destruct conns as [|c rest]; [ | simpl in Hn; lia ].
    change (fuse_atoms 0 [] atoms) with atoms.
    change (uf 0 []) with (fun z : Link => z).
    symmetry. apply map_map_atom_id.
  - destruct conns as [|[x y] rest].
    + change (fuse_atoms (S n) [] atoms) with atoms.
      change (uf (S n) []) with (fun z : Link => z).
      symmetry. apply map_map_atom_id.
    + simpl in Hn. apply le_S_n in Hn.
      simpl uf. simpl fuse_atoms.
      destruct (x =? y) eqn:Exy.
      * apply IH. exact Hn.
      * rewrite IH by (rewrite length_map; exact Hn).
        unfold subst_atoms. rewrite map_map.
        apply map_ext. intros a. rewrite map_atom_comp. reflexivity.
Qed.

Lemma nf_atoms_uf : forall t,
  nf_atoms t
  = let gc := get_connectors (flatten_atoms t) in
    map (map_atom (uf (length (fst gc)) (fst gc))) (snd gc).
Proof.
  intro t. unfold nf_atoms.
  destruct (get_connectors (flatten_atoms t)) as [conns atoms] eqn:E.
  simpl. apply fuse_atoms_uf. reflexivity.
Qed.

Lemma get_connectors_app : forall l1 l2,
  get_connectors (l1 ++ l2)
  = (fst (get_connectors l1) ++ fst (get_connectors l2),
     snd (get_connectors l1) ++ snd (get_connectors l2)).
Proof.
  induction l1 as [|a l1 IH]; intros l2; simpl.
  - destruct (get_connectors l2); reflexivity.
  - rewrite IH.
    destruct (get_connectors l1) as [c1 a1].
    destruct (get_connectors l2) as [c2 a2].
    destruct a as [p ls|x y]; reflexivity.
Qed.

(* --- the multiset of ordinary-atom shapes is a  ==m  invariant --- *)
Definition aatom_shapes (t : Term) : list (string * nat) :=
  flat_map (fun a => match a with
                     | AAtom p ls => [(p, length ls)]
                     | AConn _ _ => []
                     end) (flatten_atoms t).

Lemma aatom_shapes_mol : forall P Q,
  aatom_shapes (TMol P Q) = aatom_shapes P ++ aatom_shapes Q.
Proof. intros P Q. unfold aatom_shapes. simpl. apply flat_map_app. Qed.

Lemma congm_shapes : forall P Q, P ==m Q ->
  Permutation (aatom_shapes P) (aatom_shapes Q).
Proof.
  intros P Q H. induction H.
  - (* E1 *) unfold aatom_shapes; simpl. apply Permutation_refl.
  - (* E2 *) rewrite !aatom_shapes_mol. apply Permutation_app_comm.
  - (* E3 *) rewrite !aatom_shapes_mol, app_assoc. apply Permutation_refl.
  - (* E5 *) rewrite !aatom_shapes_mol. apply Permutation_app_tail. exact IHcongm.
  - (* E7 *) unfold aatom_shapes; simpl. apply Permutation_refl.
  - (* E9 *) unfold aatom_shapes; simpl.
    destruct A as [p ls|u v]; simpl; rewrite ?length_map; apply Permutation_refl.
  - (* refl *) apply Permutation_refl.
  - (* trans *) eapply Permutation_trans; eassumption.
  - (* sym *) apply Permutation_sym. exact IHcongm.
Qed.

(* ================================================================== *)
(*  Layer 2, take 2 :  "="  as a graph EDGE (no connector fusion)      *)
(*                                                                    *)
(*  A term denotes:  the list of ordinary atoms (nodes), plus the     *)
(*  connector-generated equivalence [edge_eq] on link names.          *)
(*  Two terms are iso (w.r.t. an interface I of free link names) when  *)
(*  there is a bijection on nodes preserving functors, such that the   *)
(*  edge_eq relation between ports — and between ports and interface   *)
(*  names — is preserved.  Interface names are fixed pointwise, which  *)
(*  is exactly what makes the (E5) congruence case compositional.     *)
(* ================================================================== *)

Definition node_atoms (t : Term) : list Atom :=
  filter (fun a => match a with AAtom _ _ => true | AConn _ _ => false end)
         (flatten_atoms t).

Definition term_conns (t : Term) : list (Link * Link) :=
  flat_map (fun a => match a with AConn x y => [(x, y)] | AAtom _ _ => [] end)
           (flatten_atoms t).

Definition edge_eq (c : list (Link * Link)) : Link -> Link -> Prop :=
  clos_refl_sym_trans Link (fun a b => In (a, b) c).

Definition portlink (ns : list Atom) (i k : nat) : option Link :=
  match nth_error ns i with
  | Some (AAtom _ ls) => nth_error ls k
  | _ => None
  end.

(* --- structural lemmas --- *)

Lemma node_atoms_mol : forall P Q,
  node_atoms (TMol P Q) = node_atoms P ++ node_atoms Q.
Proof. intros. unfold node_atoms. simpl. apply filter_app. Qed.

Lemma term_conns_mol : forall P Q,
  term_conns (TMol P Q) = term_conns P ++ term_conns Q.
Proof. intros. unfold term_conns. simpl. apply flat_map_app. Qed.

Lemma node_atoms_TZero : node_atoms TZero = []. Proof. reflexivity. Qed.
Lemma term_conns_TZero : term_conns TZero = []. Proof. reflexivity. Qed.

Lemma node_atoms_AAtom : forall p ls, node_atoms (TAtom (AAtom p ls)) = [AAtom p ls].
Proof. reflexivity. Qed.
Lemma node_atoms_AConn : forall x y, node_atoms (TAtom (AConn x y)) = [].
Proof. reflexivity. Qed.
Lemma term_conns_AAtom : forall p ls, term_conns (TAtom (AAtom p ls)) = [].
Proof. reflexivity. Qed.
Lemma term_conns_AConn : forall x y, term_conns (TAtom (AConn x y)) = [(x,y)].
Proof. reflexivity. Qed.

(* --- edge_eq is an equivalence, monotone, permutation-invariant --- *)

Lemma edge_eq_refl : forall c x, edge_eq c x x.
Proof. intros. apply rst_refl. Qed.

Lemma edge_eq_sym : forall c x y, edge_eq c x y -> edge_eq c y x.
Proof. intros. apply rst_sym. auto. Qed.

Lemma edge_eq_trans : forall c x y z,
  edge_eq c x y -> edge_eq c y z -> edge_eq c x z.
Proof. intros. eapply rst_trans; eauto. Qed.

Lemma edge_eq_step : forall c x y, In (x, y) c -> edge_eq c x y.
Proof. intros. apply rst_step. auto. Qed.

Lemma edge_eq_step' : forall c x y, In (y, x) c -> edge_eq c x y.
Proof. intros. apply rst_sym, rst_step. auto. Qed.

Lemma edge_eq_incl : forall c1 c2 x y,
  incl c1 c2 -> edge_eq c1 x y -> edge_eq c2 x y.
Proof.
  intros c1 c2 x y Hi H. induction H.
  - apply rst_step, Hi. auto.
  - apply rst_refl.
  - apply rst_sym; auto.
  - eapply rst_trans; eauto.
Qed.

Lemma edge_eq_perm : forall c1 c2 x y,
  Permutation c1 c2 -> edge_eq c1 x y -> edge_eq c2 x y.
Proof.
  intros c1 c2 x y HP. apply edge_eq_incl.
  intros p Hp. eapply Permutation_in; eauto.
Qed.

Lemma edge_eq_perm_iff : forall c1 c2 x y,
  Permutation c1 c2 -> (edge_eq c1 x y <-> edge_eq c2 x y).
Proof.
  intros. split; apply edge_eq_perm; auto. apply Permutation_sym; auto.
Qed.

(* --- interface-preserving graph isomorphism --- *)

Definition giso (I : list Link) (t1 t2 : Term) : Prop :=
  exists f g : nat -> nat,
    (forall i, g (f i) = i) /\
    (forall i, f (g i) = i) /\
    (forall i, i < length (node_atoms t1) -> f i < length (node_atoms t2)) /\
    (forall j, j < length (node_atoms t2) -> g j < length (node_atoms t1)) /\
    (forall i,
       option_map get_functor (nth_error (node_atoms t1) i)
       = option_map get_functor (nth_error (node_atoms t2) (f i))) /\
    (forall i k j l Xik Xjl Yik Yjl,
       portlink (node_atoms t1) i k = Some Xik ->
       portlink (node_atoms t1) j l = Some Xjl ->
       portlink (node_atoms t2) (f i) k = Some Yik ->
       portlink (node_atoms t2) (f j) l = Some Yjl ->
       (edge_eq (term_conns t1) Xik Xjl <-> edge_eq (term_conns t2) Yik Yjl)) /\
    (forall i k Z Xik Yik,
       In Z I ->
       portlink (node_atoms t1) i k = Some Xik ->
       portlink (node_atoms t2) (f i) k = Some Yik ->
       (edge_eq (term_conns t1) Xik Z <-> edge_eq (term_conns t2) Yik Z)) /\
    (forall Z W, In Z I -> In W I ->
       (edge_eq (term_conns t1) Z W <-> edge_eq (term_conns t2) Z W)).

Lemma giso_refl : forall I t, giso I t t.
Proof.
  intros I t. exists (fun i => i), (fun i => i).
  split; [ auto | split; [ auto | split; [ auto | split; [ auto |]]]].
  split; [ reflexivity |].
  split; [ | split ].
  - intros i k j l Xik Xjl Yik Yjl H1 H2 H3 H4.
    rewrite H1 in H3. rewrite H2 in H4. injection H3 as ->. injection H4 as ->.
    reflexivity.
  - intros i k Z Xik Yik HZ H1 H2.
    rewrite H1 in H2. injection H2 as ->. reflexivity.
  - intros Z W HZ HW. reflexivity.
Qed.

Lemma giso_sym : forall I t1 t2, giso I t1 t2 -> giso I t2 t1.
Proof.
  intros I t1 t2 (f & g & Hgf & Hfg & Hdom & Hcod & Hfun & Hconn & Hifc & Hff).
  exists g, f.
  split; [ exact Hfg | ].
  split; [ exact Hgf | ].
  split; [ exact Hcod | ].
  split; [ exact Hdom | ].
  split.
  - intros j. specialize (Hfun (g j)). rewrite Hfg in Hfun. symmetry. exact Hfun.
  - split.
    + intros i k j l Xik Xjl Yik Yjl H1 H2 H3 H4.
      specialize (Hconn (g i) k (g j) l Yik Yjl Xik Xjl).
      rewrite Hfg in Hconn. rewrite Hfg in Hconn.
      symmetry. apply Hconn; auto.
    + split.
      * intros i k Z Xik Yik HZ H1 H2.
        specialize (Hifc (g i) k Z Yik Xik HZ).
        rewrite Hfg in Hifc.
        symmetry. apply Hifc; auto.
      * intros Z W HZ HW. symmetry. apply Hff; auto.
Qed.

Lemma node_atoms_aatom : forall t, Forall is_aatom (node_atoms t).
Proof.
  intros t. unfold node_atoms. apply Forall_forall.
  intros a Hin. apply filter_In in Hin. destruct Hin as [_ Hb].
  destruct a; [ exact I | discriminate ].
Qed.

Lemma node_atoms_nth_aatom : forall t j x y,
  nth_error (node_atoms t) j = Some (AConn x y) -> False.
Proof.
  intros t j x y H.
  assert (Ha := node_atoms_aatom t).
  rewrite Forall_forall in Ha.
  apply nth_error_In in H. apply Ha in H. exact H.
Qed.

Lemma giso_port_mid : forall f t1 t2 i k Xik,
  (forall i,
     option_map get_functor (nth_error (node_atoms t1) i)
     = option_map get_functor (nth_error (node_atoms t2) (f i))) ->
  portlink (node_atoms t1) i k = Some Xik ->
  exists Mik, portlink (node_atoms t2) (f i) k = Some Mik.
Proof.
  intros f t1 t2 i k Xik Hfun H.
  unfold portlink in *.
  destruct (nth_error (node_atoms t1) i) as [[p ls|x y]|] eqn:E1; try discriminate.
  specialize (Hfun i). rewrite E1 in Hfun.
  destruct (nth_error (node_atoms t2) (f i)) as [[p' ls'|x' y']|] eqn:E2.
  - cbn in Hfun. injection Hfun as Hp Hlen.
    assert (k < length ls) by (apply nth_error_Some; congruence).
    destruct (nth_error ls' k) as [M|] eqn:E3.
    + exists M. reflexivity.
    + apply nth_error_None in E3. lia.
  - exfalso. eapply node_atoms_nth_aatom; eauto.
  - cbn in Hfun. discriminate.
Qed.

Lemma edge_eq_nil : forall x y, edge_eq [] x y <-> x = y.
Proof.
  intros x y. split.
  - intros H. induction H; try congruence. destruct H.
  - intros ->. apply edge_eq_refl.
Qed.

(* --- collapsing a connector  X=Y  (used for the (E9) case) --- *)

Lemma sl_never_X : forall Y X L, Y <> X -> substitute_link Y X L <> X.
Proof.
  intros Y X L HY. unfold substitute_link.
  destruct (L =? X) eqn:E.
  - congruence.
  - apply eqb_neq in E. congruence.
Qed.

Lemma subst_conn_no_X : forall Y X c a b,
  Y <> X -> In (a, b) (map (subst_conn Y X) c) -> a <> X /\ b <> X.
Proof.
  intros Y X c a b HY Hin.
  apply in_map_iff in Hin. destruct Hin as [[a' b'] [Heq _]].
  unfold subst_conn in Heq. simpl in Heq. injection Heq as Ha Hb.
  subst a b. split; apply sl_never_X; auto.
Qed.

Lemma edge_eq_endpoints : forall R a b,
  edge_eq R a b -> a = b \/
    (In a (flat_map (fun p => [fst p; snd p]) R) /\
     In b (flat_map (fun p => [fst p; snd p]) R)).
Proof.
  intros R a b H. induction H.
  - right. split; apply in_flat_map; exists (x, y); split; auto;
    [ left | right; left ]; reflexivity.
  - left. reflexivity.
  - destruct IHclos_refl_sym_trans as [->|[H1 H2]];
    [ left; reflexivity | right; auto ].
  - destruct IHclos_refl_sym_trans1 as [->|[Ha Hm1]];
    destruct IHclos_refl_sym_trans2 as [He|[Hm2 Hb]];
    try (left; congruence);
    right; split; (assumption || congruence).
Qed.

Lemma edge_eq_no_X : forall Y X c w,
  Y <> X -> edge_eq (map (subst_conn Y X) c) X w -> X = w.
Proof.
  intros Y X c w HY H.
  destruct (edge_eq_endpoints _ _ _ H) as [->|[Hin _]]; auto.
  exfalso. apply in_flat_map in Hin. destruct Hin as [[a' b'] [Hp Hmem]].
  apply (subst_conn_no_X Y X c a' b' HY) in Hp. destruct Hp as [HA HB].
  simpl in Hmem. destruct Hmem as [E|[E|[]]]; congruence.
Qed.

Lemma sl_eq_inv : forall Y X u v,
  Y <> X -> substitute_link Y X u = substitute_link Y X v ->
  u = v \/ (u = X /\ v = Y) \/ (u = Y /\ v = X).
Proof.
  intros Y X u v HY. unfold substitute_link.
  destruct (u =? X) eqn:Eu; destruct (v =? X) eqn:Ev; intros H.
  - apply eqb_eq in Eu, Ev. subst. auto.
  - apply eqb_eq in Eu. apply eqb_neq in Ev. subst u.
    right. left. auto.
  - apply eqb_neq in Eu. apply eqb_eq in Ev. subst v.
    right. right. auto.
  - auto.
Qed.

Lemma edge_eq_collapse_fwd : forall X Y c Z W,
  Y <> X ->
  edge_eq ((X, Y) :: c) Z W ->
  edge_eq (map (subst_conn Y X) c)
          (substitute_link Y X Z) (substitute_link Y X W).
Proof.
  intros X Y c Z W HY H. induction H.
  - destruct H as [H|H].
    + injection H as HX HY0. subst x y.
      replace (substitute_link Y X X) with Y
        by (unfold substitute_link; rewrite eqb_refl; reflexivity).
      replace (substitute_link Y X Y) with Y
        by (unfold substitute_link;
            destruct (Y =? X) eqn:E; [ apply eqb_eq in E; congruence | reflexivity ]).
      apply edge_eq_refl.
    + apply edge_eq_step, in_map_iff.
      exists (x, y). split; [ reflexivity | exact H ].
  - apply edge_eq_refl.
  - apply edge_eq_sym. auto.
  - eapply edge_eq_trans; eauto.
Qed.

Lemma edge_eq_collapse_bwd : forall X Y c a b,
  Y <> X ->
  edge_eq (map (subst_conn Y X) c) a b ->
  forall Z W, substitute_link Y X Z = a -> substitute_link Y X W = b ->
    edge_eq ((X, Y) :: c) Z W.
Proof.
  intros X Y c a b HY HH.
  induction HH as [a b Hab | a | a b Hab IH | a m b Ham IHam Hmb IHmb ];
    intros Z0 W0 Ha Hb.
  - apply in_map_iff in Hab. destruct Hab as [[a' b'] [Heq Hin]].
    unfold subst_conn in Heq; simpl in Heq; injection Heq as Hx Hy.
    assert (HZ : edge_eq ((X, Y) :: c) Z0 a').
    { assert (E : substitute_link Y X Z0 = substitute_link Y X a') by congruence.
      destruct (sl_eq_inv Y X Z0 a' HY E) as [->|[[-> ->]|[-> ->]]];
      [ apply edge_eq_refl | apply edge_eq_step; left; reflexivity
      | apply edge_eq_sym, edge_eq_step; left; reflexivity ]. }
    assert (HW : edge_eq ((X, Y) :: c) W0 b').
    { assert (E : substitute_link Y X W0 = substitute_link Y X b') by congruence.
      destruct (sl_eq_inv Y X W0 b' HY E) as [->|[[-> ->]|[-> ->]]];
      [ apply edge_eq_refl | apply edge_eq_step; left; reflexivity
      | apply edge_eq_sym, edge_eq_step; left; reflexivity ]. }
    eapply edge_eq_trans; [ exact HZ |].
    eapply edge_eq_trans; [ apply edge_eq_step; right; exact Hin |].
    apply edge_eq_sym, HW.
  - assert (E : substitute_link Y X Z0 = substitute_link Y X W0) by congruence.
    destruct (sl_eq_inv Y X Z0 W0 HY E) as [->|[[-> ->]|[-> ->]]];
    [ apply edge_eq_refl | apply edge_eq_step; left; reflexivity
    | apply edge_eq_sym, edge_eq_step; left; reflexivity ].
  - apply edge_eq_sym. apply IH; assumption.
  - assert (Hm_ne : m <> X).
    { intros ->.
      assert (Hax : X = a).
      { apply edge_eq_no_X with (Y := Y) (c := c); auto. apply edge_eq_sym, Ham. }
      apply (sl_never_X Y X Z0 HY). congruence. }
    assert (Hmm : substitute_link Y X m = m).
    { unfold substitute_link. destruct (m =? X) eqn:E;
      [ apply eqb_eq in E; congruence | reflexivity ]. }
    eapply edge_eq_trans.
    + apply (IHam Z0 m); [ exact Ha | exact Hmm ].
    + apply (IHmb m W0); [ exact Hmm | exact Hb ].
Qed.

Lemma edge_eq_collapse : forall X Y c Z W,
  Y <> X ->
  (edge_eq ((X, Y) :: c) Z W
   <-> edge_eq (map (subst_conn Y X) c)
               (substitute_link Y X Z) (substitute_link Y X W)).
Proof.
  intros X Y c Z W HY. split.
  - apply edge_eq_collapse_fwd; auto.
  - intros H. apply (edge_eq_collapse_bwd X Y c _ _ HY H); reflexivity.
Qed.

Lemma giso_iface_ext : forall I1 I2 t1 t2,
  (forall X, In X I1 <-> In X I2) ->
  giso I1 t1 t2 -> giso I2 t1 t2.
Proof.
  intros I1 I2 t1 t2 Hi
    (f & g & Hgf & Hfg & Hdom & Hcod & Hfun & Hconn & Hifc & Hff).
  exists f, g.
  split; [ exact Hgf | split; [ exact Hfg | split; [ exact Hdom |
    split; [ exact Hcod | split; [ exact Hfun | split; [ exact Hconn |
    split ]]]]]].
  - intros i k Z Xik Yik HZ. apply Hifc. apply Hi. exact HZ.
  - intros Z W HZ HW. apply Hff; apply Hi; assumption.
Qed.

Lemma giso_eq : forall I t1 t2,
  node_atoms t1 = node_atoms t2 ->
  term_conns t1 = term_conns t2 ->
  giso I t1 t2.
Proof.
  intros I t1 t2 Hn Hc.
  exists (fun i => i), (fun i => i).
  split; [ auto | split; [ auto |]].
  split; [ intros; rewrite <- Hn; auto | ].
  split; [ intros; rewrite Hn; auto | ].
  split; [ intros; rewrite Hn; auto | ].
  split; [ | split ].
  - intros i k j l Xik Xjl Yik Yjl H1 H2 H3 H4.
    rewrite <- Hn in H3, H4. rewrite H1 in H3. rewrite H2 in H4.
    injection H3 as ->. injection H4 as ->. rewrite Hc. reflexivity.
  - intros i k Z Xik Yik HZ H1 H2.
    rewrite <- Hn in H2. rewrite H1 in H2. injection H2 as ->.
    rewrite Hc. reflexivity.
  - intros Z W HZ HW. rewrite Hc. reflexivity.
Qed.

Lemma giso_trivial : forall I t1 t2,
  node_atoms t1 = [] -> node_atoms t2 = [] -> I = [] ->
  giso I t1 t2.
Proof.
  intros I t1 t2 H1 H2 HI. subst I.
  exists (fun i => i), (fun i => i).
  split; [ auto | split; [ auto |]].
  split; [ rewrite H1; cbn; intros i Hi; lia | ].
  split; [ rewrite H2; cbn; intros i Hi; lia | ].
  split; [ intros i; rewrite H1, H2; reflexivity | ].
  split; [ | split ].
  - intros i k j l Xik Xjl Yik Yjl HH. unfold portlink in HH.
    rewrite H1 in HH. destruct i; discriminate.
  - intros i k Z Xik Yik [].
  - intros Z W [].
Qed.

Lemma congm_freelinks : forall P Q, P ==m Q ->
  forall X, In X (freelinks P) <-> In X (freelinks Q).
Proof.
  intros P Q H X. rewrite !in_freelinks. apply congm_mult1_iff, H.
Qed.

Lemma get_functor_map_atom : forall fl a,
  get_functor (map_atom fl a) = get_functor a.
Proof. intros fl [p ls|x y]; simpl; [ rewrite length_map | ]; reflexivity. Qed.

Lemma portlink_map : forall fl ns i k,
  portlink (map (map_atom fl) ns) i k = option_map fl (portlink ns i k).
Proof.
  intros fl ns i k. unfold portlink.
  rewrite nth_error_map.
  destruct (nth_error ns i) as [[p ls|x y]|]; simpl; auto.
  rewrite nth_error_map. reflexivity.
Qed.

(* --- shape lemmas for the (E9) case --- *)

Lemma term_conns_E9_lhs : forall X Y (A : Atom),
  term_conns (TMol (TAtom (AConn X Y)) (TAtom A))
  = (X, Y) :: term_conns (TAtom A).
Proof. intros. rewrite term_conns_mol. reflexivity. Qed.

Lemma node_atoms_E9_lhs : forall X Y (A : Atom),
  node_atoms (TMol (TAtom (AConn X Y)) (TAtom A)) = node_atoms (TAtom A).
Proof. intros. rewrite node_atoms_mol. reflexivity. Qed.

Lemma term_conns_subst_atom : forall Y X (A : Atom),
  term_conns (substitute Y X (TAtom A))
  = map (subst_conn Y X) (term_conns (TAtom A)).
Proof.
  intros Y X [p ls|u v]; reflexivity.
Qed.

Lemma node_atoms_subst_atom : forall Y X (A : Atom),
  node_atoms (substitute Y X (TAtom A))
  = map (map_atom (substitute_link Y X)) (node_atoms (TAtom A)).
Proof.
  intros Y X [p ls|u v]; reflexivity.
Qed.

Lemma giso_trans : forall I t1 t2 t3,
  giso I t1 t2 -> giso I t2 t3 -> giso I t1 t3.
Proof.
  intros I t1 t2 t3
    (f1 & g1 & Hgf1 & Hfg1 & Hdom1 & Hcod1 & Hfun1 & Hconn1 & Hifc1 & Hff1)
    (f2 & g2 & Hgf2 & Hfg2 & Hdom2 & Hcod2 & Hfun2 & Hconn2 & Hifc2 & Hff2).
  exists (fun i => f2 (f1 i)), (fun i => g1 (g2 i)).
  split; [ intros i; rewrite Hgf2, Hgf1; reflexivity |].
  split; [ intros i; rewrite Hfg1, Hfg2; reflexivity |].
  split; [ intros i Hi; apply Hdom2, Hdom1, Hi |].
  split; [ intros j Hj; apply Hcod1, Hcod2, Hj |].
  split.
  - intros i. rewrite Hfun1. apply Hfun2.
  - split.
    + intros i k j l Xik Xjl Yik Yjl H1 H2 H3 H4.
      destruct (giso_port_mid f1 t1 t2 i k Xik Hfun1 H1) as [Mik HMik].
      destruct (giso_port_mid f1 t1 t2 j l Xjl Hfun1 H2) as [Mjl HMjl].
      eapply iff_trans.
      * apply (Hconn1 i k j l Xik Xjl Mik Mjl); auto.
      * apply (Hconn2 (f1 i) k (f1 j) l Mik Mjl Yik Yjl); auto.
    + split.
      * intros i k Z Xik Yik HZ H1 H2.
        destruct (giso_port_mid f1 t1 t2 i k Xik Hfun1 H1) as [Mik HMik].
        eapply iff_trans.
        -- apply (Hifc1 i k Z Xik Mik); auto.
        -- apply (Hifc2 (f1 i) k Z Mik Yik); auto.
      * intros Z W HZ HW.
        eapply iff_trans; [ apply Hff1 | apply Hff2 ]; auto.
Qed.

(* --- (E5) : gluing two subgraphs along a shared free interface --- *)

(* an explicit fuel-indexed path (fuel = number of steps) *)
Inductive epathn (R : Link -> Link -> Prop) : nat -> Link -> Link -> Prop :=
  | epathn_nil  : forall x, epathn R 0 x x
  | epathn_cons : forall n x y z, R x y -> epathn R n y z -> epathn R (S n) x z.

Lemma epathn_trans : forall R m n x y z,
  epathn R m x y -> epathn R n y z -> epathn R (m + n) x z.
Proof.
  intros R m n x y z p. revert n z. induction p; intros k w q; simpl; auto.
  econstructor; eauto.
Qed.

Lemma epathn_sym : forall (R : Link -> Link -> Prop),
  (forall a b, R a b -> R b a) ->
  forall n x z, epathn R n x z -> exists m, epathn R m z x.
Proof.
  intros R Hsym n x z p. induction p.
  - exists 0. constructor.
  - destruct IHp as [m Hm].
    exists (m + 1). eapply epathn_trans; [ exact Hm |].
    apply epathn_cons with x; [ apply Hsym; auto | constructor ].
Qed.

Definition link_ends (c : list (Link * Link)) : list Link :=
  flat_map (fun p => [fst p; snd p]) c.

Lemma link_ends_term_conns : forall t z,
  In z (link_ends (term_conns t)) -> In z (links t).
Proof.
  intros t z Hin. rewrite links_flatten.
  unfold link_ends, term_conns in *.
  rewrite in_flat_map in *. destruct Hin as [[x y] [Hp Hmem]].
  rewrite in_flat_map in Hp. destruct Hp as [a [Ha Hpa]].
  destruct a as [p ls|u v]; simpl in Hpa; try contradiction.
  destruct Hpa as [E|[]]. injection E as Eu Ev. subst x y.
  exists (AConn u v). split; [ exact Ha |].
  simpl. simpl in Hmem. exact Hmem.
Qed.

Lemma edge_eq_ends : forall c x y,
  edge_eq c x y -> x = y \/ (In x (link_ends c) /\ In y (link_ends c)).
Proof.
  intros c x y H.
  destruct (edge_eq_endpoints c x y H) as [->|[H1 H2]]; auto.
Qed.

Lemma portlink_In_links : forall t i k z,
  portlink (node_atoms t) i k = Some z -> In z (links t).
Proof.
  intros t i k z H. unfold portlink in H.
  destruct (nth_error (node_atoms t) i) as [[p ls|u v]|] eqn:E; try discriminate.
  apply nth_error_In in E. unfold node_atoms in E.
  apply filter_In in E. destruct E as [Ein _].
  rewrite links_flatten. rewrite in_flat_map.
  exists (AAtom p ls). split; [ exact Ein |].
  simpl. apply nth_error_In in H. exact H.
Qed.

Lemma in_freelinks_In_links : forall t z,
  In z (freelinks t) -> In z (links t).
Proof.
  intros t z H. rewrite in_freelinks in H.
  apply in_links_link_multiset. rewrite H. auto.
Qed.

Lemma edge_eq_app_epathn : forall cP cQ x y,
  edge_eq (cP ++ cQ) x y ->
  exists n, epathn (fun a b => edge_eq cP a b \/ edge_eq cQ a b) n x y.
Proof.
  intros cP cQ x y H. induction H.
  - exists 1. eapply epathn_cons; [ | apply epathn_nil ].
    apply in_app_or in H. destruct H as [Hin|Hin];
    [ left | right ]; apply edge_eq_step; exact Hin.
  - exists 0. constructor.
  - destruct IHclos_refl_sym_trans as [n Hn].
    apply epathn_sym in Hn; [ exact Hn |].
    intros a b [Hb|Hb]; [ left | right ]; apply edge_eq_sym; exact Hb.
  - destruct IHclos_refl_sym_trans1 as [m Hm].
    destruct IHclos_refl_sym_trans2 as [n Hn].
    exists (m + n). eapply epathn_trans; eauto.
Qed.

Lemma epathn_edge_eq_app : forall cP cQ n x y,
  epathn (fun a b => edge_eq cP a b \/ edge_eq cQ a b) n x y ->
  edge_eq (cP ++ cQ) x y.
Proof.
  intros cP cQ n x y H. induction H.
  - apply edge_eq_refl.
  - eapply edge_eq_trans; [ | exact IHepathn ].
    destruct H as [Hs|Hs];
    [ apply (edge_eq_incl cP) | apply (edge_eq_incl cQ) ]; auto;
    intros p Hp; apply in_or_app; auto.
Qed.

Definition Pobs (P : Term) (a : Link) : Prop :=
  (exists i k, portlink (node_atoms P) i k = Some a) \/ In a (freelinks P).

Lemma Pobs_In_links : forall P a, Pobs P a -> In a (links P).
Proof.
  intros P a [[i [k Hp]]|Hf].
  - eapply portlink_In_links; eauto.
  - apply in_freelinks_In_links; auto.
Qed.

Lemma edge_eq_end_links : forall t x y,
  edge_eq (term_conns t) x y -> x = y \/ (In x (links t) /\ In y (links t)).
Proof.
  intros t x y H. destruct (edge_eq_ends _ _ _ H) as [->|[H1 H2]]; auto.
  right. split; apply link_ends_term_conns; auto.
Qed.

Lemma shared_links_are_free : forall P Q X,
  wellformed_t (TMol P Q) ->
  In X (links P) -> In X (links Q) ->
  In X (freelinks P) /\ In X (freelinks Q).
Proof.
  intros P Q X WF H1 H2.
  apply in_links_link_multiset in H1, H2.
  assert (Hle := wellformed_t_mult_le (TMol P Q) X WF).
  rewrite multiplicity_mol in Hle.
  rewrite !in_freelinks. lia.
Qed.

Lemma glue_fwd : forall P Q,
  wellformed_t (TMol P Q) ->
  forall n x z,
    epathn (fun a b => edge_eq (term_conns P) a b \/ edge_eq (term_conns Q) a b) n x z ->
    (Pobs P x \/ Pobs Q x) -> (Pobs P z \/ Pobs Q z) ->
    clos_refl_sym_trans Link
      (fun a b => (Pobs P a /\ Pobs P b /\ edge_eq (term_conns P) a b)
               \/ (Pobs Q a /\ Pobs Q b /\ edge_eq (term_conns Q) a b))
      x z.
Proof.
  intros P Q WFPQ.
  set (cP := term_conns P). set (cQ := term_conns Q).
  set (Rglue := fun a b => (Pobs P a /\ Pobs P b /\ edge_eq cP a b)
                        \/ (Pobs Q a /\ Pobs Q b /\ edge_eq cQ a b)).
  assert (Hshared : forall z, In z (links P) -> In z (links Q) ->
                    In z (freelinks P) /\ In z (freelinks Q)).
  { intros w H1 H2. apply (shared_links_are_free P Q w WFPQ H1 H2). }
  assert (HtoP : forall w, In w (links P) -> (Pobs P w \/ Pobs Q w) -> Pobs P w).
  { intros w Hl [HP|HQ]; auto.
    right. apply (proj1 (Hshared w Hl (Pobs_In_links Q w HQ))). }
  assert (HtoQ : forall w, In w (links Q) -> (Pobs P w \/ Pobs Q w) -> Pobs Q w).
  { intros w Hl [HP|HQ]; auto.
    right. apply (proj2 (Hshared w (Pobs_In_links P w HP) Hl)). }
  induction n as [|n IHn]; intros x z Hpath Hx Hz.
  - inversion Hpath; subst. apply rst_refl.
  - inversion Hpath as [|n0 x0 y z0 Hxy rest Hn0]; subst.
    destruct (classic (Pobs P y \/ Pobs Q y)) as [Hy | Hny].
    + (* y observable: one Rglue step then IH *)
      apply rst_trans with y.
      * destruct (Leq_dec x y) as [->|Hxney].
        { apply rst_refl. }
        apply rst_step.
        destruct Hxy as [HeP | HeQ].
        { left.
          destruct (edge_eq_end_links P x y HeP) as [E|[HxlP HylP]];
            [ congruence |].
          split; [ apply (HtoP x HxlP Hx)
                 | split; [ apply (HtoP y HylP Hy) | exact HeP ] ]. }
        { right.
          destruct (edge_eq_end_links Q x y HeQ) as [E|[HxlQ HylQ]];
            [ congruence |].
          split; [ apply (HtoQ x HxlQ Hx)
                 | split; [ apply (HtoQ y HylQ Hy) | exact HeQ ] ]. }
      * apply IHn; auto.
    + (* y not observable: absorb it *)
      inversion rest as [|n1 y1 y'' z1 Hyy'' rest'' Hn1]; subst.
      * exfalso. apply Hny. exact Hz.
      * assert (Hcomb : edge_eq cP x y'' \/ edge_eq cQ x y'').
        { destruct Hxy as [HeP1 | HeQ1]; destruct Hyy'' as [HeP2 | HeQ2].
          - left. eapply edge_eq_trans; eauto.
          - (* cP x y, cQ y y'' *)
            destruct (edge_eq_end_links P x y HeP1) as [->|[_ HylP]].
            { exfalso. apply Hny. destruct Hx; auto. }
            destruct (edge_eq_end_links Q y y'' HeQ2) as [Eyy|[HylQ _]].
            { rewrite <- Eyy. left. exact HeP1. }
            exfalso. apply Hny. left. right. apply Hshared; auto.
          - (* cQ x y, cP y y'' *)
            destruct (edge_eq_end_links Q x y HeQ1) as [->|[_ HylQ]].
            { exfalso. apply Hny. destruct Hx; auto. }
            destruct (edge_eq_end_links P y y'' HeP2) as [Eyy|[HylP _]].
            { rewrite <- Eyy. right. exact HeQ1. }
            exfalso. apply Hny. left. right. apply Hshared; auto.
          - right. eapply edge_eq_trans; eauto. }
        apply (IHn x z).
        -- eapply epathn_cons; [ exact Hcomb | exact rest'' ].
        -- exact Hx.
        -- exact Hz.
Qed.

Lemma clos_rst_epathn : forall (R : Link -> Link -> Prop),
  (forall a b, R a b -> R b a) ->
  forall x y,
    clos_refl_sym_trans Link R x y <-> exists n, epathn R n x y.
Proof.
  intros R Hsym x y. split.
  - intros H. induction H.
    + exists 1. eapply epathn_cons; [ exact H | apply epathn_nil ].
    + exists 0. constructor.
    + destruct IHclos_refl_sym_trans as [n Hn].
      apply epathn_sym in Hn; auto.
    + destruct IHclos_refl_sym_trans1 as [m Hm].
      destruct IHclos_refl_sym_trans2 as [n Hn].
      exists (m + n). eapply epathn_trans; eauto.
  - intros [n H]. induction H.
    + apply rst_refl.
    + eapply rst_trans; [ apply rst_step; exact H | exact IHepathn ].
Qed.

Lemma edge_eq_epathn : forall c x y,
  edge_eq c x y <->
  exists n, epathn (fun a b => In (a, b) c \/ In (b, a) c) n x y.
Proof.
  intros c x y. split.
  - intros H. induction H.
    + exists 1. eapply epathn_cons; [ left; eassumption | apply epathn_nil ].
    + exists 0. constructor.
    + destruct IHclos_refl_sym_trans as [n Hn].
      apply epathn_sym in Hn; [ exact Hn | intros a b [Hb|Hb]; auto ].
    + destruct IHclos_refl_sym_trans1 as [m Hm].
      destruct IHclos_refl_sym_trans2 as [n Hn].
      exists (m + n). eapply epathn_trans; eauto.
  - intros [n H]. induction H.
    + apply edge_eq_refl.
    + eapply edge_eq_trans; [ | exact IHepathn ].
      destruct H as [Hs|Hs]; [ apply edge_eq_step | apply edge_eq_step' ]; auto.
Qed.

(* --- (E2) : block-swap isomorphism --- *)

Lemma giso_node_len : forall I t1 t2,
  giso I t1 t2 -> length (node_atoms t1) = length (node_atoms t2).
Proof.
  intros I t1 t2 (f & g & Hgf & Hfg & Hdom & Hcod & _).
  set (n1 := length (node_atoms t1)) in *.
  set (n2 := length (node_atoms t2)) in *.
  assert (Hsq : forall m, length (seq 0 m) = m)
    by (intros; apply length_seq).
  assert (Hmp : forall (h : nat -> nat) m, length (map h (seq 0 m)) = m)
    by (intros; rewrite length_map; apply Hsq).
  assert (H12 : n1 <= n2).
  { rewrite <- (Hmp f n1).
    transitivity (length (seq 0 n2)); [ | rewrite Hsq; reflexivity ].
    apply NoDup_incl_length.
    - apply NoDup_map_NoDup_ForallPairs; [ | apply seq_NoDup ].
      intros a b _ _ Hab. rewrite <- (Hgf a), <- (Hgf b), Hab. reflexivity.
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as [i [<- Hi]].
      apply in_seq in Hi. apply in_seq. split; [ lia |].
      simpl. apply Hdom. lia. }
  assert (H21 : n2 <= n1).
  { rewrite <- (Hmp g n2).
    transitivity (length (seq 0 n1)); [ | rewrite Hsq; reflexivity ].
    apply NoDup_incl_length.
    - apply NoDup_map_NoDup_ForallPairs; [ | apply seq_NoDup ].
      intros a b _ _ Hab. rewrite <- (Hfg a), <- (Hfg b), Hab. reflexivity.
    - intros x Hx. apply in_map_iff in Hx. destruct Hx as [j [<- Hj]].
      apply in_seq in Hj. apply in_seq. split; [ lia |].
      simpl. apply Hcod. lia. }
  lia.
Qed.

(* --- (E5) : transferring the glued relation across the node iso --- *)

Definition simP (f : nat -> nat) (P P' : Term) (a a' : Link) : Prop :=
  (In a (freelinks P) /\ a' = a)
  \/ (~ Pobs P a /\ a' = a)
  \/ (exists i k, portlink (node_atoms P) i k = Some a
              /\ portlink (node_atoms P') (f i) k = Some a').

Lemma simP_refl_free_or_notP : forall f P P' a,
  (In a (freelinks P) \/ ~ Pobs P a) -> simP f P P' a a.
Proof.
  intros f P P' a [H|H]; [ left | right; left ]; auto.
Qed.

Lemma simP_Qobs : forall f P P' Q a,
  wellformed_t (TMol P Q) -> Pobs Q a -> simP f P P' a a.
Proof.
  intros f P P' Q a WF HQ.
  destruct (classic (Pobs P a)) as [HP|HP].
  - apply simP_refl_free_or_notP. left.
    apply (proj1 (shared_links_are_free P Q a WF
                    (Pobs_In_links P a HP) (Pobs_In_links Q a HQ))).
  - apply simP_refl_free_or_notP. right. exact HP.
Qed.

Lemma edge_eq_appl : forall c1 c2 x y,
  edge_eq c1 x y -> edge_eq (c1 ++ c2) x y.
Proof.
  intros c1 c2 x y. apply edge_eq_incl. intros p Hp. apply in_or_app. auto.
Qed.

Lemma edge_eq_appr : forall c1 c2 x y,
  edge_eq c2 x y -> edge_eq (c1 ++ c2) x y.
Proof.
  intros c1 c2 x y. apply edge_eq_incl. intros p Hp. apply in_or_app. auto.
Qed.

(* the IH clauses of  giso (freelinks P) P P',  packaged *)
Definition giso_clauses (f : nat -> nat) (P P' : Term) : Prop :=
  (forall X, In X (freelinks P) <-> In X (freelinks P'))
  /\ (forall i, option_map get_functor (nth_error (node_atoms P) i)
             = option_map get_functor (nth_error (node_atoms P') (f i)))
  /\ (forall i k j l Xik Xjl Yik Yjl,
        portlink (node_atoms P) i k = Some Xik ->
        portlink (node_atoms P) j l = Some Xjl ->
        portlink (node_atoms P') (f i) k = Some Yik ->
        portlink (node_atoms P') (f j) l = Some Yjl ->
        (edge_eq (term_conns P) Xik Xjl <-> edge_eq (term_conns P') Yik Yjl))
  /\ (forall i k Z Xik Yik,
        In Z (freelinks P) ->
        portlink (node_atoms P) i k = Some Xik ->
        portlink (node_atoms P') (f i) k = Some Yik ->
        (edge_eq (term_conns P) Xik Z <-> edge_eq (term_conns P') Yik Z))
  /\ (forall Z W, In Z (freelinks P) -> In W (freelinks P) ->
        (edge_eq (term_conns P) Z W <-> edge_eq (term_conns P') Z W)).

Lemma sim_consist : forall f P P' Q,
  wellformed_t (TMol P Q) ->
  giso_clauses f P P' ->
  forall w w1 w2,
    (Pobs P w \/ Pobs Q w) ->
    simP f P P' w w1 -> simP f P P' w w2 ->
    edge_eq (term_conns P' ++ term_conns Q) w1 w2.
Proof.
  intros f P P' Q WF (Hfl & Hfun & Hconn & Hifc & Hff) w w1 w2 Hw Hs1 Hs2.
  assert (Hnp : forall a, In a (freelinks P) -> Pobs P a)
    by (intros a Ha; right; exact Ha).
  destruct Hs1 as [[Hf1 E1]|[[Hnp1 E1]|[i [k [Hpi Hpi']]]]];
  destruct Hs2 as [[Hf2 E2]|[[Hnp2 E2]|[j [l [Hpj Hpj']]]]];
  subst.
  - apply edge_eq_refl.
  - exfalso. exact (Hnp2 (Hnp w Hf1)).
  - apply edge_eq_sym, edge_eq_appl.
    apply (proj1 (Hifc j l w w w2 Hf1 Hpj Hpj')), edge_eq_refl.
  - exfalso. exact (Hnp1 (Hnp w Hf2)).
  - apply edge_eq_refl.
  - exfalso. apply (Hnp1 (or_introl (ex_intro _ j (ex_intro _ l Hpj)))).
  - apply edge_eq_appl.
    apply (proj1 (Hifc i k w w w1 Hf2 Hpi Hpi')), edge_eq_refl.
  - exfalso. apply (Hnp2 (or_introl (ex_intro _ i (ex_intro _ k Hpi)))).
  - apply edge_eq_appl.
    apply (proj1 (Hconn i k j l w w w1 w2 Hpi Hpj Hpi' Hpj')), edge_eq_refl.
Qed.

Lemma simP_total : forall f P P' Q a,
  wellformed_t (TMol P Q) ->
  (forall i, option_map get_functor (nth_error (node_atoms P) i)
           = option_map get_functor (nth_error (node_atoms P') (f i))) ->
  (Pobs P a \/ Pobs Q a) ->
  exists a', simP f P P' a a'.
Proof.
  intros f P P' Q a WF Hfun Ha.
  destruct (classic (In a (freelinks P))) as [Hf|Hf].
  { exists a. left. auto. }
  destruct (classic (Pobs P a)) as [HP|HP].
  - destruct HP as [[i [k Hp]]|Hcontra]; [ | contradiction ].
    destruct (giso_port_mid f P P' i k a Hfun Hp) as [a' Ha'].
    exists a'. right. right. exists i, k. auto.
  - exists a. right. left. auto.
Qed.

Lemma simP_Q_edge : forall f P P' Q,
  wellformed_t (TMol P Q) ->
  giso_clauses f P P' ->
  forall x x', Pobs Q x -> simP f P P' x x' ->
    edge_eq (term_conns P' ++ term_conns Q) x' x.
Proof.
  intros f P P' Q WF (Hfl & Hfun & Hconn & Hifc & Hff) x x' HQ Hs.
  destruct Hs as [[Hf ->]|[[Hnp ->]|[i [k [Hpi Hpi']]]]].
  - apply edge_eq_refl.
  - apply edge_eq_refl.
  - assert (HxP : In x (links P)) by (eapply portlink_In_links; eauto).
    assert (HxQ : In x (links Q)) by (apply Pobs_In_links; auto).
    assert (Hfx : In x (freelinks P))
      by (apply (proj1 (shared_links_are_free P Q x WF HxP HxQ))).
    apply edge_eq_appl.
    apply (proj1 (Hifc i k x x x' Hfx Hpi Hpi')), edge_eq_refl.
Qed.

Lemma step_transfer : forall f P P' Q,
  wellformed_t (TMol P Q) ->
  giso_clauses f P P' ->
  forall x y x' y',
    ((Pobs P x /\ Pobs P y /\ edge_eq (term_conns P) x y)
     \/ (Pobs Q x /\ Pobs Q y /\ edge_eq (term_conns Q) x y)) ->
    simP f P P' x x' -> simP f P P' y y' ->
    edge_eq (term_conns P' ++ term_conns Q) x' y'.
Proof.
  intros f P P' Q WF Hcl x y x' y' Hstep Hsx Hsy.
  assert (Hcl' := Hcl). destruct Hcl' as (Hfl & Hfun & Hconn & Hifc & Hff).
  destruct Hstep as [[HPx [HPy HeP]]|[HQx [HQy HeQ]]].
  - (* P-step *)
    destruct Hsx as [[Hfx ->]|[[Hnx ->]|[i [k [Hpi Hpi']]]]].
    + destruct Hsy as [[Hfy ->]|[[Hny ->]|[j [l [Hpj Hpj']]]]].
      * apply edge_eq_appl.
        apply (proj1 (Hff x y Hfx Hfy)), HeP.
      * exfalso. exact (Hny HPy).
      * apply edge_eq_appl, edge_eq_sym.
        apply (proj1 (Hifc j l x y y' Hfx Hpj Hpj')), edge_eq_sym, HeP.
    + exfalso. exact (Hnx HPx).
    + destruct Hsy as [[Hfy ->]|[[Hny ->]|[j [l [Hpj Hpj']]]]].
      * apply edge_eq_appl.
        apply (proj1 (Hifc i k y x x' Hfy Hpi Hpi')), HeP.
      * exfalso. exact (Hny HPy).
      * apply edge_eq_appl.
        apply (proj1 (Hconn i k j l x y x' y' Hpi Hpj Hpi' Hpj')), HeP.
  - (* Q-step *)
    apply edge_eq_trans with x.
    { apply (simP_Q_edge f P P' Q WF Hcl x x' HQx Hsx). }
    apply edge_eq_trans with y.
    { apply edge_eq_appr, HeQ. }
    apply edge_eq_sym.
    apply (simP_Q_edge f P P' Q WF Hcl y y' HQy Hsy).
Qed.

Lemma glue_transfer : forall f P P' Q,
  wellformed_t (TMol P Q) ->
  giso_clauses f P P' ->
  forall n x z,
    epathn (fun a b =>
              (Pobs P a /\ Pobs P b /\ edge_eq (term_conns P) a b)
           \/ (Pobs Q a /\ Pobs Q b /\ edge_eq (term_conns Q) a b)) n x z ->
    (Pobs P x \/ Pobs Q x) -> (Pobs P z \/ Pobs Q z) ->
    forall x' z', simP f P P' x x' -> simP f P P' z z' ->
    edge_eq (term_conns P' ++ term_conns Q) x' z'.
Proof.
  intros f P P' Q WF Hcl.
  assert (Hfun : forall i, option_map get_functor (nth_error (node_atoms P) i)
              = option_map get_functor (nth_error (node_atoms P') (f i)))
    by (destruct Hcl as (_ & Hfun & _); exact Hfun).
  induction n as [|n IHn]; intros x z Hpath Hx Hz x' z' Hsx Hsz.
  - assert (Hxz : x = z) by (inversion Hpath; congruence).
    subst z.
    apply (sim_consist f P P' Q WF Hcl x x' z' Hx Hsx Hsz).
  - inversion Hpath as [|n0 x0 y z0 Hstep rest Heqn]; subst.
    assert (Hy : Pobs P y \/ Pobs Q y).
    { destruct Hstep as [[_ [Hy _]]|[_ [Hy _]]]; auto. }
    destruct (simP_total f P P' Q y WF Hfun Hy) as [y' Hsy].
    apply edge_eq_trans with y'.
    + apply (step_transfer f P P' Q WF Hcl x y x' y' Hstep Hsx Hsy).
    + apply (IHn y z rest Hy Hz y' z' Hsy Hsz).
Qed.

Lemma Rglue_sym : forall P Q u v,
  (fun a b => (Pobs P a /\ Pobs P b /\ edge_eq (term_conns P) a b)
           \/ (Pobs Q a /\ Pobs Q b /\ edge_eq (term_conns Q) a b)) u v ->
  (fun a b => (Pobs P a /\ Pobs P b /\ edge_eq (term_conns P) a b)
           \/ (Pobs Q a /\ Pobs Q b /\ edge_eq (term_conns Q) a b)) v u.
Proof.
  intros P Q u v [[H1 [H2 H3]]|[H1 [H2 H3]]];
  [ left | right ]; repeat split; auto using edge_eq_sym.
Qed.

Lemma E5_edge_iff : forall f g P P' Q,
  wellformed_t (TMol P Q) -> wellformed_t (TMol P' Q) ->
  giso_clauses f P P' -> giso_clauses g P' P ->
  forall a b a' b',
    (Pobs P a \/ Pobs Q a) -> (Pobs P b \/ Pobs Q b) ->
    (Pobs P' a' \/ Pobs Q a') -> (Pobs P' b' \/ Pobs Q b') ->
    simP f P P' a a' -> simP f P P' b b' ->
    simP g P' P a' a -> simP g P' P b' b ->
    (edge_eq (term_conns P ++ term_conns Q) a b
     <-> edge_eq (term_conns P' ++ term_conns Q) a' b').
Proof.
  intros f g P P' Q WF WF' Hcl Hcl' a b a' b'
         HaP HbP HaP' HbP' Hs1 Hs2 Hs1' Hs2'.
  split; intros He.
  - apply edge_eq_app_epathn in He. destruct He as [n Hn].
    assert (Hg := glue_fwd P Q WF n a b Hn HaP HbP).
    apply (clos_rst_epathn _ (Rglue_sym P Q)) in Hg.
    destruct Hg as [m Hm].
    apply (glue_transfer f P P' Q WF Hcl m a b Hm HaP HbP a' b' Hs1 Hs2).
  - apply edge_eq_app_epathn in He. destruct He as [n Hn].
    assert (Hg := glue_fwd P' Q WF' n a' b' Hn HaP' HbP').
    apply (clos_rst_epathn _ (Rglue_sym P' Q)) in Hg.
    destruct Hg as [m Hm].
    apply (glue_transfer g P' P Q WF' Hcl' m a' b' Hm HaP' HbP' a b Hs1' Hs2').
Qed.

Lemma giso_clauses_sym : forall f g P P',
  (forall i, g (f i) = i) -> (forall i, f (g i) = i) ->
  giso_clauses f P P' -> giso_clauses g P' P.
Proof.
  intros f g P P' Hgf Hfg (Hfl & Hfun & Hconn & Hifc & Hff).
  split; [ | split; [ | split; [ | split ]]].
  - intros X. split; [ apply (proj2 (Hfl X)) | apply (proj1 (Hfl X)) ].
  - intros j. specialize (Hfun (g j)). rewrite Hfg in Hfun. symmetry. exact Hfun.
  - intros i k j l Xik Xjl Yik Yjl H1 H2 H3 H4.
    specialize (Hconn (g i) k (g j) l Yik Yjl Xik Xjl H3 H4).
    rewrite !Hfg in Hconn. apply iff_sym. exact (Hconn H1 H2).
  - intros i k Z Xik Yik HZ H1 H2.
    apply (proj2 (Hfl Z)) in HZ.
    specialize (Hifc (g i) k Z Yik Xik HZ H2).
    rewrite Hfg in Hifc. apply iff_sym. exact (Hifc H1).
  - intros Z W HZ HW.
    apply (proj2 (Hfl Z)) in HZ. apply (proj2 (Hfl W)) in HW.
    apply iff_sym. exact (Hff Z W HZ HW).
Qed.

Lemma portlink_app : forall ns1 ns2 i k,
  portlink (ns1 ++ ns2) i k =
  (if Nat.ltb i (length ns1) then portlink ns1 i k
   else portlink ns2 (i - length ns1) k).
Proof.
  intros ns1 ns2 i k. unfold portlink.
  destruct (Nat.ltb i (length ns1)) eqn:E.
  - apply PeanoNat.Nat.ltb_lt in E. rewrite nth_error_app1 by auto. reflexivity.
  - apply PeanoNat.Nat.ltb_ge in E. rewrite nth_error_app2 by auto. reflexivity.
Qed.

Lemma simP_free_mol : forall f g P P' Q Z,
  wellformed_t (TMol P Q) -> wellformed_t (TMol P' Q) ->
  (forall X, In X (freelinks P) <-> In X (freelinks P')) ->
  In Z (freelinks (TMol P Q)) ->
  simP f P P' Z Z /\ simP g P' P Z Z
  /\ (Pobs P Z \/ Pobs Q Z) /\ (Pobs P' Z \/ Pobs Q Z).
Proof.
  intros f g P P' Q Z WF WF' Hfl HZ.
  apply in_freelinks_mol in HZ.
  destruct HZ as [[HfP HnQ]|[HfQ HnP]].
  - assert (HfP' : In Z (freelinks P')) by (apply Hfl; auto).
    split; [ left; split; [ exact HfP | reflexivity ] |].
    split; [ left; split; [ exact HfP' | reflexivity ] |].
    split; [ left; right; exact HfP | left; right; exact HfP' ].
  - assert (HnP' : ~ In Z (links P')).
    { intro Hin. apply HnP, in_freelinks_In_links, Hfl.
      apply (proj1 (shared_links_are_free P' Q Z WF' Hin
                     (in_freelinks_In_links Q Z HfQ))). }
    assert (HnpP : ~ Pobs P Z) by (intro H; apply HnP, Pobs_In_links, H).
    assert (HnpP' : ~ Pobs P' Z) by (intro H; apply HnP', Pobs_In_links, H).
    split; [ right; left; split; [ exact HnpP | reflexivity ] |].
    split; [ right; left; split; [ exact HnpP' | reflexivity ] |].
    split; [ right; right; exact HfQ | right; right; exact HfQ ].
Qed.

Definition fext (np : nat) (h : nat -> nat) (i : nat) : nat :=
  if Nat.ltb i np then h i else i.

Lemma fext_lo : forall np h i, i < np -> fext np h i = h i.
Proof. intros np h i H. unfold fext. rewrite (proj2 (PeanoNat.Nat.ltb_lt _ _) H). reflexivity. Qed.

Lemma fext_hi : forall np h i, np <= i -> fext np h i = i.
Proof. intros np h i H. unfold fext. rewrite (proj2 (PeanoNat.Nat.ltb_ge _ _) H). reflexivity. Qed.

Lemma fext_fext : forall np f g,
  (forall i, g (f i) = i) -> (forall i, i < np -> f i < np) ->
  forall i, fext np g (fext np f i) = i.
Proof.
  intros np f g Hgf Hdom i.
  destruct (Compare_dec.le_lt_dec np i) as [Hge|Hlt].
  - rewrite (fext_hi _ _ _ Hge), (fext_hi _ _ _ Hge). reflexivity.
  - rewrite (fext_lo _ _ _ Hlt), (fext_lo _ _ _ (Hdom i Hlt)). apply Hgf.
Qed.

Lemma fext_bound : forall np m f i,
  (forall j, j < np -> f j < np) -> i < np + m -> fext np f i < np + m.
Proof.
  intros np m f i Hd Hi.
  destruct (Compare_dec.le_lt_dec np i) as [Hge|Hlt].
  - rewrite (fext_hi _ _ _ Hge). exact Hi.
  - rewrite (fext_lo _ _ _ Hlt). specialize (Hd i Hlt). lia.
Qed.

Definition bswap (a b i : nat) : nat :=
  if Nat.ltb i a then i + b else if Nat.ltb i (a + b) then i - a else i.

Lemma nth_error_None_ge : forall {A} (l : list A) i,
  length l <= i -> nth_error l i = None.
Proof. intros. apply nth_error_None. auto. Qed.

Lemma bswap_bswap : forall a b i, bswap b a (bswap a b i) = i.
Proof.
  intros a b i. unfold bswap.
  destruct (Nat.ltb i a) eqn:E1.
  - apply PeanoNat.Nat.ltb_lt in E1.
    destruct (Nat.ltb (i + b) b) eqn:E2; [ apply PeanoNat.Nat.ltb_lt in E2; lia |].
    destruct (Nat.ltb (i + b) (b + a)) eqn:E3; [ lia |].
    apply PeanoNat.Nat.ltb_ge in E3. lia.
  - apply PeanoNat.Nat.ltb_ge in E1.
    destruct (Nat.ltb i (a + b)) eqn:E2.
    + apply PeanoNat.Nat.ltb_lt in E2.
      destruct (Nat.ltb (i - a) b) eqn:E3; [ lia |].
      apply PeanoNat.Nat.ltb_ge in E3. lia.
    + apply PeanoNat.Nat.ltb_ge in E2.
      destruct (Nat.ltb i b) eqn:E3; [ apply PeanoNat.Nat.ltb_lt in E3; lia |].
      destruct (Nat.ltb i (b + a)) eqn:E4;
        [ apply PeanoNat.Nat.ltb_lt in E4; lia | reflexivity ].
Qed.

Lemma bswap_lt : forall a b i, i < a + b -> bswap a b i < a + b.
Proof.
  intros a b i Hi. unfold bswap.
  destruct (Nat.ltb i a) eqn:E1; [ apply PeanoNat.Nat.ltb_lt in E1; lia |].
  apply PeanoNat.Nat.ltb_ge in E1.
  destruct (Nat.ltb i (a + b)) eqn:E2; [ apply PeanoNat.Nat.ltb_lt in E2; lia |].
  apply PeanoNat.Nat.ltb_ge in E2. lia.
Qed.

Lemma nth_error_bswap : forall {A} (l1 l2 : list A) i,
  nth_error (l1 ++ l2) i
  = nth_error (l2 ++ l1) (bswap (length l1) (length l2) i).
Proof.
  intros A l1 l2 i. unfold bswap.
  destruct (Nat.ltb i (length l1)) eqn:E1.
  - apply PeanoNat.Nat.ltb_lt in E1.
    rewrite nth_error_app1 by exact E1.
    rewrite nth_error_app2 by lia.
    f_equal. lia.
  - apply PeanoNat.Nat.ltb_ge in E1.
    destruct (Nat.ltb i (length l1 + length l2)) eqn:E2.
    + apply PeanoNat.Nat.ltb_lt in E2.
      rewrite nth_error_app2 by exact E1.
      rewrite nth_error_app1 by lia.
      reflexivity.
    + apply PeanoNat.Nat.ltb_ge in E2.
      rewrite nth_error_app2 by lia.
      rewrite nth_error_app2 by lia.
      rewrite !nth_error_None_ge; [ reflexivity | lia | lia ].
Qed.

Lemma giso_app_comm : forall I P Q, giso I (TMol P Q) (TMol Q P).
Proof.
  intros I P Q.
  set (a := length (node_atoms P)).
  set (b := length (node_atoms Q)).
  exists (bswap a b), (bswap b a).
  assert (Hn1 : node_atoms (TMol P Q) = node_atoms P ++ node_atoms Q)
    by apply node_atoms_mol.
  assert (Hn2 : node_atoms (TMol Q P) = node_atoms Q ++ node_atoms P)
    by apply node_atoms_mol.
  assert (Hlen1 : length (node_atoms (TMol P Q)) = a + b)
    by (rewrite Hn1, length_app; reflexivity).
  assert (Hlen2 : length (node_atoms (TMol Q P)) = b + a)
    by (rewrite Hn2, length_app; reflexivity).
  assert (Hnth : forall i,
    nth_error (node_atoms (TMol P Q)) i
    = nth_error (node_atoms (TMol Q P)) (bswap a b i)).
  { intros i. rewrite Hn1, Hn2.
    rewrite (nth_error_bswap (node_atoms P) (node_atoms Q) i).
    reflexivity. }
  assert (Hport : forall i k,
    portlink (node_atoms (TMol P Q)) i k
    = portlink (node_atoms (TMol Q P)) (bswap a b i) k).
  { intros i k. unfold portlink. rewrite Hnth. reflexivity. }
  split; [ intros i; apply bswap_bswap |].
  split; [ intros i; apply bswap_bswap |].
  split; [ intros i Hi; rewrite Hlen1 in Hi; rewrite Hlen2;
           replace (b + a) with (a + b) by lia; apply bswap_lt, Hi |].
  split; [ intros j Hj; rewrite Hlen2 in Hj; rewrite Hlen1;
           replace (a + b) with (b + a) by lia; apply bswap_lt, Hj |].
  split; [ intros i; rewrite Hnth; reflexivity |].
  split.
  - intros i k j l Xik Xjl Yik Yjl HP1 HP2 HP3 HP4.
    rewrite Hport in HP1, HP2. rewrite HP1 in HP3. rewrite HP2 in HP4.
    injection HP3 as ->. injection HP4 as ->.
    rewrite !term_conns_mol.
    apply edge_eq_perm_iff, Permutation_app_comm.
  - split.
    + intros i k Z Xik Yik HZ HP1 HP2.
      rewrite Hport in HP1. rewrite HP1 in HP2. injection HP2 as ->.
      rewrite !term_conns_mol.
      apply edge_eq_perm_iff, Permutation_app_comm.
    + intros Z W HZ HW.
      rewrite !term_conns_mol.
      apply edge_eq_perm_iff, Permutation_app_comm.
Qed.

(* ================================================================== *)
(*  Main theorem :  P ==m Q  ->  giso (freelinks P) P Q               *)
(* ================================================================== *)

Theorem congm_giso : forall P Q, P ==m Q -> giso (freelinks P) P Q.
Proof.
  intros P Q H. induction H.
  - (* E1 : {{TZero, P}} ==m P *)
    apply giso_eq.
    + rewrite node_atoms_mol. reflexivity.
    + rewrite term_conns_mol. reflexivity.
  - (* E2 : {{P, Q}} ==m {{Q, P}} *)
    apply giso_app_comm.
  - (* E3 : {{P, (Q, R)}} ==m {{(P, Q), R}} *)
    apply giso_eq.
    + rewrite !node_atoms_mol, app_assoc. reflexivity.
    + rewrite !term_conns_mol, app_assoc. reflexivity.
  - (* E5 : {{P, Q}} ==m {{P', Q}}  from  P ==m P' *)
    rename H into WFPQ. rename H0 into WFP'Q. rename H1 into HPP'.
    pose proof IHcongm as IHc2.
    destruct IHcongm as
      (f & g & Hgf & Hfg & Hdom & Hcod & Hfun & Hconn & Hifc & Hff).
    assert (Hfleq := congm_freelinks P P' HPP').
    assert (Hcl : giso_clauses f P P').
    { unfold giso_clauses. split; [ exact Hfleq |].
      split; [ exact Hfun |]. split; [ exact Hconn |].
      split; [ exact Hifc | exact Hff ]. }
    assert (Hclg : giso_clauses g P' P)
      by exact (giso_clauses_sym f g P P' Hgf Hfg Hcl).
    assert (Hlen := giso_node_len (freelinks P) P P' IHc2).
    set (np := length (node_atoms P)) in *.
    assert (Hfdom : forall i, i < np -> f i < np).
    { intros i Hi. rewrite Hlen. apply Hdom. exact Hi. }
    assert (Hgdom : forall j, j < np -> g j < np).
    { intros j Hj. apply Hcod. rewrite <- Hlen. exact Hj. }
    assert (HnPQ : node_atoms {{P,Q}} = node_atoms P ++ node_atoms Q)
      by apply node_atoms_mol.
    assert (HnP'Q : node_atoms {{P',Q}} = node_atoms P' ++ node_atoms Q)
      by apply node_atoms_mol.
    assert (HcPQ : term_conns {{P,Q}} = term_conns P ++ term_conns Q)
      by apply term_conns_mol.
    assert (HcP'Q : term_conns {{P',Q}} = term_conns P' ++ term_conns Q)
      by apply term_conns_mol.
    assert (Hlen1 : length (node_atoms {{P,Q}}) = np + length (node_atoms Q))
      by (rewrite HnPQ, length_app; reflexivity).
    assert (Hlen2 : length (node_atoms {{P',Q}}) = np + length (node_atoms Q)).
    { rewrite HnP'Q, length_app. rewrite <- Hlen. reflexivity. }
    assert (Hport : forall i k a b,
      portlink (node_atoms {{P,Q}}) i k = Some a ->
      portlink (node_atoms {{P',Q}}) (fext np f i) k = Some b ->
      simP f P P' a b /\ simP g P' P b a
      /\ (Pobs P a \/ Pobs Q a) /\ (Pobs P' b \/ Pobs Q b)).
    { intros i k a b Ha Hb.
      rewrite HnPQ, portlink_app in Ha.
      rewrite HnP'Q, portlink_app in Hb.
      change (length (node_atoms P)) with np in Ha.
      destruct (Nat.ltb i np) eqn:E.
      - apply PeanoNat.Nat.ltb_lt in E.
        rewrite (fext_lo _ _ _ E) in Hb.
        rewrite (proj2 (PeanoNat.Nat.ltb_lt (f i) (length (node_atoms P')))
                       (eq_ind _ (fun m => f i < m) (Hfdom i E) _ Hlen)) in Hb.
        repeat split.
        + right. right. exists i, k. auto.
        + right. right. exists (f i), k. split; [ exact Hb | rewrite Hgf; exact Ha ].
        + left. left. exists i, k. exact Ha.
        + left. left. exists (f i), k. exact Hb.
      - apply PeanoNat.Nat.ltb_ge in E.
        rewrite (fext_hi _ _ _ E) in Hb.
        rewrite (proj2 (PeanoNat.Nat.ltb_ge i (length (node_atoms P')))
                       (eq_ind _ (fun m => m <= i) E _ Hlen)) in Hb.
        rewrite <- Hlen in Hb. rewrite Ha in Hb. injection Hb as Hab. subst b.
        assert (HQa : Pobs Q a) by (left; exists (i - np), k; exact Ha).
        repeat split.
        + apply (simP_Qobs f P P' Q a WFPQ HQa).
        + apply (simP_Qobs g P' P Q a WFP'Q HQa).
        + right. exact HQa.
        + right. exact HQa. }
    exists (fext np f), (fext np g).
    split; [ apply (fext_fext np f g Hgf Hfdom) |].
    split; [ apply (fext_fext np g f Hfg Hgdom) |].
    split; [ intros i Hi; rewrite Hlen1 in Hi; rewrite Hlen2;
             apply (fext_bound np _ f i Hfdom Hi) |].
    split; [ intros j Hj; rewrite Hlen2 in Hj; rewrite Hlen1;
             apply (fext_bound np _ g j Hgdom Hj) |].
    split.
    { (* gi_funct *)
      intros i. rewrite HnPQ, HnP'Q.
      destruct (Compare_dec.le_lt_dec np i) as [Hge|Hlt].
      - rewrite (fext_hi _ _ _ Hge).
        rewrite nth_error_app2 by exact Hge.
        rewrite nth_error_app2 by (rewrite <- Hlen; exact Hge).
        rewrite <- Hlen. reflexivity.
      - rewrite (fext_lo _ _ _ Hlt).
        rewrite nth_error_app1 by exact Hlt.
        rewrite nth_error_app1 by (rewrite <- Hlen; apply Hfdom; exact Hlt).
        apply Hfun. }
    split.
    { (* gi_conn *)
      intros i k j l Xik Xjl Yik Yjl HP1 HP2 HP3 HP4.
      rewrite HcPQ, HcP'Q.
      destruct (Hport i k Xik Yik HP1 HP3) as (Hs1 & Hs1' & HaP & HaP').
      destruct (Hport j l Xjl Yjl HP2 HP4) as (Hs2 & Hs2' & HbP & HbP').
      exact (E5_edge_iff f g P P' Q WFPQ WFP'Q Hcl Hclg
               Xik Xjl Yik Yjl HaP HbP HaP' HbP' Hs1 Hs2 Hs1' Hs2'). }
    split.
    { (* gi_iface *)
      intros i k Z Xik Yik HZ HP1 HP2.
      rewrite HcPQ, HcP'Q.
      destruct (Hport i k Xik Yik HP1 HP2) as (Hs1 & Hs1' & HaP & HaP').
      destruct (simP_free_mol f g P P' Q Z WFPQ WFP'Q Hfleq HZ)
        as (HsZ & HsZ' & HZP & HZP').
      exact (E5_edge_iff f g P P' Q WFPQ WFP'Q Hcl Hclg
               Xik Z Yik Z HaP HZP HaP' HZP' Hs1 HsZ Hs1' HsZ'). }
    { (* gi_ff *)
      intros Z W HZ HW.
      rewrite HcPQ, HcP'Q.
      destruct (simP_free_mol f g P P' Q Z WFPQ WFP'Q Hfleq HZ)
        as (HsZ & HsZ' & HZP & HZP').
      destruct (simP_free_mol f g P P' Q W WFPQ WFP'Q Hfleq HW)
        as (HsW & HsW' & HWP & HWP').
      exact (E5_edge_iff f g P P' Q WFPQ WFP'Q Hcl Hclg
               Z W Z W HZP HWP HZP' HWP' HsZ HsW HsZ' HsW'). }
  - (* E7 : {{X = X}} ==m TZero *)
    apply giso_trivial.
    + reflexivity.
    + reflexivity.
    + apply nil_iff_forall_not_in. intros Z. rewrite in_freelinks.
      rewrite multiplicity_TAtom_AConn.
      destruct (Leq_dec X Z); simpl; lia.
  - (* E9 : {{X = Y, A}} ==m {{A [Y/X]}} *)
    rename H into WF1. rename H0 into WF2. rename H1 into HXA.
    assert (HYX : Y <> X) by (apply not_eq_sym, (E9_neq X Y A WF1 HXA)).
    assert (HmX : multiplicity (link_multiset (TAtom A)) X = 1)
      by (apply in_freelinks, HXA).
    assert (HXnf : ~ In X (freelinks (TMol (TAtom (AConn X Y)) (TAtom A)))).
    { rewrite in_freelinks, multiplicity_mol, multiplicity_TAtom_AConn, Leq_dec_refl.
      destruct (Leq_dec Y X); [ congruence |]. rewrite HmX. simpl. lia. }
    exists (fun i => i), (fun i => i).
    split; [ auto | split; [ auto |]].
    split; [ rewrite node_atoms_E9_lhs, node_atoms_subst_atom, length_map; cbn; auto |].
    split; [ rewrite node_atoms_E9_lhs, node_atoms_subst_atom, length_map; cbn; auto |].
    split.
    { (* gi_funct *)
      intros i. rewrite node_atoms_E9_lhs.
      rewrite node_atoms_subst_atom, nth_error_map.
      destruct (nth_error (node_atoms (TAtom A)) i) as [a|]; simpl; auto.
      f_equal. symmetry. apply get_functor_map_atom. }
    split.
    { (* gi_conn *)
      intros i k j l Xik Xjl Yik Yjl HP1 HP2 HP3 HP4.
      rewrite node_atoms_E9_lhs in HP1, HP2.
      rewrite node_atoms_subst_atom, portlink_map in HP3, HP4.
      rewrite HP1 in HP3. rewrite HP2 in HP4. simpl in HP3, HP4.
      injection HP3 as HY3. injection HP4 as HY4. subst Yik Yjl.
      rewrite term_conns_E9_lhs, term_conns_subst_atom.
      apply edge_eq_collapse. exact HYX. }
    split.
    { (* gi_iface *)
      intros i k Z Xik Yik HZ HP1 HP2.
      rewrite node_atoms_E9_lhs in HP1.
      rewrite node_atoms_subst_atom, portlink_map in HP2.
      rewrite HP1 in HP2. simpl in HP2. injection HP2 as HY2. subst Yik.
      rewrite term_conns_E9_lhs, term_conns_subst_atom.
      assert (HZX : Z <> X) by (intros ->; apply HXnf; exact HZ).
      assert (HsZ : substitute_link Y X Z = Z)
        by (unfold substitute_link; apply eqb_neq in HZX; rewrite HZX; reflexivity).
      rewrite <- HsZ at 2.
      apply edge_eq_collapse. exact HYX. }
    { (* gi_ff *)
      intros Z W HZ HW.
      rewrite term_conns_E9_lhs, term_conns_subst_atom.
      assert (HZX : Z <> X) by (intros ->; apply HXnf; exact HZ).
      assert (HWX : W <> X) by (intros ->; apply HXnf; exact HW).
      assert (HsZ : substitute_link Y X Z = Z)
        by (unfold substitute_link; apply eqb_neq in HZX; rewrite HZX; reflexivity).
      assert (HsW : substitute_link Y X W = W)
        by (unfold substitute_link; apply eqb_neq in HWX; rewrite HWX; reflexivity).
      rewrite <- HsZ at 2. rewrite <- HsW at 2.
      apply edge_eq_collapse. exact HYX. }
  - (* refl *)
    apply giso_refl.
  - (* trans : P ==m Q, Q ==m R *)
    apply giso_trans with Q; [ exact IHcongm1 |].
    apply giso_iface_ext with (freelinks Q); [ | exact IHcongm2 ].
    intros X. symmetry. apply (congm_freelinks P Q); assumption.
  - (* sym : P ==m Q *)
    apply giso_iface_ext with (freelinks P).
    + intros X. apply (congm_freelinks P Q); assumption.
    + apply giso_sym. exact IHcongm.
Qed.

(* Structural congruence implies interface-preserving graph isomorphism. *)
Corollary cong_giso : forall P Q, P == Q -> giso (freelinks P) P Q.
Proof.
  intros P Q H. apply congm_giso, congm_cong_iff, H.
Qed.

(* ================================================================== *)
(*  Reverse direction (connector-free) :  giso  ->  ==m               *)
(* ================================================================== *)

(* a supply of fresh link names: strings "aa...a" of a chosen length *)
Definition achar : Ascii.ascii :=
  match "a"%string with String c _ => c | EmptyString => Ascii.zero end.
Fixpoint astr (n : nat) : string :=
  match n with 0 => EmptyString | S k => String achar (astr k) end.

Lemma astr_length : forall n, String.length (astr n) = n.
Proof. induction n; simpl; auto. Qed.

Lemma astr_inj : forall m n, astr m = astr n -> m = n.
Proof.
  intros m n H. apply (f_equal String.length) in H. rewrite !astr_length in H. exact H.
Qed.

Definition maxlen (l : list Link) : nat := fold_right (fun s => Nat.max (String.length s)) 0 l.

Lemma maxlen_ge : forall l s, In s l -> String.length s <= maxlen l.
Proof.
  induction l as [|a l IH]; intros s Hin; simpl in *.
  - contradiction.
  - destruct Hin as [->|Hin]; [ lia | ].
    specialize (IH s Hin). lia.
Qed.

Lemma fresh_links : forall (l : list Link) m,
  exists Zs, length Zs = m /\ NoDup Zs /\
    (forall Z, In Z Zs -> ~ In Z l) /\
    (forall Z, In Z Zs -> String.length Z > maxlen l).
Proof.
  intros l m.
  exists (map (fun k => astr (S (maxlen l) + k)) (seq 0 m)).
  split; [ rewrite List.length_map, List.length_seq; reflexivity |].
  split.
  { apply NoDup_map_NoDup_ForallPairs; [ | apply seq_NoDup ].
    intros a b _ _ Hab. apply astr_inj in Hab. lia. }
  assert (Hlen : forall Z, In Z (map (fun k => astr (S (maxlen l) + k)) (seq 0 m)) ->
                 String.length Z > maxlen l).
  { intros Z Hin. apply in_map_iff in Hin. destruct Hin as [k [<- _]].
    rewrite astr_length in Hab || rewrite astr_length. lia. }
  split; [ | exact Hlen ].
  intros Z Hin Habs. apply Hlen in Hin.
  apply maxlen_ge in Habs. lia.
Qed.

Fixpoint rename_term (f : Link -> Link) (t : Term) : Term :=
  match t with
  | TZero => TZero
  | TAtom a => TAtom (map_atom f a)
  | TMol t1 t2 => TMol (rename_term f t1) (rename_term f t2)
  end.

Lemma flatten_rename_term : forall f t,
  flatten_atoms (rename_term f t) = map (map_atom f) (flatten_atoms t).
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; simpl; auto.
  rewrite IH1, IH2, map_app. reflexivity.
Qed.

Lemma rename_term_ext : forall f g t,
  (forall X, In X (links t) -> f X = g X) ->
  rename_term f t = rename_term g t.
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; intros H; simpl; auto.
  - f_equal. destruct a as [p ls|x y]; simpl.
    + f_equal. apply map_ext_in. intros z Hz. apply H. simpl. exact Hz.
    + f_equal; apply H; simpl; auto.
  - simpl in H. f_equal.
    + apply IH1. intros X HX. apply H, in_or_app. auto.
    + apply IH2. intros X HX. apply H, in_or_app. auto.
Qed.

Lemma rename_term_id : forall t, rename_term (fun x => x) t = t.
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; simpl; auto.
  - f_equal. apply map_atom_id.
  - rewrite IH1, IH2. reflexivity.
Qed.

Lemma flatten_substitute : forall Y X t,
  flatten_atoms (substitute Y X t)
  = map (map_atom (substitute_link Y X)) (flatten_atoms t).
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; simpl.
  - reflexivity.
  - destruct a as [p ls|x y]; reflexivity.
  - rewrite IH1, IH2, map_app. reflexivity.
Qed.

Lemma locallink_stable_subst : forall P X Y X',
  X <> Y -> X' <> X -> X' <> Y ->
  In X' (locallinks P) -> In X' (locallinks (substitute Y X P)).
Proof.
  intros P X Y X' HXY HX' HX'Y H.
  rewrite in_locallinks in *.
  rewrite (subst_multiplicity_other P X Y X'); auto.
Qed.

Lemma links_subst_notY : forall P X Y Z,
  X <> Y -> Z <> Y -> In Z (links (substitute Y X P)) -> In Z (links P).
Proof.
  intros P X Y Z HXY HZY Hin.
  apply in_links_link_multiset in Hin.
  apply in_links_link_multiset.
  destruct (Leq_dec Z X) as [->|HZX].
  - rewrite subst_multiplicity_X in Hin by auto. lia.
  - rewrite subst_multiplicity_other in Hin; auto.
Qed.

Fixpoint apply_subs (ps : list (Link * Link)) (t : Term) : Term :=
  match ps with
  | [] => t
  | (x, y) :: rest => apply_subs rest (substitute y x t)
  end.

Lemma congm_rename_locals : forall Xs Ys P,
  wellformed_t P ->
  length Xs = length Ys ->
  NoDup Xs -> NoDup Ys ->
  (forall X, In X Xs -> In X (locallinks P)) ->
  (forall Y, In Y Ys -> ~ In Y (links P)) ->
  (forall X Y, In X Xs -> In Y Ys -> X <> Y) ->
  P ==m apply_subs (combine Xs Ys) P.
Proof.
  induction Xs as [|X Xs IH]; intros Ys P WFP Hlen HnX HnY HlocX HfrY Hdisj.
  - simpl. apply congm_refl. exact WFP.
  - destruct Ys as [|Y Ys]; [ discriminate |]. simpl in Hlen. injection Hlen as Hlen.
    inversion HnX as [|? ? HXnotin HnX']; subst.
    inversion HnY as [|? ? HYnotin HnY']; subst.
    assert (HXloc : In X (locallinks P)) by (apply HlocX; left; reflexivity).
    assert (HXY : X <> Y) by (apply Hdisj; left; reflexivity).
    assert (HYfr : ~ In Y (links P)) by (apply HfrY; left; reflexivity).
    assert (HmX : multiplicity (link_multiset P) X = 2)
      by (apply in_locallinks; exact HXloc).
    assert (HmY : multiplicity (link_multiset P) Y = 0)
      by (apply multiplicity_not_in; exact HYfr).
    assert (WFP' : wellformed_t (substitute Y X P)).
    { apply subst_wellformed_t; [ exact WFP | rewrite HmX, HmY; lia ]. }
    assert (Hstep : P ==m substitute Y X P)
      by (apply congm_E4; assumption).
    assert (HlocX' : forall X', In X' Xs -> In X' (locallinks (substitute Y X P))).
    { intros X' HX'. apply locallink_stable_subst;
        [ exact HXY
        | intro E; apply HXnotin; rewrite <- E; exact HX'
        | intro E; apply (Hdisj X' Y);
            [ right; exact HX' | left; reflexivity | exact E ]
        | apply HlocX; right; exact HX' ]. }
    assert (HfrY' : forall Y', In Y' Ys -> ~ In Y' (links (substitute Y X P))).
    { intros Y' HY' Hin.
      apply (links_subst_notY P X Y Y') in Hin;
        [ apply (HfrY Y'); [ right; exact HY' | exact Hin ]
        | exact HXY
        | intro E; apply HYnotin; rewrite <- E; exact HY' ]. }
    assert (Hdisj' : forall X' Y', In X' Xs -> In Y' Ys -> X' <> Y').
    { intros X' Y' HX' HY'. apply Hdisj; right; assumption. }
    change (apply_subs (combine (X :: Xs) (Y :: Ys)) P)
      with (apply_subs (combine Xs Ys) (substitute Y X P)).
    apply congm_trans' with (substitute Y X P); [ exact Hstep |].
    exact (IH Ys (substitute Y X P) WFP' Hlen HnX' HnY' HlocX' HfrY' Hdisj').
Qed.

Fixpoint subst_link_chain (ps : list (Link * Link)) (z : Link) : Link :=
  match ps with
  | [] => z
  | (x, y) :: rest => subst_link_chain rest (substitute_link y x z)
  end.

Lemma flatten_apply_subs : forall ps t,
  flatten_atoms (apply_subs ps t)
  = map (map_atom (subst_link_chain ps)) (flatten_atoms t).
Proof.
  induction ps as [|[x y] rest IH]; intros t; simpl.
  - rewrite map_map_atom_id. reflexivity.
  - rewrite IH, flatten_substitute, map_map.
    apply map_ext. intros a. rewrite map_atom_comp. reflexivity.
Qed.

Lemma subst_link_chain_miss : forall Xs Ys z,
  length Xs = length Ys -> ~ In z Xs -> ~ In z Ys ->
  subst_link_chain (combine Xs Ys) z = z.
Proof.
  induction Xs as [|x Xs IH]; intros Ys z Hlen HnX HnY.
  - reflexivity.
  - destruct Ys as [|y Ys]; [ discriminate |]. simpl in Hlen. injection Hlen as Hlen.
    simpl. unfold substitute_link.
    destruct (z =? x) eqn:E.
    { apply eqb_eq in E. exfalso. apply HnX. left. auto. }
    apply IH; auto; intro; [ apply HnX | apply HnY ]; right; auto.
Qed.

Lemma subst_link_chain_hit : forall Xs Ys i x y,
  NoDup Xs -> NoDup Ys -> length Xs = length Ys ->
  (forall a, In a Ys -> ~ In a Xs) ->
  nth_error Xs i = Some x -> nth_error Ys i = Some y ->
  subst_link_chain (combine Xs Ys) x = y.
Proof.
  induction Xs as [|x0 Xs IH]; intros Ys i x y HnX HnY Hlen Hdisj HeX HeY.
  - destruct i; discriminate.
  - destruct Ys as [|y0 Ys]; [ discriminate |]. simpl in Hlen. injection Hlen as Hlen.
    inversion HnX as [|? ? Hx0 HnX']; subst.
    inversion HnY as [|? ? Hy0 HnY']; subst.
    destruct i as [|i']; simpl in HeX, HeY.
    + injection HeX as ->. injection HeY as ->.
      simpl. unfold substitute_link. rewrite eqb_refl.
      apply subst_link_chain_miss;
        [ exact Hlen
        | intro Hin; apply (Hdisj y); [ left; reflexivity | right; exact Hin ]
        | exact Hy0 ].
    + simpl. unfold substitute_link.
      assert (Hxx0 : x <> x0).
      { intro E. apply Hx0. rewrite <- E. eapply nth_error_In; eauto. }
      apply eqb_neq in Hxx0. rewrite Hxx0.
      apply (IH Ys i' x y HnX' HnY' Hlen); auto.
      intros a Ha Hin. apply (Hdisj a); [ right; exact Ha | right; exact Hin ].
Qed.

(* --- extracting the link renaming from a connector-free giso --- *)

Definition has_port (P : Term) (X : Link) : Prop :=
  exists i k, portlink (node_atoms P) i k = Some X.

Lemma edge_eq_nil_cf : forall t x y,
  term_conns t = [] -> (edge_eq (term_conns t) x y <-> x = y).
Proof. intros t x y H. rewrite H. apply edge_eq_nil. Qed.

Section GisoPhi.
Variables (f g : nat -> nat) (P Q : Term).
Hypothesis Hgf : forall i, g (f i) = i.
Hypothesis Hfg : forall i, f (g i) = i.
Hypothesis Hfun : forall i,
  option_map get_functor (nth_error (node_atoms P) i)
  = option_map get_functor (nth_error (node_atoms Q) (f i)).
Hypothesis Hconn : forall i k j l Xik Xjl Yik Yjl,
  portlink (node_atoms P) i k = Some Xik ->
  portlink (node_atoms P) j l = Some Xjl ->
  portlink (node_atoms Q) (f i) k = Some Yik ->
  portlink (node_atoms Q) (f j) l = Some Yjl ->
  (edge_eq (term_conns P) Xik Xjl <-> edge_eq (term_conns Q) Yik Yjl).
Hypothesis HcfP : term_conns P = [].
Hypothesis HcfQ : term_conns Q = [].

Lemma phi_unique : forall X, has_port P X ->
  exists ! Y, forall i k, portlink (node_atoms P) i k = Some X ->
                          portlink (node_atoms Q) (f i) k = Some Y.
Proof.
  intros X [i0 [k0 Hp0]].
  destruct (giso_port_mid f P Q i0 k0 X Hfun Hp0) as [Y0 HY0].
  exists Y0. split.
  - intros i k Hp.
    destruct (giso_port_mid f P Q i k X Hfun Hp) as [Y HY].
    assert (E := Hconn i k i0 k0 X X Y Y0 Hp Hp0 HY HY0).
    rewrite (edge_eq_nil_cf P X X HcfP) in E.
    rewrite (edge_eq_nil_cf Q Y Y0 HcfQ) in E.
    rewrite <- (proj1 E eq_refl). exact HY.
  - intros Y' HY'. specialize (HY' i0 k0 Hp0). congruence.
Qed.

Definition phi (X : Link) : Link :=
  match excluded_middle_informative (has_port P X) with
  | left H => proj1_sig (constructive_definite_description _ (phi_unique X H))
  | right _ => X
  end.

Lemma phi_port : forall X i k,
  portlink (node_atoms P) i k = Some X ->
  portlink (node_atoms Q) (f i) k = Some (phi X).
Proof.
  intros X i k Hp. unfold phi.
  destruct (excluded_middle_informative (has_port P X)) as [H|H].
  - destruct (constructive_definite_description _ _) as [Y HY]. simpl.
    apply HY. exact Hp.
  - exfalso. apply H. exists i, k. exact Hp.
Qed.

End GisoPhi.

Lemma node_atoms_cf : forall t, connector_free t -> node_atoms t = flatten_atoms t.
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; intros H.
  - reflexivity.
  - destruct a; [ reflexivity | destruct H ].
  - simpl in H. destruct H as [H1 H2].
    rewrite node_atoms_mol, (IH1 H1), (IH2 H2). reflexivity.
Qed.

Lemma term_conns_cf : forall t, connector_free t -> term_conns t = [].
Proof.
  induction t as [| a | t1 IH1 t2 IH2 ]; intros H.
  - reflexivity.
  - destruct a; [ reflexivity | destruct H ].
  - simpl in H. destruct H as [H1 H2].
    rewrite term_conns_mol, (IH1 H1), (IH2 H2). reflexivity.
Qed.

Lemma In_links_has_port : forall P X,
  connector_free P -> In X (links P) -> has_port P X.
Proof.
  intros P X Hcf Hin.
  rewrite links_flatten in Hin. rewrite in_flat_map in Hin.
  destruct Hin as [a [Ha HXa]].
  rewrite <- (node_atoms_cf P Hcf) in Ha.
  apply In_nth_error in Ha. destruct Ha as [i Hi].
  destruct a as [p ls|x y].
  - simpl in HXa. apply In_nth_error in HXa. destruct HXa as [k Hk].
    exists i, k. unfold portlink. rewrite Hi. exact Hk.
  - assert (Hff := node_atoms_aatom P).
    rewrite Forall_forall in Hff.
    apply nth_error_In in Hi. apply Hff in Hi. contradiction.
Qed.

Lemma phi_free_id : forall f P Q Hfun Hconn HcfP HcfQ,
  connector_free P -> connector_free Q ->
  (forall i k Z Xik Yik,
     In Z (freelinks P) ->
     portlink (node_atoms P) i k = Some Xik ->
     portlink (node_atoms Q) (f i) k = Some Yik ->
     (edge_eq (term_conns P) Xik Z <-> edge_eq (term_conns Q) Yik Z)) ->
  forall X, In X (freelinks P) ->
    phi f P Q Hfun Hconn HcfP HcfQ X = X.
Proof.
  intros f P Q Hfun Hconn HcfP HcfQ HcfP' HcfQ' Hifc X HX.
  assert (Hpx : has_port P X).
  { apply In_links_has_port; auto. apply in_freelinks_In_links, HX. }
  destruct Hpx as [i [k Hp]].
  assert (Hq := phi_port f P Q Hfun Hconn HcfP HcfQ X i k Hp).
  assert (E := Hifc i k X X (phi f P Q Hfun Hconn HcfP HcfQ X) HX Hp Hq).
  rewrite (edge_eq_nil_cf P X X HcfP) in E.
  rewrite (edge_eq_nil_cf Q _ X HcfQ) in E.
  exact (proj1 E eq_refl).
Qed.

Lemma phi_perm : forall f g P Q Hfun Hconn HcfP HcfQ,
  (forall i, f (g i) = i) ->
  (forall j, j < length (node_atoms Q) -> g j < length (node_atoms P)) ->
  (forall i, i < length (node_atoms P) -> f i < length (node_atoms Q)) ->
  connector_free P -> connector_free Q ->
  length (node_atoms P) = length (node_atoms Q) ->
  Permutation (map (map_atom (phi f P Q Hfun Hconn HcfP HcfQ)) (flatten_atoms P))
              (flatten_atoms Q).
Proof.
  intros f g P Q Hfun Hconn HcfP HcfQ Hfg Hcod Hdom HcfP' HcfQ' Hlen.
  set (ph := phi f P Q Hfun Hconn HcfP HcfQ).
  rewrite <- (node_atoms_cf P HcfP'), <- (node_atoms_cf Q HcfQ').
  apply Permutation_nth_error.
  split.
  { rewrite length_map. exact Hlen. }
  exists g. split.
  { intros x y Hxy. rewrite <- (Hfg x), <- (Hfg y), Hxy. reflexivity. }
  intros j. rewrite nth_error_map.
  destruct (nth_error (node_atoms P) (g j)) as [a|] eqn:Ea.
  - assert (Haa : exists p ls, a = AAtom p ls).
    { assert (HF := node_atoms_aatom P). rewrite Forall_forall in HF.
      apply nth_error_In in Ea. apply HF in Ea.
      destruct a as [p ls|x y]; [ eauto | contradiction ]. }
    destruct Haa as [p [ls ->]].
    assert (Hfunj := Hfun (g j)). rewrite Hfg in Hfunj. rewrite Ea in Hfunj.
    destruct (nth_error (node_atoms Q) j) as [b|] eqn:Eb;
      [ | cbn in Hfunj; discriminate ].
    assert (Hbb : exists p' ls', b = AAtom p' ls').
    { assert (HF := node_atoms_aatom Q). rewrite Forall_forall in HF.
      apply nth_error_In in Eb. apply HF in Eb.
      destruct b as [p' ls'|x y]; [ eauto | contradiction ]. }
    destruct Hbb as [p' [ls' ->]].
    cbn in Hfunj.
    injection Hfunj as Hp Hll.
    subst p'. simpl.
    f_equal. f_equal. f_equal.
    apply nth_error_ext. intros k.
    rewrite nth_error_map.
    destruct (nth_error ls k) as [x|] eqn:Ex.
    + assert (Hpx : portlink (node_atoms P) (g j) k = Some x)
        by (unfold portlink; rewrite Ea; exact Ex).
      assert (Hq := phi_port f P Q Hfun Hconn HcfP HcfQ x (g j) k Hpx).
      rewrite Hfg in Hq.
      unfold portlink in Hq. rewrite Eb in Hq. rewrite Hq. reflexivity.
    + apply nth_error_None in Ex.
      destruct (nth_error ls' k) as [y|] eqn:Ey; [ | reflexivity ].
      exfalso.
      assert (k < length ls') by (apply nth_error_Some; rewrite Ey; discriminate).
      lia.
  - destruct (nth_error (node_atoms Q) j) as [b|] eqn:Eb; [ | reflexivity ].
    exfalso.
    apply nth_error_None in Ea.
    assert (j < length (node_atoms Q)).
    { apply nth_error_Some. rewrite Eb. discriminate. }
    apply Hcod in H. lia.
Qed.

Lemma map_atom_ext_in : forall (f g : Link -> Link) a,
  (forall x, In x (links_of_atom a) -> f x = g x) ->
  map_atom f a = map_atom g a.
Proof.
  intros f g [p ls|x y] H; simpl in *; f_equal.
  - apply map_ext_in. exact H.
  - apply H. auto.
  - apply H. auto.
Qed.

Lemma map_map_atom_ext_in : forall (f g : Link -> Link) l,
  (forall x, In x (flat_map links_of_atom l) -> f x = g x) ->
  map (map_atom f) l = map (map_atom g) l.
Proof.
  intros f g l H. apply map_ext_in. intros a Ha.
  apply map_atom_ext_in. intros x Hx. apply H.
  apply in_flat_map. exists a. auto.
Qed.

Lemma locallinks_freelinks_disjoint : forall t X,
  In X (locallinks t) -> In X (freelinks t) -> False.
Proof.
  intros t X H1 H2. rewrite in_locallinks in H1. rewrite in_freelinks in H2. lia.
Qed.

Lemma phi_inj : forall f P Q Hfun Hconn HcfP HcfQ,
  connector_free P -> connector_free Q ->
  forall X X', In X (links P) -> In X' (links P) ->
    phi f P Q Hfun Hconn HcfP HcfQ X = phi f P Q Hfun Hconn HcfP HcfQ X' -> X = X'.
Proof.
  intros f P Q Hfun Hconn HcfP HcfQ HcfP' HcfQ' X X' HX HX' Heq.
  destruct (In_links_has_port P X HcfP' HX) as [i [k Hp]].
  destruct (In_links_has_port P X' HcfP' HX') as [i' [k' Hp']].
  assert (Hq  := phi_port f P Q Hfun Hconn HcfP HcfQ X i k Hp).
  assert (Hq' := phi_port f P Q Hfun Hconn HcfP HcfQ X' i' k' Hp').
  rewrite Heq in Hq.
  assert (E := Hconn i k i' k' X X' _ _ Hp Hp' Hq Hq').
  rewrite (edge_eq_nil_cf P X X' HcfP) in E.
  rewrite (edge_eq_nil_cf Q _ _ HcfQ) in E.
  apply (proj2 E). reflexivity.
Qed.

Lemma NoDup_locallinks : forall t, NoDup (locallinks t).
Proof.
  intros t. unfold locallinks. apply NoDup_filter.
  unfold unique_links. apply NoDup_nodup.
Qed.

Lemma flat_map_links_map_atom : forall (r : Link -> Link) l,
  flat_map links_of_atom (map (map_atom r) l) = map r (flat_map links_of_atom l).
Proof.
  induction l as [|a l IH]; simpl; auto.
  rewrite IH, links_of_atom_map_atom, map_app. reflexivity.
Qed.

Lemma link_multiset_flatten_eq : forall t1 t2,
  flatten_atoms t1 = flatten_atoms t2 ->
  link_multiset t1 = link_multiset t2.
Proof.
  intros t1 t2 H. unfold link_multiset. rewrite !links_flatten, H. reflexivity.
Qed.

Lemma link_multiset_rename : forall (r : Link -> Link) t Y,
  multiplicity (link_multiset (rename_term r t)) Y
  = multiplicity (list_to_multiset (map r (links t))) Y.
Proof.
  intros r t Y. unfold link_multiset.
  rewrite links_flatten, flatten_rename_term, flat_map_links_map_atom.
  rewrite <- links_flatten. reflexivity.
Qed.

(* [mult_cons] is now defined earlier, alongside [cong]/[congm]. *)

Lemma mult_rename_eq : forall (r : Link -> Link) ll X0,
  (forall x, In x ll -> r x = r X0 -> x = X0) ->
  multiplicity (list_to_multiset (map r ll)) (r X0)
  = multiplicity (list_to_multiset ll) X0.
Proof.
  induction ll as [|x ll IH]; intros X0 Hinj.
  - reflexivity.
  - simpl (map r _). rewrite !mult_cons.
    destruct (Leq_dec (r x) (r X0)) as [E|E].
    + assert (Hx : x = X0) by (apply (Hinj x); [ left; reflexivity | exact E ]).
      subst x. rewrite Leq_dec_refl. cbn [Nat.add].
      f_equal. apply IH. intros z Hz. apply Hinj. right. exact Hz.
    + destruct (Leq_dec x X0) as [Ex|Ex]; [ subst x; congruence |].
      cbn [Nat.add]. apply IH. intros z Hz. apply Hinj. right. exact Hz.
Qed.

Lemma mult_rename_notimg : forall (r : Link -> Link) ll Y,
  (forall x, In x ll -> r x <> Y) ->
  multiplicity (list_to_multiset (map r ll)) Y = 0.
Proof.
  induction ll as [|x ll IH]; intros Y H.
  - reflexivity.
  - simpl (map r _). rewrite mult_cons.
    destruct (Leq_dec (r x) Y) as [E|E].
    + exfalso. apply (H x); [ left; reflexivity | exact E ].
    + cbn [Nat.add]. apply IH. intros z Hz. apply H. right. exact Hz.
Qed.

Lemma In_locallinks_links : forall t X, In X (locallinks t) -> In X (links t).
Proof.
  intros t X H. apply in_locallinks in H.
  apply in_links_link_multiset. lia.
Qed.

Lemma nth_error_ex : forall {A} (l : list A) i,
  i < length l -> exists a, nth_error l i = Some a.
Proof.
  intros A l i H. destruct (nth_error l i) as [a|] eqn:E.
  - exists a. reflexivity.
  - apply nth_error_None in E. lia.
Qed.

Lemma chain_hit_of_in : forall Xs Ys X,
  NoDup Xs -> NoDup Ys -> length Xs = length Ys ->
  (forall a, In a Ys -> ~ In a Xs) ->
  In X Xs ->
  exists y, In y Ys /\ subst_link_chain (combine Xs Ys) X = y.
Proof.
  intros Xs Ys X HnX HnY Hlen Hdisj Hin.
  apply In_nth_error in Hin. destruct Hin as [i HeX].
  assert (Hi : i < length Ys).
  { rewrite <- Hlen. apply nth_error_Some. rewrite HeX. discriminate. }
  destruct (nth_error_ex Ys i Hi) as [y HeY].
  exists y. split; [ eapply nth_error_In; eauto |].
  eapply subst_link_chain_hit; eauto.
Qed.

Lemma subst_link_chain_inj_on : forall Xs Ys (S : list Link),
  NoDup Xs -> NoDup Ys -> length Xs = length Ys ->
  (forall a, In a Ys -> ~ In a Xs) ->
  (forall a, In a Ys -> ~ In a S) ->
  forall X X', In X S -> In X' S ->
    subst_link_chain (combine Xs Ys) X = subst_link_chain (combine Xs Ys) X' -> X = X'.
Proof.
  intros Xs Ys S HnX HnY Hlen Hdisj HdisjS X X' HX HX' Heq.
  assert (Hmiss : forall z, In z S -> ~ In z Xs ->
                  subst_link_chain (combine Xs Ys) z = z).
  { intros z HzS HzX. apply subst_link_chain_miss; auto.
    intro. apply (HdisjS z); auto. }
  assert (Hhit : forall z, In z Xs -> exists i w,
                  nth_error Xs i = Some z /\ nth_error Ys i = Some w /\
                  In w Ys /\ subst_link_chain (combine Xs Ys) z = w).
  { intros z HzX. apply In_nth_error in HzX. destruct HzX as [i HeX].
    assert (Hi : i < length Ys)
      by (rewrite <- Hlen; apply nth_error_Some; rewrite HeX; discriminate).
    destruct (nth_error_ex Ys i Hi) as [w Hw].
    exists i, w. repeat split; auto.
    - eapply nth_error_In; eauto.
    - eapply subst_link_chain_hit; eauto. }
  destruct (classic (In X Xs)) as [HXin|HXin];
  destruct (classic (In X' Xs)) as [HX'in|HX'in].
  - destruct (Hhit X HXin) as [i [w [HeX [HeY [HwY Hv]]]]].
    destruct (Hhit X' HX'in) as [i' [w' [HeX' [HeY' [Hw'Y Hv']]]]].
    rewrite Hv, Hv' in Heq. subst w'.
    assert (i = i').
    { apply (proj1 (NoDup_nth_error Ys) HnY i i').
      - apply nth_error_Some. rewrite HeY. discriminate.
      - rewrite HeY, HeY'. reflexivity. }
    subst i'. rewrite HeX in HeX'. injection HeX' as ->. reflexivity.
  - exfalso. destruct (Hhit X HXin) as [i [w [HeX [HeY [HwY Hv]]]]].
    rewrite Hv, (Hmiss X' HX' HX'in) in Heq. subst w.
    apply (HdisjS X' HwY HX').
  - exfalso. destruct (Hhit X' HX'in) as [i [w [HeX [HeY [HwY Hv]]]]].
    rewrite Hv, (Hmiss X HX HXin) in Heq. subst w.
    apply (HdisjS X HwY HX).
  - rewrite (Hmiss X HX HXin), (Hmiss X' HX' HX'in) in Heq. exact Heq.
Qed.

Lemma chain_surj : forall Xs Ys Z,
  NoDup Xs -> NoDup Ys -> length Xs = length Ys ->
  (forall a, In a Ys -> ~ In a Xs) ->
  In Z Ys -> exists X, In X Xs /\ subst_link_chain (combine Xs Ys) X = Z.
Proof.
  intros Xs Ys Z HnX HnY Hlen Hdisj HZ.
  apply In_nth_error in HZ. destruct HZ as [i HeY].
  assert (Hi : i < length Xs)
    by (rewrite Hlen; apply nth_error_Some; rewrite HeY; discriminate).
  destruct (nth_error_ex Xs i Hi) as [X HeX].
  exists X. split; [ eapply nth_error_In; eauto |].
  eapply subst_link_chain_hit; eauto.
Qed.

Lemma phi_In_links_Q : forall f P Q Hfun Hconn HcfP HcfQ,
  connector_free P ->
  forall X, In X (links P) -> In (phi f P Q Hfun Hconn HcfP HcfQ X) (links Q).
Proof.
  intros f P Q Hfun Hconn HcfP HcfQ HcfP' X HX.
  destruct (In_links_has_port P X HcfP' HX) as [i [k Hp]].
  assert (Hq := phi_port f P Q Hfun Hconn HcfP HcfQ X i k Hp).
  eapply portlink_In_links; eauto.
Qed.

Lemma nu_compose_on : forall Ls Zs Ts (rho : Link -> Link) X,
  NoDup Ls -> NoDup Zs -> NoDup Ts ->
  length Ls = length Zs -> length Zs = length Ts ->
  Ts = map rho Ls ->
  (forall a, In a Zs -> ~ In a Ls) ->
  (forall a, In a Zs -> ~ In a Ts) ->
  In X Ls ->
  subst_link_chain (combine Zs Ts) (subst_link_chain (combine Ls Zs) X) = rho X.
Proof.
  intros Ls Zs Ts rho X HnL HnZ HnT HlLZ HlZT HTdef HZL HZT HX.
  apply In_nth_error in HX. destruct HX as [i HeL].
  assert (Hi : i < length Zs)
    by (rewrite <- HlLZ; apply nth_error_Some; rewrite HeL; discriminate).
  destruct (nth_error_ex Zs i Hi) as [w Hw].
  assert (Ev1 := subst_link_chain_hit Ls Zs i X w HnL HnZ HlLZ HZL HeL Hw).
  rewrite Ev1.
  assert (HeT : nth_error Ts i = Some (rho X)).
  { rewrite HTdef, nth_error_map, HeL. reflexivity. }
  apply (subst_link_chain_hit Zs Ts i w (rho X) HnZ HnT HlZT); auto.
  intros a Ha Hin. apply (HZT a Hin Ha).
Qed.

Lemma in_locallinks_or_free : forall P X,
  wellformed_t P -> In X (links P) ->
  In X (locallinks P) \/ In X (freelinks P).
Proof.
  intros P X W HX.
  assert (H1 : 1 <= multiplicity (link_multiset P) X)
    by (apply in_links_link_multiset; exact HX).
  assert (H2 := wellformed_t_mult_le P X W).
  destruct (multiplicity (link_multiset P) X) as [|[|[|n]]] eqn:E; try lia.
  - right. apply in_freelinks. lia.
  - left. apply in_locallinks. lia.
Qed.

Lemma congm_rename_by : forall P (rho : Link -> Link),
  wellformed_t P ->
  (forall X, In X (freelinks P) -> rho X = X) ->
  (forall X X', In X (links P) -> In X' (links P) -> rho X = rho X' -> X = X') ->
  (forall X, In X (locallinks P) -> ~ In (rho X) (freelinks P)) ->
  exists P2,
    P ==m P2 /\ flatten_atoms P2 = map (map_atom rho) (flatten_atoms P).
Proof.
  intros P rho WFP Hfr Hinj Hnf.
  set (Ls := locallinks P).
  set (Ts := map rho Ls).
  assert (HnLs : NoDup Ls) by apply NoDup_locallinks.
  assert (HLsL : forall X, In X Ls -> In X (links P)) by (apply In_locallinks_links).
  assert (HnTs : NoDup Ts).
  { apply NoDup_map_NoDup_ForallPairs; [ | exact HnLs ].
    intros a b Ha Hb Hab. apply Hinj; [ apply HLsL; exact Ha | apply HLsL; exact Hb | exact Hab ]. }
  destruct (fresh_links (links P ++ Ts) (length Ls))
    as (Zs & HZlen & HZnd & HZfr & _).
  assert (HZnP : forall Z, In Z Zs -> ~ In Z (links P))
    by (intros Z HZ HC; apply (HZfr Z HZ); apply in_or_app; auto).
  assert (HZnTs : forall Z, In Z Zs -> ~ In Z Ts)
    by (intros Z HZ HC; apply (HZfr Z HZ); apply in_or_app; auto).
  assert (HZnLs : forall Z, In Z Zs -> ~ In Z Ls)
    by (intros Z HZ HC; apply (HZnP Z HZ), HLsL, HC).
  assert (HlenLZ : length Ls = length Zs) by (rewrite HZlen; reflexivity).
  assert (HlenZT : length Zs = length Ts).
  { unfold Ts. rewrite length_map. symmetry. exact HlenLZ. }
  assert (HZfrP : forall Z, In Z Zs -> ~ In Z (freelinks P))
    by (intros Z HZ HC; apply (HZnP Z HZ), in_freelinks_In_links, HC).
  remember (subst_link_chain (combine Ls Zs)) as nu1 eqn:Hnu1.
  assert (Hnu1inj : forall X X', In X (links P) -> In X' (links P) ->
                    nu1 X = nu1 X' -> X = X').
  { intros X X' HX HX' Heq. rewrite Hnu1 in Heq.
    exact (subst_link_chain_inj_on Ls Zs (links P) HnLs HZnd HlenLZ HZnLs HZnP
             X X' HX HX' Heq). }
  assert (Hnu1hit : forall X, In X Ls -> In (nu1 X) Zs).
  { intros X HX.
    destruct (chain_hit_of_in Ls Zs X HnLs HZnd HlenLZ HZnLs HX) as [y [Hy Hyv]].
    rewrite <- Hnu1 in Hyv. rewrite Hyv. exact Hy. }
  assert (Hnu1miss : forall X, ~ In X Ls -> ~ In X Zs -> nu1 X = X).
  { intros X HX HZ. rewrite Hnu1. apply subst_link_chain_miss; auto. }
  set (P1 := apply_subs (combine Ls Zs) P).
  assert (Hstep1 : P ==m P1).
  { apply congm_rename_locals; auto.
    intros X Z HX HZ ->. apply (HZnLs Z HZ HX). }
  assert (WFP1 : wellformed_t P1)
    by exact (proj2 (congm_wellformed_t _ _ Hstep1)).
  assert (HflatP1 : flatten_atoms P1 = map (map_atom nu1) (flatten_atoms P)).
  { rewrite Hnu1. apply flatten_apply_subs. }
  assert (HlmP1 : forall Y, multiplicity (link_multiset P1) Y
                          = multiplicity (list_to_multiset (map nu1 (links P))) Y).
  { intros Y.
    rewrite (link_multiset_flatten_eq P1 (rename_term nu1 P))
      by (rewrite HflatP1, flatten_rename_term; reflexivity).
    apply link_multiset_rename. }
  assert (HZloc : forall Z, In Z Zs -> In Z (locallinks P1)).
  { intros Z HZ.
    destruct (chain_surj Ls Zs Z HnLs HZnd HlenLZ HZnLs HZ) as [X [HX HXv]].
    rewrite <- Hnu1 in HXv.
    apply in_locallinks. rewrite HlmP1. rewrite <- HXv.
    rewrite (mult_rename_eq nu1 (links P) X).
    - fold (link_multiset P). apply in_locallinks. exact HX.
    - intros z Hz Hzeq. apply Hnu1inj; auto using HLsL. }
  assert (HTnP1 : forall T, In T Ts -> ~ In T (links P1)).
  { intros T HT HC.
    apply in_map_iff in HT. destruct HT as [X [HXeq HX]].
    apply in_links_link_multiset in HC. rewrite HlmP1 in HC.
    rewrite (mult_rename_notimg nu1 (links P) T) in HC; [ lia |].
    intros z Hz Hzeq.
    destruct (in_locallinks_or_free P z WFP Hz) as [Hzl|Hzf].
    - apply Hnu1hit in Hzl. rewrite Hzeq, <- HXeq in Hzl.
      apply (HZnTs (rho X) Hzl). apply in_map. exact HX.
    - assert (Hznl : ~ In z Ls)
        by (intro C; apply (locallinks_freelinks_disjoint P z); [ exact C | exact Hzf ]).
      assert (Hznz : ~ In z Zs) by (intro C; apply (HZfrP z C Hzf)).
      rewrite (Hnu1miss z Hznl Hznz) in Hzeq.
      apply (Hnf X HX). rewrite HXeq, <- Hzeq. exact Hzf. }
  set (P2 := apply_subs (combine Zs Ts) P1).
  assert (Hstep2 : P1 ==m P2).
  { apply congm_rename_locals; auto.
    intros Z T HZ HT E. subst T. apply (HZnTs Z HZ HT). }
  remember (subst_link_chain (combine Zs Ts)) as nu2 eqn:Hnu2.
  assert (Hnu2flat : flatten_atoms P2 = map (map_atom nu2) (flatten_atoms P1)).
  { rewrite Hnu2. apply flatten_apply_subs. }
  assert (Hcompose : forall z, In z (links P) -> nu2 (nu1 z) = rho z).
  { intros z Hz.
    destruct (in_locallinks_or_free P z WFP Hz) as [Hzl|Hzf].
    - assert (E := nu_compose_on Ls Zs Ts rho z HnLs HZnd HnTs
                    HlenLZ HlenZT eq_refl HZnLs HZnTs Hzl).
      rewrite Hnu1, Hnu2. exact E.
    - assert (Hznl : ~ In z Ls)
        by (intro C; apply (locallinks_freelinks_disjoint P z); [ exact C | exact Hzf ]).
      assert (Hznz : ~ In z Zs) by (intro C; apply (HZfrP z C Hzf)).
      assert (Hznt : ~ In z Ts).
      { intro C. apply in_map_iff in C. destruct C as [w [Hw Hwl]].
        apply (Hnf w Hwl). rewrite Hw. exact Hzf. }
      rewrite (Hnu1miss z Hznl Hznz).
      rewrite Hnu2. rewrite subst_link_chain_miss; auto.
      symmetry. apply Hfr. exact Hzf. }
  exists P2. split.
  - apply congm_trans' with P1; assumption.
  - rewrite Hnu2flat, HflatP1, map_map.
    apply map_ext_in. intros a Ha.
    rewrite map_atom_comp.
    apply map_atom_ext_in. intros x Hx.
    apply Hcompose.
    rewrite links_flatten. apply in_flat_map. exists a. auto.
Qed.

Lemma giso_cf_congm : forall P Q,
  wellformed_t P -> wellformed_t Q ->
  connector_free P -> connector_free Q ->
  giso (freelinks P) P Q -> P ==m Q.
Proof.
  intros P Q WFP WFQ HcfP HcfQ Hiso.
  assert (Hlen := giso_node_len _ _ _ Hiso).
  destruct Hiso as (f & g & Hgf & Hfg & Hdom & Hcod & Hfun & Hconn & Hifc & Hff).
  assert (HtcP : term_conns P = []) by (apply term_conns_cf; exact HcfP).
  assert (HtcQ : term_conns Q = []) by (apply term_conns_cf; exact HcfQ).
  set (ph := phi f P Q Hfun Hconn HtcP HtcQ).
  assert (Hph_free : forall X, In X (freelinks P) -> ph X = X).
  { intros X HX.
    exact (phi_free_id f P Q Hfun Hconn HtcP HtcQ HcfP HcfQ Hifc X HX). }
  assert (Hph_inj : forall X X', In X (links P) -> In X' (links P) ->
                    ph X = ph X' -> X = X').
  { exact (phi_inj f P Q Hfun Hconn HtcP HtcQ HcfP HcfQ). }
  assert (Hph_nf : forall X, In X (locallinks P) -> ~ In (ph X) (freelinks P)).
  { intros X HX Hin.
    assert (HXl : In X (links P)) by (apply In_locallinks_links; exact HX).
    assert (HphXl : In (ph X) (links P)) by (apply in_freelinks_In_links; exact Hin).
    assert (Hpp : ph (ph X) = ph X)
      by exact (phi_free_id f P Q Hfun Hconn HtcP HtcQ HcfP HcfQ Hifc (ph X) Hin).
    assert (HeqX : ph X = X) by (apply Hph_inj; auto).
    apply (locallinks_freelinks_disjoint P X);
      [ exact HX | rewrite <- HeqX; exact Hin ]. }
  destruct (congm_rename_by P ph WFP Hph_free Hph_inj Hph_nf)
    as [P2 [Hstep HflatP2]].
  assert (WFP2 : wellformed_t P2)
    by exact (proj2 (congm_wellformed_t _ _ Hstep)).
  apply congm_trans' with P2; [ exact Hstep |].
  assert (Hperm : Permutation (map (map_atom ph) (flatten_atoms P)) (flatten_atoms Q)).
  { exact (phi_perm f g P Q Hfun Hconn HtcP HtcQ Hfg Hcod Hdom HcfP HcfQ Hlen). }
  apply congm_trans' with (make_mol (flatten_atoms P2)); [ apply cong_flatten; exact WFP2 |].
  rewrite HflatP2.
  apply congm_trans' with (make_mol (flatten_atoms Q)).
  - apply make_mol_perm; [ exact Hperm |].
    rewrite <- HflatP2. apply wellformed_t_flatten_make_mol. exact WFP2.
  - apply congm_sym'. apply cong_flatten. exact WFQ.
Qed.

(* Reverse direction for closed terms: giso [] P Q -> P ==m Q.
   Reduce both sides to their connector-free normal forms (normalize_cong,
   valid because closed), transport the iso along congm_giso, then apply the
   connector-free reverse direction. *)
Theorem giso_closed_congm : forall P Q,
  wellformed_t P -> wellformed_t Q -> Closed P -> Closed Q ->
  giso [] P Q -> P ==m Q.
Proof.
  intros P Q WFP WFQ HCP HCQ Hiso.
  assert (HPn : P ==m normalize P) by (apply normalize_cong; assumption).
  assert (HQn : Q ==m normalize Q) by (apply normalize_cong; assumption).
  assert (WFPn : wellformed_t (normalize P))
    by exact (proj2 (congm_wellformed_t _ _ HPn)).
  assert (WFQn : wellformed_t (normalize Q))
    by exact (proj2 (congm_wellformed_t _ _ HQn)).
  assert (HCPn : Closed (normalize P))
    by (apply (proj1 (congm_Closed _ _ HPn)); exact HCP).
  assert (HisoP : giso [] P (normalize P)).
  { assert (H := congm_giso _ _ HPn). rewrite HCP in H. exact H. }
  assert (HisoQ : giso [] Q (normalize Q)).
  { assert (H := congm_giso _ _ HQn). rewrite HCQ in H. exact H. }
  assert (Hn : giso [] (normalize P) (normalize Q)).
  { apply giso_trans with P; [ apply giso_sym; exact HisoP |].
    apply giso_trans with Q; [ exact Hiso | exact HisoQ ]. }
  assert (HcfP : connector_free (normalize P)) by apply normalize_connector_free.
  assert (HcfQ : connector_free (normalize Q)) by apply normalize_connector_free.
  assert (Hcf : giso (freelinks (normalize P)) (normalize P) (normalize Q))
    by (rewrite HCPn; exact Hn).
  assert (Hmid := giso_cf_congm _ _ WFPn WFQn HcfP HcfQ Hcf).
  apply congm_trans' with (normalize P); [ exact HPn |].
  apply congm_trans' with (normalize Q); [ exact Hmid |].
  apply congm_sym'. exact HQn.
Qed.

(* The closed-term correspondence (design note's Theorem 3 / Corollary 1):
   for closed wellformed terms, structural congruence coincides with
   interface-free graph isomorphism. *)
Theorem congm_closed_giso_iff : forall P Q,
  wellformed_t P -> wellformed_t Q -> Closed P -> Closed Q ->
  (P ==m Q <-> giso [] P Q).
Proof.
  intros P Q WFP WFQ HCP HCQ. split.
  - intros H. assert (G := congm_giso _ _ H). rewrite HCP in G. exact G.
  - apply giso_closed_congm; assumption.
Qed.

Corollary cong_closed_giso_iff : forall P Q,
  wellformed_t P -> wellformed_t Q -> Closed P -> Closed Q ->
  (P == Q <-> giso [] P Q).
Proof.
  intros P Q WFP WFQ HCP HCQ.
  rewrite congm_cong_iff. apply congm_closed_giso_iff; assumption.
Qed.

(* ================================================================== *)
(*  Layer 3 (open case) : connector elimination for non-closed terms  *)
(* ================================================================== *)

Lemma wf_conn_atom : forall X Y, wellformed_t (TAtom (AConn X Y)).
Proof.
  intros X Y. rewrite wellformed_t_forall. intros z _.
  rewrite multiplicity_TAtom_AConn.
  destruct (Leq_dec X z); destruct (Leq_dec Y z); simpl; lia.
Qed.

Lemma congm_conn_sym : forall X Y R,
  wellformed_t (TMol (TAtom (AConn X Y)) R) ->
  TMol (TAtom (AConn X Y)) R ==m TMol (TAtom (AConn Y X)) R.
Proof.
  intros X Y R W.
  apply congm_E5.
  - exact W.
  - apply wellformed_t_link_multiset with (TMol (TAtom (AConn X Y)) R); [ | exact W ].
    intros a. rewrite !multiplicity_mol, !multiplicity_TAtom_AConn. lia.
  - exact (congm_E8 X Y).
Qed.

Lemma congm_E9ex' : forall X Y P,
  wellformed_t {{ X = Y, P }} -> wellformed_t {{ P[X/Y] }} ->
  In Y (freelinks P) ->
  {{ X = Y, P }} ==m {{ P[X/Y] }}.
Proof.
  intros X Y P W1 W2 HY.
  assert (Wsym : wellformed_t {{ Y = X, P }}).
  { apply wellformed_t_link_multiset with {{ X = Y, P }}; [ | exact W1 ].
    intros a. rewrite !multiplicity_mol, !multiplicity_TAtom_AConn. lia. }
  apply congm_trans' with {{ Y = X, P }}.
  - apply congm_conn_sym. exact W1.
  - apply congm_E9ex; [ exact Wsym | exact W2 | exact HY ].
Qed.

Lemma subst_atoms_aatom : forall Y X l,
  Forall is_aatom l -> Forall is_aatom (subst_atoms Y X l).
Proof.
  intros Y X l H. unfold subst_atoms. apply Forall_map.
  eapply Forall_impl; [ | exact H ]. intros a Ha. apply map_atom_is_aatom, Ha.
Qed.

Lemma conns_as_atoms_cons : forall x y cs,
  conns_as_atoms ((x,y) :: cs) = AConn x y :: conns_as_atoms cs.
Proof. reflexivity. Qed.

Lemma link_multiset_make_mol_perm : forall l1 l2,
  Permutation l1 l2 ->
  meq (link_multiset (make_mol l1)) (link_multiset (make_mol l2)).
Proof.
  intros l1 l2 HP a. unfold link_multiset.
  rewrite !links_make_mol.
  apply list_to_multiset_perm. apply Permutation_flat_map. exact HP.
Qed.

Lemma mult_TMol_conn : forall x y R z,
  multiplicity (link_multiset (TMol (TAtom (AConn x y)) R)) z
  = (if Leq_dec x z then 1 else 0) + (if Leq_dec y z then 1 else 0)
    + multiplicity (link_multiset R) z.
Proof.
  intros x y R z.
  rewrite multiplicity_mol, multiplicity_TAtom_AConn. reflexivity.
Qed.

Lemma peel_conns : forall n cs a,
  length cs <= n ->
  Forall is_aatom a ->
  wellformed_t (make_mol (conns_as_atoms cs ++ a)) ->
  exists cs' a',
    make_mol (conns_as_atoms cs ++ a) ==m make_mol (conns_as_atoms cs' ++ a') /\
    Forall is_aatom a' /\
    (forall c, In c cs' ->
       fst c <> snd c /\
       multiplicity (link_multiset (make_mol (conns_as_atoms cs' ++ a'))) (fst c) = 1 /\
       multiplicity (link_multiset (make_mol (conns_as_atoms cs' ++ a'))) (snd c) = 1).
Proof.
  induction n as [|n IH]; intros cs a Hn Ha WF.
  - destruct cs as [|c cs]; [ | simpl in Hn; lia ].
    exists [], a. split; [ apply congm_refl; exact WF |]. split; [ exact Ha |].
    intros c []; contradiction.
  - set (T := make_mol (conns_as_atoms cs ++ a)) in *.
    destruct (classic (exists c, In c cs /\
                ~ (fst c <> snd c /\
                   multiplicity (link_multiset T) (fst c) = 1 /\
                   multiplicity (link_multiset T) (snd c) = 1)))
      as [Hex | Hno].
    + destruct Hex as [[x y] [Hin Hpeel]]. simpl in Hpeel.
      apply in_split in Hin. destruct Hin as [l1 [l2 Hcs]].
      assert (Hperm : Permutation cs ((x,y) :: (l1 ++ l2))).
      { rewrite Hcs. apply Permutation_sym, Permutation_middle. }
      set (cs1 := l1 ++ l2) in *.
      assert (Hlen1 : length cs1 <= n).
      { assert (length cs = S (length cs1)).
        { rewrite Hcs. unfold cs1. rewrite !length_app. simpl. lia. }
        lia. }
      set (R := make_mol (conns_as_atoms cs1 ++ a)) in *.
      assert (HpermA : Permutation (conns_as_atoms cs ++ a)
                                   (AConn x y :: conns_as_atoms cs1 ++ a)).
      { change (AConn x y :: conns_as_atoms cs1 ++ a)
          with ((AConn x y :: conns_as_atoms cs1) ++ a).
        apply Permutation_app_tail.
        change (AConn x y :: conns_as_atoms cs1)
          with (conns_as_atoms ((x,y) :: cs1)).
        apply Permutation_map. exact Hperm. }
      assert (HTeq : T ==m TMol (TAtom (AConn x y)) R).
      { unfold T, R.
        change (TMol (TAtom (AConn x y)) (make_mol (conns_as_atoms cs1 ++ a)))
          with (make_mol (AConn x y :: conns_as_atoms cs1 ++ a)).
        apply make_mol_perm; [ exact HpermA | exact WF ]. }
      assert (WF1 : wellformed_t (TMol (TAtom (AConn x y)) R))
        by exact (proj2 (congm_wellformed_t _ _ HTeq)).
      assert (WFR : wellformed_t R) by (apply wellformed_t_inj in WF1; tauto).
      assert (Hmeq : forall z, multiplicity (link_multiset T) z
                     = multiplicity (link_multiset (TMol (TAtom (AConn x y)) R)) z).
      { intros z. unfold T.
        change (TMol (TAtom (AConn x y)) R)
          with (make_mol (AConn x y :: conns_as_atoms cs1 ++ a)).
        apply (link_multiset_make_mol_perm _ _ HpermA). }
      assert (Hpeeled : exists cs2 a2,
                TMol (TAtom (AConn x y)) R ==m make_mol (conns_as_atoms cs2 ++ a2) /\
                Forall is_aatom a2 /\ length cs2 <= n).
      { destruct (Leq_dec x y) as [Exy | Exy].
        - subst y. exists cs1, a.
          split; [ | split; [ exact Ha | exact Hlen1 ] ].
          apply congm_trans' with (TMol TZero R).
          + apply congm_E5;
              [ exact WF1 | apply wellformed_t_TZero_l, WFR | apply congm_E7 ].
          + apply congm_E1, WFR.
        - assert (HmxT : multiplicity (link_multiset T) x
                         = 1 + multiplicity (link_multiset R) x).
          { rewrite Hmeq, mult_TMol_conn, Leq_dec_refl.
            destruct (Leq_dec y x); [ congruence | simpl; lia ]. }
          assert (HmyT : multiplicity (link_multiset T) y
                         = 1 + multiplicity (link_multiset R) y).
          { rewrite Hmeq, mult_TMol_conn, Leq_dec_refl.
            destruct (Leq_dec x y); [ congruence | simpl; lia ]. }
          assert (Hlex : multiplicity (link_multiset R) x <= 1).
          { assert (Hle := wellformed_t_mult_le _ x WF1). rewrite <- Hmeq in Hle. lia. }
          assert (Hley : multiplicity (link_multiset R) y <= 1).
          { assert (Hle := wellformed_t_mult_le _ y WF1). rewrite <- Hmeq in Hle. lia. }
          assert (Hor : multiplicity (link_multiset R) x = 1 \/
                        multiplicity (link_multiset R) y = 1).
          { destruct (classic (multiplicity (link_multiset R) x = 1)) as [K|K];
              [ left; exact K |].
            right.
            destruct (classic (multiplicity (link_multiset R) y = 1)) as [K2|K2];
              [ exact K2 |].
            exfalso. apply Hpeel. split; [ exact Exy | split; lia ]. }
          destruct Hor as [Hx1 | Hy1].
          + assert (WFsub : wellformed_t (substitute y x R)).
            { apply subst_wellformed_t; [ exact WFR |].
              assert (Hle := wellformed_t_mult_le _ y WFR). lia. }
            assert (HA : TMol (TAtom (AConn x y)) R ==m substitute y x R).
            { apply (congm_E9ex x y R); [ exact WF1 | exact WFsub | apply in_freelinks; exact Hx1 ]. }
            unfold R in HA.
            rewrite substitute_make_mol, subst_atoms_app,
                    subst_atoms_conns_as_atoms in HA.
            exists (map (subst_conn y x) cs1), (subst_atoms y x a).
            split; [ exact HA | split ].
            * apply subst_atoms_aatom, Ha.
            * rewrite length_map. exact Hlen1.
          + assert (WFsub : wellformed_t (substitute x y R)).
            { apply subst_wellformed_t; [ exact WFR |].
              assert (Hle := wellformed_t_mult_le _ x WFR). lia. }
            assert (HA : TMol (TAtom (AConn x y)) R ==m substitute x y R).
            { apply (congm_E9ex' x y R); [ exact WF1 | exact WFsub | apply in_freelinks; exact Hy1 ]. }
            unfold R in HA.
            rewrite substitute_make_mol, subst_atoms_app,
                    subst_atoms_conns_as_atoms in HA.
            exists (map (subst_conn x y) cs1), (subst_atoms x y a).
            split; [ exact HA | split ].
            * apply subst_atoms_aatom, Ha.
            * rewrite length_map. exact Hlen1. }
      destruct Hpeeled as [cs2 [a2 [HA2 [Ha2 Hlen2]]]].
      assert (WF2 : wellformed_t (make_mol (conns_as_atoms cs2 ++ a2)))
        by exact (proj2 (congm_wellformed_t _ _ HA2)).
      destruct (IH cs2 a2 Hlen2 Ha2 WF2) as [cs' [a' [Hstep [Ha' Hprop]]]].
      exists cs', a'. split; [ | split; [ exact Ha' | exact Hprop ] ].
      apply congm_trans' with (TMol (TAtom (AConn x y)) R); [ exact HTeq |].
      apply congm_trans' with (make_mol (conns_as_atoms cs2 ++ a2)); [ exact HA2 | exact Hstep ].
    + exists cs, a.
      split; [ apply congm_refl; exact WF |]. split; [ exact Ha |].
      intros c Hc. apply NNPP. intro Hbad. apply Hno. exists c. split; assumption.
Qed.

Lemma mult_list_count : forall l x,
  multiplicity (list_to_multiset l) x = count_occ Leq_dec l x.
Proof.
  induction l as [|y l IH]; intros x; [ reflexivity |].
  rewrite mult_cons, IH. simpl. destruct (Leq_dec y x); simpl; lia.
Qed.

Lemma flat_map_endpoints_conns : forall cs,
  flat_map (fun c => [fst c; snd c]) cs
  = flat_map links_of_atom (conns_as_atoms cs).
Proof.
  induction cs as [|[x y] cs IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma cong_open_nf : forall P, wellformed_t P ->
  exists cs a,
    P ==m make_mol (conns_as_atoms cs ++ a) /\
    Forall is_aatom a /\
    (forall c, In c cs ->
       fst c <> snd c /\
       In (fst c) (freelinks P) /\ In (snd c) (freelinks P)) /\
    NoDup (flat_map (fun c => [fst c; snd c]) cs).
Proof.
  intros P WF.
  destruct (get_connectors (flatten_atoms P)) as [cs0 a0] eqn:Egc.
  assert (Hperm : Permutation (flatten_atoms P) (conns_as_atoms cs0 ++ a0))
    by (apply get_connectors_perm; exact Egc).
  assert (Hf : P ==m make_mol (flatten_atoms P)) by (apply cong_flatten; exact WF).
  assert (WFf : wellformed_t (make_mol (flatten_atoms P)))
    by (apply wellformed_t_flatten_make_mol; exact WF).
  assert (Hp : make_mol (flatten_atoms P) ==m make_mol (conns_as_atoms cs0 ++ a0))
    by (apply make_mol_perm; [ exact Hperm | exact WFf ]).
  assert (Ha0 : Forall is_aatom a0).
  { assert (H := get_connectors_atoms_aatom (flatten_atoms P)).
    rewrite Egc in H. exact H. }
  assert (WF0 : wellformed_t (make_mol (conns_as_atoms cs0 ++ a0)))
    by exact (proj2 (congm_wellformed_t _ _ Hp)).
  destruct (peel_conns (length cs0) cs0 a0 (le_n _) Ha0 WF0)
    as [cs [a [Hstep [Ha Hprop]]]].
  set (nf := make_mol (conns_as_atoms cs ++ a)) in *.
  assert (HPeq : P ==m nf).
  { apply congm_trans' with (make_mol (flatten_atoms P)); [ exact Hf |].
    apply congm_trans' with (make_mol (conns_as_atoms cs0 ++ a0)); [ exact Hp | exact Hstep ]. }
  exists cs, a. split; [ exact HPeq | split; [ exact Ha | split ] ].
  - intros c Hc. destruct (Hprop c Hc) as [Hne [Hm1 Hm2]].
    split; [ exact Hne | split ].
    + apply in_freelinks. apply (proj2 (congm_mult1_iff P nf HPeq (fst c))). exact Hm1.
    + apply in_freelinks. apply (proj2 (congm_mult1_iff P nf HPeq (snd c))). exact Hm2.
  - apply (proj2 (NoDup_count_occ Leq_dec _)).
    intros Z.
    destruct (in_dec Leq_dec Z (flat_map (fun c => [fst c; snd c]) cs)) as [Hin|Hnin].
    2:{ rewrite (count_occ_not_In Leq_dec) in Hnin. lia. }
    assert (HZmult : multiplicity (link_multiset nf) Z = 1).
    { apply in_flat_map in Hin. destruct Hin as [c [Hc HZc]].
      destruct (Hprop c Hc) as [_ [Hm1 Hm2]].
      destruct HZc as [<-|[<-|[]]]; assumption. }
    assert (Hle : count_occ Leq_dec (flat_map (fun c => [fst c; snd c]) cs) Z
                  <= multiplicity (link_multiset nf) Z).
    { unfold nf. unfold link_multiset. rewrite links_make_mol, flat_map_app.
      rewrite mult_list_count, count_occ_app.
      rewrite flat_map_endpoints_conns. lia. }
    lia.
Qed.

(* ---- the nf shape: term_conns / node_atoms of  make_mol (conns_as_atoms cs ++ a) ---- *)

Lemma term_conns_conns_as_atoms : forall cs,
  flat_map (fun a => match a with AConn x y => [(x, y)] | AAtom _ _ => [] end)
           (conns_as_atoms cs) = cs.
Proof.
  induction cs as [|[x y] cs IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma flat_map_conns_aatom : forall a,
  Forall is_aatom a ->
  flat_map (fun a => match a with AConn x y => [(x, y)] | AAtom _ _ => [] end) a = [].
Proof.
  induction a as [|h a IH]; intros H; [ reflexivity |].
  inversion H as [|? ? Hh Ha]; subst.
  destruct h as [p ls|x y]; [ simpl; apply IH; exact Ha | destruct Hh ].
Qed.

Lemma filter_conns_as_atoms : forall cs,
  filter (fun a => match a with AAtom _ _ => true | AConn _ _ => false end)
         (conns_as_atoms cs) = [].
Proof.
  induction cs as [|[x y] cs IH]; simpl; [ reflexivity | exact IH ].
Qed.

Lemma filter_aatom_id : forall a,
  Forall is_aatom a ->
  filter (fun a => match a with AAtom _ _ => true | AConn _ _ => false end) a = a.
Proof.
  induction a as [|h a IH]; intros H; [ reflexivity |].
  inversion H as [|? ? Hh Ha]; subst.
  destruct h as [p ls|x y]; [ simpl; rewrite IH; [ reflexivity | exact Ha ] | destruct Hh ].
Qed.

Lemma term_conns_nf : forall cs a,
  Forall is_aatom a ->
  term_conns (make_mol (conns_as_atoms cs ++ a)) = cs.
Proof.
  intros cs a Ha. unfold term_conns.
  rewrite flatten_make_mol, flat_map_app.
  rewrite term_conns_conns_as_atoms, flat_map_conns_aatom by exact Ha.
  apply app_nil_r.
Qed.

Lemma node_atoms_nf : forall cs a,
  Forall is_aatom a ->
  node_atoms (make_mol (conns_as_atoms cs ++ a)) = a.
Proof.
  intros cs a Ha. unfold node_atoms.
  rewrite flatten_make_mol, filter_app.
  rewrite filter_conns_as_atoms, filter_aatom_id by exact Ha.
  reflexivity.
Qed.

(* ---- matchings (NoDup endpoints) ---- *)

Definition endpoints (c : list (Link * Link)) : list Link :=
  flat_map (fun p => [fst p; snd p]) c.

Lemma nodup_app_disjoint : forall {A} (l l' : list A) x,
  NoDup (l ++ l') -> In x l -> In x l' -> False.
Proof.
  induction l as [|a l IH]; intros l' x H Hl Hl'; [ contradiction |].
  simpl in H. inversion H as [|? ? Hnin Hnd]; subst.
  destruct Hl as [->|Hl].
  - apply Hnin, in_or_app. right. exact Hl'.
  - eapply IH; eauto.
Qed.

Lemma matching_endpoint_unique : forall c p1 p2 z,
  NoDup (endpoints c) ->
  In p1 c -> In p2 c ->
  In z [fst p1; snd p1] -> In z [fst p2; snd p2] ->
  p1 = p2.
Proof.
  intros c p1 p2 z Hnd H1 H2 Hz1 Hz2.
  destruct (classic (p1 = p2)) as [E|Hne]; [ exact E |]. exfalso.
  apply in_split in H1. destruct H1 as [L1 [L2 Hc]].
  subst c. unfold endpoints in Hnd. rewrite flat_map_app in Hnd. simpl in Hnd.
  set (E1 := flat_map (fun p : Link*Link => [fst p; snd p]) L1) in *.
  set (E2 := flat_map (fun p : Link*Link => [fst p; snd p]) L2) in *.
  assert (Hp2 : In p2 (L1 ++ L2)).
  { apply in_app_or in H2. destruct H2 as [H2|[H2|H2]];
      [ apply in_or_app; auto | congruence | apply in_or_app; auto ]. }
  assert (HzLR : In z (E1 ++ E2)).
  { apply in_app_or in Hp2. apply in_or_app.
    destruct Hp2 as [Hp2|Hp2]; [ left | right ];
      apply in_flat_map; exists p2; auto. }
  apply in_app_or in HzLR. destruct HzLR as [HzL|HzR].
  - eapply nodup_app_disjoint with (l := E1) (l' := [fst p1; snd p1] ++ E2);
      [ exact Hnd | exact HzL | apply in_or_app; left; exact Hz1 ].
  - eapply nodup_app_disjoint with (l := E1 ++ [fst p1; snd p1]) (l' := E2);
      [ rewrite <- app_assoc; exact Hnd
      | apply in_or_app; right; exact Hz1
      | exact HzR ].
Qed.

Lemma In_endpoints_l : forall c x y, In (x,y) c -> In x (endpoints c).
Proof.
  intros c x y H. unfold endpoints. apply in_flat_map. exists (x,y); split; auto. left; auto.
Qed.

Lemma In_endpoints_r : forall c x y, In (x,y) c -> In y (endpoints c).
Proof.
  intros c x y H. unfold endpoints. apply in_flat_map. exists (x,y); split; auto. right; left; auto.
Qed.

(* in a NoDup-endpoint matching, a shared endpoint forces equal pairs *)
Lemma matching_no_share : forall c x z y,
  NoDup (endpoints c) -> In (x,z) c -> In (z,y) c -> x = y.
Proof.
  intros c x z y Hnd Hxz Hzy.
  assert (E : (x,z) = (z,y)).
  { apply (matching_endpoint_unique c (x,z) (z,y) z Hnd Hxz Hzy);
      [ right; left; reflexivity | left; reflexivity ]. }
  inversion E; subst; reflexivity.
Qed.

Lemma matching_no_share_ll : forall c x z y,
  NoDup (endpoints c) -> In (z,x) c -> In (z,y) c -> x = y.
Proof.
  intros c x z y Hnd H1 H2.
  assert (E : (z,x) = (z,y)).
  { apply (matching_endpoint_unique c (z,x) (z,y) z Hnd H1 H2);
      left; reflexivity. }
  inversion E; subst; reflexivity.
Qed.

Lemma matching_no_share_rr : forall c x z y,
  NoDup (endpoints c) -> In (x,z) c -> In (y,z) c -> x = y.
Proof.
  intros c x z y Hnd H1 H2.
  assert (E : (x,z) = (y,z)).
  { apply (matching_endpoint_unique c (x,z) (y,z) z Hnd H1 H2);
      right; left; reflexivity. }
  inversion E; subst; reflexivity.
Qed.

Lemma edge_eq_matching_fwd : forall c x y,
  NoDup (endpoints c) ->
  edge_eq c x y -> x = y \/ In (x,y) c \/ In (y,x) c.
Proof.
  intros c x y Hnd H. unfold edge_eq in H.
  induction H as [x y HR | x | x y H IH | x m w H1 IH1 H2 IH2].
  - right; left; exact HR.
  - left; reflexivity.
  - destruct IH as [->|[K|K]];
      [ left; reflexivity | right; right; exact K | right; left; exact K ].
  - destruct IH1 as [Em|[A|A]].
    + subst m. exact IH2.
    + destruct IH2 as [Em|[B|B]].
      * subst m. right; left; exact A.
      * left. exact (matching_no_share c x m w Hnd A B).
      * left. exact (matching_no_share_rr c x m w Hnd A B).
    + destruct IH2 as [Em|[B|B]].
      * subst m. right; right; exact A.
      * left. exact (matching_no_share_ll c x m w Hnd A B).
      * left. exact (eq_sym (matching_no_share c w m x Hnd B A)).
Qed.

Lemma edge_eq_matching : forall c x y,
  NoDup (endpoints c) -> x <> y ->
  (edge_eq c x y <-> In (x,y) c \/ In (y,x) c).
Proof.
  intros c x y Hnd Hxy. split.
  - intro H. destruct (edge_eq_matching_fwd c x y Hnd H) as [E|D];
      [ contradiction | exact D ].
  - intros [K|K]; [ apply edge_eq_step | apply edge_eq_step' ]; exact K.
Qed.

Lemma congm_cong_r : forall P Q Q',
  wellformed_t (TMol P Q) -> wellformed_t (TMol P Q') ->
  Q ==m Q' -> TMol P Q ==m TMol P Q'.
Proof.
  intros P Q Q' W W' H.
  assert (WQP : wellformed_t (TMol Q P)).
  { apply wellformed_t_link_multiset with (TMol P Q); [ | exact W ].
    intro a. rewrite !multiplicity_mol. lia. }
  assert (WQ'P : wellformed_t (TMol Q' P)).
  { apply wellformed_t_link_multiset with (TMol P Q'); [ | exact W' ].
    intro a. rewrite !multiplicity_mol. lia. }
  apply congm_trans' with (TMol Q P); [ apply congm_E2; exact W |].
  apply congm_trans' with (TMol Q' P); [ | apply congm_E2; exact WQ'P ].
  apply congm_E5; [ exact WQP | exact WQ'P | exact H ].
Qed.

Lemma endpoints_app : forall c1 c2,
  endpoints (c1 ++ c2) = endpoints c1 ++ endpoints c2.
Proof. intros. unfold endpoints. apply flat_map_app. Qed.

Lemma endpoints_cons : forall x y c,
  endpoints ((x,y) :: c) = x :: y :: endpoints c.
Proof. reflexivity. Qed.

Lemma NoDup_endpoints_mid : forall L1 x y L2,
  NoDup (endpoints (L1 ++ (x,y) :: L2)) ->
  NoDup (endpoints (L1 ++ L2)).
Proof.
  intros L1 x y L2 H.
  rewrite endpoints_app, endpoints_cons in H.
  rewrite endpoints_app.
  apply NoDup_remove_1 in H.
  apply NoDup_remove_1 in H.
  exact H.
Qed.

Lemma NoDup_endpoints_mid' : forall L1 c L2,
  NoDup (endpoints (L1 ++ c :: L2)) -> NoDup (endpoints (L1 ++ L2)).
Proof. intros L1 [x y] L2. apply NoDup_endpoints_mid. Qed.

Lemma matching_reorder : forall M1 M2 A,
  NoDup (endpoints M1) -> NoDup (endpoints M2) ->
  length M1 = length M2 ->
  (forall x y, In (x,y) M1 -> In (x,y) M2 \/ In (y,x) M2) ->
  wellformed_t (make_mol (conns_as_atoms M1 ++ A)) ->
  wellformed_t (make_mol (conns_as_atoms M2 ++ A)) ->
  make_mol (conns_as_atoms M1 ++ A) ==m make_mol (conns_as_atoms M2 ++ A).
Proof.
  induction M1 as [|[x y] M1 IH]; intros M2 A Hnd1 Hnd2 Hlen Hpair WF1 WF2.
  - destruct M2 as [|c M2];
      [ apply congm_refl; exact WF1 | simpl in Hlen; discriminate ].
  - assert (Hxy : In (x,y) M2 \/ In (y,x) M2) by (apply Hpair; left; reflexivity).
    rewrite endpoints_cons in Hnd1.
    rewrite NoDup_cons_iff in Hnd1. destruct Hnd1 as [Hxnin Hnd1].
    rewrite NoDup_cons_iff in Hnd1. destruct Hnd1 as [Hynin Hnd1M].
    assert (Hxne : x <> y) by (intro E; subst y; apply Hxnin; left; reflexivity).
    assert (WFleft : wellformed_t (TMol (TAtom (AConn x y))
                       (make_mol (conns_as_atoms M1 ++ A)))).
    { change (TMol (TAtom (AConn x y)) (make_mol (conns_as_atoms M1 ++ A)))
        with (make_mol (AConn x y :: conns_as_atoms M1 ++ A)).
      change (AConn x y :: conns_as_atoms M1 ++ A)
        with (conns_as_atoms ((x,y)::M1) ++ A). exact WF1. }
    assert (WFR1 : wellformed_t (make_mol (conns_as_atoms M1 ++ A)))
      by (apply wellformed_t_inj in WFleft; tauto).
    assert (Hsplit : exists L1 L2 (flip:bool),
              M2 = L1 ++ (if flip then (y,x) else (x,y)) :: L2).
    { destruct Hxy as [Hin|Hin]; apply in_split in Hin;
        destruct Hin as [L1 [L2 HM2]];
        [ exists L1, L2, false | exists L1, L2, true ]; exact HM2. }
    destruct Hsplit as [L1 [L2 [flip HM2]]].
    set (c0 := if flip then (y,x) else (x,y)) in *.
    assert (HM2c : M2 = L1 ++ c0 :: L2) by exact HM2. clear HM2. rename HM2c into HM2.
    assert (Hc0x : fst c0 = (if flip then y else x)) by (destruct flip; reflexivity).
    assert (Hc0y : snd c0 = (if flip then x else y)) by (destruct flip; reflexivity).
    assert (HpermM2 : Permutation M2 (c0 :: (L1 ++ L2))).
    { rewrite HM2. apply Permutation_sym. apply Permutation_middle. }
    assert (HpermA : Permutation (conns_as_atoms M2 ++ A)
                     (AConn (fst c0) (snd c0) :: conns_as_atoms (L1 ++ L2) ++ A)).
    { change (AConn (fst c0) (snd c0) :: conns_as_atoms (L1 ++ L2) ++ A)
        with ((AConn (fst c0) (snd c0) :: conns_as_atoms (L1 ++ L2)) ++ A).
      apply Permutation_app_tail.
      change (AConn (fst c0) (snd c0) :: conns_as_atoms (L1 ++ L2))
        with (conns_as_atoms (c0 :: L1 ++ L2)).
      apply Permutation_map. exact HpermM2. }
    set (R2 := make_mol (conns_as_atoms (L1 ++ L2) ++ A)) in *.
    assert (HM2eq : make_mol (conns_as_atoms M2 ++ A)
              ==m TMol (TAtom (AConn (fst c0) (snd c0))) R2).
    { unfold R2.
      change (TMol (TAtom (AConn (fst c0) (snd c0)))
                   (make_mol (conns_as_atoms (L1 ++ L2) ++ A)))
        with (make_mol (AConn (fst c0) (snd c0) :: conns_as_atoms (L1 ++ L2) ++ A)).
      apply make_mol_perm; [ exact HpermA | exact WF2 ]. }
    assert (WFm : wellformed_t (TMol (TAtom (AConn (fst c0) (snd c0))) R2))
      by exact (proj2 (congm_wellformed_t _ _ HM2eq)).
    assert (WFR2 : wellformed_t R2) by (apply wellformed_t_inj in WFm; tauto).
    assert (Wmid : wellformed_t (TMol (TAtom (AConn x y)) R2)).
    { apply wellformed_t_link_multiset with (TMol (TAtom (AConn (fst c0) (snd c0))) R2);
        [ | exact WFm ].
      intro a. rewrite !multiplicity_mol, !multiplicity_TAtom_AConn.
      rewrite Hc0x, Hc0y. destruct flip; lia. }
    assert (Hnd2' : NoDup (endpoints (L1 ++ L2))).
    { eapply NoDup_endpoints_mid'. rewrite <- HM2. exact Hnd2. }
    assert (Hlen' : length M1 = length (L1 ++ L2)).
    { assert (length M2 = S (length (L1 ++ L2)))
        by (rewrite HM2, !length_app; simpl; lia).
      simpl in Hlen. lia. }
    assert (Hpair' : forall a b, In (a,b) M1 ->
                     In (a,b) (L1 ++ L2) \/ In (b,a) (L1 ++ L2)).
    { intros a b Hab.
      assert (Hne1 : (a,b) <> (x,y)).
      { intro E. injection E as -> ->. apply Hxnin. right.
        exact (In_endpoints_l M1 x y Hab). }
      assert (Hne2 : (a,b) <> (y,x)).
      { intro E. injection E as -> ->. apply Hxnin. right.
        exact (In_endpoints_r M1 y x Hab). }
      assert (Hin2 : In (a,b) M2 \/ In (b,a) M2)
        by (apply Hpair; right; exact Hab).
      rewrite HM2 in Hin2.
      destruct Hin2 as [K|K]; apply in_app_or in K; destruct K as [K|[K|K]].
      - left. apply in_or_app. left. exact K.
      - exfalso. unfold c0 in K. destruct flip;
          [ apply Hne2 | apply Hne1 ]; congruence.
      - left. apply in_or_app. right. exact K.
      - right. apply in_or_app. left. exact K.
      - exfalso. unfold c0 in K. destruct flip;
          [ apply Hne1 | apply Hne2 ]; congruence.
      - right. apply in_or_app. right. exact K. }
    assert (Hrec : make_mol (conns_as_atoms M1 ++ A) ==m R2)
      by exact (IH (L1 ++ L2) A Hnd1M Hnd2' Hlen' Hpair' WFR1 WFR2).
    change (conns_as_atoms ((x,y)::M1) ++ A)
      with (AConn x y :: (conns_as_atoms M1 ++ A)).
    change (make_mol (AConn x y :: (conns_as_atoms M1 ++ A)))
      with (TMol (TAtom (AConn x y)) (make_mol (conns_as_atoms M1 ++ A))).
    apply congm_trans' with (TMol (TAtom (AConn (fst c0) (snd c0))) R2).
    2:{ apply congm_sym'. exact HM2eq. }
    apply congm_trans' with (TMol (TAtom (AConn x y)) R2).
    { apply congm_cong_r; [ exact WFleft | exact Wmid | exact Hrec ]. }
    destruct flip.
    + rewrite Hc0x, Hc0y. apply congm_conn_sym. exact Wmid.
    + rewrite Hc0x, Hc0y. apply congm_refl.
      apply wellformed_t_link_multiset with (TMol (TAtom (AConn x y)) R2);
        [ intro a; reflexivity | exact Wmid ].
Qed.

Lemma flat_map_links_conns : forall M,
  flat_map links_of_atom (conns_as_atoms M) = endpoints M.
Proof.
  induction M as [|[x y] M IH]; simpl; [ reflexivity | rewrite IH; reflexivity ].
Qed.

Lemma links_nf_split : forall M A,
  links (make_mol (conns_as_atoms M ++ A))
  = endpoints M ++ flat_map links_of_atom A.
Proof.
  intros M A. rewrite links_make_mol, flat_map_app, flat_map_links_conns. reflexivity.
Qed.

Lemma endpoints_length : forall M,
  length (endpoints M) = 2 * length M.
Proof.
  induction M as [|[x y] M IH]; simpl; [ reflexivity | rewrite IH; lia ].
Qed.

Lemma mult_nf_notendpoint : forall M A Z,
  ~ In Z (endpoints M) ->
  multiplicity (link_multiset (make_mol (conns_as_atoms M ++ A))) Z
  = multiplicity (link_multiset (make_mol A)) Z.
Proof.
  intros M A Z HZ. unfold link_multiset.
  rewrite links_nf_split, links_make_mol.
  rewrite !mult_list_count, count_occ_app.
  rewrite (count_occ_not_In Leq_dec) in HZ. lia.
Qed.

Lemma matching_endpoints_disjoint_A : forall M A,
  (forall c, In c M ->
     In (fst c) (freelinks (make_mol (conns_as_atoms M ++ A))) /\
     In (snd c) (freelinks (make_mol (conns_as_atoms M ++ A)))) ->
  NoDup (endpoints M) ->
  forall Z, In Z (endpoints M) -> ~ In Z (flat_map links_of_atom A).
Proof.
  intros M A Hfr Hnd Z HZ HZA.
  assert (Hm1 : multiplicity (link_multiset (make_mol (conns_as_atoms M ++ A))) Z = 1).
  { unfold endpoints in HZ. apply in_flat_map in HZ.
    destruct HZ as [c [Hc Hzc]].
    destruct (Hfr c Hc) as [H1 H2].
    apply in_freelinks in H1. apply in_freelinks in H2.
    destruct Hzc as [<-|[<-|[]]]; assumption. }
  unfold link_multiset in Hm1. rewrite links_nf_split, mult_list_count in Hm1.
  rewrite count_occ_app in Hm1.
  assert (HcM : count_occ Leq_dec (endpoints M) Z >= 1).
  { apply (count_occ_In Leq_dec). exact HZ. }
  assert (HcA : count_occ Leq_dec (flat_map links_of_atom A) Z >= 1).
  { apply (count_occ_In Leq_dec). exact HZA. }
  lia.
Qed.

Lemma giso_matching_pairs : forall M1 A1 M2 A2 I,
  (forall c, In c M1 -> fst c <> snd c /\ In (fst c) I /\ In (snd c) I) ->
  NoDup (endpoints M2) ->
  Forall is_aatom A1 -> Forall is_aatom A2 ->
  (forall Z W, In Z I -> In W I ->
     (edge_eq (term_conns (make_mol (conns_as_atoms M1 ++ A1))) Z W
      <-> edge_eq (term_conns (make_mol (conns_as_atoms M2 ++ A2))) Z W)) ->
  forall a b, In (a,b) M1 -> In (a,b) M2 \/ In (b,a) M2.
Proof.
  intros M1 A1 M2 A2 I Hfr Hnd2 HA1 HA2 Hff a b Hab.
  destruct (Hfr (a,b) Hab) as [Hne [Ha Hb]]. simpl in Hne, Ha, Hb.
  assert (E1 : edge_eq (term_conns (make_mol (conns_as_atoms M1 ++ A1))) a b).
  { rewrite term_conns_nf by exact HA1. apply edge_eq_step. exact Hab. }
  assert (E2 : edge_eq (term_conns (make_mol (conns_as_atoms M2 ++ A2))) a b)
    by (apply (Hff a b Ha Hb); exact E1).
  rewrite term_conns_nf in E2 by exact HA2.
  apply (edge_eq_matching M2 a b Hnd2 Hne) in E2. exact E2.
Qed.

Lemma matching_same_len : forall M1 M2,
  NoDup (endpoints M1) -> NoDup (endpoints M2) ->
  (forall a b, In (a,b) M1 -> In (a,b) M2 \/ In (b,a) M2) ->
  (forall a b, In (a,b) M2 -> In (a,b) M1 \/ In (b,a) M1) ->
  length M1 = length M2.
Proof.
  intros M1 M2 Hnd1 Hnd2 H12 H21.
  assert (mk : forall (Ma Mb : list (Link*Link)),
             (forall a b, In (a,b) Ma -> In (a,b) Mb \/ In (b,a) Mb) ->
             incl (endpoints Ma) (endpoints Mb)).
  { intros Ma Mb H Z HZ. unfold endpoints in HZ |- *.
    apply in_flat_map in HZ. destruct HZ as [[a b] [Hab Hz]].
    destruct (H a b Hab) as [K|K]; apply in_flat_map;
      [ exists (a,b) | exists (b,a) ]; (split; [ exact K |]);
      simpl in Hz |- *; tauto. }
  assert (Hlen : length (endpoints M1) = length (endpoints M2)).
  { apply PeanoNat.Nat.le_antisymm; apply NoDup_incl_length; auto. }
  rewrite !endpoints_length in Hlen. lia.
Qed.

Lemma matching_endpoints_incl : forall M1 M2,
  (forall a b, In (a,b) M1 -> In (a,b) M2 \/ In (b,a) M2) ->
  incl (endpoints M1) (endpoints M2).
Proof.
  intros M1 M2 H Z HZ. unfold endpoints in HZ |- *.
  apply in_flat_map in HZ. destruct HZ as [[a b] [Hab Hz]].
  destruct (H a b Hab) as [K|K]; apply in_flat_map;
    [ exists (a,b) | exists (b,a) ]; (split; [ exact K |]); simpl in Hz |- *; tauto.
Qed.

Lemma edge_eq_not_endpoint : forall c x y,
  ~ In x (endpoints c) -> (edge_eq c x y <-> x = y).
Proof.
  intros c x y HX. split.
  - intros H. destruct (edge_eq_endpoints c x y H) as [E|[Hin _]];
      [ exact E | contradiction ].
  - intros ->. apply edge_eq_refl.
Qed.

Lemma meq_nodup_same : forall l1 l2,
  NoDup l1 -> NoDup l2 -> incl l1 l2 -> incl l2 l1 ->
  meq (list_to_multiset l1) (list_to_multiset l2).
Proof.
  intros l1 l2 Hnd1 Hnd2 H12 H21 Z.
  rewrite !mult_list_count.
  destruct (in_dec Leq_dec Z l1) as [Hin1|Hnin1].
  - rewrite (proj1 (NoDup_count_occ' Leq_dec l1) Hnd1 Z Hin1).
    rewrite (proj1 (NoDup_count_occ' Leq_dec l2) Hnd2 Z (H12 Z Hin1)).
    reflexivity.
  - rewrite (proj1 (count_occ_not_In Leq_dec l1 Z) Hnin1).
    destruct (in_dec Leq_dec Z l2) as [Hin2|Hnin2].
    + exfalso. apply Hnin1, H21, Hin2.
    + rewrite (proj1 (count_occ_not_In Leq_dec l2 Z) Hnin2). reflexivity.
Qed.

Lemma wellformed_t_make_mol_app_r : forall l1 l2,
  wellformed_t (make_mol (l1 ++ l2)) -> wellformed_t (make_mol l2).
Proof.
  intros l1 l2 H.
  apply wellformed_t_mol_make_mol in H.
  apply wellformed_t_inj in H. tauto.
Qed.

Lemma In_flat_map_links_portlink : forall ns i k X,
  portlink ns i k = Some X -> In X (flat_map links_of_atom ns).
Proof.
  intros ns i k X H. unfold portlink in H.
  destruct (nth_error ns i) as [a|] eqn:Ea; [ | discriminate ].
  destruct a as [p ls|x y]; [ | discriminate ].
  apply in_flat_map. exists (AAtom p ls). split.
  - eapply nth_error_In; eauto.
  - simpl. eapply nth_error_In; eauto.
Qed.

Lemma giso_nf_congm : forall M1 A1 M2 A2,
  Forall is_aatom A1 -> Forall is_aatom A2 ->
  wellformed_t (make_mol (conns_as_atoms M1 ++ A1)) ->
  wellformed_t (make_mol (conns_as_atoms M2 ++ A2)) ->
  (forall c, In c M1 -> fst c <> snd c /\
     In (fst c) (freelinks (make_mol (conns_as_atoms M1 ++ A1))) /\
     In (snd c) (freelinks (make_mol (conns_as_atoms M1 ++ A1)))) ->
  NoDup (endpoints M1) ->
  (forall c, In c M2 -> fst c <> snd c /\
     In (fst c) (freelinks (make_mol (conns_as_atoms M2 ++ A2))) /\
     In (snd c) (freelinks (make_mol (conns_as_atoms M2 ++ A2)))) ->
  NoDup (endpoints M2) ->
  (forall Z, In Z (freelinks (make_mol (conns_as_atoms M1 ++ A1)))
        <-> In Z (freelinks (make_mol (conns_as_atoms M2 ++ A2)))) ->
  giso (freelinks (make_mol (conns_as_atoms M1 ++ A1)))
       (make_mol (conns_as_atoms M1 ++ A1))
       (make_mol (conns_as_atoms M2 ++ A2)) ->
  make_mol (conns_as_atoms M1 ++ A1) ==m make_mol (conns_as_atoms M2 ++ A2).
Proof.
  intros M1 A1 M2 A2 HA1 HA2 WF1 WF2 Hm1 Hnd1 Hm2 Hnd2 Hfree Hiso.
  set (nf1 := make_mol (conns_as_atoms M1 ++ A1)) in *.
  set (nf2 := make_mol (conns_as_atoms M2 ++ A2)) in *.
  destruct Hiso as (f & g & Hgf & Hfg & Hdom & Hcod & Hfun & Hconn & Hifc & Hff).
  assert (TC1 : term_conns nf1 = M1) by (apply term_conns_nf; exact HA1).
  assert (TC2 : term_conns nf2 = M2) by (apply term_conns_nf; exact HA2).
  assert (NA1 : node_atoms nf1 = A1) by (apply node_atoms_nf; exact HA1).
  assert (NA2 : node_atoms nf2 = A2) by (apply node_atoms_nf; exact HA2).
  assert (NB1 : node_atoms (make_mol A1) = A1) by (apply (node_atoms_nf [] A1 HA1)).
  assert (NB2 : node_atoms (make_mol A2) = A2) by (apply (node_atoms_nf [] A2 HA2)).
  assert (TB1 : term_conns (make_mol A1) = []) by (apply (term_conns_nf [] A1 HA1)).
  assert (TB2 : term_conns (make_mol A2) = []) by (apply (term_conns_nf [] A2 HA2)).
  assert (WFA1 : wellformed_t (make_mol A1))
    by (apply wellformed_t_make_mol_app_r with (conns_as_atoms M1); exact WF1).
  assert (WFA2 : wellformed_t (make_mol A2))
    by (apply wellformed_t_make_mol_app_r with (conns_as_atoms M2); exact WF2).
  assert (CFA1 : connector_free (make_mol A1)) by (apply connector_free_make_mol; exact HA1).
  assert (CFA2 : connector_free (make_mol A2)) by (apply connector_free_make_mol; exact HA2).
  assert (Hdisj1 : forall Z, In Z (endpoints M1) -> ~ In Z (flat_map links_of_atom A1)).
  { apply matching_endpoints_disjoint_A; [ | exact Hnd1 ].
    intros c Hc. destruct (Hm1 c Hc) as [_ [P Q]]. split; assumption. }
  assert (Hdisj2 : forall Z, In Z (endpoints M2) -> ~ In Z (flat_map links_of_atom A2)).
  { apply matching_endpoints_disjoint_A; [ | exact Hnd2 ].
    intros c Hc. destruct (Hm2 c Hc) as [_ [P Q]]. split; assumption. }
  assert (HP12 : forall a b, In (a,b) M1 -> In (a,b) M2 \/ In (b,a) M2)
    by exact (giso_matching_pairs M1 A1 M2 A2 (freelinks nf1) Hm1 Hnd2 HA1 HA2 Hff).
  assert (Hff' : forall Z W, In Z (freelinks nf2) -> In W (freelinks nf2) ->
     (edge_eq (term_conns nf2) Z W <-> edge_eq (term_conns nf1) Z W)).
  { intros Z W HZ HW. apply (proj2 (Hfree Z)) in HZ. apply (proj2 (Hfree W)) in HW.
    apply iff_sym, Hff; assumption. }
  assert (HP21 : forall a b, In (a,b) M2 -> In (a,b) M1 \/ In (b,a) M1)
    by exact (giso_matching_pairs M2 A2 M1 A1 (freelinks nf2) Hm2 Hnd1 HA2 HA1 Hff').
  assert (HLen : length M1 = length M2)
    by (apply matching_same_len; assumption).
  assert (Hep12 : incl (endpoints M1) (endpoints M2))
    by (apply matching_endpoints_incl; exact HP12).
  assert (Hep21 : incl (endpoints M2) (endpoints M1))
    by (apply matching_endpoints_incl; exact HP21).
  (* --- Part (ii): giso between the connector-free cores --- *)
  assert (Hfree_A : forall Z, In Z (freelinks (make_mol A1)) ->
                    In Z (freelinks nf1) /\ ~ In Z (endpoints M1)).
  { intros Z HZ. apply in_freelinks in HZ.
    assert (HZlk : In Z (flat_map links_of_atom A1)).
    { assert (In Z (links (make_mol A1)))
        by (apply in_links_link_multiset; lia).
      rewrite links_make_mol in H. exact H. }
    assert (HnZ : ~ In Z (endpoints M1)).
    { intro C. apply (Hdisj1 Z C HZlk). }
    split; [ | exact HnZ ].
    apply in_freelinks. unfold nf1.
    rewrite (mult_nf_notendpoint M1 A1 Z HnZ). exact HZ. }
  assert (HgisoA : giso (freelinks (make_mol A1)) (make_mol A1) (make_mol A2)).
  { exists f, g.
    split; [ exact Hgf | ]. split; [ exact Hfg | ].
    split.
    { intros i Hi. rewrite NB2. rewrite NB1 in Hi.
      specialize (Hdom i). rewrite NA1, NA2 in Hdom. auto. }
    split.
    { intros j Hj. rewrite NB1. rewrite NB2 in Hj.
      specialize (Hcod j). rewrite NA1, NA2 in Hcod. auto. }
    split.
    { intros i. rewrite NB1, NB2. specialize (Hfun i). rewrite NA1, NA2 in Hfun. exact Hfun. }
    split.
    { intros i k j l Xik Xjl Yik Yjl P1 P2 P3 P4.
      rewrite TB1, TB2. rewrite !edge_eq_nil.
      rewrite NB1 in P1, P2. rewrite NB2 in P3, P4.
      assert (Q := Hconn i k j l Xik Xjl Yik Yjl).
      rewrite NA1 in Q. rewrite NA2 in Q.
      specialize (Q P1 P2 P3 P4). rewrite TC1, TC2 in Q.
      assert (HnX1 : ~ In Xik (endpoints M1))
        by (intro C; apply (Hdisj1 _ C); apply (In_flat_map_links_portlink A1 i k); exact P1).
      assert (HnX2 : ~ In Xjl (endpoints M1))
        by (intro C; apply (Hdisj1 _ C); apply (In_flat_map_links_portlink A1 j l); exact P2).
      assert (HnY1 : ~ In Yik (endpoints M2))
        by (intro C; apply (Hdisj2 _ C); apply (In_flat_map_links_portlink A2 (f i) k); exact P3).
      assert (HnY2 : ~ In Yjl (endpoints M2))
        by (intro C; apply (Hdisj2 _ C); apply (In_flat_map_links_portlink A2 (f j) l); exact P4).
      rewrite (edge_eq_not_endpoint M1 Xik Xjl HnX1) in Q.
      rewrite (edge_eq_not_endpoint M2 Yik Yjl HnY1) in Q.
      exact Q. }
    split.
    { intros i k Z Xik Yik HZ P1 P3.
      rewrite TB1, TB2. rewrite !edge_eq_nil.
      destruct (Hfree_A Z HZ) as [HZf HnZ1].
      rewrite NB1 in P1. rewrite NB2 in P3.
      assert (Q := Hifc i k Z Xik Yik HZf).
      rewrite NA1 in Q. rewrite NA2 in Q.
      specialize (Q P1 P3). rewrite TC1, TC2 in Q.
      assert (HnX1 : ~ In Xik (endpoints M1))
        by (intro C; apply (Hdisj1 _ C); apply (In_flat_map_links_portlink A1 i k); exact P1).
      assert (HnY1 : ~ In Yik (endpoints M2))
        by (intro C; apply (Hdisj2 _ C); apply (In_flat_map_links_portlink A2 (f i) k); exact P3).
      assert (HnZ2 : ~ In Z (endpoints M2)) by (intro C; apply HnZ1, Hep21, C).
      rewrite (edge_eq_not_endpoint M1 Xik Z HnX1) in Q.
      rewrite (edge_eq_not_endpoint M2 Yik Z HnY1) in Q.
      exact Q. }
    { intros Z W HZ HW. rewrite TB1, TB2. reflexivity. } }
  assert (HA12 : make_mol A1 ==m make_mol A2)
    by (apply giso_cf_congm; assumption).
  (* --- Part (i)+(iii): assembly --- *)
  assert (Wconn12 : meq (link_multiset (make_mol (conns_as_atoms M1)))
                        (link_multiset (make_mol (conns_as_atoms M2)))).
  { unfold link_multiset. rewrite !links_make_mol, !flat_map_links_conns.
    apply meq_nodup_same; assumption. }
  assert (WmolM1A2 : wellformed_t (TMol (make_mol (conns_as_atoms M1)) (make_mol A2))).
  { apply wellformed_t_link_multiset with
      (TMol (make_mol (conns_as_atoms M2)) (make_mol A2)).
    - intro z. rewrite !multiplicity_mol. rewrite (Wconn12 z). reflexivity.
    - apply wellformed_t_mol_make_mol. exact WF2. }
  assert (WnfM1A2 : wellformed_t (make_mol (conns_as_atoms M1 ++ A2))).
  { apply wellformed_t_link_multiset with
      (TMol (make_mol (conns_as_atoms M1)) (make_mol A2)).
    - apply link_multiset_mol_make_mol.
    - exact WmolM1A2. }
  apply congm_trans' with (make_mol (conns_as_atoms M1 ++ A2)).
  - (* nf1 ==m make_mol (conns_as_atoms M1 ++ A2) via congr on the A part *)
    apply congm_trans' with (TMol (make_mol (conns_as_atoms M1)) (make_mol A1)).
    { apply make_mol_app. exact WF1. }
    apply congm_trans' with (TMol (make_mol (conns_as_atoms M1)) (make_mol A2)).
    { assert (WmolM1A1 : wellformed_t (TMol (make_mol (conns_as_atoms M1)) (make_mol A1)))
        by (apply wellformed_t_mol_make_mol; exact WF1).
      apply congm_cong_r; [ exact WmolM1A1 | exact WmolM1A2 | exact HA12 ]. }
    apply congm_sym'. apply make_mol_app. exact WnfM1A2.
  - (* matching reorder *)
    apply matching_reorder; try assumption.
Qed.

(* The open reverse direction: an interface-preserving graph isomorphism
   between two wellformed terms with the same free links implies structural
   congruence. *)
Theorem giso_congm : forall P Q,
  wellformed_t P -> wellformed_t Q ->
  (forall X, In X (freelinks P) <-> In X (freelinks Q)) ->
  giso (freelinks P) P Q -> P ==m Q.
Proof.
  intros P Q WFP WFQ Hfree Hiso.
  destruct (cong_open_nf P WFP) as (M1 & A1 & HPeq & HA1 & Hm1 & Hnd1).
  destruct (cong_open_nf Q WFQ) as (M2 & A2 & HQeq & HA2 & Hm2 & Hnd2).
  set (nf1 := make_mol (conns_as_atoms M1 ++ A1)) in *.
  set (nf2 := make_mol (conns_as_atoms M2 ++ A2)) in *.
  assert (WF1 : wellformed_t nf1) by exact (proj2 (congm_wellformed_t _ _ HPeq)).
  assert (WF2 : wellformed_t nf2) by exact (proj2 (congm_wellformed_t _ _ HQeq)).
  assert (HfnP : forall X, In X (freelinks nf1) <-> In X (freelinks P))
    by (intros X; symmetry; apply congm_freelinks; exact HPeq).
  assert (HfnQ : forall X, In X (freelinks nf2) <-> In X (freelinks Q))
    by (intros X; symmetry; apply congm_freelinks; exact HQeq).
  assert (Hfnf : forall X, In X (freelinks nf1) <-> In X (freelinks nf2)).
  { intros X. rewrite HfnP, HfnQ. apply Hfree. }
  assert (Hisonf : giso (freelinks nf1) nf1 nf2).
  { apply giso_trans with P.
    - apply giso_sym.
      assert (H := congm_giso _ _ HPeq).
      apply (giso_iface_ext (freelinks P) (freelinks nf1)); [ | exact H ].
      intros X. symmetry. apply HfnP.
    - apply giso_trans with Q.
      + apply (giso_iface_ext (freelinks P) (freelinks nf1)); [ | exact Hiso ].
        intros X. symmetry. apply HfnP.
      + assert (H := congm_giso _ _ HQeq).
        apply (giso_iface_ext (freelinks Q) (freelinks nf1)); [ | exact H ].
        intros X. split; intro K.
        * apply (proj2 (HfnQ X)) in K. apply (proj2 (Hfnf X)) in K. exact K.
        * apply (proj1 (Hfnf X)) in K. apply (proj1 (HfnQ X)) in K. exact K. }
  assert (Hm1' : forall c, In c M1 -> fst c <> snd c /\
     In (fst c) (freelinks nf1) /\ In (snd c) (freelinks nf1)).
  { intros c Hc. destruct (Hm1 c Hc) as [Hne [Ha Hb]].
    split; [ exact Hne | split; apply HfnP; assumption ]. }
  assert (Hm2' : forall c, In c M2 -> fst c <> snd c /\
     In (fst c) (freelinks nf2) /\ In (snd c) (freelinks nf2)).
  { intros c Hc. destruct (Hm2 c Hc) as [Hne [Ha Hb]].
    split; [ exact Hne | split; apply HfnQ; assumption ]. }
  assert (Hmid : nf1 ==m nf2).
  { exact (giso_nf_congm M1 A1 M2 A2 HA1 HA2 WF1 WF2 Hm1' Hnd1 Hm2' Hnd2 Hfnf Hisonf). }
  apply congm_trans' with nf1; [ exact HPeq |].
  apply congm_trans' with nf2; [ exact Hmid |].
  apply congm_sym'. exact HQeq.
Qed.

(* Full correspondence for terms sharing an interface (design note's
   Theorem 3, without the closedness restriction). *)
Theorem congm_giso_iff : forall P Q,
  wellformed_t P -> wellformed_t Q ->
  (forall X, In X (freelinks P) <-> In X (freelinks Q)) ->
  (P ==m Q <-> giso (freelinks P) P Q).
Proof.
  intros P Q WFP WFQ Hfree. split.
  - apply congm_giso.
  - apply giso_congm; assumption.
Qed.

Corollary cong_giso_iff : forall P Q,
  wellformed_t P -> wellformed_t Q ->
  (forall X, In X (freelinks P) <-> In X (freelinks Q)) ->
  (P == Q <-> giso (freelinks P) P Q).
Proof.
  intros P Q WFP WFQ Hfree.
  rewrite congm_cong_iff. apply congm_giso_iff; assumption.
Qed.

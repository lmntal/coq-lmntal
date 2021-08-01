Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

Require Import Multiset.

(* Module LMNtalSyntax. *)
(* Inductive Link := 
  | LLink (name:string). *)
Definition Link := string.

(* Definition Atom : Type := string * list Link. *)

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

(* Check GMol (GAtom "p1" (cons "X" (cons "Y" nil))) GZero. *)
(* p1(X,Y), 0 *)

Inductive Rule : Type :=
  | React (lhs rhs:Graph).

Inductive RuleSet : Type :=
  | RZero
  | RRule (rule:Rule)
  | RMol (r1 r2:RuleSet).

Coercion RRule : Rule >-> RuleSet.
Coercion GAtom : Atom >-> Graph.
(* Coercion LLink : string >-> Link. *)

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
(* Notation "" := GZero (in custom lmntal at level 0, only parsing).
Notation "" := RZero (in custom lmntal at level 0, only parsing). *)
(* Notation "0" := GZero (in custom lmntal at level 0, only printing).
Notation "0" := RZero (in custom lmntal at level 0, only printing). *)
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

(* Fixpoint count_map_sub (ls unique : list Link) : list (Link * nat) :=
  match unique with
  | [] => []
  | h::t => (h, count_occ Leq_dec ls h)::(count_map_sub ls t)
  end.

Definition count_map (g: Graph) : list (Link * nat) :=
  count_map_sub (links g) (unique_links g).

Compute count_map_sub ["X";"Y";"X";"Y";"F"] ["X";"Y";"F"]. *)

Definition list_to_multiset (l:list Link) : multiset Link :=
  fold_right (fun x a => munion (SingletonBag eq Leq_dec x) a) (EmptyBag Link) l.

Definition link_multiset (g: Graph) : multiset Link :=
  list_to_multiset (links g).

Definition freelinks (g: Graph) : list Link := fold_right 
  (fun x a => if (Nat.eqb (multiplicity (link_multiset g) x) 1) then x::a else a) [] (unique_links g).

Definition locallinks (g: Graph) : list Link := fold_right
  (fun x a => if (Nat.eqb (multiplicity (link_multiset g) x) 2) then x::a else a) [] (unique_links g).

Compute freelinks {{ "p"("X","Y"),"q"("Y","X","F") }}.
Compute locallinks {{ "p"("X","Y"),"q"("Y","X","F") }}.

Check forallb.

(* A graph is well-formed if each link name occurs at most twice in it *)
Definition wellformed_g (g:Graph) : Prop :=
  forallb (fun x => Nat.leb (multiplicity (link_multiset g) x) 2) (unique_links g) = true.
  (* fold_right (fun x a => (multiplicity (link_multiset g) x) <= 2 /\ a) True (unique_links g). *)

Lemma wellformed_g_forall: forall g, wellformed_g g <->
  forall x, In x (unique_links g) -> (multiplicity (link_multiset g) x) <= 2.
Proof.
  intros g.
  split.
  - intros H1 x H2.
    unfold wellformed_g in H1. rewrite forallb_forall in H1.
    apply H1 in H2. rewrite PeanoNat.Nat.leb_le in H2.
    apply H2.
  - intros H1. unfold wellformed_g. rewrite forallb_forall.
    intros x H2. rewrite PeanoNat.Nat.leb_le.
    apply H1. apply H2.
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

Reserved Notation "p ~= q" (at level 40).

Inductive cong : Graph -> Graph -> Prop :=
  | cong_E1 : forall P, {{GZero, P}} ~= P
  | cong_E2 : forall P Q, {{P, Q}} ~= {{Q, P}}
  | cong_E3 : forall P Q R, {{P, (Q, R)}} ~= {{(P, Q), R}}
  | cong_E4 : forall P X Y, In X (locallinks P) -> P ~= {{ P[Y/X] }}
  | cong_E5 : forall P P' Q, P ~= P' -> {{ P,Q }} ~= {{ P',Q }}
  | cong_E7 : forall X, {{ X = X }} ~= GZero
  | cong_E8 : forall X Y, {{ X = Y }} ~= {{ Y = X }}
  | cong_E9 : forall X Y (A:Atom), In X (freelinks A) ->
                {{ X = Y, A }} ~= {{ A[Y/X] }}
  | cong_refl : forall P, P ~= P
  | cong_trans : forall P Q R, P ~= Q -> Q ~= R -> P ~= R
  | cong_sym : forall P Q, P ~= Q -> Q ~= P
  where "p '~=' q" := (cong p q).

(* Reserved Notation "p '==' q" (at level 40).
Inductive cong_wf : Graph -> Graph -> Prop :=
  | cong_wf_step : forall P Q,  wellformed_g P -> wellformed_g Q ->
                                  P ~= Q -> P == Q
  | cong_wf_trans : forall P Q R, P == Q -> Q == R -> P == R
  where "p '==' q" := (cong_wf p q). *)

(* Lemma cong_wf_sym : forall P Q, P == Q -> Q == P.
Proof.
  intros P Q H. *)
  

Definition cong_wf (p q : Graph) := wellformed_g p /\ wellformed_g q /\ p ~= q.
Notation "p '==' q" := (cong_wf p q) (at level 40).

Lemma cong_wf_refl : forall P, wellformed_g P -> P == P.
Proof.
  intros P. unfold cong_wf.
  split. { auto. }
  split. { auto. }
  apply cong_refl.
Qed.

Lemma cong_wf_trans: forall P Q R, P == Q -> Q == R -> P == R.
Proof.
  intros P Q R [HPQP [HPQQ HPQ]] [HQRQ [HQRR HQR]].
  unfold cong_wf.
  split. { apply HPQP. }
  split. { apply HQRR. }
  apply (cong_trans _ Q _).
  - apply HPQ.
  - apply HQR.
Qed.

Lemma cong_wf_sym: forall P Q, P == Q -> Q == P.
Proof.
  intros P Q [HP [HQ H]].
  split. { apply HQ. }
  split. { apply HP. }
  apply cong_sym.
  apply H.
Qed.

Example cong_example : {{ "p"("X","X") }} == {{ "p"("Y","Y") }}.
Proof.
  unfold cong_wf. unfold wellformed_g.
  simpl.
  split. { auto. }
  split. { auto. }
  assert (H: ({{ "p"("Y","Y") }}:Graph) = {{ "p"("X","X")["Y"/"X"] }}).
  { reflexivity. }
  rewrite H.
  apply cong_E4.
  simpl. left. reflexivity.
Qed.

Reserved Notation "p '~[' r ']->' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).

Inductive rrel : Rule -> Graph -> Graph -> Prop :=
  | rrel_R1 : forall G1 G1' G2 r,
                G1 ~[ r ]-> G1' -> {{G1,G2}} ~[ r ]-> {{G1',G2}}
  | rrel_R3 : forall G1 G1' G2 G2' r,
                G2 == G1 -> G1 ~[ r ]-> G1' -> G1' == G2' ->
                G2 ~[ r ]-> G2'
  | rrel_R6 : forall T U, T ~[ T :- U ]-> U
  where "p '~[' r ']->' q" := (rrel r p q).

Definition rrel_wf (r:Rule) (p q:Graph) : Prop :=
  wellformed_g p /\ wellformed_g q /\ wellformed_r r
    /\ p ~[ r ]-> q.
Notation "p '-[' r ']->' q" := (rrel_wf r p q) (at level 40, r custom lmntal at level 99, p constr, q constr at next level).

Reserved Notation "p '-[' r ']->*' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Inductive rrel_wf_rep : Rule -> Graph -> Graph -> Prop :=
  | rrel_wf_rep_refl : forall r a b, a == b -> a -[ r ]->* b
  | rrel_wf_rep_step : forall r a b c, a -[ r ]->* b -> b -[ r ]-> c -> a -[ r ]->* c
  where "p '-[' r ']->*' q" := (rrel_wf_rep r p q).

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
  unfold rrel_wf.
  split. { unfold wellformed_g. simpl. auto. }
  split. { unfold wellformed_g. simpl. auto. }
  split. { unfold wellformed_r. unfold link_list_eq. simpl. apply meq_refl. }
  apply rrel_R3 with (G1:={{"b" ("X"), "c" ("X"), "a" ()}}) (G1':={{"d" (), "a" ()}}).
  - unfold cong_wf. simpl.
    split. { unfold wellformed_g. simpl. auto. }
    split. { unfold wellformed_g. simpl. auto. }
    apply cong_trans with (Q:={{"a"(),("b"("Z"),"c"("Z"))}}).
    + apply cong_sym. apply cong_E3.
    + apply cong_trans with (Q:={{"b" ("Z"), "c" ("Z"), "a" ()}}).
      * apply cong_E2.
      * assert (H1: {{"b"("X"), "c"("X"), "a"()}}={{("b"("Z"), "c"("Z"),"a"())["X"/"Z"] }}).
        { reflexivity. }
        rewrite H1.
        apply cong_E4.
        simpl. left. reflexivity.
  - apply rrel_R1. apply rrel_R6.
  - unfold cong_wf. simpl.
    split. { reflexivity. }
    split. { reflexivity. }
    apply cong_E2.
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
  (* intros l1.
  induction l1 as [|h1 t1 IH].
  - intros l2. destruct l2 as [|h2 t2].
    + reflexivity.
    + reflexivity.
  - intros l2. simpl. destruct l2 as [|h2 t2].
    + reflexivity.
    + simpl. destruct (h1 =? h2) eqn:E.
      * rewrite eqb_sym in E.
        rewrite E. apply IH.
      * rewrite eqb_sym in E.
        rewrite E. *)

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

Lemma in_unique_links:
  forall g x, In x (unique_links g) <-> In x (links g).
Proof.
  intros g x.
  unfold unique_links.
  apply nodup_In.
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
    + apply H. rewrite in_unique_links. rewrite links_mol.
      rewrite in_unique_links in H1. left. apply H1.
  - rewrite wellformed_g_forall. intros x H1.
    apply PeanoNat.Nat.le_trans with (multiplicity (link_multiset {{G1, G2}}) x).
    + apply multiplicity_munionR with (link_multiset G1).
      apply link_multiset_mol.
    + apply H. rewrite in_unique_links. rewrite links_mol.
      rewrite in_unique_links in H1. right. apply H1.
Qed.

(* 
Lemma wellformed_g_cong :
  forall P Q, wellformed_g P -> cong P Q -> wellformed_g Q.
Proof.
  intros P Q HwfP Hcong.
  rewrite wellformed_g_forall.
  rewrite wellformed_g_forall in HwfP.
  induction Hcong; auto.
  - intros x H.
    assert (A: meq (link_multiset {{P,Q}}) (link_multiset {{Q,P}})).
    { apply meq_trans with (munion (link_multiset {{P}}) (link_multiset {{Q}})).
      { apply link_multiset_mol. }
      apply meq_trans with (munion (link_multiset {{Q}}) (link_multiset {{P}})).
      { apply munion_comm. }
      apply meq_sym.
      apply link_multiset_mol. }
    unfold meq in A. rewrite <- A.
    apply HwfP.
    apply in_unique_links. apply links_mol.
    apply in_unique_links in H. apply links_mol in H.
    destruct H; auto.
  - intros x H.
    assert (A: meq (link_multiset {{P,Q,R}}) (link_multiset {{P,(Q,R)}})).
    { apply meq_trans with (munion (link_multiset {{P,Q}}) (link_multiset {{R}})).
      { apply link_multiset_mol. }
      apply meq_trans with (munion (munion (link_multiset P) (link_multiset Q)) (link_multiset R)).
      { apply meq_left. apply link_multiset_mol. }
      apply meq_trans with (munion (link_multiset P) (munion (link_multiset Q) (link_multiset R))).
      { apply munion_ass. }
      apply meq_trans with (munion (link_multiset P) (link_multiset {{Q,R}})).
      { apply meq_right. apply meq_sym. apply link_multiset_mol. }
      apply meq_sym. apply link_multiset_mol.
    }
    rewrite A. apply HwfP.
    apply in_unique_links. repeat rewrite links_mol.
    apply in_unique_links in H. repeat rewrite links_mol in H.
    destruct H as [[|]|]; auto.
  - intros x H1. admit.
  - admit.
  - admit.
  - admit.
  - admit.
Abort. *)
    

Theorem inv_rrel: forall r G G', G' -[r]-> G
  -> let inv_r := inv r in G -[ inv_r ]-> G'.
Proof.
  intros r G G' H. simpl.
  unfold rrel_wf. unfold rrel_wf in H.
  destruct H as [H1 [H2 [H3 H4]]].
  split. { apply H2. }
  split. { apply H1. }
  split. { simpl. destruct r. apply link_list_eq_commut.
           simpl in H3. apply H3. }
  simpl.
  induction H4 as [G1 G1' G2 r' IH1 IH2 | G1 G1' G2 G2' r' IH1 IH2 IH3 IH4 | T U].
  - (* Case (R1) *)
    apply rrel_R1. apply IH2.
    + apply wellformed_g_inj with (G2:=G2). apply H1.
    + apply wellformed_g_inj with (G2:=G2). apply H2.
    + apply H3.
  - (* Case (R3) *)
    apply rrel_R3 with (G1') (G1).
    + apply cong_wf_sym. apply IH4.
    + apply IH3.
      * destruct IH1 as [_ [H _]]. apply H.
      * destruct IH4 as [H [_ _]]. apply H.
      * apply H3.
    + apply cong_wf_sym. apply IH1.
  - (* Case (R6) *)
    apply rrel_R6.
Qed.

Lemma inv_inv : forall r, inv (inv r) = r.
Proof.
  intros [lhs rhs]. reflexivity.
Qed.

Theorem inv_rrel_iff: forall r G G', G' -[r]-> G
  <-> let inv_r := inv r in G -[ inv_r ]-> G'.
Proof.
  intros r G G'.
  split.
  - apply inv_rrel.
  - simpl. intros H. apply inv_rrel in H.
    rewrite inv_inv in H.
    apply H.
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

(* End LMNtalSyntax. *)

Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

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

Fixpoint count_map_sub (ls unique : list Link) : list (Link * nat) :=
  match unique with
  | [] => []
  | h::t => (h, count_occ Leq_dec ls h)::(count_map_sub ls t)
  end.

Definition count_map (g: Graph) : list (Link * nat) :=
  count_map_sub (links g) (unique_links g).

Compute count_map_sub ["X";"Y";"X";"Y";"F"] ["X";"Y";"F"].

Definition freelinks (g: Graph) : list Link := fold_right 
  (fun p a => match p with
    (x,n) => if (Nat.eqb n 1) then x::a else a
  end) [] (count_map g).

Definition locallinks (g: Graph) : list Link := fold_right 
(fun p a => match p with
  (x,n) => if (Nat.eqb n 2) then x::a else a
end) [] (count_map g).

Compute freelinks {{ "p"("X","Y"),"q"("Y","X","F") }}.
Compute locallinks {{ "p"("X","Y"),"q"("Y","X","F") }}.

(* A graph is well-formed if each link name occurs at most twice in it *)
Definition wellformed_g (g:Graph) : bool := fold_right
  (fun p a => match p with
    (x,n) => if (Nat.leb n 2) then a else false
  end) true (count_map g).

Fixpoint link_list_eqb (l1 l2 : list Link) : bool :=
  match l1,l2 with
  | [],[] => true
  | [],_ => false
  | h1::t1,_ => match (remove_one h1 l2) with
                | (true, l) => link_list_eqb t1 l
                | (false, _) => false
                end
  end.

Definition wellformed_r (r:Rule) : bool :=
  match r with
  | {{lhs :- rhs}} => link_list_eqb (freelinks lhs) (freelinks rhs)
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
  | cong_E1 : forall P, {{GZero, P}} == P
  | cong_E2 : forall P Q, {{P, Q}} == {{Q, P}}
  | cong_E3 : forall P Q R, {{P, (Q, R)}} == {{(P, Q), R}}
  | cong_E4 : forall P X Y, In X (locallinks P) -> P == {{ P[Y/X] }}
  | cong_E5 : forall P P' Q, P == P' -> {{ P,Q }} == {{ P',Q }}
  | cong_E7 : forall X, {{ X = X }} == GZero
  | cong_E8 : forall X Y, {{ X = Y }} == {{ Y = X }}
  | cong_E9 : forall X Y (A:Atom), In X (freelinks A) ->
                {{ X = Y, A }} == {{ A[Y/X] }}
  | cong_refl : forall P, P == P
  | cong_trans : forall P Q R, P == Q -> Q == R -> P == R
  | cong_sym : forall P Q, P == Q -> Q == P
  where "p '==' q" := (cong p q).

Definition cong_wf (p q : Graph) := wellformed_g p = true /\ wellformed_g q = true /\ cong p q.
Notation "p '==' q" := (cong_wf p q) (at level 40).

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

Reserved Notation "p '-[' r ']->' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).

Inductive rrel : Rule -> Graph -> Graph -> Prop :=
  | rrel_R1 : forall G1 G1' G2 r,
                G1 -[ r ]-> G1' -> {{G1,G2}} -[ r ]-> {{G1',G2}}
  | rrel_R3 : forall G1 G1' G2 G2' r,
                G2 == G1 -> G1 -[ r ]-> G1' -> G1' == G2' ->
                G2 -[ r ]-> G2'
  | rrel_R6 : forall T U, T -[ T :- U ]-> U
  where "p '-[' r ']->' q" := (rrel r p q).

Definition rrel_wf (r:Rule) (p q:Graph) : Prop :=
  wellformed_g p = true /\ wellformed_g q = true /\ wellformed_r r = true
    /\ rrel r p q.
Notation "p '-[' r ']->' q" := (rrel_wf r p q).

Reserved Notation "p '=[' r ']=>' q" (at level 40, r custom lmntal at level 99, p constr, q constr at next level).
Fixpoint rrel_ruleset (rs : RuleSet) (p q : Graph) : Prop :=
  match rs with
  | RZero => False
  | RRule r => p -[ r ]-> q
  | RMol a b => p =[ a ]=> q /\ p =[ b ]=> q
  end
  where "p '=[' rs ']=>' q" := (rrel_ruleset rs p q).

Example rrel_example :
  {{ "a"(), "b"("Z"), "c"("Z") }}
  -[ "b"("X"),"c"("X") :- "d"() ]->
  {{ "a"(), "d"() }}.
Proof.
  unfold rrel_wf.
  split. { auto. }
  split. { auto. }
  split. { auto. }
  apply rrel_R3 with (G1:={{"b" ("X"), "c" ("X"), "a" ()}}) (G1':={{"d" (), "a" ()}}).
  - unfold cong_wf. simpl.
    split. { reflexivity. }
    split. { reflexivity. }
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

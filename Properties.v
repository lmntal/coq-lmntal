Require Import String.
Open Scope string_scope.
Require Import List.
Import ListNotations.
Open Scope list_scope.

From LMNTAL Require Export LMNtalSyntax.
From LMNTAL Require Export LMNtalGraph.
From LMNTAL Require Export Util.

(* Fixpoint term_to_atom_list2 (t: LMNtalSyntax.Graph) : list LMNtalSyntax.Atom :=
  match t with
  | GZero => []
  | GAtom atom => [atom]
  | GMol g1 g2 => (term_to_atom_list2 g1)++(term_to_atom_list2 g2)
  end. *)

(* Check LMNtalSyntax.Graph. *)

Definition nat_dec := PeanoNat.Nat.eq_dec.

Definition atom_list_to_empty_atoms (al: list (nat * LMNtalSyntax.Atom)) :=
  fold_right (fun x g => match x with
  | (atomid, AAtom name links) => newatom g atomid name (length links)
  end) LMNtalGraph.empty al.

Definition fuse_ports p1 p2 g :=
  match p1, p2 with
  | null, null => g
  | null, p => setport_force g p null
  | p, null => setport_force g p null
  | p1, p2 => newlink_force p1 p2 g
  end.

Definition fuse_connector (na: (nat * LMNtalSyntax.Atom)) (g : LMNtalGraph.Graph) :=
  match na with
  | (atomid, AAtom name links) => 
      if string_dec name "="
      then match links with
        | [_; _] =>
          let p1 := getport g (link atomid 0) in
          let p2 := getport g (link atomid 1) in
          match p1, p2 with
          | Some x, Some y => fuse_ports x y (removeatom g atomid)
          | _, _ => g
          end
        | _ => g 
        end 
      else g
  end.

Definition fuse_connectors (al : list (nat * LMNtalSyntax.Atom)) (g : LMNtalGraph.Graph) :=
  fold_right fuse_connector g al.

Definition newlink_ports (x:(string * list (nat * nat))) (g:LMNtalGraph.Graph) :=
  match x with
  | (_, [(id1,pos1); (id2,pos2)]) => match newlink (link id1 pos1) (link id2 pos2) g with
    | Some g' => g'
    | None => g
    end
  | _ => g
  end.

Definition make_links (g: LMNtalGraph.Graph) (pl : list (string * list (nat * nat))) :=
  fold_right newlink_ports g pl.

Definition atom_list_to_raw_graph (al: list LMNtalSyntax.Atom) : LMNtalGraph.Graph :=
  let ial := add_indices O al in
  let g := atom_list_to_empty_atoms ial in
  let pl := atom_list_to_port_list al in
    make_links g pl.

Definition atom_list_to_graph (al: list LMNtalSyntax.Atom) : LMNtalGraph.Graph :=
  let ial := add_indices O al in
    fuse_connectors ial (atom_list_to_raw_graph al).

Definition term_to_graph (t: LMNtalSyntax.Graph) : LMNtalGraph.Graph :=
  atom_list_to_graph (term_to_atom_list t).

(* 任意の置換を互換の積にする *)
(* Fixpoint decompose_sub (l : list nat) (i : nat) :=
  if Nat.ltb i (length l) then
    let j := nth i l 0 in
      if nat_dec i j
      then decompose_sub l (S i)
      else
        (i, j) :: decompose_sub (swap l i j) (S i)
  else []. *)
Fixpoint decompose_sub (l rest : list nat) (i : nat) :=
  match rest with
  | [] => []
  | _ :: t =>
    let j := nth i l 0 in
      if nat_dec i j
      then decompose_sub l t (S i)
      else
        (i, j) :: decompose_sub (swap i j l) t (S i)
  end.

Definition decompose l := decompose_sub l l 0.

Definition make_graph_swap_list P Q :=
  let sp := count_atoms P in
  let sq := count_atoms Q in
  decompose ((seq sp sq) ++ (seq 0 sp)).

(* Compute (decompose [4;5;1;2;0;3]). *)

Lemma term_to_graph_gzero :
  term_to_graph GZero = empty.
Proof. auto. Qed.

Lemma term_to_graph_gzero_p :
  forall P, term_to_graph {{ GZero, P }} = term_to_graph P.
Proof. auto. Qed.

Lemma term_to_atom_list_p_gzero:
  forall P, term_to_atom_list {{ P, GZero }} = term_to_atom_list P.
Proof.
  unfold term_to_atom_list.
  symmetry.
  apply app_nil_end.
Qed.

Lemma term_to_graph_p_gzero :
  forall P, term_to_graph {{ P, GZero }} = term_to_graph P.
Proof.
  intro.
  induction P.
  - auto.
  - auto.
  - unfold term_to_graph. f_equal. apply term_to_atom_list_p_gzero.
Qed.

Lemma nth_error_nil :
  forall i A, @nth_error A [] i = None.
Proof.
  intros i A.
  induction i.
  - reflexivity.
  - reflexivity.
Qed.

Lemma swap_nil :
  forall i j A, @swap A i j [] = [].
Proof.
  intros i j A.
  unfold swap. simpl.
  rewrite nth_error_nil.
  reflexivity.
Qed.

Lemma swap_singleton :
  forall i j A (a:A), @swap A i j [a] = [a].
Proof.
  intros i j A a.
  unfold swap. simpl.
  destruct i.
  - simpl. destruct j.
    + simpl. reflexivity.
    + simpl. rewrite nth_error_nil.
      reflexivity.
  - simpl. rewrite nth_error_nil. reflexivity.
Qed.

Lemma swap_atomid_empty :
  forall i1 i2 n, swap_atomid i1 i2 empty n = empty n.
Proof.
  intros i1 i2 n.
  unfold empty. unfold swap_atomid.
  destruct (nat_dec n i1); auto.
  destruct (nat_dec n i2); auto.
Qed.

Lemma nth_error_cons_S :
  forall A h t n, @nth_error A (h::t) (S n) = @nth_error A t n.
Proof. auto. Qed.

Lemma swap_cons_S :
  forall A h t i1 i2, @swap A (S i1) (S i2) (h::t) = h::(@swap A i1 i2 t).
Proof.
  intros A h t i1 i2.
  unfold swap. simpl.
  destruct (nth_error t i1); destruct (nth_error t i2); auto.
  repeat rewrite PeanoNat.Nat.sub_0_r.
  reflexivity.
Qed.

Lemma swap_refl :
  forall A n l, @swap A n n l = l.
Proof.
  intros A n l.
  generalize dependent n.
  induction l.
  - intros n. unfold swap. simpl. rewrite nth_error_nil. reflexivity.
  - intros n. destruct n; auto.
    rewrite swap_cons_S. rewrite IHl. reflexivity.
Qed.

Fixpoint subst_nth_snd {I A} n (x:A) (l: list (I * A)) : list (I * A) :=
  match l with 
  | (i,h) :: t => if PeanoNat.Nat.eq_dec n 0
              then (i,x) :: t
              else (i,h) :: (subst_nth_snd (n-1) x t)
  | [] => []
  end.

Definition swap_snd {I A} i j (l: list (I*A)) :=
  let xi := nth_error l i in 
  let xj := nth_error l j in
  match xi, xj with
  | Some (_,yi), Some (_,yj) => subst_nth_snd i yj (subst_nth_snd j yi l)
  | _, _ => l
  end.

Lemma swap_snd_nil :
  forall {I A} i1 i2, @swap_snd I A i1 i2 [] = [].
Proof.
  intros I A i1 i2.
  unfold swap_snd. rewrite nth_error_nil.
  reflexivity.
Qed.

Lemma swap_snd_cons_S:
  forall I A h t i1 i2,
    @swap_snd I A (S i1) (S i2) (h::t) = h::(@swap_snd I A i1 i2 t).
Proof.
  intros I A [hi h] t i1 i2.
  unfold swap_snd. simpl.
  destruct (nth_error t i1) as [[xi x]|];
  destruct (nth_error t i2) as [[yi y]|]; auto.
  repeat rewrite PeanoNat.Nat.sub_0_r.
  reflexivity.
Qed.

Lemma nth_error_add_indices_Some :
  forall A i l n (p:nat*A),
  nth_error (add_indices i l) n = Some p <->
  exists x, nth_error l n = Some x /\ p = (i+n, x).
Proof.
  intros A i l.
  generalize dependent i.
  induction l.
  - intros i n [ni a].
    split.
    + intros H. exists a.
      simpl in H. rewrite nth_error_nil in H.
      discriminate H.
    + intros H. rewrite nth_error_nil in H.
      destruct H. destruct H. discriminate H.
  - intros i n [ni y].
    split.
    + intros H. exists y.
      destruct n.
      * simpl. simpl in H.
        inversion H. rewrite PeanoNat.Nat.add_0_r.
        auto.
      * simpl. simpl in H.
        rewrite <- PeanoNat.Nat.add_succ_comm.
        apply IHl in H.
        destruct H. destruct H. inversion H0.
        auto.
    + intros H. simpl.
      destruct n.
      * simpl.
        destruct H. simpl in H.
        destruct H. inversion H0.
        inversion H. rewrite PeanoNat.Nat.add_0_r.
        reflexivity.
      * simpl.
        apply IHl. destruct H. simpl in H.
        destruct H. inversion H0.
        exists x. split; auto.
        rewrite PeanoNat.Nat.add_succ_comm.
        reflexivity.
Qed.

Lemma nth_error_add_indices_None :
  forall A i (l:list A) n,
  nth_error (add_indices i l) n = None <->
  nth_error l n = None.
Proof.
  intros A i l n.
  generalize dependent n.
  generalize dependent i.
  induction l.
  - intros i n. simpl. split.
    + intros H. apply nth_error_nil.
    + intros H. apply nth_error_nil.
  - intros i n. simpl. split.
    + intros H. destruct n.
      * simpl in H. discriminate H.
      * simpl. apply IHl in H. apply H.
    + intros H. destruct n.
      * simpl in H. discriminate H.
      * simpl. simpl in H. apply IHl. apply H.
Qed.

Lemma add_indices_subst_nth :
  forall {A} n i (a:A) l,
    add_indices n (subst_nth i a l)
    = subst_nth_snd i a (add_indices n l).
Proof.
  intros A n i a l.
  generalize dependent i.
  generalize dependent n.
  induction l; auto.
  intros n i.
  destruct i; auto.
  simpl. f_equal.
  apply IHl.
Qed.

Lemma add_indices_swap :
  forall {A} n i1 i2 (l: list A),
    add_indices n (swap i1 i2 l) = swap_snd i1 i2 (add_indices n l).
Proof.
  intros A n i1 i2 l.
  generalize dependent i2.
  generalize dependent i1.
  generalize dependent n.
  induction l.
  - intros n i1 i2. rewrite swap_nil. simpl.
    rewrite swap_snd_nil. reflexivity.
  - intros n i1 i2. destruct i1; destruct i2; auto; simpl.
    + unfold swap. unfold swap_snd.
      simpl. rewrite PeanoNat.Nat.sub_0_r.
      destruct (nth_error l i2) eqn:E1;
      destruct (nth_error (add_indices (S n) l) i2) eqn:E2; simpl; auto.
      * destruct p. apply nth_error_add_indices_Some in E2.
        destruct E2. rewrite add_indices_subst_nth.
        f_equal. f_equal. destruct H.
        inversion H0. rewrite H in E1. inversion E1.
        auto.
      * rewrite nth_error_add_indices_None in E2.
        rewrite E2 in E1. discriminate E1.
      * destruct p. apply nth_error_add_indices_Some in E2.
        destruct E2. destruct H. rewrite H in E1.
        discriminate E1.
    + unfold swap. unfold swap_snd.
      simpl. rewrite PeanoNat.Nat.sub_0_r.
      destruct (nth_error l i1) eqn:E1;
      destruct (nth_error (add_indices (S n) l) i1) eqn:E2; simpl; auto.
      * destruct p. rewrite add_indices_subst_nth.
        apply nth_error_add_indices_Some in E2.
        destruct E2. destruct H. inversion H0.
        rewrite E1 in H. inversion H.
        reflexivity.
      * apply nth_error_add_indices_None in E2.
        rewrite E2 in E1. discriminate E1.
      * apply nth_error_add_indices_Some in E2.
        destruct E2.
        destruct H. rewrite E1 in H. discriminate H.
    + rewrite swap_cons_S. simpl.
      rewrite swap_snd_cons_S. f_equal.
      apply IHl.
Qed.

(* Lemma atom_list_to_port_list_swap :
  forall 
    atom_list_to_port_list (swap i1 i2 l)
    = swap *)

Lemma atom_list_to_raw_graph_nil :
  forall n, atom_list_to_raw_graph [] n = None.
Proof.
  intros n.
  unfold atom_list_to_raw_graph.
  auto.
Qed.

Lemma atom_list_to_raw_graph_Some :
  forall l n,
    atom_list_to_raw_graph l n <> None
    <-> n < length l.
Proof.
  intros l.
  (* induction l; intros n; split; intros H.  *)
  (* - rewrite atom_list_to_raw_graph_nil in H.
    destruct H. reflexivity.
  - simpl in H. Search (_<0). apply PeanoNat.Nat.nlt_0_r in H.
    destruct H.
  -  *)
  intros n. split; intros H.
  - unfold atom_list_to_raw_graph in H.
    unfold make_links in H.
    unfold atom_list_to_empty_atoms in H.
Admitted.

Lemma swap_atomid_atom_list_to_raw_graph_swap :
  forall i1 i2 l,
    i1 < length l -> i2 < length l ->
      forall n, swap_atomid i1 i2 (atom_list_to_raw_graph (swap i1 i2 l)) n
      = atom_list_to_raw_graph l n.
Proof.
  intros i1 i2 l H1 H2 n.
  destruct (PeanoNat.Nat.eq_dec n i1) eqn:E1;
  destruct (PeanoNat.Nat.eq_dec n i2) eqn:E2.
  - rewrite <- e. rewrite <- e0.
    rewrite swap_atomid_n_n.
    rewrite swap_refl. reflexivity.
  - rewrite e. unfold swap_atomid. unfold bind.
    rewrite nat_eq_dec_refl.
    destruct (atom_list_to_raw_graph (swap i1 i2 l) i2) eqn:E3;
    destruct (atom_list_to_raw_graph l i1) eqn:E4; auto.
    + admit.
    + exfalso. admit.
    + exfalso. admit.
  -  
Admitted.

Lemma atom_list_to_raw_graph_atom_list_to_graph :
  forall l1 l2,
    atom_list_to_raw_graph l1 = atom_list_to_raw_graph l2 ->
    atom_list_to_graph l1 = atom_list_to_graph l2.
Proof.
  intros l1 l2 H.
  unfold atom_list_to_graph.
  rewrite H. 
  unfold atom_list_to_raw_graph in H.
Admitted.

Lemma swap_atomid_atom_list_to_graph_swap :
  forall i1 i2 l,
    i1 < length l -> i2 < length l ->
      forall n, swap_atomid i1 i2 (atom_list_to_graph (swap i1 i2 l)) n
      = atom_list_to_graph l n.
Proof.
  intros i1 i2 l.
  intros H1 H2 n.
  unfold atom_list_to_graph.
  unfold swap_atomid. unfold bind.
  destruct (PeanoNat.Nat.eq_dec n i1).
  - rewrite e. rewrite add_indices_swap.
Admitted.

  (* generalize dependent i2.
  generalize dependent i1.
  induction l; intros i1 i2 H1 H2 n.
  { rewrite swap_nil. unfold atom_list_to_graph.
    simpl. apply swap_atomid_empty. } *)

Lemma swap_atom_id_atom_list_to_graph :
  forall i1 i2 l,
    i1 < length l -> i2 < length l ->
      forall n, swap_atomid i1 i2 (atom_list_to_graph l) n
        = atom_list_to_graph (swap i1 i2 l) n.
Proof.
  intros i1 i2 l.
  generalize dependent i2.
  generalize dependent i1.
  induction l; intros i1 i2 H1 H2 n.
  { unfold atom_list_to_graph. rewrite swap_nil.
    simpl. apply swap_atomid_empty. }
  destruct i1; destruct i2.
  - rewrite swap_refl. rewrite swap_atomid_n_n.
    reflexivity.
  - unfold swap. simpl. unfold swap_atomid.
    destruct n; simpl.
    + simpl in H2. apply Lt.lt_S_n in H2.
      destruct (nth_error l i2) eqn:E.
      * rewrite PeanoNat.Nat.sub_0_r.
        unfold bind.
        unfold swap_atomid_atom.
        destruct (atom_list_to_graph (a :: l) (S i2)) eqn:E1.
        { unfold atom_list_to_graph. simpl.
          destruct a0 eqn:E2. destruct a1 eqn:E3.
          simpl. destruct (string_dec name "=").
          - destruct links; simpl.
            + unfold atom_list_to_port_list.
              simpl. unfold add_atom_to_port_list.
              simpl. destruct (add_indices 1 (subst_nth i2 a l)); simpl.
              * unfold newatom. unfold upd_graph.
                simpl. f_equal. unfold make_atom.
                f_equal.  }
      apply nth_error_Some in H2.
  
  (* destruct (nat_dec n i1);
  destruct (nat_dec n i2).
  - simpl. rewrite <- e0. rewrite <- e.
    unfold swap_atomid. rewrite nat_eq_dec_refl.
    rewrite swap_refl. reflexivity.
  - destruct i1; destruct i2.
    + rewrite swap_refl. *)
Admitted.
  

Lemma swap_atom_id_term_to_graph :
  forall i1 i2 P Q,
    i1 < length (term_to_atom_list P) ->
    i2 < length (term_to_atom_list P) ->
    swap i1 i2 (term_to_atom_list P) = term_to_atom_list Q
    -> isomorphic (swap_atomid i1 i2 (term_to_graph P)) (term_to_graph Q).
Proof.
  intros i1 i2 P Q H1 H2 H.
  exists []. intros n. simpl.
  unfold term_to_graph.
  rewrite <- H.

  (* generalize dependent i2.
  generalize dependent i1.
  induction P.
  - intros i1 i2 Q H. simpl in H.
    apply PeanoNat.Nat.nlt_0_r in H.
    contradiction H.
  - intros i1 i2 Q H1 H2. simpl in H1. simpl in H2.
    apply PeanoNat.Nat.lt_1_r in H1.
    apply PeanoNat.Nat.lt_1_r in H2.
    rewrite H1. rewrite H2.
    simpl. unfold swap. simpl. intros H.
    unfold term_to_graph.
    rewrite <- H. simpl.
    unfold isomorphic. exists [].
    unfold equiv. intros n.
    simpl. destruct n; auto.
  - intros i1 i2 Q H1 H2. simpl.
    intros H. unfold term_to_graph.
    rewrite <- H. simpl.
    exists [].
    simpl. intros n.
     *)
    
    (* rewrite swap_nil in H.
    unfold term_to_graph. simpl.
    rewrite <- H. unfold atom_list_to_graph.
    simpl. unfold isomorphic.
    exists [].
    intros n. unfold swap_atomid.
    unfold empty. simpl.
    destruct (nat_dec n i1).
    + auto.
    + destruct (nat_dec n i2).
      * auto.
      * auto.
  - intros Q H.
    simpl in H. rewrite swap_singleton in H.
    unfold term_to_graph.
    rewrite <- H. simpl.
    unfold isomorphic.
    unfold equiv.
    destruct (nat_dec i1 0).
    + destruct (nat_dec i2 0).
      * exists []. intros n.
        simpl. *)
Admitted.

Lemma swap_atomid_list_term_to_graph :
  forall P Q l,
    swap_list l (term_to_atom_list P) = term_to_atom_list Q
      -> equiv (swap_atomid_list l (term_to_graph P))
          (term_to_graph Q).
Proof.
  intros P Q l.
  generalize dependent Q.
  induction l.
  - intros Q H. simpl. simpl in H.
    unfold term_to_graph.
    rewrite H.
    unfold equiv.
    intros n.
    reflexivity.
  - intros Q H. simpl.
    destruct a as [i1 i2].
    simpl in H.
    unfold term_to_graph.
    rewrite <- H.
Admitted.

Lemma term_to_graph_swap :
  forall P Q, exists l,
    equiv 
      (swap_atomid_list l (term_to_graph {{ P, Q }}))
      (term_to_graph {{ Q, P }}).
Proof.
  intros P Q.
  exists (make_graph_swap_list P Q).
  induction P.
  - rewrite term_to_graph_gzero_p.
    rewrite term_to_graph_p_gzero.
    simpl. unfold equiv. reflexivity.
  - simpl. unfold make_graph_swap_list. simpl.
    induction Q.
    + unfold equiv. auto.
    + simpl. replace (count_atoms atom0) with 1.
      * unfold term_to_graph.
Admitted.

Lemma term_to_atom_list_comma_assoc :
  forall P Q R,
    term_to_atom_list {{ P, (Q, R) }}
    = term_to_atom_list {{ P, Q, R }}.
Proof.
  intros P.
  induction P.
  - auto.
  - auto.
  - intros Q R. simpl. rewrite app_assoc. reflexivity.
Qed.

Lemma term_to_graph_link_subst :
  forall P X Y,
    In X (locallinks P) ->
    wellformed_g P -> wellformed_g {{ P[Y/X] }} ->
    equiv (term_to_graph P) (term_to_graph {{ P[Y/X] }}).
Proof.
  intros P X Y H1 H2 H3.
Admitted.

Lemma cong_to_iso_E5 :
  forall P P' Q,
    isomorphic (term_to_graph {{ P }}) (term_to_graph {{ P' }}) ->
    isomorphic (term_to_graph {{ P, Q }}) (term_to_graph {{ P', Q }}).
Proof.
  intros P P' Q.
  generalize dependent P'.
  generalize dependent P.
  induction Q.
  - intros P P' H.
    rewrite term_to_graph_p_gzero.
    rewrite term_to_graph_p_gzero. apply H.
  - intros P P' H.
    unfold term_to_graph. simpl.
Admitted.

Theorem cong_to_iso :
  forall t1 t2 g1 g2,
    g1 = term_to_graph t1 ->
    g2 = term_to_graph t2 ->
    cong_wf t1 t2 -> isomorphic g1 g2.
Proof.
  intros t1 t2 g1 g2 Hg1 Hg2 H.
  generalize dependent g2.
  generalize dependent g1.
  destruct H.
  destruct H0.
  induction H1; intros g1 Hg1 g2 Hg2;
  unfold isomorphic; rewrite Hg1; rewrite Hg2.
  - exists []. rewrite term_to_graph_gzero_p.
    simpl. unfold equiv. reflexivity.
  - apply term_to_graph_swap.
  - exists []. simpl.
    unfold equiv. unfold term_to_graph.
    rewrite term_to_atom_list_comma_assoc.
    reflexivity.
  - exists []. simpl.
    apply term_to_graph_link_subst; auto.
  - apply cong_to_iso_E5. apply IHcong; auto.
    + apply wellformed_g_inj in H. destruct H. apply H.
    + apply wellformed_g_inj in H0. destruct H0. apply H0.
  - exists []. simpl.
    unfold equiv. intros n.
    unfold term_to_graph. simpl.
    unfold atom_list_to_graph. simpl.
    unfold bind. simpl.
    unfold atom_list_to_raw_graph. simpl.
    unfold atom_list_to_port_list. simpl.
    unfold add_atom_to_port_list. simpl.
    rewrite string_dec_refl. simpl.
    unfold removeatom. unfold upd_graph. simpl.
    unfold newlink_force. simpl. unfold empty.
    induction n; auto.
  - exists []. simpl. unfold equiv.
    intros n. unfold term_to_graph. simpl.
    unfold atom_list_to_graph. simpl.
    unfold atom_list_to_raw_graph. simpl.
    unfold atom_list_to_port_list. simpl.
    unfold add_atom_to_port_list. simpl.
    destruct (string_dec X Y).
    + rewrite e. rewrite string_dec_refl. simpl. reflexivity.
    + destruct (string_dec Y X).
      * destruct n0. rewrite e. reflexivity.
      * simpl. reflexivity.
  - admit.
  - apply isomorphic_refl.
  - apply isomorphic_trans with (G2:=(term_to_graph Q)).
    + apply IHcong1; auto. admit.
    + apply IHcong2; auto. admit.
  - apply isomorphic_sym.
    + apply IHcong; auto.
Admitted.

Theorem iso_to_cong :
  forall t1 t2 g1 g2,
    g1 = term_to_graph t1 ->
    g2 = term_to_graph t2 ->
    isomorphic g1 g2 -> cong_wf t1 t2.
Admitted.


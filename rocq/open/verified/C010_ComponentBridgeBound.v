(** * C-010: k components need k - 1 bridges, and k - 1 suffice.

    Convention: a graph is a list of undirected edges, each a pair of
    natural-number vertices.  [Reach es S x] holds when the vertex x is
    reachable from a vertex of the start list S along edges of es, each
    edge used in either direction.  The components are given by a labeling
    [comp] of the vertices with labels 0 .. k - 1: an internal edge joins
    two vertices with the same label, and a bridge is any further edge.

    [bridge_lower_bound]: when the internal edges together with the bridges
    make every vertex of a list reachable from one vertex, and the labels of
    the listed vertices cover 0 .. k - 1, there are at least k - 1 bridges.
    The proof maps each path to the quotient graph on labels, where an
    internal edge becomes a loop and a bridge an edge between labels, and
    bounds the quotient: the vertices reachable from a start list S along es
    number at most |S| + |es| ([closure_length], [closure_complete]).
    [path_bridges_connect] attains the bound on the quotient: the k - 1
    bridges (i, i + 1) connect the labels 0 .. k - 1.

    [seven_components_need_six_bridges] is the instance k = 7 that
    C010_ConnectivityObstruction states as 7 - 1 = 6.  That the seven
    box-kites are the components of the zero-divisor graph on the 42
    assessors is the premise of that header; this module takes the labeling
    as a hypothesis and proves no statement about the zero-divisor graph. *)

From Stdlib Require Import List Arith Lia.
Import ListNotations.

Definition edge : Type := (nat * nat)%type.

Inductive Reach (es : list edge) (S : list nat) : nat -> Prop :=
| reach_start : forall x, In x S -> Reach es S x
| reach_step : forall y z,
    Reach es S y -> In (y, z) es \/ In (z, y) es -> Reach es S z.

(** The closure of S under es, computed edge by edge: an edge with one end
    in the closure of S under the remaining edges adds its other end to the
    start list. *)
Fixpoint closure (es : list edge) (S : list nat) : list nat :=
  match es with
  | [] => S
  | (a, b) :: r =>
      if in_dec Nat.eq_dec a (closure r S) then closure r (b :: S)
      else if in_dec Nat.eq_dec b (closure r S) then closure r (a :: S)
      else closure r S
  end.

Lemma closure_length :
  forall es S, length (closure es S) <= length S + length es.
Proof.
  induction es as [|[a b] r IH]; intros S; simpl.
  - lia.
  - destruct (in_dec Nat.eq_dec a (closure r S)).
    + specialize (IH (b :: S)). simpl in IH. lia.
    + destruct (in_dec Nat.eq_dec b (closure r S)).
      * specialize (IH (a :: S)). simpl in IH. lia.
      * specialize (IH S). lia.
Qed.

Lemma reach_more_edges :
  forall es es' S x,
    (forall e, In e es -> In e es') -> Reach es S x -> Reach es' S x.
Proof.
  intros es es' S x Hincl H.
  induction H as [x Hx | y z Hy IHy Hyz].
  - apply reach_start. exact Hx.
  - apply (reach_step es' S y z IHy).
    destruct Hyz as [Hyz | Hyz]; [left | right]; apply Hincl; exact Hyz.
Qed.

Lemma reach_through :
  forall es S S' x,
    (forall y, In y S' -> Reach es S y) -> Reach es S' x -> Reach es S x.
Proof.
  intros es S S' x HS' H.
  induction H as [x Hx | y z Hy IHy Hyz].
  - apply HS'. exact Hx.
  - exact (reach_step es S y z IHy Hyz).
Qed.

Lemma reach_more_start :
  forall es S S' x,
    (forall y, In y S -> In y S') -> Reach es S x -> Reach es S' x.
Proof.
  intros es S S' x Hincl H.
  apply (reach_through es S' S x); [| exact H].
  intros y Hy. apply reach_start. apply Hincl. exact Hy.
Qed.

Lemma closure_sound :
  forall es S x, In x (closure es S) -> Reach es S x.
Proof.
  induction es as [|[a b] r IH]; intros S x Hx; simpl in Hx.
  - apply reach_start. exact Hx.
  - assert (Hw : forall T y, Reach r T y -> Reach ((a, b) :: r) T y).
    { intros T y. apply reach_more_edges. intros e He. right. exact He. }
    destruct (in_dec Nat.eq_dec a (closure r S)) as [Ha | Ha].
    + apply (reach_through _ S (b :: S)); [| exact (Hw _ _ (IH _ _ Hx))].
      intros y [Hy | Hy].
      * subst y. apply (reach_step _ S a b); [exact (Hw _ _ (IH _ _ Ha)) |].
        left. left. reflexivity.
      * apply reach_start. exact Hy.
    + destruct (in_dec Nat.eq_dec b (closure r S)) as [Hb | Hb].
      * apply (reach_through _ S (a :: S)); [| exact (Hw _ _ (IH _ _ Hx))].
        intros y [Hy | Hy].
        -- subst y. apply (reach_step _ S b a); [exact (Hw _ _ (IH _ _ Hb)) |].
           right. left. reflexivity.
        -- apply reach_start. exact Hy.
      * exact (Hw _ _ (IH _ _ Hx)).
Qed.

Lemma closure_complete :
  forall es S x, Reach es S x -> In x (closure es S).
Proof.
  induction es as [|[a b] r IH]; intros S x H; simpl.
  - induction H as [x Hx | y z Hy IHy Hyz].
    + exact Hx.
    + destruct Hyz as [[] | []].
  - destruct (in_dec Nat.eq_dec a (closure r S)) as [Ha | Ha].
    + apply IH.
      induction H as [x Hx | y z Hy IHy Hyz].
      * apply reach_start. right. exact Hx.
      * destruct Hyz as [[E | Hyz] | [E | Hyz]].
        -- injection E as E1 E2. subst z. apply reach_start. left. reflexivity.
        -- exact (reach_step r (b :: S) y z IHy (or_introl Hyz)).
        -- injection E as E1 E2. subst z.
           apply (reach_more_start r S); [intros w Hw; right; exact Hw |].
           apply closure_sound. exact Ha.
        -- exact (reach_step r (b :: S) y z IHy (or_intror Hyz)).
    + destruct (in_dec Nat.eq_dec b (closure r S)) as [Hb | Hb].
      * apply IH.
        induction H as [x Hx | y z Hy IHy Hyz].
        -- apply reach_start. right. exact Hx.
        -- destruct Hyz as [[E | Hyz] | [E | Hyz]].
           ++ injection E as E1 E2. subst z.
              apply (reach_more_start r S); [intros w Hw; right; exact Hw |].
              apply closure_sound. exact Hb.
           ++ exact (reach_step r (a :: S) y z IHy (or_introl Hyz)).
           ++ injection E as E1 E2. subst z. apply reach_start. left. reflexivity.
           ++ exact (reach_step r (a :: S) y z IHy (or_intror Hyz)).
      * apply IH.
        induction H as [x Hx | y z Hy IHy Hyz].
        -- apply reach_start. exact Hx.
        -- destruct Hyz as [[E | Hyz] | [E | Hyz]].
           ++ injection E as E1 E2. subst y.
              exfalso. apply Ha. apply IH. exact IHy.
           ++ exact (reach_step r S y z IHy (or_introl Hyz)).
           ++ injection E as E1 E2. subst y.
              exfalso. apply Hb. apply IH. exact IHy.
           ++ exact (reach_step r S y z IHy (or_intror Hyz)).
Qed.

(** Every vertex 0 .. k - 1 reachable from one vertex along es needs
    k - 1 edges. *)
Theorem reach_all_lower_bound :
  forall es s k, (forall x, x < k -> Reach es [s] x) -> k - 1 <= length es.
Proof.
  intros es s k H.
  assert (Hincl : incl (seq 0 k) (closure es [s])).
  { intros x Hx. apply in_seq in Hx. apply closure_complete. apply H. lia. }
  pose proof (NoDup_incl_length (seq_NoDup k 0) Hincl) as Hlen.
  rewrite length_seq in Hlen.
  pose proof (closure_length es [s]) as Hc. simpl in Hc. lia.
Qed.

Definition quotient (comp : nat -> nat) (bridges : list edge) : list edge :=
  map (fun e => (comp (fst e), comp (snd e))) bridges.

Lemma reach_quotient :
  forall comp internal bridges S x,
    (forall e, In e internal -> comp (fst e) = comp (snd e)) ->
    Reach (internal ++ bridges) S x ->
    Reach (quotient comp bridges) (map comp S) (comp x).
Proof.
  intros comp internal bridges S x Hint H.
  induction H as [x Hx | y z Hy IHy Hyz].
  - apply reach_start. apply in_map. exact Hx.
  - assert (Hq : forall u v, In (u, v) bridges ->
                   In (comp u, comp v) (quotient comp bridges)).
    { intros u v Huv. unfold quotient.
      change (comp u, comp v)
        with ((fun e : edge => (comp (fst e), comp (snd e))) (u, v)).
      apply in_map. exact Huv. }
    destruct Hyz as [Hyz | Hyz]; apply in_app_or in Hyz;
      destruct Hyz as [Hyz | Hyz].
    + pose proof (Hint (y, z) Hyz) as E. simpl in E. rewrite <- E. exact IHy.
    + exact (reach_step _ _ (comp y) (comp z) IHy (or_introl (Hq y z Hyz))).
    + pose proof (Hint (z, y) Hyz) as E. simpl in E. rewrite E. exact IHy.
    + exact (reach_step _ _ (comp y) (comp z) IHy (or_intror (Hq z y Hyz))).
Qed.

(** k components, joined by internal edges and bridges into one connected
    vertex list, need k - 1 bridges. *)
Theorem bridge_lower_bound :
  forall (k : nat) (comp : nat -> nat) (vs : list nat) (v0 : nat)
         (internal bridges : list edge),
    (forall e, In e internal -> comp (fst e) = comp (snd e)) ->
    (forall x, In x vs -> Reach (internal ++ bridges) [v0] x) ->
    (forall c, c < k -> exists x, In x vs /\ comp x = c) ->
    k - 1 <= length bridges.
Proof.
  intros k comp vs v0 internal bridges Hint Hconn Hcover.
  assert (Hq : forall c, c < k -> Reach (quotient comp bridges) [comp v0] c).
  { intros c Hc. destruct (Hcover c Hc) as [x [Hx Ex]]. subst c.
    exact (reach_quotient comp internal bridges [v0] x Hint (Hconn x Hx)). }
  pose proof (reach_all_lower_bound _ _ k Hq) as Hb.
  unfold quotient in Hb. rewrite length_map in Hb. exact Hb.
Qed.

Definition path_bridges (k : nat) : list edge :=
  map (fun i => (i, S i)) (seq 0 (k - 1)).

Theorem path_bridges_length : forall k, length (path_bridges k) = k - 1.
Proof.
  intros k. unfold path_bridges. rewrite length_map, length_seq. reflexivity.
Qed.

Theorem path_bridges_connect :
  forall k x, x < k -> Reach (path_bridges k) [0] x.
Proof.
  intros k x. induction x as [|x IH]; intros Hx.
  - apply reach_start. left. reflexivity.
  - apply (reach_step _ _ x (S x)); [apply IH; lia |].
    left. unfold path_bridges. apply in_map_iff. exists x.
    split; [reflexivity | apply in_seq; lia].
Qed.

Theorem seven_components_need_six_bridges :
  forall (comp : nat -> nat) (vs : list nat) (v0 : nat)
         (internal bridges : list edge),
    (forall e, In e internal -> comp (fst e) = comp (snd e)) ->
    (forall x, In x vs -> Reach (internal ++ bridges) [v0] x) ->
    (forall c, c < 7 -> exists x, In x vs /\ comp x = c) ->
    6 <= length bridges.
Proof.
  intros comp vs v0 internal bridges Hint Hconn Hcover.
  exact (bridge_lower_bound 7 comp vs v0 internal bridges Hint Hconn Hcover).
Qed.

Theorem six_bridges_connect_seven_components :
  length (path_bridges 7) = 6 /\
  forall c, c < 7 -> Reach (path_bridges 7) [0] c.
Proof.
  split; [apply path_bridges_length | apply path_bridges_connect].
Qed.

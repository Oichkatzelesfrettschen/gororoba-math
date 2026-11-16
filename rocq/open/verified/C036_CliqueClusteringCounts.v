(** * C-036: triangle and path counts of K_4 and K_{2,2,2}.

    Convention: a graph on the vertices 0 .. n-1 is a boolean adjacency
    function.  The triangles are the triples i < j < k that are pairwise
    adjacent; the connected triples are the triples (v, a, b) with a < b
    that are both adjacent to v, so each counts one path a - v - b.  The
    global clustering coefficient is 3 * triangles / connected triples.
    K_4 is the complete graph on four vertices, and in K_{2,2,2} (the
    octahedron) the part of vertex v is v / 2 and two vertices are adjacent
    exactly when their parts differ.

    The module proves, by evaluation on the six and four vertices:
    - K_4 has 4 triangles and 12 connected triples, so its clustering
      coefficient is 3 * 4 / 12 = 1;
    - K_{2,2,2} has 12 edges, 8 triangles (one vertex from each part) and 36
      connected triples (6 vertices of degree 4, each with 6 neighbor
      pairs), so its clustering coefficient is 3 * 8 / 36 = 2/3.
    Hence the complete tripartite graph with parts of size 2 has triangles
    and a nonzero clustering coefficient.

    The module proves no bound C >= 1/4 or C >= 1/3 for any graph class and
    relates neither graph to a triality structure. *)

From Stdlib Require Import List Arith Bool.
Import ListNotations.

Definition adjacency := nat -> nat -> bool.

Definition k4_adjacent (u v : nat) : bool := negb (Nat.eqb u v).

Definition k222_adjacent (u v : nat) : bool := negb (Nat.eqb (u / 2) (v / 2)).

Definition edge_count (n : nat) (adj : adjacency) : nat :=
  length (filter (fun p => (Nat.ltb (fst p) (snd p) && adj (fst p) (snd p))%bool)
                 (list_prod (seq 0 n) (seq 0 n))).

Definition triangle_count (n : nat) (adj : adjacency) : nat :=
  length (filter (fun t =>
            let i := fst (fst t) in let j := snd (fst t) in let k := snd t in
            (Nat.ltb i j && Nat.ltb j k && adj i j && adj j k && adj i k)%bool)
          (list_prod (list_prod (seq 0 n) (seq 0 n)) (seq 0 n))).

Definition connected_triple_count (n : nat) (adj : adjacency) : nat :=
  length (filter (fun t =>
            let v := fst (fst t) in let a := snd (fst t) in let b := snd t in
            (Nat.ltb a b && adj v a && adj v b)%bool)
          (list_prod (list_prod (seq 0 n) (seq 0 n)) (seq 0 n))).

Theorem k4_counts :
  edge_count 4 k4_adjacent = 6 /\
  triangle_count 4 k4_adjacent = 4 /\
  connected_triple_count 4 k4_adjacent = 12.
Proof. vm_compute. repeat split. Qed.

Theorem k4_clustering_is_one :
  3 * triangle_count 4 k4_adjacent = connected_triple_count 4 k4_adjacent.
Proof. vm_compute. reflexivity. Qed.

Theorem k222_counts :
  edge_count 6 k222_adjacent = 12 /\
  triangle_count 6 k222_adjacent = 8 /\
  connected_triple_count 6 k222_adjacent = 36.
Proof. vm_compute. repeat split. Qed.

Theorem k222_clustering_is_two_thirds :
  3 * (3 * triangle_count 6 k222_adjacent) =
  2 * connected_triple_count 6 k222_adjacent.
Proof. vm_compute. reflexivity. Qed.

Theorem k222_has_triangles : triangle_count 6 k222_adjacent <> 0.
Proof. vm_compute. discriminate. Qed.

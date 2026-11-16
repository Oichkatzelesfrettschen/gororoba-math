(** * C-882: edge count and adjacency spectrum of the octahedron K_{2,2,2}.

    Convention: the vertices of K_{2,2,2} are 0 .. 5 and the part of vertex v
    is v / 2, so two vertices are adjacent exactly when their parts differ.
    The adjacency matrix is the 6 x 6 matrix over Z with entry 1 for an
    adjacent pair and 0 otherwise.

    The module proves:
    - the graph has 12 edges, counted as the pairs u < v of adjacent
      vertices;
    - six pairwise orthogonal nonzero integer vectors are eigenvectors of
      the adjacency matrix with the eigenvalues 4, -2, -2, 0, 0, 0, and the
      difference of the largest and the smallest of these eigenvalues is 6.
      Orthogonal nonzero vectors are linearly independent, so six of them
      span Q^6 and the list is the whole spectrum; that implication is not
      formalized here.

    The module relates K_{2,2,2} to no zero-divisor graph of a
    Cayley-Dickson algebra: that identification of the dimension-16
    octahedron, and the dimension-64 edge count that C882_dim64_upper_bound
    compares with the zero-divisor edge count, have no theorem here or in
    C882_ParityCliqueExact.v. *)

From Stdlib Require Import List ZArith Arith Lia Bool.
Import ListNotations.

Open Scope Z_scope.

Definition k222_adjacent (u v : nat) : bool :=
  negb (Nat.eqb (u / 2) (v / 2)).

Definition k222_vertices : list nat := seq 0 6.

Definition k222_edge_count : nat :=
  length (filter (fun p => (Nat.ltb (fst p) (snd p) && k222_adjacent (fst p) (snd p))%bool)
                 (list_prod k222_vertices k222_vertices)).

Theorem k222_has_12_edges : k222_edge_count = 12%nat.
Proof. vm_compute. reflexivity. Qed.

Definition k222_matrix : list (list Z) :=
  map (fun u => map (fun v => if k222_adjacent u v then 1 else 0) k222_vertices)
      k222_vertices.

Definition dot (x y : list Z) : Z :=
  fold_right Z.add 0 (map (fun p => fst p * snd p) (combine x y)).

Definition matvec (m : list (list Z)) (x : list Z) : list Z :=
  map (fun row => dot row x) m.

(** Eigenvalue and eigenvector pairs: the all-ones vector, two vectors that
    are constant on each part and sum to zero over the six vertices, and the
    three differences of the two vertices of a part. *)
Definition k222_eigenpairs : list (Z * list Z) :=
  [ (4, [1; 1; 1; 1; 1; 1]);
    (-2, [1; 1; -1; -1; 0; 0]);
    (-2, [1; 1; 1; 1; -2; -2]);
    (0, [1; -1; 0; 0; 0; 0]);
    (0, [0; 0; 1; -1; 0; 0]);
    (0, [0; 0; 0; 0; 1; -1]) ].

Theorem k222_eigenpairs_are_eigenvectors :
  forallb (fun p => forallb (fun e => Z.eqb (fst e) (snd e))
             (combine (matvec k222_matrix (snd p)) (map (Z.mul (fst p)) (snd p))))
          k222_eigenpairs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem k222_eigenvectors_nonzero :
  forallb (fun p => Z.ltb 0 (dot (snd p) (snd p))) k222_eigenpairs = true.
Proof. vm_compute. reflexivity. Qed.

Theorem k222_eigenvectors_pairwise_orthogonal :
  forallb (fun ij =>
    (Nat.leb (snd ij) (fst ij) ||
     Z.eqb (dot (snd (nth (fst ij) k222_eigenpairs (0, [])))
                (snd (nth (snd ij) k222_eigenpairs (0, [])))) 0)%bool)
    (list_prod (seq 0 6) (seq 0 6)) = true.
Proof. vm_compute. reflexivity. Qed.

Definition k222_eigenvalues : list Z := map fst k222_eigenpairs.

Theorem k222_spectral_gap :
  fold_right Z.max (-100) k222_eigenvalues -
  fold_right Z.min 100 k222_eigenvalues = 6.
Proof. vm_compute. reflexivity. Qed.

(** The eigenvalues sum to the trace of the adjacency matrix, which is 0. *)
Theorem k222_trace_zero :
  fold_right Z.add 0 k222_eigenvalues = 0 /\
  fold_right Z.add 0 (map (fun i => nth i (nth i k222_matrix []) 0) (seq 0 6)) = 0.
Proof. vm_compute. split; reflexivity. Qed.

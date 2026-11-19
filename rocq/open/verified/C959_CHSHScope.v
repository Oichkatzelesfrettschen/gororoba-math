(** * C959 successor: the CHSH bound of a local deterministic assignment.

    Convention.  A deterministic local assignment is a quadruple
    (a, a', b, b') of real outcomes, each +1 or -1: a and a' are the two
    outcomes of the first party for its two settings, b and b' those of the
    second party.  The correlation of a setting pair is the product of the
    outcomes, and [chsh_S] of [BellCHSH] is S = E(a,b) - E(a,b') + E(a',b)
    + E(a',b').  A local hidden-variable model is a finite probability
    distribution over such assignments: [mix] lists nonnegative weights
    summing to one with an assignment each, and the correlation of a
    setting pair is the weighted sum of the products.

    Results.
    - [chsh_deterministic_bound]: |S| <= 2 for every deterministic
      assignment of +1 and -1 outcomes.
    - [chsh_lhv_bound]: |S| <= 2 for every finite mixture of such
      assignments, with S computed from the mixed correlations.
    - [chsh_deterministic_attains_two]: the bound is attained.
    - [chsh_lhv_attains_every_value]: every real s with |s| <= 2 is the S
      of a two-assignment mixture; in particular the value S = -1.506 of
      the 512-dimensional experiment is the S of a local deterministic
      mixture ([chsh_observed_value_lhv]).

    Scope.  These theorems prove the mathematical bound, and that one
    value of S below 2 in absolute value is reproduced by a local
    deterministic mixture, so it does not by itself separate local from
    non-local models.  They prove nothing about the Cayley-Dickson
    associator experiment.  The interpretation that its statistics come
    from a local deterministic assignment (the claim of the docstring of
    [cd_lhv_interpretation] in [C959_CHSHClassicalBound]) is not proved,
    for three reasons.
    - The original theorem bounds the constant -1506/1000, a recorded
      measurement; its statement mentions no probe, algebra or
      correlation, so it holds whatever process produced that number.
    - A statement about associator-probe statistics needs a formal sampling
      model: the distribution of the probes, the measurement operator as a
      function of them, and the pairing of the two parties.  A search for
      the word chsh over rocq/ at this commit finds only [BellCHSH], the
      original and this file, and the original imports only [Prelude] and
      [BellCHSH]; none defines such a model.
    - |S| <= 2 is one necessary condition on four correlations, and a
      proof that it holds for a process would not make the process a
      mixture of deterministic assignments: the criterion for that is the
      full set of CHSH inequalities (A. Fine, Phys. Rev. Lett. 48 (1982)
      291, the publication record of which OpenAlex matches by title,
      author and year; the criterion is stated here from the
      literature as recalled, not from a held copy of the paper).  This file proves only the necessary direction,
      for the single combination S. *)

From Stdlib Require Import Reals Lra List.
From OpenGororoba Require Import Prelude BellCHSH.
Import ListNotations.

Open Scope R_scope.

Definition pm1 (x : R) : Prop := x = 1 \/ x = -1.

Definition assignment : Type := (R * R * R * R)%type.

Definition assignment_pm1 (g : assignment) : Prop :=
  match g with (a, a', b, b') => pm1 a /\ pm1 a' /\ pm1 b /\ pm1 b' end.

Definition assignment_S (g : assignment) : R :=
  match g with
  | (a, a', b, b') => chsh_S (a * b) (a * b') (a' * b) (a' * b')
  end.

Theorem chsh_deterministic_bound : forall g,
  assignment_pm1 g -> Rabs (assignment_S g) <= 2.
Proof.
  intros [[[a a'] b] b'] (Ha & Ha' & Hb & Hb').
  cbn [assignment_S]. unfold chsh_S.
  apply Rabs_le.
  destruct Ha as [-> | ->], Ha' as [-> | ->], Hb as [-> | ->],
    Hb' as [-> | ->];
    split; lra.
Qed.

Theorem chsh_deterministic_attains_two :
  assignment_pm1 (1, 1, 1, 1) /\ assignment_S (1, 1, 1, 1) = 2.
Proof.
  split.
  - repeat split; left; reflexivity.
  - cbn [assignment_S]. unfold chsh_S. lra.
Qed.

(** A weighted assignment: a weight and a deterministic assignment. *)
Definition mix : Type := list (R * assignment).

Fixpoint mix_weight (m : mix) : R :=
  match m with [] => 0 | (w, _) :: r => w + mix_weight r end.

Fixpoint mix_nonneg (m : mix) : Prop :=
  match m with [] => True | (w, _) :: r => 0 <= w /\ mix_nonneg r end.

Fixpoint mix_pm1 (m : mix) : Prop :=
  match m with [] => True | (_, g) :: r => assignment_pm1 g /\ mix_pm1 r end.

Fixpoint corr_ab (m : mix) : R :=
  match m with [] => 0 | (w, (a, _, b, _)) :: r => w * (a * b) + corr_ab r end.

Fixpoint corr_ab' (m : mix) : R :=
  match m with [] => 0 | (w, (a, _, _, b')) :: r => w * (a * b') + corr_ab' r end.

Fixpoint corr_a'b (m : mix) : R :=
  match m with [] => 0 | (w, (_, a', b, _)) :: r => w * (a' * b) + corr_a'b r end.

Fixpoint corr_a'b' (m : mix) : R :=
  match m with
  | [] => 0 | (w, (_, a', _, b')) :: r => w * (a' * b') + corr_a'b' r end.

Definition mix_S (m : mix) : R :=
  chsh_S (corr_ab m) (corr_ab' m) (corr_a'b m) (corr_a'b' m).

Fixpoint mix_S_sum (m : mix) : R :=
  match m with [] => 0 | (w, g) :: r => w * assignment_S g + mix_S_sum r end.

Lemma mix_S_linear : forall m, mix_S m = mix_S_sum m.
Proof.
  induction m as [|[w [[[a a'] b] b']] r IH]; unfold mix_S in *.
  - cbn [corr_ab corr_ab' corr_a'b corr_a'b' mix_S_sum]. unfold chsh_S. lra.
  - cbn [corr_ab corr_ab' corr_a'b corr_a'b' mix_S_sum assignment_S].
    unfold chsh_S in *. rewrite <- IH. ring.
Qed.

Lemma mix_S_sum_bounds : forall m,
  mix_nonneg m -> mix_pm1 m ->
  - (2 * mix_weight m) <= mix_S_sum m <= 2 * mix_weight m.
Proof.
  induction m as [|[w g] r IH]; intros Hn Hp.
  - cbn. lra.
  - cbn [mix_nonneg mix_pm1] in Hn, Hp. destruct Hn as [Hw Hn],
      Hp as [Hg Hp].
    specialize (IH Hn Hp).
    pose proof (chsh_deterministic_bound g Hg) as B.
    assert (B1 : -2 <= assignment_S g /\ assignment_S g <= 2)
      by (unfold Rabs in B; destruct (Rcase_abs (assignment_S g)); lra).
    destruct B1 as [B1 B2].
    assert (0 <= w * (2 - assignment_S g)) by (apply Rmult_le_pos; lra).
    assert (0 <= w * (assignment_S g + 2)) by (apply Rmult_le_pos; lra).
    cbn [mix_S_sum mix_weight].
    split; lra.
Qed.

Theorem chsh_lhv_bound : forall m,
  mix_nonneg m -> mix_pm1 m -> mix_weight m = 1 -> Rabs (mix_S m) <= 2.
Proof.
  intros m Hn Hp Hw. rewrite mix_S_linear.
  pose proof (mix_S_sum_bounds m Hn Hp) as [B1 B2].
  rewrite Hw in B1, B2. apply Rabs_le. lra.
Qed.

(** The S = 2 and S = -2 assignments: (1, 1, 1, 1) and (1, -1, 1, 1). *)
Theorem chsh_lhv_attains_every_value : forall s,
  -2 <= s <= 2 ->
  exists m, mix_nonneg m /\ mix_pm1 m /\ mix_weight m = 1 /\ mix_S m = s.
Proof.
  intros s [H1 H2].
  exists [((2 + s) / 4, (1, 1, 1, 1)); ((2 - s) / 4, (1, -1, 1, 1))].
  refine (conj _ (conj _ (conj _ _))).
  - cbn [mix_nonneg]. split; [lra | split; [lra | exact I]].
  - cbn [mix_pm1 assignment_pm1]. split; [|split; [|exact I]];
      repeat split; unfold pm1; first [left; reflexivity | right; reflexivity].
  - cbn [mix_weight]. lra.
  - rewrite mix_S_linear. cbn [mix_S_sum assignment_S]. unfold chsh_S. lra.
Qed.

Theorem chsh_observed_value_lhv :
  exists m, mix_nonneg m /\ mix_pm1 m /\ mix_weight m = 1 /\
    mix_S m = -1506 / 1000.
Proof.
  apply chsh_lhv_attains_every_value. lra.
Qed.

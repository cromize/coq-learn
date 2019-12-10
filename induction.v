From LF Require Export basics.

(** Proof by Induction *)

(* the match in the definition of + can't be simplified *)
Theorem plus_n_O_firsttry : forall n : nat,
  n = n + 0.
Proof.
  intros n.
  simpl.
Abort.

Theorem plus_n_O_secondtry : forall n : nat,
  n = n + 0.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - simpl.
Abort.

Theorem plus_n_O : forall n : nat, n = n + 0.
Proof.
  intros n. induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite <- IHn'. reflexivity. Qed.

(* Exercise 1. standard (basic_induction) *)

Theorem mult_0_r : forall n : nat,
  n * 0 = 0.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite -> IHn'. reflexivity. Qed.

Theorem plus_n_Sm : forall n m : nat,
  S (n + m) = n + (S m).
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    + reflexivity.
    + reflexivity.
  - induction m as [| m' Ihm'].
    + simpl. rewrite <- IHn'. reflexivity.
    + simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
  n + m = m + n.
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    + reflexivity.
    + simpl. rewrite <- IHm'. reflexivity.
  - induction m as [| m' IHm'].
    + simpl. rewrite -> IHn'. reflexivity.
    + simpl. rewrite -> IHn'.
      simpl. rewrite <- IHm'.
      rewrite <- IHn'. reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
  n + (m + p) = (n + m) + p.
Proof.
  induction n as [| n' IHn'].
  - induction m as [| m' IHm'].
    + induction p as [| p' IHp'].
      * reflexivity.
      * reflexivity.
    + induction p as [| p' IHp'].
      * reflexivity.
      * reflexivity.
  - induction m as [| m' IHm'].
    + induction p as [| p' IHp'].
      * simpl. rewrite <- IHn'. reflexivity.
      * simpl. rewrite <- IHn'. reflexivity.
    + induction p as [| p' IHp'].
      * simpl. rewrite <- IHn'. reflexivity.
      * simpl. rewrite <- IHn'. reflexivity.
Qed.

(* Exercise 2. standard (double_plus) *)

Fixpoint double (n : nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl. rewrite plus_comm.
    simpl. rewrite -> IHn'.
    reflexivity.
Qed.

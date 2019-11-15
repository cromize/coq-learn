(* https://softwarefoundations.cis.upenn.edu/lf-current/Basics.html *)

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.
Proof. simpl. reflexivity. Qed.

(** Boolean Logic *)

Inductive bool : Type :=
  | true
  | false.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

(* Truth table for OR *)
Example test_orb1: (orb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb2: (orb false false) = false.
Proof. simpl. reflexivity. Qed.

Example test_orb3: (orb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_orb4: (orb true true) = true.
Proof. simpl. reflexivity. Qed.

(* define new notation *)
Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).

Example test_orb5: false || false || true = true.
Proof. simpl. reflexivity. Qed.

(* Exercise: 1. standard (nandb) *)

Definition nandb (b1 : bool) (b2 : bool) : bool :=
  negb (andb b1 b2).

(* Truth table for NAND *)
Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.

Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 2. standard (andb3) *)

Definition andb3 (b1 : bool) (b2 : bool) (b3 : bool) : bool :=
  andb (andb b1 b2) b3.

(* Truth table for 3xAND *)
Example test_andb31: (andb3 true true true) = true.
Proof. simpl. reflexivity. Qed.

Example test_andb32: (andb3 false true true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb33: (andb3 true false true) = false.
Proof. simpl. reflexivity. Qed.

Example test_andb34: (andb3 true true false) = false.
Proof. simpl. reflexivity. Qed.

(** Inductives *)
(* note: Inductive constructor can take in argument *)

Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary q => false
  end.

Definition isred (c : color) : bool :=
  match c with
  | black => false
  | white => false
  | primary red => true
  | primary _ => false
  end.

Inductive bit : Type :=
  | b0
  | b1.

Inductive nibble : Type :=
  | bits (b0 b1 b2 b3 : bit).

(* is nibble *)
(* Check (bits b1 b0 b1 b0). *)

Definition all_zero (nb : nibble) : bool :=
  match nb with
  | (bits b0 b0 b0 b0) => true
  | (bits _ _ _ _ ) => false
  end.

(* False *)
(* Compute (all_zero (bits b1 b0 b1 b0)). *)

(* True *)
(* Compute (all_zero (bits b0 b0 b0 b0)). *)

(* Peano natural unary numbers *)

Module NatPlayground. 

Inductive nat : Type :=
  | O
  | S (n : nat).

Definition pred (n : nat) : nat :=
  match n with
  | O => O
  | S n' => n'
  end.

End NatPlayground. 

(* print peano format into decimal (doesn't work in our NatPlayground *)
(* Check (S (S (S (S O)))). *)

Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

(* Compute (minustwo 4). *)

(*
Check S.
Check pred.
Check minustwo.
*)

(** Recursion *)

(* Fixpoint is generic primitive recursion keyword *)
Fixpoint evenb (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => evenb n'
  end.

Definition oddb (n : nat) : bool := negb (evenb n).

Example test_oddb1: oddb 1 = true.
Proof. simpl. reflexivity. Qed.

Example test_oddb2: oddb 4 = false.
Proof. simpl. reflexivity. Qed.

Module NatPlayground2.

Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(* Compute (plus 3 2). *)

Fixpoint mult (n m : nat) : nat :=
  match n with
  | O => O
  | S n' => plus m (mult n' m)
  end.

Example test_mult1: (mult 3 3) = 9.
Proof. simpl. reflexivity. Qed.

Fixpoint minus (n m : nat) : nat :=
  match n, m with
  | O , _ => O
  | S _ , O => n
  | S n' , S m' => minus n' m'
  end.

Example test_minus1: (minus 3 1) = 2.
Proof. simpl. reflexivity. Qed.

End NatPlayground2.

Fixpoint exp (base power : nat) : nat :=
  match power with
  | O => S O
  | S p => mult base (exp base p)
  end.

Example test_exp1: (exp 3 2) = 9.
Proof. simpl. reflexivity. Qed.

(* Exercise: 3. standard (factorial) *)

Fixpoint factorial (n : nat) : nat :=
  match n with
  | O => S O
  | S n' => mult (S n') (factorial n')
  end.

Example test_factorial1: (factorial 3) = 6.
Proof. simpl. reflexivity. Qed.

Example test_factorial2: (factorial 5) = (mult 10 12).
Proof. simpl. reflexivity. Qed.

Notation "x + y" := (plus x y)
                        (at level 50, left associativity)
                        : nat_scope.
Notation "x - y" := (minus x y)
                        (at level 50, left associativity)
                        : nat_scope.
Notation "x * y" := (mult x y)
                        (at level 40, left associativity)
                        : nat_scope.

(* Check ((0 + 1) + 1). *)

(* from book
Fixpoint eqb (n m : nat) : bool :=
  match n with
  | O => match m with
          | O => true
          | S m' => false
          end
  | S n' => match m with
            | O => false
            | S m' => eqb n' m'
            end
  end.
*)

Fixpoint eqb (n m : nat) : bool :=
  match n, m with
  | O , O => true
  | O , _ => false
  | S _, O => false
  | S n' , S m' => eqb n' m'
  end.

Example test_eqb1: (eqb 3 3) = true.
Proof. simpl. reflexivity. Qed.

Example test_eqb2: (eqb 3 4) = false.
Proof. simpl. reflexivity. Qed.

(* from book
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.
*)

Fixpoint leb (n m : nat) : bool :=
  match n, m with
  | O , _ => true 
  | S _ , O => false
  | S n' , S m' => leb n' m'
  end.

Example test_leb1: (leb 2 2) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb2: (leb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_leb3: (leb 4 2) = false.
Proof. simpl. reflexivity. Qed.

Notation "x =? y" := (eqb x y) (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y) (at level 70) : nat_scope.

Example test_leb3': (4 <=? 2) = false.
Proof. simpl. reflexivity. Qed.

(* Exercise: 4. standard (ltb) *)

Definition ltb (n m : nat) : bool :=
  match minus m n with 
  | O => false
  | S n' => true
  end.

Notation "x <? y" := (ltb x y) (at level 70) : nat_scope.

Example test_ltb1: (ltb 2 2) = false.
Proof. simpl. reflexivity. Qed.

Example test_ltb2: (ltb 2 4) = true.
Proof. simpl. reflexivity. Qed.

Example test_ltb3: (ltb 4 2) = false.
Proof. simpl. reflexivity. Qed.

(** Proof by Simplification *)

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. reflexivity. Qed.

(* _l means on the left *)
Theorem plus_1_l : forall n : nat, 1 + n = S n.
Proof.
  intros n. reflexivity. Qed.

Theorem multi_0_l : forall n : nat, 0 * n = 0.
Proof.
  intros n. reflexivity. Qed.

(** Proof by Rewriting *)

Theorem plus_is_example : forall n m : nat,
  n = m ->
  n + n = m + m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.

(* Exercise: 5. standard (plus_is_exercise) *)

Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.
Proof.
  intros n m o.
  intros H H'.
  rewrite -> H.
  rewrite <- H'.
  reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
  (0 + n) * m = n * m.
Proof.
  intros n m.
  rewrite -> plus_O_n.
  reflexivity. Qed.

(* Exercise: 6. standard (mult S 1) *)

Theorem mult_S_1 : forall n m : nat,
  m = S n ->
  m * (1 + n) = m * m.
Proof.
  intros n m.
  intros H.
  rewrite -> H.
  reflexivity. Qed.


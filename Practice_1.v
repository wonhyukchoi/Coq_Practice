(**
    1) To compile the file, first download the following files

    Coq_Lecture1_Basics.v
    Coq_Lecture2_Induction_List.v
    Coq_Lecture3_Tactics_v

    in the same directory.

    2) Then compile Coq_Lecture3_Tactics_Logic.v by
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List Coq_Lecture3_Tactics_Logic]
*)

Require Import Coq_Lecture3_Tactics_Logic.

(* ################################################################# *)
(** * Problem 1 *)

Lemma double_negb:
  forall b, negb (negb b) = b.
Proof.
  intros. destruct b; reflexivity.
Qed.



(* ################################################################# *)
(** * Problem 2 *)

Module Integer.

  (** In this problem, we will define Integer types together.
      Let's first define Positive Integers. *)

  Inductive Positive :=
  | I (* 1 *)
  | S (p: Positive).

  (** Integer can then be inductively defined using Positive. *)
  Inductive Integer :=
  | O (* 0 *)
  | Pos (p: Positive)
  | Neg (p: Positive).

  (** Please define the negi function to calculate the negation of an integer *)

  Definition negi (i: Integer): Integer :=
    match i with
    | O     => O
    | Pos p => Neg p
    | Neg p => Pos p
    end.

  Example test_negi1: negi O = O.
  Proof. reflexivity. Qed.

  Example test_negi2: negi (Pos I) = Neg I.
  Proof. reflexivity. Qed.


  (** Please define the add1 function to add 1 to the given integer *)
  Definition add1 (i: Integer): Integer :=
    match i with
    | O => Pos I
    | Pos p => Pos (S p)
    | Neg (S p) => Neg p
    | Neg I => O
    end.

  Example test_add11: add1 O = Pos I.
  Proof. reflexivity. Qed.


  Example test_add12: add1 (Neg I) = O.
  Proof. reflexivity. Qed.

  Example test_add13: add1 (Pos I) = Pos (S I).
  Proof. reflexivity. Qed.

End Integer.

(* ################################################################# *)
(** * Problem 3 *)

Module NatPlayground3.

  (** In the class, we have defined our own plus and mult for nat. *)
  Print NatPlayground2.plus.
  Print NatPlayground2.mult.
  (** Let's try to define our own exponential function for nat. *)
  Fixpoint exp (base power : nat) : nat :=
    match power with
    | O => 1
    | S n => base * (exp base n)
    end.

  Lemma exp_1: forall power, exp 1 power = 1.
  Proof.
    intros power. induction power as [|n IHn].
    - reflexivity.
    - simpl. rewrite IHn. reflexivity.
  Qed.

  Eval compute in (exp 2 4).

End NatPlayground3.

(* ################################################################# *)
(** * Problem 4 *)

Module NatPlayground4.

  (** Let's prove some properties of plus and mult  *)
  Theorem plus_assoc : forall m n t : nat,
    m + (n + t) = m + n + t.
  Proof.
    intros m n t.
    induction m as [|m' Ihm].
    - reflexivity.
    - simpl. rewrite Ihm. reflexivity.
  Qed.

  Print plus_comm.

  (** Hint use plus_assoc and plus_comm *)
  Theorem plus_comm' : forall m n t : nat,
      m + n + t = m + t + n.
  Proof.
    intros m n t. induction m as  [|m' Ihm].
    - apply plus_comm.
    - simpl. rewrite Ihm. reflexivity.
  Qed.

  (** Hint use plus_assoc and plus_comm' *)
  Theorem mult_plus_distr : forall m n t : nat,
      m * (n + t) = m * n + m * t.
  Proof.
    intros m n t. induction m as [|m' Ihm]; try reflexivity.
    simpl. rewrite Ihm.
    assert (forall a b c: nat, b=c -> a+b=a+c) as plus_same.
    {
      intros a b c H.
      rewrite H. reflexivity.
    }
    assert (forall x y z w : nat,
        x + y + (z + w) = x + z + (y + w)) as mult_plus_distr'.
    {
      intros x y z w.
      rewrite <- (plus_assoc x y (z+w)).
      rewrite <- (plus_assoc x z (y+w)).
      apply (plus_same x (y+ (z + w)) (z+(y + w))).
      rewrite plus_comm. rewrite <- (plus_assoc z w y).
      apply (plus_same z (w+y) (y+w)).
      apply plus_comm.
    }
    apply mult_plus_distr'.
Qed.

End NatPlayground4.


(* ################################################################# *)
(** * Problem 5 *)

(** Prove the following properties over beq_nat *)
Print beq_nat.

Lemma beq_nat_eq:
  forall n m,
    beq_nat n m = true ->
    n = m.
Proof.
  induction n as [|n' Ihn].
  - intros m H. inversion H as [H1].
    destruct m.
    + reflexivity.
    + inversion H1.
  - intros m H.
    simpl in H.
    destruct m.
    + inversion H.
    + apply Ihn in H.
      rewrite H. reflexivity.
Qed.

Lemma beq_nat_eq':
  forall n m,
    n = m
    -> beq_nat n m = true.
Proof.
  induction n as [|n' Ihn].
  - intros m eq. rewrite <- eq. reflexivity.
  - intros m eq. 
    destruct m.
    + rewrite eq. reflexivity.
    + simpl. apply Ihn. inversion eq. reflexivity.
Qed.


(** Hint: recall the Lecure for logic *)
Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

Theorem beq_nat_neg:
  forall n : nat, beq_nat 0 (S n) = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem beq_nat_neg':
  forall n : nat, beq_nat (S n) 0 = false.
Proof.
  intros n. simpl. reflexivity.
Qed.

Theorem not_zero:
  forall n : nat, 0 <> (S n).
Proof.
  intros n H.
  inversion H.
Qed.

Lemma beq_nat_neq:
  forall n m,
    beq_nat n m = false ->
    n <> m.
Proof.
  induction n as [|n' Ihn].
  - intros m H. inversion H as [H0].
    destruct m.
    + inversion H0.
    + apply not_zero.
  - intros m H. inversion H as [H0].
    destruct m.
    + intro H1. symmetry in H1. inversion H1.
    + intro H1. inversion H1 as [H2].
      apply beq_nat_eq' in H2. rewrite H2 in H0.
      inversion H0.
Qed.

(** Hint use ex_falso_quodlibet *)
Lemma beq_nat_neq':
  forall n m,
    n <> m
    -> beq_nat n m = false.
Proof.
  induction n as [|n' Ihn].
  - intros m H.
    destruct m.
    + apply ex_falso_quodlibet. apply H. reflexivity.
    + apply beq_nat_neg.
  - intros m H.
    destruct m.
    + apply beq_nat_neg'.
    + simpl.
      assert (forall x y : nat, S x <> S y -> x <> y) as neq_nat.
      {
        intros x y H0 H1.
        rewrite H1 in H0.
        destruct y; apply H0; reflexivity.
      }
      apply neq_nat in H.
      apply Ihn in H. exact H.
Qed.


(* ################################################################# *)
(** * Problem 6 *)

(** *** Bags via Lists *)

(** A [bag] (or [multiset]) is like a set, except that each element
    can appear multiple times rather than just once.  One possible
    implementation is to represent a bag of numbers as a list. *)

Definition bag := list nat.

(** Complete the following definitions for the functions
    [count], [sum], [add], and [member] for bags. *)

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | [] => 0
  | x::xs => if beq_nat x v then S(count v xs)
           else count v xs
  end.


(** All these proofs can be done just by [reflexivity]. *)
Example test_count1:              count 1 [1;2;3;1;4;1] = 3.
Proof. reflexivity. Qed.

Example test_count2:              count 6 [1;2;3;1;4;1] = 0.
Proof. reflexivity. Qed.

(** Multiset [sum] is similar to set [union]: [sum a b] contains all
    the elements of [a] and of [b].  (Mathematicians usually define
    [union] on multisets a little bit differently -- using max instead
    of sum -- which is why we don't use that name for this operation.)
    For [sum] we're giving you a header that does not give explicit
    names to the arguments.  Moreover, it uses the keyword
    [Definition] instead of [Fixpoint], so even if you had names for
    the arguments, you wouldn't be able to process them recursively.
    The point of stating the question this way is to encourage you to
    think about whether [sum] can be implemented in another way --
    perhaps by using functions that have already been defined.  *)

Definition sum : bag -> bag -> bag:=
    app.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity. Qed.

Definition add (v:nat) (s:bag) : bag :=
  v::s.

Example test_add1:                count 1 (add 1 [1;4;1]) = 3.
Proof. reflexivity. Qed.

Example test_add2:                count 5 (add 1 [1;4;1]) = 0.
Proof. reflexivity. Qed.

Definition member (v:nat) (s:bag) : bool :=
  if beq_nat (count v s) 0 then false else true.

Example test_member1:             member 1 [1;4;1] = true.
Proof. reflexivity. Qed.

Example test_member2:             member 2 [1;4;1] = false.
Proof. reflexivity. Qed.

(**
    1) To compile the file, first download the following files

    Coq_Lecture4_Program.v
    Coq_Lecture5_Hoare.v

    in the same directory.

    2) Then compile Coq_Lecture4_Program.v and Coq_Lecture5_Hoare.v by
    [coqc Coq_Lecture4_Program.v]
    [coqc Coq_Lecture5_Hoare.v]

*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Import Coq_Lecture4_Program.
Require Export Coq_Lecture5_Hoare.

Local Open Scope aexp_scope.
Local Open Scope bexp_scope.

(** As we discussed in the last lecture, some decorations inof dcom are redundant.
    In this assignment, we will design a new dcom which only contains the pre- and post-conditions,
    plus the loop invariants *)

Inductive dcom : Type :=
| DCSkip
| DCSeq (d1 d2:  dcom)
| DCAsgn (X: string) (e: aexp)
| DCIf (b: bexp) (d1: dcom) (d2: dcom)
| DCWhile (b: bexp) (inv: Assertion) (body: dcom).

Inductive decorated : Type :=
  | Decorated : Assertion -> dcom -> Assertion -> decorated.

Delimit Scope decorated_scope with decorated.

Notation "'SKIP'" := DCSkip.
Notation "l '::=' a"
  := (DCAsgn l a)
       (at level 60, a at next level) : decorated_scope.
Notation "'WHILE' b [[ INV ]] 'DO'  d 'END'"
  := (DCWhile b INV d)
       (at level 80, right associativity) : decorated_scope.
Notation "'IFB' b 'THEN' d 'ELSE' d' 'FI'"
  := (DCIf b d d')
       (at level 80, right associativity) : decorated_scope.
Notation " d ;; d' "
  := (DCSeq d d')
       (at level 80, right associativity) : decorated_scope.
Notation "[[ P ]] d [[ Q ]]"
  := (Decorated P d Q) (at level 90, d at next level) : decorated_scope.

Open Scope decorated_scope.

Example dec_while : decorated :=
  [[ fun st => True ]]
  WHILE !(X =? 0)
  [[ fun _ => True ]]
  DO
    X ::= X .- 1
  END
  [[ fun st => st X = 0 ]].

(* ################################################################# *)
(** * Problem 1 *)
(** It is easy to go from a [dcom] to a [com] by erasing all
    annotations. *)
Fixpoint extract (d:dcom) : com :=
  match d with
  | DCSkip             => SKIP%com
  | DCSeq d1 d2        => (extract d1 ;; extract d2)%com
  | DCAsgn Y e         => (Y ::= e)%com
  | DCIf b d1 d2       => (IFB b THEN extract d1 ELSE extract d2 FI)%com
  | DCWhile b _ body => (WHILE b DO extract body END)%com
  end.

Definition extract_dec (dec : decorated) : com :=
  match dec with
  | Decorated _ d _ => extract d
  end.

Local Open Scope com_scope.

Example extract_correct:
  extract_dec dec_while =
  WHILE !(X =? 0)
  DO
    X ::= X .- 1
  END.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Problem 2 *)
(** It is straightforward to extract the precondition and
    postcondition from a decorated program. *)

Definition pre_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d Q => P
  end.

Definition post_dec (dec : decorated) : Assertion :=
  match dec with
  | Decorated P d Q => Q
  end.

(** We can express what it means for a decorated program to be
    correct as follows: *)
Definition dec_correct (dec : decorated): Prop :=
  {{pre_dec dec}} (extract_dec dec) {{post_dec dec}}.

Example dec_correct_correct:
  dec_correct dec_while =
  {{ fun st => True }}
  WHILE !(X =? 0)
  DO
    X ::= X .- 1
  END
  {{ fun st => st X = 0 }}.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Problem 3 *)
(** To check whether this Hoare triple is _valid_, we need a way to
    extract the "proof obligations" or the verification conditions
    from a decorated program. The function [VC] takes a [dcom] [d] together
    with a postcondition [Q] and returns a pair of assertions (wp, sd).
    [wp] stands for a weak precondition, while [sd] stands for the
    side conditions that have to hold. Note that this wp is not the
    weakest precondition and sd is used to show that the given loop invariants
    satisfy the required conditions*)

Definition assert_implies (P Q : Assertion) : Assertion :=
  fun st =>  P st -> Q st.
Definition assert_and (P Q : Assertion) : Assertion :=
  fun st =>  P st /\ Q st.
Definition assert_not (P : Assertion) : Assertion :=
  fun st =>  ~ P st.
Definition ATrue : Assertion :=
  fun st => True.

Notation "P ->> Q" := (assert_implies P Q) (at level 80).
Notation "P //\ Q" := (assert_and P Q) (at level 70).
Notation "~~ P" := (assert_not P) (at level 60).

Fixpoint VC (d:dcom) (Q : Assertion) : Assertion * Assertion :=
  match d with
    (* Skip: wp is Q and no side conditions *)
  | DCSkip => (Q, ATrue)
    (* Seq: wp is calculated using wp2 of d2.
       sd is the conjunction of sd1 and sd2 since the validity
       of loop invariants are independent
       *)
  | DCSeq d1 d2 =>
    match VC d2 Q with
    | (wp2, sd2) =>
      match VC d1 wp2 with
      | (wp1, sd1) =>
        (wp1, sd1 //\ sd2)
      end
    end
  | DCAsgn X a => (Q [a // X], ATrue)

  (* If: again the validity of loop invariants in different
     branches are independent *)
  | DCIf b d1 d2 =>
    match VC d1 Q, VC d2 Q with
    | (wp1, sd1), (wp2, sd2) =>
      ((bassn b ->> wp1)
         //\ (~~(bassn b) ->> wp2),
       (sd1 //\ sd2))
    end

  (* While: wp is the loop invariants.
     sd checks
     1) inv & b implies the wp of the loop body;
     2) sd of the loop body holds;
     3) inv & ~b implies the post condition *)
  | DCWhile b INV d =>
    (INV,
     match VC d INV with
     | (wp, sd) =>
       (INV //\ bassn b ->> wp)
         //\ sd
         //\ (INV //\ ~~(bassn b) ->> Q)
     end)
end.

(** The verification condition for the decorated program is that
    1) the precondition implies wp;
    2) sd always hold *)
Definition VC_dec (dec : decorated) : Prop :=
  match dec with
  | Decorated P d Q =>
    match VC d Q with
    | (wp, sd) =>
      forall st, (P st -> wp st) /\ sd st
    end
  end.

(** And now the key theorem, stating that [verification_conditions]
    does its job correctly.  Not surprisingly, we need to use each of
    the Hoare Logic rules at some point in the proof. *)
Theorem verification_correct : forall d,
  VC_dec d -> dec_correct d.
Proof.
  destruct d as [P d Q].
  generalize dependent Q.
  generalize dependent P.
  induction d.
  - intros P Q H.
    simpl in H.
    unfold dec_correct.
    unfold dec_correct. unfold pre_dec. unfold post_dec.
    unfold extract_dec. unfold extract.
    assert (forall P, {{P}} CSkip {{P}}) as hoare_skip.
    {
      intros P' st st' H' HP. inversion H'. subst. assumption.
    }
    unfold hoare_triple in *.
    intros.
    pose (H st').
    destruct a.
    apply H2.
    eapply hoare_skip.
    apply H0. exact H1.
  - intros P Q H.
    simpl in H.
    destruct (VC d2 Q) eqn:H0.
    destruct (VC d1 a) eqn:H1.
    unfold dec_correct in *.
    unfold pre_dec in *. unfold post_dec in *.
    unfold extract_dec in *.
    simpl in *. eapply (hoare_seq P a Q).
    Focus 2.
    apply IHd1.
    rewrite H1.
    intros.
    pose (H st).
    destruct a3.
    split. assumption.
    destruct H3. assumption.
    apply IHd2.
    rewrite H0.
    intros.
    pose (H st).
    destruct a3.
    split. auto.
    destruct H3. assumption.
  - intros P Q H. simpl in *.
    unfold dec_correct.
    unfold pre_dec. unfold post_dec.
    unfold extract_dec.
    unfold extract.
    unfold hoare_triple.
    intros.
    pose (H st).
    eapply (hoare_asgn Q X e).
    + apply H0.
    + intuition.
  - unfold dec_correct. unfold pre_dec. unfold post_dec.
    simpl in *.
    intros P Q H.
    pose proof(IHd1 (fun st => P st /\ beval st b = true) Q) as I1.
    pose proof(IHd2 (fun st => P st /\ beval st b = false) Q) as I2.
    destruct (VC d1 Q) as [wp sd] eqn: H0.
    destruct (VC d2 Q) as [wp2 sd2] eqn: H1.
    apply hoare_if.
    + unfold dec_correct in *.
      unfold pre_dec in *. unfold post_dec in *.
      unfold extract_dec in *.
      unfold "->>" in *.
      unfold hoare_triple in *.
      unfold "//\" in *.
      intros.
      destruct H3.
      eapply I1.
      intros.
      pose (H st0).
      destruct a.
      split.
      intros.
      destruct H7.
      destruct H6.
      destruct H5.
      assumption.
      apply H5. assumption.
      destruct H6. assumption.
      apply H2.
      auto.
    + unfold dec_correct in *.
      unfold pre_dec in *. unfold post_dec in *.
      unfold extract_dec in *.
      unfold "->>" in *.
      unfold hoare_triple in *.
      unfold "//\" in *.
      intros.
      destruct H3.
      eapply I2.
      intros.
      pose (H st0).
      destruct a.
      split.
      intros.
      destruct H7.
      destruct H6.
      destruct H5.
      assumption.
      apply H10.
      apply bexp_eval_false in H8.
      assumption.
      destruct H6. assumption.
      apply H2.
      split.
      assumption.
      unfold bassn in *.
      destruct beval.
      simpl in *. Focus 2.
      reflexivity.
      destruct H4.
      reflexivity.
  - unfold dec_correct in *.
    unfold pre_dec in *. unfold post_dec in *.
    unfold extract_dec in *.
    simpl in *.
    intros P Q H.
    unfold assert_and in *.
    unfold assert_implies in *.
    unfold bassn in *.
    unfold assert_not in *.
    unfold hoare_triple in *.
    eapply hoare_weak_pre; eauto; simpl in *.
    eapply hoare_weak_post; eauto; simpl in *.
    apply hoare_while; unfold bassn in *; unfold hoare_triple in *.
    + intros.
      destruct H1.
      pose proof(IHd P Q).
      destruct (VC d Q) as [wp sd].
      eapply H3; clear H3. Focus 2.
      * apply H0.
      * intros st0.
        split. intros.
        admit.
        admit.
      * admit.
    + pose proof(IHd (fun st => P st /\ beval st b = true) P) as I1.
      destruct (VC d P) as [wp sd].
      eapply I1.
      intros.
      split.
      intros.
      destruct H2.
      pose (H st0).
      destruct a.
      simpl in *.
      destruct (VC d inv) as [wp0 sd0].
      destruct H5.
      destruct H5.
      Admitted. 


(* ################################################################# *)
(** * Problem 4 *)
(** Now that all the pieces are in place, we can build tactics to verify programs. *)

Ltac my_simpl :=
  unfold assert_implies, assn_sub, "~~", "//\", bassn, beval, aeval, t_update in *;
  repeat simpl in *; intros;
  repeat match goal with
         | [ H0: _ /\ _ |- _ ] => destruct H0
         end;
  simplb; eauto; try omega; try congruence.

Ltac verify :=
  intros;
  match goal with
  | [|- dec_correct _ ] =>
    apply verification_correct;
    simpl; repeat split; repeat my_simpl
  end.


(* ################################################################# *)
(** * Problem 5 *)
(** In this program, we use the automation developed above to verify
    formal decorated programs. *)

Theorem dec_while_correct :
  dec_correct dec_while.
Proof.
  verify.
Qed.


Open Scope decorated_scope.

Example subtract_slowly_dec (m:nat) (p:nat) : decorated :=
  [[ fun st => st X = m /\ st Z = p ]]
  WHILE ! (X =? 0)
  [[ fun st => st Z - st X = p - m ]]
  DO
     Z ::= Z .- 1;;
     X ::= X .- 1
  END
  [[ fun st => st Z = p - m ]].

Theorem subtract_slowly_dec_correct : forall m p,
    dec_correct (subtract_slowly_dec m p).
Proof. verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Swapping Using Addition and Subtraction *)
Open Scope com_scope.

Definition swap : com :=
  X ::= X .+ Y;;
  Y ::= X .- Y;;
  X ::= X .- Y.

Open Scope decorated_scope.

Definition swap_dec m n : decorated :=
  [[ fun st => st X = m /\ st Y = n ]]
  X ::= X .+ Y ;;
  Y ::= X .- Y ;;
  X ::= X .- Y
  [[ fun st => st X = n /\ st Y = m]].

Theorem swap_correct : forall m n,
    dec_correct (swap_dec m n).
Proof. verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Simple Conditionals *)
Definition if_minus_plus_com :=
  IFB X <=? Y
  THEN Z ::= Y .- X
  ELSE Y ::= X .+ Z
  FI.

Definition if_minus_plus_dec :=
  [[ fun st => True ]]
  IFB X <=? Y  THEN
    Z ::= Y .- X
  ELSE
    Y ::= X .+ Z
  FI
  [[ fun st => st Y = st X + st Z ]].

Theorem if_minus_plus_correct :
  dec_correct if_minus_plus_dec.
Proof. verify. Qed.

Definition if_minus_dec :=
  [[ fun st => True ]]
  IFB X <=? Y THEN
    Z ::= Y .- X
  ELSE
    Z ::= X .- Y
  FI
  [[ fun st => st Z + st X = st Y \/ st Z + st Y = st X ]].

Theorem if_minus_correct :
  dec_correct if_minus_dec.
Proof.
  verify.
Qed.


(* ----------------------------------------------------------------- *)
(** *** Division *)
Definition div_mod_dec (a b : nat) : decorated :=
  [[ fun st => True ]]
  X ::= a ;;
  Y ::= 0 ;;
  WHILE b <=? X
  [[ fun st => b * st Y + st X = a ]]
  DO
    X ::= X .- b ;;
    Y ::= Y .+ 1
  END
  [[ fun st => b * st Y + st X = a /\ (st X < b) ]].

Theorem div_mod_dec_correct : forall a b,
  dec_correct (div_mod_dec a b).
Proof.
  verify.
  rewrite mult_plus_distr_l.
  omega.
Qed.

Local Opaque minus mult plus.

(* ----------------------------------------------------------------- *)
(** *** Square Roots *)
Definition sqrt_dec m : decorated :=
  [[ fun st => st X = m ]]
  Z ::= 0 ;;
  WHILE (Z .+ 1) .* (Z .+ 1) <=? X
  [[ fun st => st X = m /\ st Z*st Z<=m ]]
  DO
    Z ::= Z .+ 1
  END
  [[ fun st => st Z*st Z<=m /\ m<(st Z+1)*(st Z+1) ]].

Theorem sqrt_correct : forall m,
  dec_correct (sqrt_dec m).
Proof. verify. Qed.

(* ----------------------------------------------------------------- *)
(** *** Two loops *)
Definition two_loops_dec (a b c : nat) : decorated :=
  [[ fun st => True ]]
  X ::= 0 ;;
  Y ::= 0 ;;
  Z ::= c ;;
  WHILE !(X =? a)
  [[ fun st => st Z = st X + c /\ st Y = 0 ]]
  DO
    X ::= X .+ 1 ;;
    Z ::= Z .+ 1
  END ;;
  WHILE !(Y =? b)
  [[ fun st => st Z = a + st Y + c ]]
  DO
    Y ::= Y .+ 1 ;;
    Z ::= Z .+ 1
  END
  [[ fun st => st Z = a + b + c ]].

Theorem two_loops_correct : forall a b c,
  dec_correct (two_loops_dec a b c).
Proof. verify. Qed.

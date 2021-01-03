(** 
    1) To compile the file, first download the following files
    
    Coq_Lecture4_Program.v              
    
    in the same directory.
    
    2) Then compile Coq_Lecture4_Program.v by
    [coqc Coq_Lecture4_Program]

*)

Require Import Coq.Bool.Bool.
Require Import Coq.Arith.Arith.
Require Import Coq.Arith.EqNat.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Import ListNotations.

Require Export Coq_Lecture4_Program.

(** * Problem 1 ~ Problem 6 *)
(** Imperative languages like C and Java often include a [break] or
    similar statement for interrupting the execution of loops. In this
    assignment we consider how to add [break] to Imp.  First, we need to
    enrich the language of commands with an additional case. *)

Inductive com : Type :=
  | CSkip : com
  | CBreak : com               (* <-- new *)
  | CAss : string -> aexp -> com
  | CSeq : com -> com -> com
  | CIf : bexp -> com -> com -> com
  | CWhile : bexp -> com -> com.

Notation "'SKIP'" :=
  CSkip.
Notation "'BREAK'" :=
  CBreak.
Notation "x '::=' a" :=
  (CAss x a) (at level 60).
Notation "c1 ;; c2" :=
  (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" :=
  (CWhile b c) (at level 80, right associativity).
Notation "'IFB' c1 'THEN' c2 'ELSE' c3 'FI'" :=
  (CIf c1 c2 c3) (at level 80, right associativity).

(** Next, we need to define the behavior of [BREAK].  Informally,
    whenever [BREAK] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [BREAK]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [BREAK]. In those cases, [BREAK] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X ::= 0;;
       Y ::= 1;;
       WHILE 0 <> Y DO
         WHILE TRUE DO
           BREAK
         END;;
         X ::= 1;;
         Y ::= Y .- 1
       END

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [BREAK] statement: *)

Inductive result : Type :=
  | SContinue : result
  | SBreak : result.

Reserved Notation "c1 '/' st '\\' s '/' st'"
                  (at level 40, st, s at level 39).

(** Intuitively, [c / st \\ s / st'] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[c / st \\ s / st']" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([c / st \\ st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [SKIP], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [BREAK], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [IFB b THEN c1 ELSE c2 FI], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ;; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [WHILE b DO c END], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [BREAK] only terminates the
      innermost loop, [WHILE] signals [SContinue]. *)

(* ################################################################# *)
(** * Problem 1 *)

(** Based on the above description, complete the definition of the
    [ceval] relation. *)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
      SKIP / st \\ SContinue / st
  | E_Break : forall st,
      BREAK / st \\ SBreak / st
  | E_Ass: forall st a1 n x,
      aeval st a1 = n ->
      (x ::= a1) / st \\ SContinue / st & {x --> n}
  | E_Seq_Continue: forall c1 c2 r st st' st'',
      c1 / st \\ SContinue / st' ->
      c2 / st' \\ r / st'' ->
      (c1;; c2) / st \\ r / st''
  | E_Seq_Break : forall c1 c2 st st',
      c1 / st \\ SBreak / st' ->
      (c1;; c2) / st \\ SBreak / st'
  | E_IfTrue: forall st st' b c1 c2 r,
      beval st b = true ->
      c1 / st \\ r / st' ->
     (IFB b THEN c1 ELSE c2 FI) / st \\ r / st'
  | E_IfFalse: forall st st' b c1 c2 r,
      beval st b = false ->
      c2 / st \\ r / st' ->
      (IFB b THEN c1 ELSE c2 FI) / st \\ r / st'
  | E_WhileFalse: forall b st c,
      beval st b = false ->
      (WHILE b DO c END) / st \\ SContinue / st
  | E_While_Break: forall st st' b c,
      beval st b = true ->
      c / st \\ SBreak / st' ->
      (WHILE b DO c END) / st \\ SContinue / st'
  | E_While_Continue: forall st st' st'' b c,
      beval st b = true ->
      c / st \\ SContinue / st' ->
      (WHILE b DO c END) / st' \\ SContinue / st'' ->
      (WHILE b DO c END) / st \\ SContinue / st''

  where "c1 '/' st '\\' s '/' st'" := (ceval c1 st s st').

Local Open Scope aexp_scope.
Local Open Scope bexp_scope.

Definition example: com :=
  X ::= 0;;
  Y ::= 1;;
  WHILE !(0 =? Y) DO
    WHILE true DO
      BREAK
    END;;
    X ::= 1;;
    Y ::= Y .- 1
  END.

Ltac inversion_program st :=
  match goal with
  | [Htf: true = false |- _] => inversion Htf
  | [Hft: false = true |- _] => inversion Hft
  | [Hst0: _ / ?st0 \\ _ / _  |- _ ] =>
    match st0 with
    | context[st] => (* context[st] means that the term contains st*)
      inversion Hst0; subst; simpl in *; clear Hst0
    end
  end.

Theorem ceval_example:
  forall st st',
    example / st \\ SContinue / st' ->
    st' X = 1 /\ st' Y = 0.
Proof.
  intros.
  repeat inversion_program st.
  rewrite t_update_eq.
  rewrite t_update_neq.
  - rewrite t_update_eq. split; reflexivity.
  - intro HF; inversion HF. 
Qed.

(* ################################################################# *)
(** * Problem 2 *)
Theorem break_ignore : forall c st st' s,
     (BREAK;; c) / st \\ s / st' ->
     st = st'.
Proof.
  intros c st st' s H.
  inversion H; subst.
  - inversion H2.
  - inversion H5. reflexivity.
Qed.


(* ################################################################# *)
(** * Problem 3 *)
Theorem while_continue : forall b c st st' s,
  (WHILE b DO c END) / st \\ s / st' ->
  s = SContinue.
Proof.
  intros b c st st' s H.
  inversion H; reflexivity.
Qed.


(* ################################################################# *)
(** * Problem 4 *)
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  c / st \\ SBreak / st' ->
  (WHILE b DO c END) / st \\ SContinue / st'.
Proof.
  intros b c st st' H H0.
  apply E_While_Break.
  - exact H.
  - exact H0.
Qed.


(* ################################################################# *)
(** * Problem 5 *)
(** Hint: use induction over He **)
Theorem while_break_true :
  forall p b c st st' 
         (Heq: p = (WHILE b DO c END))
         (He: p / st \\ SContinue / st')
         (Heval: beval st' b = true),
    exists st'', c / st'' \\ SBreak / st'.
Proof.
  intros p b c st st' Heq He Heval.
  induction He; try (inversion Heq); subst.
  rewrite H in Heval.
  - inversion Heval.
  - exists st. exact He.
  - apply IHHe2.
    + reflexivity.
    + exact Heval.
Qed.


(* ################################################################# *)
(** * Problem 6 *)
(** Hint: refer to the deterministic for the original com taught in class **)
Theorem ceval_deterministic: forall (c:com) st st1 st2 s1 s2,
     c / st \\ s1 / st1  ->
     c / st \\ s2 / st2 ->
     st1 = st2 /\ s1 = s2.
Proof.
  intros c st st1 st2 s1 s2 E1.
  revert st2 s2.
  induction E1; intros st2 s2 E2; inversion E2; subst.
  - split; reflexivity.
  - split; reflexivity.
  - split; reflexivity.
  - apply IHE1_1 in H1. destruct H1.
        subst. apply IHE1_2. assumption.
  - apply IHE1_1 in H4. inversion H4. discriminate.
  - apply IHE1 in H1. inversion H1. discriminate.
  - split; try reflexivity. apply IHE1 in H4.
    inversion H4. assumption.
  - apply IHE1 in H7. assumption.
  - rewrite H in H6. discriminate.
  - rewrite H in H6. discriminate.
  - apply IHE1 in H7. assumption.
  - split;reflexivity.
  - rewrite H in H2. discriminate.
  - rewrite H in H2. discriminate.
  - rewrite H in H5. discriminate.
  - split; try reflexivity. apply IHE1 in H6.
    inversion H6. assumption.
  - split;try reflexivity. apply IHE1 in H3.
    inversion H3. discriminate.
  - rewrite H in H5. discriminate.
  - split; try reflexivity. apply IHE1_1 in H6.
    inversion H6. discriminate.
  - apply IHE1_1 in H3. inversion H3.
    split; try reflexivity.
    eapply IHE1_2. rewrite H0.
    apply H7.
Qed.

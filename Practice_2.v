(** 
    1) To compile the file, first download the following files
    
    Coq_Lecture1_Basics.v
    Coq_Lecture2_Induction_List.v
    Coq_Lecture3_Tactics_Logic.v 
    Coq_Lecture4_Program.v              
    
    in the same directory.
    
    2) Then compile Coq_Lecture4_Program.v by
    [coqc Coq_Lecture1_Basics Coq_Lecture2_Induction_List Coq_Lecture3_Tactics_Logic Coq_Lecture4_Program]
    
*)

Require Export Coq_Lecture3_Tactics_Logic Coq_Lecture4_Program.

(* ################################################################# *)
(** * Problem 1 *)

(** Prove the following Theorem  *)
Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b.
  destruct (f true) eqn:ftrue.
  - rewrite ftrue. apply ftrue.
  - destruct (f false) eqn:ffalse.
    + apply ftrue.
    + apply ffalse.
  - destruct (f false) eqn:ffalse; destruct (f true) eqn:ftrue.
    + apply ftrue.
    + apply ffalse.
    + rewrite ffalse. apply ffalse.
    + rewrite ffalse. apply ffalse.
Qed.


(* ################################################################# *)
(** * Problem 2 *)

(** Prove by induction. *)

Theorem filter_exercise : forall (X : Type) (l lf : list X) (test : X -> bool)
                             (x : X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X l lf test x eq.
  induction l as [|l' l].
  - inversion eq.
  - simpl in eq. destruct (test l') eqn:testl'.
    + inversion eq. rewrite <- H0. apply testl'.
    + apply IHl. apply eq.
Qed.



(* ################################################################# *)
(** * Problem 3 ~ Problem 6 *)
(** Old HP Calculators, programming languages like Forth and Postscript,
    and abstract machines like the Java Virtual Machine all evaluate
    arithmetic expressions using a _stack_. For instance, the expression

      (2*3)+(3*(4-2))

   would be written as

      2 3 * 3 4 2 - * +

   and evaluated like this (where we show the program being evaluated
   on the right and the contents of the stack on the left):

      [ ]           |    2 3 * 3 4 2 - * +
      [2]           |    3 * 3 4 2 - * +
      [3, 2]        |    * 3 4 2 - * +
      [6]           |    3 4 2 - * +
      [3, 6]        |    4 2 - * +
      [4, 3, 6]     |    2 - * +
      [2, 4, 3, 6]  |    - * +
      [2, 3, 6]     |    * +
      [6, 6]        |    +
      [12]          |

  The goal of the following problems is to write a small compiler that
  translates [aexp]s into stack machine instructions.

  The instruction set for our stack language will consist of the
  following instructions:
     - [SPush n]: Push the number [n] on the stack.
     - [SLoad x]: Load the identifier [x] from the store and push it
                  on the stack
     - [SPlus]:   Pop the two top numbers from the stack, add them, and
                  push the result onto the stack.
     - [SMinus]:  Similar, but subtract.
     - [SMult]:   Similar, but multiply. *)

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : string -> sinstr
| SPlus : sinstr
| SMinus : sinstr
| SMult : sinstr.

(* ################################################################# *)
(** * Problem 3 *)

(** Write a function to evaluate programs in the stack language. It
    should take as input a state, a stack represented as a list of
    numbers (top stack item is the head of the list), and a program
    represented as a list of instructions, and it should return the
    stack after executing the program.  Test your function on the
    examples below.

    Note that the specification leaves unspecified what to do when
    encountering an [SPlus], [SMinus], or [SMult] instruction if the
    stack contains less than two elements. The function should return
    None for these unspecified cases. But our compiler will never 
    emit such a malformed program. *)

(** Execute an instruction **)
Definition s_execute_instr (st : state) (stack : list nat)
         (instr : sinstr)
  : option (list nat) :=
  match instr with
  | SPush n => Some (n :: stack)
  | SLoad x => Some (st x :: stack)
  | SPlus => match stack with
            | x :: y :: stack' => Some (x+y :: stack')
            | _ => None
            end
  | SMinus => match stack with
             | x :: y :: stack' => Some (y-x :: stack')
             | _ => None
             end
  | SMult => match stack with
            | x :: y :: stack' => Some (x*y::stack')
            | _ => None
            end
  end.

(** Execute a program **)                                           
Fixpoint s_execute (st : state) (stack : list nat)
                   (prog : list sinstr)
  : option (list nat) :=
  match prog with
  | [] => Some (stack)
  | instr::prog' => match (s_execute_instr st stack instr) with
                  | Some stack' => s_execute st stack' prog'
                  | None => None
                  end
  end.

Example s_execute1 :
     s_execute { --> 0 } []
       [SPush 5; SPush 3; SPush 1; SMinus]
     = Some [2; 5].
Proof. reflexivity. Qed.

Example s_execute2 :
     s_execute { X --> 3 } [3;4]
       [SPush 4; SLoad X; SMult; SPlus]
   = Some [15; 4].
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Problem 4 *)

(** Next, write a function that compiles an [aexp] into a stack
    machine program. The effect of running the program should be the
    same as pushing the value of the expression on the stack. *)


Print aexp.

Fixpoint s_compile (e : aexp) : list sinstr :=
  match e with
  | ANum n => [SPush n]
  | AId var => [SLoad var]
  | APlus exp1 exp2 => s_compile exp1 ++ s_compile exp2 ++ [SPlus]
  | AMinus exp1 exp2 => s_compile exp1 ++ s_compile exp2 ++ [SMinus]
  | AMult exp1 exp2 => s_compile exp1 ++ s_compile exp2 ++ [SMult]
  end.


(** After you've defined [s_compile], prove the following to test
    that it works. *)

Local Open Scope aexp_scope.

Example s_compile1 :
  s_compile (X .- (2 .* Y))
  = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * Problem 5 *)

(** Prove the following property for s_execute *)


Theorem s_execute_mono : forall (l1 l2: list sinstr) (sk sk': list nat) (st : state),
  s_execute st sk l1 = Some sk' ->
  s_execute st sk (l1 ++ l2) = s_execute st sk' l2.
Proof.
  intros l1.
  induction l1 as [| l1' l1].
  - intros l2 sk sk' st H. simpl.
    inversion H. reflexivity.
  - intros l2 sk sk' st H.
    assert (forall (x:sinstr) (xs ys: list sinstr), (x::xs) ++ys = x::(xs++ys)) as app_comm_cons.
    {
      auto.
    }
    rewrite app_comm_cons.
    unfold s_execute in *. destruct (s_execute_instr st sk l1').
    + eapply IHl1. apply H.
    + inversion H.
Qed.




(* ################################################################# *)
(** * Problem 6 *)
    
(** Now we'll prove the correctness of the compiler implemented in the
    previous exercise.  Remember that the specification left
    unspecified what to do when encountering an [SPlus], [SMinus], or
    [SMult] instruction if the stack contains less than two
    elements.  (In order to make your correctness proof easier you
    might find it helpful to go back and change your implementation!)

    Prove the following theorem.  You will need to start by stating a
    more general lemma to get a usable induction hypothesis; the main
    theorem will then be a simple corollary of this lemma. *)

Require Export Coq.omega.Omega.
Require Export Coq.Arith.Mult.

Theorem s_compile_correct' : forall (e : aexp) (sk: list nat) (st : state),
  s_execute st sk (s_compile e) = Some (aeval st e :: sk).
Proof.
  intros e.
  induction e.
  - intros sk st. reflexivity.
  - intros sk st. reflexivity.
  - simpl. intros.
    erewrite s_execute_mono. Focus 2.
    apply IHe1.
    erewrite s_execute_mono. Focus 2.
    apply IHe2.
    simpl. replace (aeval st e2 + aeval st e1) with (aeval st e1 + aeval st e2).
    reflexivity. omega.
  - simpl. intros.
    erewrite s_execute_mono. Focus 2.
    apply IHe1.
    erewrite s_execute_mono. Focus 2.
    apply IHe2.
    simpl. replace (aeval st e2 + aeval st e1) with (aeval st e1 + aeval st e2).
    reflexivity. omega.
  - simpl. intros.
    erewrite s_execute_mono. Focus 2.
    apply IHe1.
    erewrite s_execute_mono. Focus 2.
    apply IHe2.
    simpl. replace (aeval st e2 * aeval st e1) with (aeval st e1 * aeval st e2).
    reflexivity. apply mult_comm.
Qed.


Theorem s_compile_correct : forall (st : state) (e : aexp),
  s_execute st [] (s_compile e) = Some [ aeval st e ].
Proof.
  intros st e.
  erewrite s_compile_correct'. reflexivity.
Qed.

(** * Imp: Simple Imperative Programs *)

(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp.
Set Default Goal Selector "!".

(** Next, we need to define the behavior of [break].  Informally,
    whenever [break] is executed in a sequence of commands, it stops
    the execution of that sequence and signals that the innermost
    enclosing loop should terminate.  (If there aren't any
    enclosing loops, then the whole program simply terminates.)  The
    final state should be the same as the one in which the [break]
    statement was executed.

    One important point is what to do when there are multiple loops
    enclosing a given [break]. In those cases, [break] should only
    terminate the _innermost_ loop. Thus, after executing the
    following...

       X := 0;
       Y := 1;
       while 0 <> Y do
         while true do
           break
         end;
         X := 1;
         Y := Y - 1
       end

    ... the value of [X] should be [1], and not [0].

    One way of expressing this behavior is to add another parameter to
    the evaluation relation that specifies whether evaluation of a
    command executes a [break] statement: *)

Inductive result : Type :=
  | SContinue
  | SBreak.

Reserved Notation "st '=[' c ']=>' st' '/' s"
     (at level 40, c custom com at level 99, st' constr at next level).

(** Intuitively, [st =[ c ]=> st' / s] means that, if [c] is started in
    state [st], then it terminates in state [st'] and either signals
    that the innermost surrounding loop (or the whole program) should
    exit immediately ([s = SBreak]) or that execution should continue
    normally ([s = SContinue]).

    The definition of the "[st =[ c ]=> st' / s]" relation is very
    similar to the one we gave above for the regular evaluation
    relation ([st =[ c ]=> st']) -- we just need to handle the
    termination signals appropriately:

    - If the command is [skip], then the state doesn't change and
      execution of any enclosing loop can continue normally.

    - If the command is [break], the state stays unchanged but we
      signal a [SBreak].

    - If the command is an assignment, then we update the binding for
      that variable in the state accordingly and signal that execution
      can continue normally.

    - If the command is of the form [if b then c1 else c2 end], then
      the state is updated as in the original semantics of Imp, except
      that we also propagate the signal from the execution of
      whichever branch was taken.

    - If the command is a sequence [c1 ; c2], we first execute
      [c1].  If this yields a [SBreak], we skip the execution of [c2]
      and propagate the [SBreak] signal to the surrounding context;
      the resulting state is the same as the one obtained by
      executing [c1] alone. Otherwise, we execute [c2] on the state
      obtained after executing [c1], and propagate the signal
      generated there.

    - Finally, for a loop of the form [while b do c end], the
      semantics is almost the same as before. The only difference is
      that, when [b] evaluates to true, we execute [c] and check the
      signal that it raises.  If that signal is [SContinue], then the
      execution proceeds as in the original semantics. Otherwise, we
      stop the execution of the loop, and the resulting state is the
      same as the one resulting from the execution of the current
      iteration.  In either case, since [break] only terminates the
      innermost loop, [while] signals [SContinue]. *)

(** 3.1. TODO: Based on the above description, complete the definition of the
               [ceval] relation. 
*)

Inductive ceval : com -> state -> result -> state -> Prop :=
  | E_Skip : forall st,
               st =[ <{ skip }> ]=> st / SContinue
  | E_Break : forall st,
                st =[ <{ break }> ]=> st / SBreak
  | E_Asgn : forall st y n x,
              aeval st y = n ->
              st =[ <{ x := y }> ]=> (x !-> n ; st) / SContinue
  | E_IfTrue : forall st st' cond x y s,
                beval st cond = true ->
                st =[ x ]=> st' / s ->
                st =[ <{ if cond then x else y end }> ]=> st' / s
  | E_IfFalse : forall st st' cond x y s,
                  beval st cond = false ->
                  st =[ y ]=> st' / s ->
                  st =[ <{ if cond then x else y end }> ]=> st' / s
  | E_Seq_Break : forall x y st st',
                    st =[ x ]=> st' / SBreak ->
                    st =[ <{ x ; y }> ]=> st' / SBreak
  | E_Seq_Continue : forall x y st st' st'' s,
                      st =[ x ]=> st' / SContinue ->
                      st' =[ y ]=> st'' / s ->
                      st =[ <{ x ; y }> ]=> st'' / s
  | E_While_False : forall cond st x,
                      beval st cond = false ->
                      st =[ <{ while cond do x end }> ]=> st / SContinue
  | E_While_True_Break : forall st st' cond x,
                          beval st cond = true ->
                          st =[ x ]=> st' / SBreak ->
                          st =[ <{ while cond do x end }> ]=> st' / SContinue
  | E_While_True_Continue : forall st st' st'' cond x s,
                              beval st cond = true ->
                              st =[ x ]=> st' / SContinue ->
                              st' =[ <{ while cond do x end }> ]=> st'' / s ->
                              st =[ <{ while cond do x end }> ]=> st'' / SContinue

  where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').


(** 
  3.2. TODO: Prove the following six properties of your definition of [ceval].
             Note that your semantics needs to satisfy these properties: if any of 
             these properties becomes unprovable, you should revise your definition of `ceval`. 
             Add a succint comment before each property explaining the property in your own words.
*)

(**
  The theorem means that when a program starts with a `break` its state does not change, since its execution
  will terminate immediately after the execution of the `break`, without executing the subsequent instructions.
*)
Theorem break_ignore : forall c st st' s,
     st =[ break; c ]=> st' / s ->
     st = st'.
Proof.
  intros c st st' s H.
  inversion H; subst.
  - inversion H5. reflexivity. 
  - inversion H2.
Qed.

(**
  The theorem means that every `while` loop terminates with result SContinue.
*)
Theorem while_continue : forall b c st st' s,
  st =[ while b do c end ]=> st' / s ->
  s = SContinue.
Proof.
  intros b c st st' s H.
  inversion H; subst; reflexivity.
Qed.

(**
  The theorem means that when the block of a `while` loop raises a SBreak signal,
  the loop terminates with result SContinue.
*)
Theorem while_stops_on_break : forall b c st st',
  beval st b = true ->
  st =[ c ]=> st' / SBreak ->
  st =[ while b do c end ]=> st' / SContinue.
Proof.
  intros b c st st' H H'.
  apply E_While_True_Break; assumption.
Qed.

(**
  The theorem means that if the first instruction of a sequence raises a SContinue signal, and the second one too,
  the resulting state of executing the sequence is the one resulting from executing both instructions consecutively,
  and it also raises a SContinue signal.
*)
Theorem seq_continue : forall c1 c2 st st' st'',
  st =[ c1 ]=> st' / SContinue ->
  st' =[ c2 ]=> st'' / SContinue ->
  st =[ c1 ; c2 ]=> st'' / SContinue.
Proof.
  intros c1 c2 st st' st'' H H'.
  apply E_Seq_Continue with st'; assumption.
Qed.

(**
  The theorem means that if the first instruction of a sequence raises a SBreak signal, the resulting state of
  executing the sequence is the one resulting from executing only the first instruction, and it also raises a
  SBreak signal.
*)
Theorem seq_stops_on_break : forall c1 c2 st st',
  st =[ c1 ]=> st' / SBreak ->
  st =[ c1 ; c2 ]=> st' / SBreak.
Proof.
  intros c1 c2 st st' H.
  apply E_Seq_Break.
  assumption.
Qed.

(**
  The theorem means that if a `while` loop terminates after a certain iteration, and the condition of the `while`
  is true when applied to the state resulting from that iteration, then there is a state that, when executing the
  block of the `while` on that state, it raises a SBreak signal.
*)
Theorem while_break_true : forall b c st st',
  st =[ while b do c end ]=> st' / SContinue ->
  beval st' b = true ->
  exists st'', st'' =[ c ]=> st' / SBreak.
Proof.
  intros b c st st' H H'.
  remember <{ while b do c end }> as _while.
  induction H; inversion Heq_while; subst.
  - rewrite H in H'. discriminate H'.
  - exists st. assumption.
  - apply IHceval2.
    + reflexivity.
    + assumption.
Qed.

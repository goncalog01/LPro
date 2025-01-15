(* ################################################################# *)
(** * Additional Properties 

      It might be a good idea to read the relevant book chapters/sections before or as you
      develop your solution. The properties below are discussed and some of them proved
      for the original Imp formulation.
*)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From FirstProject Require Import Maps Imp Interpreter RelationalEvaluation.
Set Default Goal Selector "!".


(**
  3.2. TODO: Prove all the properties below that are stated without proof.
             Add a succint comment before each property explaining the property in your own words.
*)

(* ################################################################# *)
(** * Property of the Step-Indexed Interpreter *)

(**
  The theorem means that, after a certain number of steps, eventually a program always terminates with the same state and result,
  regardless of how many more steps are executed after that.
*)
Theorem ceval_step_more: forall i1 i2 st st' res c,
i1 <= i2 ->
ceval_step st c i1 = Some (st', res) ->
ceval_step st c i2 = Some (st', res).
Proof.
  induction i1 as [|i1']; intros i2 st st' res c Hle Hceval.
  - simpl in Hceval. discriminate Hceval.
  - destruct i2 as [|i2']; inversion Hle; assert (Hle': i1' <= i2') by lia; destruct c.
    + simpl in Hceval. inversion Hceval. reflexivity.
    + simpl in Hceval. inversion Hceval. reflexivity.
    + simpl in Hceval. inversion Hceval. reflexivity.
    + simpl in Hceval. simpl. destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * destruct p. apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. rewrite <- H0. assumption.
      * rewrite <- H0. rewrite Heqst1'o. assumption.
    + simpl in Hceval. simpl. destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.
    + simpl in Hceval. simpl. destruct (beval st b); try assumption. destruct (ceval_step st c i1') eqn: Heqst1'o.
      * destruct p. apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. rewrite <- H0. assumption.
      * rewrite <- H0. rewrite Heqst1'o. discriminate.
    + simpl in Hceval. inversion Hceval. reflexivity.
    + simpl in Hceval. inversion Hceval. reflexivity.
    + simpl in Hceval. inversion Hceval. reflexivity.
    + simpl in Hceval. simpl. destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      * destruct p. apply (IHi1' i2') in Heqst1'o; try assumption. rewrite Heqst1'o. destruct r; try assumption.
        apply IHi1'; try assumption.
      * discriminate Hceval.
    + simpl in Hceval. simpl. destruct (beval st b); apply (IHi1' i2') in Hceval; try assumption.
    + simpl in Hceval. simpl. destruct (beval st b); try assumption. destruct (ceval_step st c i1') eqn: Heqst1'o.
      * destruct p. apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. destruct r; try assumption.
        apply IHi1'; try assumption.
      * discriminate Hceval.
Qed.

(* ################################################################# *)
(** * Relational vs. Step-Indexed Evaluation *)

(** As for arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation would actually
    amount to the same thing in the end.  This section shows that this
    is the case. *)

(**
  The theorem means that, if there is a program that when passed to the step-indexed evaluator with an initial state st,
  after a certain number of execution steps, terminates with state st' and result res, then there is a relation in the
  relational evaluator that represents that same execution.
*)
Theorem ceval_step__ceval: forall c st st' res,
    (exists i, ceval_step st c i = Some (st', res)) ->
    st =[ c ]=> st' / res.
Proof.
intros c st st' res H.
inversion H as [i E].
clear H.
generalize dependent res.
generalize dependent st'.
generalize dependent st.
generalize dependent c.
induction i as [| i' ].
- intros c st st' res H. simpl in H. discriminate H.
- intros c st st' res H. destruct c; simpl in H; inversion H; subst; clear H.
  + apply E_Skip.
  + apply E_Break.
  + apply E_Asgn. reflexivity.
  + destruct (ceval_step st c1 i') eqn:Heqr1.
    * destruct p. destruct res.
      ** apply E_Seq_Continue with s.
        *** apply IHi'. rewrite Heqr1. destruct r.
          **** reflexivity.
          **** discriminate.
        *** apply IHi'. destruct r.
          **** assumption.
          **** discriminate H1.
      ** destruct r.
        *** apply E_Seq_Continue with s; apply IHi'; try assumption.
        *** apply E_Seq_Break. apply IHi'. rewrite Heqr1. assumption.
    * discriminate H1.
  + destruct (beval st b) eqn:Heqr.
    * apply E_IfTrue; try assumption. apply IHi'. assumption.
    * apply E_IfFalse; try assumption. apply IHi'. assumption.
  + destruct (beval st b) eqn:Heqr.
    * destruct (ceval_step st c i') eqn:Heqr1.
      ** destruct p. destruct res; destruct r.
        *** apply E_While_True_Continue with s SContinue; try assumption.
          **** apply IHi'. assumption.
          **** apply IHi'. assumption.
        *** apply E_While_True_Break; try assumption.
            apply IHi'. rewrite Heqr1. inversion H1. reflexivity.
        *** apply IHi' in H1. inversion H1.
        *** discriminate H1.
      ** discriminate H1.
    * destruct res.
      ** inversion H1. apply E_While_False. rewrite <- H0. assumption.
      ** discriminate H1.
Qed.

(** 
  TODO: For the following proof, you'll need [ceval_step_more] in a
  few places, as well as some basic facts about [<=] and [plus]. *)

(**
  The theorem means that, if there is a relation in the relational evaluator that represents the execution of a program
  that starts in state st and terminates in state st' with result res, then that same execution can be replicated in the
  step-indexed evaluator after a certain number of execution steps.
*)
Theorem ceval__ceval_step: forall c st st' res,
    st =[ c ]=> st' / res ->
    exists i, ceval_step st c i = Some (st', res).
Proof.
  intros c st st' res Hce.
  induction Hce.
    - exists 1. simpl. reflexivity.
    - exists 1. simpl. reflexivity.
    - exists 1. simpl. rewrite H. reflexivity.
    - destruct IHHce. exists (1 + x0). simpl. rewrite H. assumption.
    - destruct IHHce. exists (1 + x0). simpl. rewrite H. assumption.
    - destruct IHHce. exists (1 + x0). simpl. rewrite H. reflexivity.
    - destruct IHHce1. destruct IHHce2. exists (1 + x0 + x1). simpl. destruct (ceval_step st x (x0 + x1)) eqn:eqstep.
      + apply ceval_step_more with (i2 := x0 + x1) in H.
        * rewrite H in eqstep. inversion eqstep. subst. apply ceval_step_more with (i1 := x1).
          ** lia.
          ** assumption.
        * lia.
      + apply ceval_step_more with (i2 := x0 + x1) in H.
        * rewrite eqstep in H. discriminate H.
        * lia.
    - exists 1. simpl. rewrite H. reflexivity.
    - destruct IHHce. exists (1 + x0). simpl. rewrite H. destruct (ceval_step st x x0) eqn:eqstep.
      + destruct p. destruct r.
        * discriminate H0.
        * inversion H0. reflexivity.
      + discriminate H0.
    - destruct IHHce1. destruct IHHce2. exists (1 + x0 + x1). simpl. rewrite H. destruct (ceval_step st x (x0 + x1)) eqn:eqstep.
      + apply ceval_step_more with (i2 := x0 + x1) in H0.
        * rewrite eqstep in H0. inversion H0. subst. apply ceval_step_more with (i1 := x1).
          ** lia.
          ** inversion Hce2; subst; try assumption.
        * lia.
      + apply ceval_step_more with (i2 := x0 + x1) in H0.
        * rewrite eqstep in H0. discriminate H0.
        * lia.
Qed.



(* Note that with the above properties, we can say that both semantics are equivalent! *)

Theorem ceval_and_ceval_step_coincide: forall c st st' res,
    st =[ c ]=> st' / res
<-> exists i, ceval_step st c i = Some (st', res).
Proof.
intros c st st'.
split. 
 - apply ceval__ceval_step. 
 - apply ceval_step__ceval.
Qed.


(* ################################################################# *)
(** * Determinism of Evaluation Again *)

(** Using the fact that the relational and step-indexed definition of
  evaluation are the same, we can give a short proof that the
  evaluation _relation_ is deterministic. *)

(* TODO: Write/explain the following proof in natural language, 
         using your own words. *)  

(**
  The proof start by using the `intros` tactic to move the universally quantified variables
  and the hypotheses from the goal into the context. Then, it invokes the `apply` tactic to
  use the ceval__ceval_step theorem in order to transform the relations that appear as hypotheses
  in the goal into the corresponding executions in the step-indexed evaluator. After that, it uses
  the `inversion` tactic in the hypotheses to introduce into the context the assumptions needed to
  verify the hypotheses. It then invokes the `apply` tactic to use the ceval_step_more theorem on
  the assumption introduced from the inversion of the first hypothesis, which creates 2 subgoals.
  In the first subgoal, it uses the same `apply` tactic with ceval_step_more, but on the assumption
  introduced from the inversion of the second hypothesis, which also creates 2 more subgoals.
  To solve the first subgoal, it uses the `rewrite` tactic, using the first assumption to rewrite the
  second one. It then uses the `inversion` tactic on the second assumption to introduce new assumptions
  to the context, which also rewrites the subgoal. Finally, it uses the `reflexivity` tactic to finish
  the subgoal, since both sides of the equation are equal. The second subgoal of the second `apply` is
  an inequality, so it is easily solved by the `lia` tactic, which finishes the first subgoal of the
  first `apply`. The second subgoal is also an inequality, also solved by the `lia` tactic, finishing
  the proof.
*)
Theorem ceval_deterministic' : forall c st st1 st2 res1 res2,
   st =[ c ]=> st1 / res1 ->
   st =[ c ]=> st2 / res2 ->
   st1 = st2.
Proof.
intros c st st1 st2 res1 res2 He1 He2.
apply ceval__ceval_step in He1.
apply ceval__ceval_step in He2.
inversion He1 as [i1 E1].
inversion He2 as [i2 E2].
apply ceval_step_more with (i2 := i1 + i2) in E1.
 - apply ceval_step_more with (i2 := i1 + i2) in E2.
  -- rewrite E1 in E2. inversion E2. reflexivity.
  -- lia. 
 - lia.  
 Qed.
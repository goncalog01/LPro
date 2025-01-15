(** * An Evaluation Function for Imp *)


(** Taken from the chapter Imp:
  https://softwarefoundations.cis.upenn.edu/lf-current/ImpCEvalFun.html

    It might be a good idea to read the chapter before or as you
    develop your solution.
*)

From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From FirstProject Require Import Imp Maps RelationalEvaluation.

(* Let's import the result datatype from the relational evaluation file *)
(* From FirstProject Require Import RelationalEvaluation. *)

(** We can improve the readability of this version by introducing a
    bit of auxiliary notation to hide the plumbing involved in
    repeatedly matching against optional states. *)

(*
Notation "'LETOPT' x <== e1 'IN' e2"
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).
*)

(** 2.1. TODO: Implement ceval_step as specified. To improve readability,
               you are strongly encouraged to define auxiliary notation.
               See the notation LETOPT commented above (or in the ImpCEval chapter).
*)

Fixpoint ceval_step (st : state) (c : com) (i : nat): option (state*result) :=
  match i with
  | 0 => None
  | S i' => match c with
            | <{ break }> => Some (st, SBreak)
            | <{ skip }> => Some (st, SContinue)
            | <{ x := y }> => Some ((x !-> (aeval st y) ; st), SContinue)
            | <{ x ; y }> => match (ceval_step st x i') with
                             | Some (st', SContinue) => (ceval_step st' y i')
                             | Some (st', SBreak) => Some (st', SBreak)      
                             | None => None
                             end
            | <{ if cond then x else y end }> => if (beval st cond) then (ceval_step st x i') else (ceval_step st y i')
            | <{ while cond do x end }> => if (beval st cond)
                                           then match (ceval_step st x i') with 
                                                | Some (st', SBreak) => Some (st', SContinue)
                                                | Some (st', SContinue) => ceval_step st' c i'
                                                | None => None
                                                end
                                           else Some (st, SContinue)
            end
  end.

(* The following definition is taken from the book and it can be used to
   test the step-indexed interpreter. *)
Definition test_ceval (st:state) (c:com) :=
  match ceval_step st c 500 with
  | None    => None
  | Some (st, _) => Some (st X, st Y, st Z)
  end.

Example example_test_ceval :
     test_ceval empty_st

     <{ X := 2;
        if (X <= 1)
        then Y := 3
        else Z := 4
        end }>

     = Some (2, 0, 4).
Proof. reflexivity. Qed.


(** 
  2.2. TODO: Prove the following three properties.
             Add a succint explanation in your own words of why `equivalence1` and `inequivalence1` are valid.
*)

(**
  The theorem is valid because both programs have a `break` statement before the subsequent command,
  so either both programs terminate immediately after executing the `break` with result SBreak and the same state
  (since there are no instructions before the `break`) or both terminate with None (if i0 = i1 = 0).
*)
Theorem equivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
=
ceval_step st <{ break; skip }> i1
).
Proof.
  intros st c.
  exists 1.
  intros [| H'].
  - simpl. reflexivity.
  - destruct H'; simpl; reflexivity.
Qed.

(**
  The theorem is valid because the first program has a `break` as the first instruction, so its execution will
  terminate immediately after executing the `break` with result SBreak, while the second program has a `skip`
  as the only instruction, so its execution will terminate with result SContinue (for i0 > 0)
*)
Theorem inequivalence1: forall st c,
(exists i0,
forall i1, i1>=i0 ->
ceval_step st <{ break; c }> i1
<>
ceval_step st <{ skip }> i1
).
Proof.
  intros st c.
  exists 1.
  intros.
  destruct H.
  - discriminate.
  - destruct m; discriminate.
Qed.

Theorem p1_equivalent_p2: forall st,
  (exists i0,
    forall i1, i1>=i0 ->
      ceval_step st p1 i1 = ceval_step st p2 i1
  ).
Proof.
  intros st.
  exists 6.
  intros.
  destruct H; try reflexivity.
  destruct m; try reflexivity; try lia.
  destruct (S m); try reflexivity; try lia.
  destruct n; try reflexivity; try lia.
  destruct (S n); try reflexivity; try lia.
  destruct n0; try reflexivity; try lia.
  destruct (S n0); try reflexivity; try lia.
  destruct n1; try reflexivity; try lia.
  destruct (S n1); try reflexivity; try lia.
  destruct n2; try reflexivity; try lia.
Qed.

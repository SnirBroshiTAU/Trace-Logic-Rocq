Require Import Classical.
Require Import FinFun.
Require Import Lia.
Require Import List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationClasses.
Require Import String.
Require Import ZArith.
From Project Require Import LanguageWithLines.

(*
  This file shows a way to improve ./TraceLogic2020.v
  by adding proper line numbers instead of timestamps
  being a function of statements,
  which should improve some of the shortcomings of the previous approach
*)

(*
  "Trace Logic for Inductive Loop Reasoning"
  by Pamina Georgiou, Bernhard Gleiss, Laura Kovács
  Aug 2020
  https://arxiv.org/pdf/2008.01387
*)

Fixpoint subprogram_line_diff (c : com) :=
  match c with
  | CSkip _ => 1
  | CAsgn _ _ _ => 1
  | CArrAsgn _ _ _ _ => 1
  | CSeq _ c1 c2 => subprogram_line_diff c1 + subprogram_line_diff c2
  | CIf _ _ c1 c2 => 1 + subprogram_line_diff c1 + subprogram_line_diff c2
  | CWhile _ _ c => 1 + subprogram_line_diff c
  end.

Inductive HasConsistentLineNumbers : nat -> com -> Prop :=
  | HasConsistentLineNumbersSkip (line : nat) :
      HasConsistentLineNumbers line (CSkip line)
  | HasConsistentLineNumbersAsgn (line : nat) (x : string) (a : aexp) :
      HasConsistentLineNumbers line (CAsgn line x a)
  | HasConsistentLineNumbersArrAsgn (line : nat) (x : string) (a1 : aexp) (a2 : aexp) :
      HasConsistentLineNumbers line (CArrAsgn line x a1 a2)
  | HasConsistentLineNumbersSeq (line : nat) (c1 c2 : com) :
      HasConsistentLineNumbers line c1 ->
      HasConsistentLineNumbers (line + subprogram_line_diff c1) c2 ->
      HasConsistentLineNumbers line (CSeq line c1 c2)
  | HasConsistentLineNumbersIf (line : nat) (b : bexp) (c1 c2 : com) :
      HasConsistentLineNumbers (S line) c1 ->
      HasConsistentLineNumbers ((S line) + subprogram_line_diff c1) c2 ->
      HasConsistentLineNumbers line (CIf line b c1 c2)
  | HasConsistentLineNumbersWhile (line : nat) (b : bexp) (c : com) :
      HasConsistentLineNumbers (S (S line)) c ->
      HasConsistentLineNumbers line (CWhile line b c)
  .

Ltac assert_compute H E :=
  let v := eval compute in E in
  assert (H : E = v) by reflexivity.

Example consistent_line_numbers_example :
  HasConsistentLineNumbers 0 (
    CWhile 0 BTrue (
      CIf 2 BTrue (
        CAsgn 3 "x" (ANum 3)
      ) (
        CSkip 4
      )
    )
  ).
Proof.
  repeat constructor.
Qed.

Inductive IsImmediateSubprogram : com -> com -> Prop :=
  | IsImmediateSubprogramSeq1 (line : nat) (c1 c2 : com)
    : IsImmediateSubprogram (CSeq line c1 c2) c1
  | IsImmediateSubprogramSeq2 (line : nat) (c1 c2 : com)
    : IsImmediateSubprogram (CSeq line c1 c2) c2
  | IsImmediateSubprogramIfThen (line : nat) (b : bexp) (c1 c2 : com)
    : IsImmediateSubprogram (CIf line b c1 c2) c1
  | IsImmediateSubprogramIfElse (line : nat) (b : bexp) (c1 c2 : com)
    : IsImmediateSubprogram (CIf line b c1 c2) c2
  | IsImmediateSubprogramWhile (line : nat) (b : bexp) (c : com)
    : IsImmediateSubprogram (CWhile line b c) c
  .

Example immediate_subprogram_example :
  let p2 := (
    CAsgn 3 "x" (ANum 3)
  ) in
  let p1 := (
    CIf 2 BTrue (
      p2
    ) (
      CSkip 4
    )
  ) in
  IsImmediateSubprogram p1 p2.
Proof.
  apply IsImmediateSubprogramIfThen.
Qed.

(* reflexive transitive closure *)
Definition IsSubprogram := clos_refl_trans com IsImmediateSubprogram.

Example subprogram_example :
  let p2 := (
    CAsgn 3 "x" (ANum 3)
  ) in
  let p1 := (
    CWhile 0 BTrue (
      CIf 2 BTrue (
        CAsgn 3 "x" (ANum 3)
      ) (
        CSkip 4
      )
    )
  ) in
  IsSubprogram p1 p2.
Proof.
  eapply rt_trans; apply rt_step.
  - apply IsImmediateSubprogramWhile.
  - apply IsImmediateSubprogramIfThen.
Qed.

(* the type is denoted as $\mathbb{L}$ in the paper *)
(* each instance is the location of each line, denoted as $l_s \in S_{T_p}$ in the paper *)
(* this represents the time before the line $line$ ran *)
Inductive Timepoint : Type :=
  | TimepointAt (line : nat) (enclIts : list nat)
  .

(* denoted as $v \in S_V$ in the paper *)
Definition IntVar : Type := Timepoint -> Z.
Definition ArrayVar : Type := Z -> IntVar.

(* the paper assumes we're always talking about a specific program *)
Parameter program : com.
Axiom consistent_program_line_numbers : HasConsistentLineNumbers 0 program.
(* we'll need to know all variables in the program *)
Parameter AllIntVars : list IntVar.
Parameter AllArrayVars : list ArrayVar.
(* and their names *)
Parameter IntVarByName : string -> IntVar.
Parameter ArrayVarByName : string -> ArrayVar.

(* the paper also assumes we're always talking about a specific trace of the program *)
(* we'll need to know the values of expressions at every timestep *)
Parameter aeval : forall (tp : Timepoint), aexp -> Z.
Parameter beval : forall (tp : Timepoint), bexp -> bool.

(* we'll need to know the last loop iteration of each line, denoted as $n_s \in S_n$ in the paper. also denoted ${lastIt}_s$ *)
Parameter LastLoopIteration : forall (t : Timepoint), nat.
Axiom last_loop_iteration_cond_is_false : forall line cond c enclIts,
  IsSubprogram program (CWhile line cond c) ->
  let it := LastLoopIteration (TimepointAt line enclIts) in
  beval (TimepointAt line (it :: enclIts)) cond = false.
Axiom last_loop_iteration_before_cond_is_true : forall line cond c it enclIts,
  IsSubprogram program (CWhile line cond c) ->
  it < LastLoopIteration (TimepointAt line enclIts) ->
  beval (TimepointAt (S line) (it :: enclIts)) cond = true.

(* NOTE: since it's easier to add/remove elements from the heed of lists,
enclosing iterations (enclIts) are saved in reverse order, like a stack *)

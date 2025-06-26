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
  | CIf _ _ c1 c2 => 1 + subprogram_line_diff c1 + 1 + subprogram_line_diff c2 + 1
  | CWhile _ _ c => 1 + 1 + subprogram_line_diff c + 1
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
      HasConsistentLineNumbers (line + 1) c1 ->
      HasConsistentLineNumbers (line + 1 + subprogram_line_diff c1 + 1) c2 ->
      HasConsistentLineNumbers line (CIf line b c1 c2)
  | HasConsistentLineNumbersWhile (line : nat) (b : bexp) (c : com) :
      HasConsistentLineNumbers (line + 1 + 1) c ->
      HasConsistentLineNumbers line (CWhile line b c)
  .

Example consistent_line_numbers_example :
  HasConsistentLineNumbers 0 (
    CWhile 0 BTrue (
      CIf 2 BTrue (
        CAsgn 3 "x" (ANum 3)
      ) (
        CSkip 5
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
      CSkip 5
    )
  ) in
  IsImmediateSubprogram p1 p2.
Proof.
  apply IsImmediateSubprogramIfThen.
Qed.

(* reflexive transitive closure *)
Definition IsSubprogram := clos_refl_trans com IsImmediateSubprogram.
Hint Unfold IsSubprogram : core.

Example subprogram_example :
  let p2 := (
    CAsgn 3 "x" (ANum 3)
  ) in
  let p1 := (
    CWhile 0 BTrue (
      CIf 2 BTrue (
        p2
      ) (
        CSkip 5
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

(* denoted as ${start}_p$ in the paper *)
Definition line_before (subprogram : com) :=
  match subprogram with
    | CSkip line => line
    | CAsgn line _ _ => line
    | CArrAsgn line _ _ _ => line
    | CSeq line _ _ => line
    | CIf line _ _ _ => line
    | CWhile line _ _ => line
  end.
Definition time_before (subprogram : com) (enclIts : list nat) :=
  TimepointAt (line_before subprogram) enclIts.

(* denoted as ${end}_p$ in the paper *)
Definition line_after (subprogram : com) :=
  line_before subprogram + subprogram_line_diff subprogram.
Definition time_after (subprogram : com) (enclIts : list nat) :=
  TimepointAt (line_after subprogram) enclIts.

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
Axiom last_loop_iteration_cond_is_false : forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall enclIts,
  let it := LastLoopIteration (time_before subprogram enclIts) in
  beval (TimepointAt (line_before subprogram + 1) (it :: enclIts)) cond = false.
Axiom last_loop_iteration_before_cond_is_true : forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall it enclIts,
  it < LastLoopIteration (time_before subprogram enclIts) ->
  beval (TimepointAt (line_before subprogram + 1) (it :: enclIts)) cond = true.

(* NOTE: since it's easier to add/remove elements from the heed of lists,
enclosing iterations (enclIts) are saved in reverse order, like a stack *)


(* ================================================================= *)
(* Trace Logic semantics                                             *)
(* ================================================================= *)

(* equality between timepoints *)
Definition EqInt (v : IntVar) (tp1 tp2 : Timepoint) : Prop :=
  v tp1 = v tp2.
Definition EqArray (v : ArrayVar) (tp1 tp2 : Timepoint) : Prop :=
  forall (pos : Z), v pos tp1 = v pos tp2.
Definition EqAll (tp1 tp2 : Timepoint) : Prop :=
  List.Forall (fun v => EqInt v tp1 tp2) AllIntVars
  /\ List.Forall (fun v => EqArray v tp1 tp2) AllArrayVars.

(* timepoints differing by a single assignment *)
Definition Update (v : IntVar) (e : aexp) (tp1 tp2 : Timepoint) : Prop :=
  v tp2 = aeval tp1 e
  /\ List.Forall (fun v' => v' = v \/ EqInt v' tp1 tp2) AllIntVars
  /\ List.Forall (fun v' => EqArray v' tp1 tp2) AllArrayVars.
Definition UpdateArray (v : ArrayVar) (e1 e2 : aexp) (tp1 tp2 : Timepoint) : Prop :=
  (forall (pos : Z), pos = aeval tp1 e1 \/ v pos tp2 = v pos tp1)
  /\ v (aeval tp1 e1) tp2 = aeval tp1 e2
  /\ List.Forall (fun v' => EqInt v' tp1 tp2) AllIntVars
  /\ List.Forall (fun v' => v' = v \/ EqArray v' tp1 tp2) AllArrayVars.


(* define the Trace Logic semantics of a subprogram, denoted by double square brackets in the paper *)
(* unlike the paper, this does not use `Reach` but rather recursion *)
(* also unlike the paper, since we have unique timepoints we need to sprinkle some more $EqAll$ *)
Fixpoint trace_logic_semantics (enclIts : list nat) (subprogram : com) : Prop :=
  match subprogram with
    | CSkip line =>
        EqAll (time_before subprogram enclIts) (time_after subprogram enclIts)
    | CAsgn line v e =>
        Update (IntVarByName v) e (time_before subprogram enclIts) (time_after subprogram enclIts)
    | CArrAsgn line v e1 e2 =>
        UpdateArray (ArrayVarByName v) e1 e2 (time_before subprogram enclIts) (time_after subprogram enclIts)
    | CSeq line c1 c2 =>
        trace_logic_semantics enclIts c1
        /\ trace_logic_semantics enclIts c2
    | CIf line cond c1 c2 =>
        let c := if beval (time_before subprogram enclIts) cond then c1 else c2 in
        EqAll (time_before subprogram enclIts) (time_before c enclIts)
        /\ EqAll (time_after c enclIts) (time_after subprogram enclIts)
        /\ trace_logic_semantics enclIts c
    | CWhile line cond c =>
        let lastIt := LastLoopIteration (time_before subprogram enclIts) in
        let time_before_condition := TimepointAt (line_before subprogram + 1) in
        EqAll (time_before subprogram enclIts) (time_before_condition (0 :: enclIts))
        /\ (forall (it : nat), it < lastIt ->
          beval (time_before_condition (it :: enclIts)) cond = true
          /\ EqAll (time_before_condition (it :: enclIts)) (time_before c (it :: enclIts))
          /\ EqAll (time_after c (it :: enclIts)) (time_before_condition (S it :: enclIts))
          /\ trace_logic_semantics (it :: enclIts) c
        )
        /\ beval (time_before_condition (lastIt :: enclIts)) cond = false
        /\ EqAll (time_before_condition (lastIt :: enclIts)) (time_after subprogram enclIts)
  end.

Definition trace_logic_semantics_for_program := trace_logic_semantics (@nil nat) program.


(* ================================================================= *)
(* Trace Logic small-step semantics                                  *)
(* ================================================================= *)

(* SOS stands for small-step operational semantics *)
(* from Appendix A *)
Inductive ReachSOS : Timepoint -> Prop :=
  | ReachSOSStart :
      ReachSOS (time_before program (@nil nat))
  | ReachSOSSkip enclIts line :
      let subprogram := CSkip line in
      IsSubprogram program subprogram ->
      ReachSOS (time_before subprogram enclIts) ->
      ReachSOS (time_after subprogram enclIts)
  | ReachSOSAsgn enclIts line v e :
      let subprogram := CAsgn line v e in
      IsSubprogram program subprogram ->
      ReachSOS (time_before subprogram enclIts) ->
      ReachSOS (time_after subprogram enclIts)
  | ReachSOSArrAsgn enclIts line v e1 e2 :
      let subprogram := CArrAsgn line v e1 e2 in
      IsSubprogram program subprogram ->
      ReachSOS (time_before subprogram enclIts) ->
      ReachSOS (time_after subprogram enclIts)
  | ReachSOSIfTrueB enclIts line cond c1 c2 :
      let subprogram := CIf line cond c1 c2 in
      IsSubprogram program subprogram ->
      ReachSOS (time_before subprogram enclIts) ->
      beval (time_before subprogram enclIts) cond = true ->
      ReachSOS (time_before c1 enclIts)
  | ReachSOSIfTrueA enclIts line cond c1 c2 :
      let subprogram := CIf line cond c1 c2 in
      IsSubprogram program subprogram ->
      ReachSOS (time_after c1 enclIts) ->
      ReachSOS (time_after subprogram enclIts)
  | ReachSOSIfFalseB enclIts line cond c1 c2 :
      let subprogram := CIf line cond c1 c2 in
      IsSubprogram program subprogram ->
      ReachSOS (time_before subprogram enclIts) ->
      beval (time_before subprogram enclIts) cond = false ->
      ReachSOS (time_before c2 enclIts)
  | ReachSOSIfFalseA enclIts line cond c1 c2 :
      let subprogram := CIf line cond c1 c2 in
      IsSubprogram program subprogram ->
      ReachSOS (time_after c2 enclIts) ->
      ReachSOS (time_after subprogram enclIts)
  | ReachSOSWhileStart enclIts line cond c :
      let subprogram := CWhile line cond c in
      IsSubprogram program subprogram ->
      ReachSOS (time_before subprogram enclIts) ->
      ReachSOS (TimepointAt (line_before subprogram + 1) (0 :: enclIts))
  | ReachSOSWhileTrue enclIts line it cond c :
      let subprogram := CWhile line cond c in
      IsSubprogram program subprogram ->
      let tBeforeIteration := TimepointAt (line_before subprogram + 1) (it :: enclIts) in
      ReachSOS tBeforeIteration ->
      beval tBeforeIteration cond = true ->
      ReachSOS (time_before c (it :: enclIts))
  | ReachSOSWhileLoop enclIts line it cond c :
      let subprogram := CWhile line cond c in
      IsSubprogram program subprogram ->
      ReachSOS (time_after c (it :: enclIts)) ->
      ReachSOS (TimepointAt (line_before subprogram + 1) (S it :: enclIts))
  | ReachSOSWhileFalse enclIts line it cond c :
      let subprogram := CWhile line cond c in
      IsSubprogram program subprogram ->
      let tBeforeIteration := TimepointAt (line_before subprogram + 1) (it :: enclIts) in
      ReachSOS tBeforeIteration ->
      beval tBeforeIteration cond = false ->
      ReachSOS (time_after subprogram enclIts)
  .
(* NOTE: 'B' = 'before', 'A' = 'after' *)

(* every rule concludes a Reach and has another conclusion alongside it *)
Axiom SOSConclusionSkip : forall enclIts line,
  let subprogram := CSkip line in
  IsSubprogram program subprogram ->
  ReachSOS (time_before subprogram enclIts) ->
  EqAll (time_before subprogram enclIts) (time_after subprogram enclIts).
Axiom SOSConclusionAsgn : forall enclIts line v e,
  let subprogram := CAsgn line v e in
  IsSubprogram program subprogram ->
  ReachSOS (time_before subprogram enclIts) ->
  Update (IntVarByName v) e (time_before subprogram enclIts) (time_after subprogram enclIts).
Axiom SOSConclusionArrAsgn : forall enclIts line v e1 e2,
  let subprogram := CArrAsgn line v e1 e2 in
  IsSubprogram program subprogram ->
  ReachSOS (time_before subprogram enclIts) ->
  UpdateArray (ArrayVarByName v) e1 e2 (time_before subprogram enclIts) (time_after subprogram enclIts).
Axiom SOSConclusionIfTrueB : forall enclIts line cond c1 c2,
  let subprogram := CIf line cond c1 c2 in
  IsSubprogram program subprogram ->
  ReachSOS (time_before subprogram enclIts) ->
  beval (time_before subprogram enclIts) cond = true ->
  EqAll (time_before subprogram enclIts) (time_before c1 enclIts).
Axiom SOSConclusionIfTrueA : forall enclIts line cond c1 c2,
  let subprogram := CIf line cond c1 c2 in
  IsSubprogram program subprogram ->
  ReachSOS (time_after c1 enclIts) ->
  EqAll (time_after c1 enclIts) (time_after subprogram enclIts).
Axiom SOSConclusionIfFalseB : forall enclIts line cond c1 c2,
  let subprogram := CIf line cond c1 c2 in
  IsSubprogram program subprogram ->
  ReachSOS (time_before subprogram enclIts) ->
  beval (time_before subprogram enclIts) cond = false ->
  EqAll (time_before subprogram enclIts) (time_before c2 enclIts).
Axiom SOSConclusionIfFalseA : forall enclIts line cond c1 c2,
  let subprogram := CIf line cond c1 c2 in
  IsSubprogram program subprogram ->
  ReachSOS (time_after c2 enclIts) ->
  EqAll (time_after c2 enclIts) (time_after subprogram enclIts).
Axiom SOSConclusionWhileStart : forall enclIts line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  ReachSOS (time_before subprogram enclIts) ->
  EqAll (time_before subprogram enclIts) (TimepointAt (line_before subprogram + 1) (0 :: enclIts)).
Axiom SOSConclusionWhileTrue : forall enclIts line cond c it,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  let tBeforeIteration := TimepointAt (line_before subprogram + 1) (it :: enclIts) in
  ReachSOS tBeforeIteration ->
  beval tBeforeIteration cond = true ->
  EqAll tBeforeIteration (time_before c (it :: enclIts)).
Axiom SOSConclusionWhileLoop : forall enclIts line it cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  ReachSOS (time_after c (it :: enclIts)) ->
  EqAll (time_after c (it :: enclIts)) (TimepointAt (line_before subprogram + 1) (S it :: enclIts)).
Axiom SOSConclusionWhileFalse : forall enclIts line cond c it,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  let tBeforeIteration := TimepointAt (line_before subprogram + 1) (it :: enclIts) in
  ReachSOS tBeforeIteration ->
  beval tBeforeIteration cond = false ->
  EqAll tBeforeIteration (time_after subprogram enclIts).


(* Proof of W-soundness with respect to small-step operational semantics (Theorem 1) *)

(* first a few lemmas *)

Lemma consistent_lines_for_immediate_subprogram :
  forall line program subprogram,
  HasConsistentLineNumbers line program ->
  IsImmediateSubprogram program subprogram ->
  exists line', HasConsistentLineNumbers line' subprogram.
Proof.
  intros line program subprogram Hline Hsub.
  inversion Hsub; subst;
  inversion Hline; subst;
  eauto.
Qed.

Lemma consistent_lines_for_subprogram :
  forall line program,
  HasConsistentLineNumbers line program ->
  forall subprogram,
  IsSubprogram program subprogram ->
  exists line', HasConsistentLineNumbers line' subprogram.
Proof.
  intros line program subprogram Hline Hsub.
  generalize dependent line.
  induction Hsub;
  intros line Hline.
  - (* step *)
    eauto using consistent_lines_for_immediate_subprogram.
  - (* reflexive *)
    exists line.
    auto.
  - (* transitive *)
    apply IHHsub1 in Hline.
    destruct Hline as [line' Hline'].
    eauto.
Qed.

Definition consistent_lines_for_subprogram_of_program :=
  consistent_lines_for_subprogram _ _ consistent_program_line_numbers.

Lemma consistent_lines_implies_line_before :
  forall line program,
  HasConsistentLineNumbers line program ->
  line_before program = line.
Proof.
  intros line program Hline.
  inversion Hline; subst; auto.
Qed.

Lemma is_immediate_subprogram_bounds_lines :
  forall line program,
  HasConsistentLineNumbers line program ->
  forall subprogram,
  IsImmediateSubprogram program subprogram ->
  line_before program <= line_before subprogram /\
  line_after subprogram <= line_after program.
Proof.
  intros line program Hline.
  intros subprogram Hsub.
  inversion Hsub; subst;
  inversion Hline; subst;
  rename line0 into line;
  repeat match goal with
  | H : HasConsistentLineNumbers _ _ |- _ =>
    apply consistent_lines_implies_line_before in H
  end;
  unfold line_after;
  simpl;
  lia.
Qed.

Lemma is_subprogram_bounds_lines :
  forall line program,
  HasConsistentLineNumbers line program ->
  forall subprogram,
  IsSubprogram program subprogram ->
  line_before program <= line_before subprogram /\
  line_after subprogram <= line_after program.
Proof.
  intros line program subprogram Hline Hsub.
  generalize dependent line.
  induction Hsub;
  intros line Hline.
  - (* step *)
    eauto using is_immediate_subprogram_bounds_lines.
  - (* reflexive *)
    lia.
  - (* transitive *)
    eapply consistent_lines_for_subprogram in Hsub1; eauto.
    destruct Hsub1 as [line' Hsub1].
    apply IHHsub1 in Hline.
    apply IHHsub2 in Hsub1.
    lia.
Qed.

Definition is_subprogram_bounds_lines_of_program :=
  is_subprogram_bounds_lines _ _ consistent_program_line_numbers.

Lemma is_subprogram_1n :
  forall program subprogram,
  IsSubprogram program subprogram
  <->
  clos_refl_trans_1n com IsImmediateSubprogram program subprogram.
Proof.
  intros program subprogram.
  split; intros Hsub;
  induction Hsub;
  eauto using rt1n_refl, rt1n_trans, rt_step, rt_refl, rt_trans.
  clear Hsub1 Hsub2.
  induction IHHsub1;
  eauto using rt1n_trans.
Qed.

Lemma is_subprogram_next_step :
  forall p p',
  IsSubprogram p p' ->
  p = p' \/
  exists p'',
  IsImmediateSubprogram p p'' /\
  IsSubprogram p'' p'.
Proof.
  intros p p' Hsub.
  apply is_subprogram_1n in Hsub.
  inversion Hsub; subst; auto.
  right.
  exists y.
  split; auto.
  apply is_subprogram_1n.
  auto.
Qed.

Lemma line_diff_non_zero :
  forall program,
  subprogram_line_diff program >= 1.
Proof.
  intros program.
  induction program;
  simpl;
  lia.
Qed.

Lemma immediate_subprogram_increases_line_diff :
  forall program subprogram,
  IsImmediateSubprogram program subprogram ->
  subprogram_line_diff program > subprogram_line_diff subprogram.
Proof.
  intros program subprogram Hsub.
  inversion Hsub;
  simpl; try lia.
  - pose proof (line_diff_non_zero c2).
    simpl; lia.
  - pose proof (line_diff_non_zero c1).
    simpl; lia.
Qed.

Lemma subprograms_cannot_overlap :
  forall line p,
  HasConsistentLineNumbers line p ->
  forall p1 p2,
  IsSubprogram p p1 ->
  IsSubprogram p p2 ->
  (
    line_after p1 <= line_before p2
    \/
    line_after p2 <= line_before p1
    \/
    IsSubprogram p1 p2
    \/
    IsSubprogram p2 p1
  ).
Proof.
  intros line p Hline.
  intros p1 p2 Hsub1 Hsub2.
  apply is_subprogram_1n in Hsub1.
  generalize dependent line.
  induction Hsub1 as [| p p1' p1 Himm1]; auto.
  intros line Hline.
  destruct (is_subprogram_next_step _ _ Hsub2) as [Heq | [p2' [Himm2 Hsub2']]].
  - subst.
    right. right. right.
    apply is_subprogram_1n.
    eauto using rt1n_trans.
  - apply is_subprogram_1n in Hsub1.
    destruct (consistent_lines_for_immediate_subprogram _ _ _ Hline Himm1) as [line1 Hline1].
    specialize IHHsub1 with (line := line1) (Hline := Hline1).
    pose proof (is_subprogram_bounds_lines _ _ Hline1 _ Hsub1) as Hbound1.
    clear line1 Hline1.
    destruct (consistent_lines_for_immediate_subprogram _ _ _ Hline Himm2) as [line2 Hline2].
    pose proof (is_subprogram_bounds_lines _ _ Hline2 _ Hsub2') as Hbound2.
    clear line2 Hline2.
    destruct p;
    inversion Himm1; subst;
    inversion Himm2; subst;
    auto;
    clear IHHsub1;
    inversion Hline; subst;
    repeat match goal with
    | H : HasConsistentLineNumbers _ _
    |- _ =>
      apply consistent_lines_implies_line_before in H
    end;
    unfold line_after in *; lia.
Qed.

Definition subprograms_of_program_cannot_overlap :=
  subprograms_cannot_overlap _ _ consistent_program_line_numbers.


(* we need tactics to disprove overlapping statements *)

Ltac prove_impossible_overlap p1 p2 :=
  match goal with
  | Hsub1 : IsSubprogram program p1,
    Hsub2 : IsSubprogram program p2
  |- _ =>
    let Hline1 := fresh in
    let line1 := fresh in
    let Hline2 := fresh in
    let line2 := fresh in
    (* get consistent-lines hypotheses for all subprograms of the subprograms *)
    try match goal with | p := _ : com |- _ => constr_eq p p1; (* only do this if p1 has a local definitions *)
      destruct (consistent_lines_for_subprogram_of_program _ Hsub1) as [line1 Hline1];
      inversion Hline1; subst; clear Hline1
    end;
    destruct (consistent_lines_for_subprogram_of_program _ Hsub2) as [line2 Hline2];
    inversion Hline2; subst; clear Hline2;
    (* convert them to equations about line numbers *)
    repeat match goal with
    | H : HasConsistentLineNumbers _ _
    |- _ =>
      apply consistent_lines_implies_line_before in H
    end;
    (* get the consistent-lines hypotheses again since we lost them *)
    destruct (consistent_lines_for_subprogram_of_program _ Hsub1) as [line1 Hline1];
    try match goal with | p := _ : com |- _ => constr_eq p p1; (* only do this if p1 has a local definitions *)
      inversion Hline1; subst; clear Hline1
    end;
    destruct (consistent_lines_for_subprogram_of_program _ Hsub2) as [line2 Hline2];
    inversion Hline2; subst; clear Hline2;
    (* now prove the subprograms cannot overlap *)
    let H := fresh in
    destruct (subprograms_of_program_cannot_overlap _ _ Hsub1 Hsub2) as [H | [H | [H | H]]];
    unfold line_after in *; simpl in *; try lia;
    let Heq := fresh in
    let p := fresh in
    let Himm := fresh in
    let Hsub := fresh in
    (
      destruct (is_subprogram_next_step _ _ H) as [Heq | [p [Himm Hsub]]];
      [
        auto; inversion Heq; subst; simpl in *; try lia
        |
        (* first check if program can even contain subprograms *)
        pose proof (line_diff_non_zero p);
        pose proof (immediate_subprogram_increases_line_diff _ _ Himm);
        try lia;
        (* then compare with line bounds of every immediate subprogram *)
        inversion Himm; subst;
        eapply is_subprogram_bounds_lines in Hsub; eauto;
        unfold line_after in Hsub; simpl in Hsub; try lia
      ]
    )
  end.

Ltac solve_impossible_overlap :=
  try solve [
    match goal with
    | p1 := _ : com, p2 := _ : com
    |- _ =>
      prove_impossible_overlap p1 p2
    end
  ].


(* lemmas about inverting reach, using the tactic *)

Lemma reach_line_end_implies_line_start :
  forall subprogramLine,
  IsSubprogram program subprogramLine ->
  subprogram_line_diff subprogramLine = 1 ->
  forall enclIts,
  ReachSOS (time_after subprogramLine enclIts) ->
  ReachSOS (time_before subprogramLine enclIts).
Proof.
  intros subprogramLine HsubLine Hdiff.
  intros enclIts Hafter.
  inversion Hafter; subst;
  try solve [
    unfold line_after in H;
    rewrite Hdiff in H;
    simpl in H;
    simpl in H2;
    assert (line = line_before subprogramLine) by lia;
    subst;
    auto
  ];
  try solve [ prove_impossible_overlap subprogramLine subprogram ].
  apply is_subprogram_bounds_lines_of_program in HsubLine.
  unfold line_after in *.
  lia.
Qed.

Lemma reach_seq1_start_implies_seq_start :
  forall line c1 c2,
  let subprogram := CSeq line c1 c2 in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_before c1 enclIts) ->
  ReachSOS (time_before subprogram enclIts).
Proof.
  intros line c1 c2 subprogram Hsub.
  intros enclIts Hbefore.
  unfold time_before.
  simpl.
  destruct (consistent_lines_for_subprogram_of_program _ Hsub) as [line' Hline].
  inversion Hline; subst.
  apply consistent_lines_implies_line_before in H2.
  rewrite <- H2.
  auto.
Qed.

Lemma reach_seq2_start_implies_seq1_end :
  forall line c1 c2,
  let subprogram := CSeq line c1 c2 in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_before c2 enclIts) ->
  ReachSOS (time_after c1 enclIts).
Proof.
  intros line c1 c2 subprogram Hsub.
  intros enclIts Hbefore.
  destruct (consistent_lines_for_subprogram_of_program _ Hsub) as [line' Hline].
  inversion Hline; subst.
  apply consistent_lines_implies_line_before in H2.
  apply consistent_lines_implies_line_before in H4.
  assert (Hmid : time_after c1 enclIts = time_before c2 enclIts). {
    unfold time_before.
    unfold time_after.
    unfold line_after.
    f_equal.
    lia.
  }
  rewrite Hmid.
  auto.
Qed.

Lemma reach_seq_end_implies_seq2_end :
  forall line c1 c2,
  let subprogram := CSeq line c1 c2 in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_after subprogram enclIts) ->
  ReachSOS (time_after c2 enclIts).
Proof.
  intros line c1 c2 subprogram Hsub.
  intros enclIts Hafter.
  destruct (consistent_lines_for_subprogram_of_program _ Hsub) as [line' Hline].
  inversion Hline; subst.
  apply consistent_lines_implies_line_before in H4.
  assert (Hend : time_after c2 enclIts = time_after subprogram enclIts). {
    unfold time_after.
    unfold line_after.
    f_equal.
    simpl.
    lia.
  }
  rewrite Hend.
  auto.
Qed.

Lemma reach_if_then_start_implies_condition_true :
  forall line cond c1 c2,
  let subprogram := CIf line cond c1 c2 in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_before c1 enclIts) ->
  ReachSOS (time_before subprogram enclIts) /\
  beval (time_before subprogram enclIts) cond = true.
Proof.
  intros line cond c1 c2 subprogram Hsub.
  intros enclIts Hbefore.
  inversion Hbefore; subst;
  solve_impossible_overlap.
  - destruct (consistent_lines_for_subprogram_of_program _ Hsub) as [line' Hline'].
    inversion Hline'; subst.
    apply consistent_lines_implies_line_before in H3.
    apply is_subprogram_bounds_lines_of_program in Hsub.
    cbn in *; lia.
  - assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
    inversion Heq; subst.
    auto.
Qed.

Lemma reach_if_else_start_implies_condition_false :
  forall line cond c1 c2,
  let subprogram := CIf line cond c1 c2 in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_before c2 enclIts) ->
  ReachSOS (time_before subprogram enclIts) /\
  beval (time_before subprogram enclIts) cond = false.
Proof.
  intros line cond c1 c2 subprogram Hsub.
  intros enclIts Hbefore.
  inversion Hbefore; subst;
  solve_impossible_overlap.
  - destruct (consistent_lines_for_subprogram_of_program _ Hsub) as [line' Hline'].
    inversion Hline'; subst.
    apply consistent_lines_implies_line_before in H6.
    apply is_subprogram_bounds_lines_of_program in Hsub.
    cbn in *; lia.
  - assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
    inversion Heq; subst.
    auto.
Qed.

Lemma reach_if_end_implies_after_c1_or_c2 :
  forall line cond c1 c2,
  let subprogram := CIf line cond c1 c2 in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_after subprogram enclIts) ->
  ReachSOS (time_after c1 enclIts) \/
  ReachSOS (time_after c2 enclIts).
Proof.
  intros line cond c1 c2 subprogram Hsub.
  intros enclIts Hafter.
  inversion Hafter; subst;
  solve_impossible_overlap.
  - apply is_subprogram_bounds_lines_of_program in Hsub.
    cbn in *; lia.
  - left.
    assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
    inversion Heq; subst.
    auto.
  - right.
    assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
    inversion Heq; subst.
    auto.
Qed.

Lemma reach_first_while_condition_implies_while_start :
  forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (TimepointAt (line_before subprogram + 1) (0 :: enclIts)) ->
  ReachSOS (time_before subprogram enclIts).
Proof.
  intros line cond c subprogram Hsub.
  intros enclIts Hbefore.
  inversion Hbefore; subst;
  solve_impossible_overlap.
  assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
  inversion Heq; subst.
  auto.
Qed.

Lemma reach_while_body_start_implies_condition_true :
  forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall it enclIts,
  ReachSOS (time_before c (it :: enclIts)) ->
  let tBeforeIteration := TimepointAt (line_before subprogram + 1) (it :: enclIts) in
  ReachSOS tBeforeIteration /\
  beval tBeforeIteration cond = true.
Proof.
  intros line cond c subprogram Hsub.
  intros it enclIts Hbefore tBeforeIteration.
  inversion Hbefore; subst;
  solve_impossible_overlap.
  assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
  inversion Heq; subst.
  auto.
Qed.

Lemma reach_while_condition_implies_while_body_end :
  forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall it enclIts,
  ReachSOS (TimepointAt (line_before subprogram + 1) (S it :: enclIts)) ->
  ReachSOS (time_after c (it :: enclIts)).
Proof.
  intros line cond c subprogram Hsub.
  intros it enclIts Hbefore.
  inversion Hbefore; subst;
  solve_impossible_overlap.
  assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
  inversion Heq; subst.
  auto.
Qed.

Lemma reach_while_end_implies_condition_false :
  forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_after subprogram enclIts) ->
  exists it,
  let tBeforeIteration := TimepointAt (line_before subprogram + 1) (it :: enclIts) in
  ReachSOS tBeforeIteration /\
  beval tBeforeIteration cond = false.
Proof.
  intros line cond c subprogram Hsub.
  intros enclIts Hafter.
  inversion Hafter; subst;
  solve_impossible_overlap.
  - apply is_subprogram_bounds_lines_of_program in Hsub.
    cbn in *; lia.
  - assert (Heq : subprogram = subprogram0) by solve_impossible_overlap.
    inversion Heq; subst.
    exists it.
    auto.
Qed.

Lemma reach_after_implies_before :
  forall subprogram,
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_after subprogram enclIts) ->
  ReachSOS (time_before subprogram enclIts).
Proof.
  intros subprogram.
  induction subprogram;
  intros Hsub enclIts Hafter;
  auto using reach_line_end_implies_line_start.
  - (* seq *)
    eauto 20 using
      reach_seq1_start_implies_seq_start,
      reach_seq2_start_implies_seq1_end,
      reach_seq_end_implies_seq2_end,
      IsImmediateSubprogramSeq1,
      IsImmediateSubprogramSeq2,
      rt_trans,
      rt_step.
  - (* if *)
    destruct (reach_if_end_implies_after_c1_or_c2 _ _ _ _ Hsub _ Hafter) as [HafterThen | HafterElse].
    + (* if then *)
      assert (Hsub1 : IsSubprogram program subprogram1) by eauto using
        IsImmediateSubprogramIfThen, rt_trans, rt_step.
      assert (Hbefore1 : ReachSOS (time_before subprogram1 enclIts)) by auto.
      destruct (reach_if_then_start_implies_condition_true _ _ _ _ Hsub _ Hbefore1) as [Hbefore _].
      auto.
    + (* if else *)
      assert (Hsub2 : IsSubprogram program subprogram2) by eauto using
        IsImmediateSubprogramIfElse, rt_trans, rt_step.
      assert (Hbefore2 : ReachSOS (time_before subprogram2 enclIts)) by auto.
      destruct (reach_if_else_start_implies_condition_false _ _ _ _ Hsub _ Hbefore2) as [Hbefore _].
      auto.
  - (* while *)
    destruct (reach_while_end_implies_condition_false _ _ _ Hsub _ Hafter) as [it [Hbefore _]].
    induction it.
    + auto using reach_first_while_condition_implies_while_start.
    + apply IHit.
      apply reach_while_body_start_implies_condition_true;
      eauto 20 using
        reach_while_condition_implies_while_body_end,
        IsImmediateSubprogramWhile,
        rt_trans,
        rt_step.
Qed.

Lemma while_reach_semantics :
  forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_after subprogram enclIts) ->
  exists itEnd,
  let time_before_condition := TimepointAt (line_before subprogram + 1) in
  ReachSOS (time_before_condition (itEnd :: enclIts)) /\
  beval (time_before_condition (itEnd :: enclIts)) cond = false /\
  forall it,
  it < itEnd ->
  ReachSOS (time_before_condition (it :: enclIts)) /\
  beval (time_before_condition (it :: enclIts)) cond = true /\
  ReachSOS (time_after c (it :: enclIts)).
Proof.
  intros line cond c subprogram Hsub.
  intros enclIts Hafter.
  apply reach_while_end_implies_condition_false in Hafter; auto.
  destruct Hafter as [itEnd [HbeforeCond Hcond]].
  exists itEnd.
  intros time_before_condition.
  split; [| split]; auto.
  clear Hcond.
  induction itEnd;
  intros it Hit;
  inversion Hit;
  pose proof HbeforeCond as HafterBody;
  apply reach_while_condition_implies_while_body_end in HafterBody; auto;
  pose proof HafterBody as HbeforeBody;
  apply reach_after_implies_before in HbeforeBody; eauto using IsImmediateSubprogramWhile, rt_trans, rt_step;
  pose proof HbeforeBody as Hcond';
  eapply reach_while_body_start_implies_condition_true in Hcond'; eauto;
  destruct Hcond' as [HbeforeCond' Hcond'];
  auto.
Qed.

Lemma while_reach_semantics_for_last_loop_iteration :
  forall line cond c,
  let subprogram := CWhile line cond c in
  IsSubprogram program subprogram ->
  forall enclIts,
  ReachSOS (time_after subprogram enclIts) ->
  let itEnd := LastLoopIteration (time_before subprogram enclIts) in
  let time_before_condition := TimepointAt (line_before subprogram + 1) in
  ReachSOS (time_before_condition (itEnd :: enclIts)) /\
  forall it,
  it < itEnd ->
  ReachSOS (time_before_condition (it :: enclIts)) /\
  ReachSOS (time_after c (it :: enclIts)).
Proof.
  intros line cond c subprogram Hsub.
  intros enclIts Hafter.
  intros itEnd.
  pose proof (while_reach_semantics _ _ _ Hsub _ Hafter) as Hwhile.
  fold subprogram in Hwhile.
  destruct Hwhile as [itEnd' [HbeforeLastCond [Hfalse Hwhile]]].
  assert (HitEnd : itEnd = itEnd'). {
    destruct (Nat.compare_spec itEnd itEnd') as [HitEnd | HitEnd | HitEnd]; auto.
    - destruct (Hwhile itEnd HitEnd) as [_ [Htrue _]].
      unfold itEnd in Htrue.
      unfold subprogram in Htrue.
      rewrite (last_loop_iteration_cond_is_false _ _ _ Hsub enclIts) in Htrue.
      discriminate.
    - unfold subprogram in Hfalse.
      rewrite (last_loop_iteration_before_cond_is_true _ _ _ Hsub _ enclIts HitEnd) in Hfalse.
      discriminate.
  }
  subst.
  split; auto.
  intros it Hit.
  destruct (Hwhile it Hit) as [HbeforeCond [Htrue HafterBody]].
  auto.
Qed.


(* W-soundness for subprograms *)
Lemma trace_logic_semantics_soundness_for_subprograms :
  forall subprogram enclIts,
  IsSubprogram program subprogram ->
  ReachSOS (time_after subprogram enclIts) ->
  trace_logic_semantics enclIts subprogram.
Proof.
  intros subprogram.
  induction subprogram;
  intros enclIts Hsub Hafter;
  assert (Hbefore : ReachSOS (time_before _ enclIts)) by eauto using reach_after_implies_before;
  unfold trace_logic_semantics;
  fold trace_logic_semantics.
  - (* skip *)
    auto using SOSConclusionSkip.
  - (* v := e *)
    auto using SOSConclusionAsgn.
  - (* v:[e1] := e2 *)
    auto using SOSConclusionArrAsgn.
  - (* c1; c2 *)
    eauto 20 using
      reach_seq2_start_implies_seq1_end,
      reach_seq_end_implies_seq2_end,
      reach_after_implies_before,
      IsImmediateSubprogramSeq1,
      IsImmediateSubprogramSeq2,
      rt_trans,
      rt_step.
  - (* if (cond) { c1 } else { c2 } *)
    destruct (reach_if_end_implies_after_c1_or_c2 _ _ _ _ Hsub _ Hafter) as [HafterThen | HafterElse].
    + assert (Hsub1 : IsSubprogram program subprogram1) by eauto using
        IsImmediateSubprogramIfThen, rt_trans, rt_step.
      destruct (
        reach_if_then_start_implies_condition_true _ _ _ _ Hsub _ (
          reach_after_implies_before _ Hsub1 _ HafterThen
        )
      ) as [_ Hcond].
      rewrite Hcond.
      eauto 10 using
        SOSConclusionIfTrueB,
        SOSConclusionIfTrueA,
        reach_after_implies_before,
        reach_if_then_start_implies_condition_true.
    + assert (Hsub2 : IsSubprogram program subprogram2) by eauto using
        IsImmediateSubprogramIfElse, rt_trans, rt_step.
      destruct (
        reach_if_else_start_implies_condition_false _ _ _ _ Hsub _ (
          reach_after_implies_before _ Hsub2 _ HafterElse
        )
      ) as [_ Hcond].
      rewrite Hcond.
      eauto 10 using
        SOSConclusionIfFalseB,
        SOSConclusionIfFalseA,
        reach_after_implies_before,
        reach_if_else_start_implies_condition_false.
  - (* while (cond) { c } *)
    destruct (while_reach_semantics_for_last_loop_iteration _ _ _ Hsub _ Hafter) as [HbeforeLastCond Hwhile].
    split; [| split; [| split]]; eauto using
      SOSConclusionWhileStart,
      SOSConclusionWhileFalse,
      last_loop_iteration_cond_is_false.
    intros it Hit.
    destruct (Hwhile it Hit) as [HbeforeCond HafterBody].
    split; [| split; [| split]]; eauto using
      SOSConclusionWhileTrue,
      SOSConclusionWhileLoop,
      last_loop_iteration_before_cond_is_true,
      IsImmediateSubprogramWhile,
      rt_trans,
      rt_step.
Qed.

(* main result: W-soundness of the semantics of the entire program *)
Theorem trace_logic_semantics_soundness_for_program :
  ReachSOS (time_after program (@nil nat)) ->
  trace_logic_semantics_for_program.
Proof.
  eapply trace_logic_semantics_soundness_for_subprograms.
  apply rt_refl.
Qed.

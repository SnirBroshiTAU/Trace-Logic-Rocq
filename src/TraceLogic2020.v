Require Import Classical.
Require Import FinFun.
Require Import Lia.
Require Import List.
Require Import Relation_Definitions.
Require Import RelationClasses.
Require Import String.
Require Import ZArith.
From Project Require Import Language.

(*
  "Trace Logic for Inductive Loop Reasoning"
  by Pamina Georgiou, Bernhard Gleiss, Laura Kovács
  Aug 2020
  https://arxiv.org/pdf/2008.01387
*)

Example figure1 : com := <{
  I := 0;
  J := 0;
  while (I < length A) {
    if (A[I] >= 0) {
      B:[J] := A[I];
      J := J + 1
    };
    I := I + 1
  }
}>.

Open Scope nat_scope.

(* the type is denoted as $\mathbb{L}$ in the paper *)
(* each instance is the location of each line, denoted as $l_s \in S_{T_p}$ in the paper *)
Inductive Timepoint : Type :=
  (* these are a combination of $l_s$, ${tp}_s$, ${start}_p$, ${end}_p$ from the paper *)
  | TimeBefore (subprogram : com) (enclIts : list nat)
  | TimeAfter (subprogram : com) (enclIts : list nat)
  (* for loops we define a timepoint before evaluating the condition of each iteration *)
  | TimeBeforeIteration (subprogram : loop) (enclIts : list nat)
  .

(* denoted as $v \in S_V$ in the paper *)
Definition IntVar : Type := Timepoint -> Z.
Definition ArrayVar : Type := Z -> IntVar.

(* the paper assumes we're always talking about a specific program *)
Parameter program : com.
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
Parameter LastLoopIteration : forall (subprogram : loop) (enclIts : list nat), nat.
Axiom last_loop_iteration_cond_is_false : forall cond c enclIts,
  let it := LastLoopIteration (LWhile cond c) enclIts in
  beval (TimeBeforeIteration (LWhile cond c) (it :: enclIts)) cond = false.
Axiom last_loop_iteration_before_cond_is_true : forall cond c it enclIts,
  it < LastLoopIteration (LWhile cond c) enclIts ->
  beval (TimeBeforeIteration (LWhile cond c) (it :: enclIts)) cond = true.

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
    | <{ skip }> =>
        EqAll (TimeBefore subprogram enclIts) (TimeAfter subprogram enclIts)
    | <{ v := e }> =>
        Update (IntVarByName v) e (TimeBefore subprogram enclIts) (TimeAfter subprogram enclIts)
    | <{ v:[e1] := e2 }> =>
        UpdateArray (ArrayVarByName v) e1 e2 (TimeBefore subprogram enclIts) (TimeAfter subprogram enclIts)
    | <{ c1 ; c2 }> =>
        EqAll (TimeBefore subprogram enclIts) (TimeBefore c1 enclIts)
        /\ EqAll (TimeAfter c1 enclIts) (TimeBefore c2 enclIts)
        /\ EqAll (TimeAfter c2 enclIts) (TimeAfter subprogram enclIts)
        /\ trace_logic_semantics enclIts c1
        /\ trace_logic_semantics enclIts c2
    | <{ if (cond) { c1 } else { c2 } }> =>
        let c := if beval (TimeBefore subprogram enclIts) cond then c1 else c2 in
        EqAll (TimeBefore subprogram enclIts) (TimeBefore c enclIts)
        /\ EqAll (TimeAfter c enclIts) (TimeAfter subprogram enclIts)
        /\ trace_logic_semantics enclIts c
    | <{ while (cond) { c } }> =>
        let loop := LWhile cond c in
        let lastIt := LastLoopIteration loop enclIts in
        EqAll (TimeBefore subprogram enclIts) (TimeBeforeIteration loop (0 :: enclIts))
        /\ (forall (it : nat), it < lastIt ->
          beval (TimeBeforeIteration loop (it :: enclIts)) cond = true
          /\ EqAll (TimeBeforeIteration loop (it :: enclIts)) (TimeBefore c (it :: enclIts))
          /\ EqAll (TimeAfter c (it :: enclIts)) (TimeBeforeIteration loop (S it :: enclIts))
          /\ trace_logic_semantics (it :: enclIts) c
        )
        /\ beval (TimeBeforeIteration loop (lastIt :: enclIts)) cond = false
        /\ EqAll (TimeBeforeIteration loop (lastIt :: enclIts)) (TimeAfter subprogram enclIts)
  end.

Definition trace_logic_semantics_for_program := trace_logic_semantics (@nil nat) program.


(* since we have more timepoints, we add a few more rules than the paper *)
(* we don't use this, but we include it for completion *)
Inductive Reach : Timepoint -> Prop :=
  | ReachStart :
      (* we start the program *)
      Reach (TimeBefore program (@nil nat))
  | ReachEnd :
      (* we assume termination *)
      Reach (TimeAfter program (@nil nat))
  | ReachSeq1B subprogram enclIts c1 c2 :
      (subprogram = <{ c1; c2 }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      Reach (TimeBefore c1 enclIts)
  | ReachSeq1A subprogram enclIts c1 c2 :
      (subprogram = <{ c1; c2 }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      Reach (TimeAfter c1 enclIts)
  | ReachSeq2B subprogram enclIts c1 c2 :
      (subprogram = <{ c1; c2 }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      Reach (TimeBefore c2 enclIts)
  | ReachSeq2A subprogram enclIts c1 c2 :
      (subprogram = <{ c1; c2 }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      Reach (TimeAfter c2 enclIts)
  | ReachIfTrueB subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      beval (TimeBefore subprogram enclIts) cond = true ->
      Reach (TimeBefore c1 enclIts)
  | ReachIfTrueA subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      beval (TimeBefore subprogram enclIts) cond = true ->
      Reach (TimeAfter c1 enclIts)
  | ReachIfFalseB subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      beval (TimeBefore subprogram enclIts) cond = false ->
      Reach (TimeBefore c2 enclIts)
  | ReachIfFalseA subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      beval (TimeBefore subprogram enclIts) cond = false ->
      Reach (TimeAfter c2 enclIts)
  | ReachWhileIteration subprogram enclIts it cond c :
      (subprogram = <{ while (cond) { c } }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      it <= LastLoopIteration (LWhile cond c) enclIts ->
      Reach (TimeBeforeIteration (LWhile cond c) (it :: enclIts))
  | ReachWhileBody subprogram enclIts it cond c :
      (subprogram = <{ while (cond) { c } }>) ->
      Reach (TimeBefore subprogram enclIts) ->
      it < LastLoopIteration (LWhile cond c) enclIts ->
      Reach (TimeBefore c (it :: enclIts))
  .
(* NOTE: 'B' = 'before', 'A' = 'after' *)


(* ================================================================= *)
(* Trace Logic small-step semantics                                  *)
(* ================================================================= *)

(* SOS stands for small-step operational semantics *)
(* from Appendix A *)
Inductive ReachSOS : Timepoint -> Prop :=
  | ReachSOSStart :
      ReachSOS (TimeBefore program (@nil nat))
  | ReachSOSSkip subprogram enclIts :
      (subprogram = <{ skip }>) ->
      ReachSOS (TimeBefore subprogram enclIts) ->
      ReachSOS (TimeAfter subprogram enclIts)
  | ReachSOSAsgn subprogram enclIts v e :
      (subprogram = <{ v := e }>) ->
      ReachSOS (TimeBefore subprogram enclIts) ->
      ReachSOS (TimeAfter subprogram enclIts)
  | ReachSOSArrAsgn subprogram enclIts v e1 e2 :
      (subprogram = <{ v:[e1] := e2 }>) ->
      ReachSOS (TimeBefore subprogram enclIts) ->
      ReachSOS (TimeAfter subprogram enclIts)
  | ReachSOSSeqStart subprogram enclIts c1 c2 :
      (subprogram = <{ c1; c2 }>) ->
      ReachSOS (TimeBefore subprogram enclIts) ->
      ReachSOS (TimeBefore c1 enclIts)
  | ReachSOSSeqMiddle subprogram enclIts c1 c2 :
      (subprogram = <{ c1; c2 }>) ->
      ReachSOS (TimeAfter c1 enclIts) ->
      ReachSOS (TimeBefore c2 enclIts)
  | ReachSOSSeqEnd subprogram enclIts c1 c2 :
      (subprogram = <{ c1; c2 }>) ->
      ReachSOS (TimeAfter c2 enclIts) ->
      ReachSOS (TimeAfter subprogram enclIts)
  | ReachSOSIfTrueB subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      ReachSOS (TimeBefore subprogram enclIts) ->
      beval (TimeBefore subprogram enclIts) cond = true ->
      ReachSOS (TimeBefore c1 enclIts)
  | ReachSOSIfTrueA subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      ReachSOS (TimeAfter c1 enclIts) ->
      ReachSOS (TimeAfter subprogram enclIts)
  | ReachSOSIfFalseB subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      ReachSOS (TimeBefore subprogram enclIts) ->
      beval (TimeBefore subprogram enclIts) cond = false ->
      ReachSOS (TimeBefore c2 enclIts)
  | ReachSOSIfFalseA subprogram enclIts cond c1 c2 :
      (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
      ReachSOS (TimeAfter c2 enclIts) ->
      ReachSOS (TimeAfter subprogram enclIts)
  | ReachSOSWhileStart subprogram enclIts cond c :
      (subprogram = <{ while (cond) { c } }>) ->
      ReachSOS (TimeBefore subprogram enclIts) ->
      ReachSOS (TimeBeforeIteration (LWhile cond c) (0 :: enclIts))
  | ReachSOSWhileTrue subprogram enclIts it cond c :
      (subprogram = <{ while (cond) { c } }>) ->
      let tBeforeIteration := TimeBeforeIteration (LWhile cond c) (it :: enclIts) in
      ReachSOS tBeforeIteration ->
      beval tBeforeIteration cond = true ->
      ReachSOS (TimeBefore c (it :: enclIts))
  | ReachSOSWhileLoop subprogram enclIts it cond c :
      (subprogram = <{ while (cond) { c } }>) ->
      ReachSOS (TimeAfter c (it :: enclIts)) ->
      ReachSOS (TimeBeforeIteration (LWhile cond c) (S it :: enclIts))
  | ReachSOSWhileFalse subprogram enclIts it cond c :
      (subprogram = <{ while (cond) { c } }>) ->
      let tBeforeIteration := TimeBeforeIteration (LWhile cond c) (it :: enclIts) in
      ReachSOS tBeforeIteration ->
      beval tBeforeIteration cond = false ->
      ReachSOS (TimeAfter subprogram enclIts)
  .

(* every rule concludes a Reach and has another conclusion alongside it *)
Axiom SOSConclusionSkip : forall subprogram enclIts,
  (subprogram = <{ skip }>) ->
  ReachSOS (TimeBefore subprogram enclIts) ->
  EqAll (TimeBefore subprogram enclIts) (TimeAfter subprogram enclIts).
Axiom SOSConclusionAsgn : forall subprogram enclIts v e,
  (subprogram = <{ v := e }>) ->
  ReachSOS (TimeBefore subprogram enclIts) ->
  Update (IntVarByName v) e (TimeBefore subprogram enclIts) (TimeAfter subprogram enclIts).
Axiom SOSConclusionArrAsgn : forall subprogram enclIts v e1 e2,
  (subprogram = <{ v:[e1] := e2 }>) ->
  ReachSOS (TimeBefore subprogram enclIts) ->
  UpdateArray (ArrayVarByName v) e1 e2 (TimeBefore subprogram enclIts) (TimeAfter subprogram enclIts).
Axiom SOSConclusionSeqStart : forall subprogram enclIts c1 c2,
  (subprogram = <{ c1; c2 }>) ->
  ReachSOS (TimeBefore subprogram enclIts) ->
  EqAll (TimeBefore subprogram enclIts) (TimeBefore c1 enclIts).
Axiom SOSConclusionSeqMiddle : forall subprogram enclIts c1 c2,
  (subprogram = <{ c1; c2 }>) ->
  ReachSOS (TimeAfter c1 enclIts) ->
  EqAll (TimeAfter c1 enclIts) (TimeBefore c2 enclIts).
Axiom SOSConclusionSeqEnd : forall subprogram enclIts c1 c2,
  (subprogram = <{ c1; c2 }>) ->
  ReachSOS (TimeAfter c2 enclIts) ->
  EqAll (TimeAfter c2 enclIts) (TimeAfter subprogram enclIts).
Axiom SOSConclusionIfTrueB : forall subprogram enclIts cond c1 c2,
  (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
  ReachSOS (TimeBefore subprogram enclIts) ->
  beval (TimeBefore subprogram enclIts) cond = true ->
  EqAll (TimeBefore subprogram enclIts) (TimeBefore c1 enclIts).
Axiom SOSConclusionIfTrueA : forall subprogram enclIts cond c1 c2,
  (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
  ReachSOS (TimeAfter c1 enclIts) ->
  EqAll (TimeAfter c1 enclIts) (TimeAfter subprogram enclIts).
Axiom SOSConclusionIfFalseB : forall subprogram enclIts cond c1 c2,
  (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
  ReachSOS (TimeBefore subprogram enclIts) ->
  beval (TimeBefore subprogram enclIts) cond = false ->
  EqAll (TimeBefore subprogram enclIts) (TimeBefore c2 enclIts).
Axiom SOSConclusionIfFalseA : forall subprogram enclIts cond c1 c2,
  (subprogram = <{ if (cond) { c1 } else { c2 } }>) ->
  ReachSOS (TimeAfter c2 enclIts) ->
  EqAll (TimeAfter c2 enclIts) (TimeAfter subprogram enclIts).
Axiom SOSConclusionWhileStart : forall subprogram enclIts cond c,
  (subprogram = <{ while (cond) { c } }>) ->
  ReachSOS (TimeBefore subprogram enclIts) ->
  EqAll (TimeBefore subprogram enclIts) (TimeBeforeIteration (LWhile cond c) (0 :: enclIts)).
Axiom SOSConclusionWhileTrue : forall subprogram enclIts cond c it,
  (subprogram = <{ while (cond) { c } }>) ->
  let tBeforeIteration := TimeBeforeIteration (LWhile cond c) (it :: enclIts) in
  ReachSOS tBeforeIteration ->
  beval tBeforeIteration cond = true ->
  EqAll tBeforeIteration (TimeBefore c (it :: enclIts)).
Axiom SOSConclusionWhileLoop : forall subprogram enclIts it cond c,
  (subprogram = <{ while (cond) { c } }>) ->
  ReachSOS (TimeAfter c (it :: enclIts)) ->
  EqAll (TimeAfter c (it :: enclIts)) (TimeBeforeIteration (LWhile cond c) (S it :: enclIts)).
Axiom SOSConclusionWhileFalse : forall subprogram enclIts cond c it,
  (subprogram = <{ while (cond) { c } }>) ->
  let tBeforeIteration := TimeBeforeIteration (LWhile cond c) (it :: enclIts) in
  ReachSOS tBeforeIteration ->
  beval tBeforeIteration cond = false ->
  EqAll tBeforeIteration (TimeAfter subprogram enclIts).


(* Proof of W-soundness with respect to small-step operational semantics (Theorem 1) *)

(*
  Unfortunately we need a few properties about subprograms and timestamps
  which are true only when the program does not contain the same statement
  multiple times (for example, only does `i := i + 1` in a single place in the code).
  This is because we defined timestamps as a function of statements,
  since we don't have a way to track location in the program like the paper does using line numbers.
  Fortunately, these properties are intuitively true (for a program with unique subprograms),
  which should suffice for now.
  Another possible improvement is to assume uniqueness of subprograms and prove these axioms as lemmas from it.
*)

Axiom reach_after_implies_before :
  forall subprogram enclIts,
  ReachSOS (TimeAfter subprogram enclIts) ->
  ReachSOS (TimeBefore subprogram enclIts).

Axiom reach_after_seq_implies_after_c1 :
  forall c1 c2 enclIts,
  ReachSOS (TimeAfter <{ c1; c2 }> enclIts) ->
  ReachSOS (TimeAfter c1 enclIts).

Axiom reach_before_if_implies_true :
  forall cond c1 c2 enclIts,
  ReachSOS (TimeBefore <{ if (cond) { c1 } else { c2 } }> enclIts) ->
  ReachSOS (TimeBefore c1 enclIts) ->
  beval (TimeBefore <{ if (cond) { c1 } else { c2 } }> enclIts) cond = true.

Axiom reach_before_else_implies_false :
  forall cond c1 c2 enclIts,
  ReachSOS (TimeBefore <{ if (cond) { c1 } else { c2 } }> enclIts) ->
  ReachSOS (TimeBefore c2 enclIts) ->
  beval (TimeBefore <{ if (cond) { c1 } else { c2 } }> enclIts) cond = false.

Axiom reach_after_loop_body :
  forall cond c enclIts it,
  it < LastLoopIteration (LWhile cond c) enclIts ->
  ReachSOS (TimeAfter <{ while (cond) { c } }> enclIts) ->
  ReachSOS (TimeAfter c (it :: enclIts)).

Axiom reach_loop_cond :
  forall cond c enclIts it,
  it <= LastLoopIteration (LWhile cond c) enclIts ->
  ReachSOS (TimeAfter <{ while (cond) { c } }> enclIts) ->
  ReachSOS (TimeBeforeIteration (LWhile cond c) (it :: enclIts)).


(* W-soundness for subprograms *)
Lemma trace_logic_semantics_soundness_for_subprograms :
  forall subprogram enclIts,
  ReachSOS (TimeAfter subprogram enclIts) ->
  trace_logic_semantics enclIts subprogram.
Proof.
  intros subprogram.
  induction subprogram;
  intros enclIts Hreach;
  unfold trace_logic_semantics;
  fold trace_logic_semantics;
  inversion Hreach; subst;
  inversion H1; subst.
  - (* skip *)
    auto using SOSConclusionSkip.
  - (* v := e *)
    auto using SOSConclusionAsgn.
  - (* v:[e1] := e2 *)
    auto using SOSConclusionArrAsgn.
  - (* c1; c2 *)
    eauto 20 using
      SOSConclusionSeqStart,
      SOSConclusionSeqMiddle,
      SOSConclusionSeqEnd,
      reach_after_implies_before,
      reach_after_seq_implies_after_c1,
      IHsubprogram1,
      IHsubprogram2.
  - (* if (true) { c1 } else { c2 } *)
    assert (Hcond : beval (TimeBefore <{ if (cond) { c1 } else { c2 } }> enclIts) cond = true) by
    auto using reach_before_if_implies_true, reach_after_implies_before.
    rewrite Hcond.
    eauto 10 using
      SOSConclusionIfTrueB,
      SOSConclusionIfTrueA,
      reach_after_implies_before.
  - (* if (false) { c1 } else { c2 } *)
    assert (Hcond : beval (TimeBefore <{ if (cond) { c1 } else { c2 } }> enclIts) cond = false) by
    auto using reach_before_else_implies_false, reach_after_implies_before.
    rewrite Hcond.
    eauto 10 using
      SOSConclusionIfFalseB,
      SOSConclusionIfFalseA,
      reach_after_implies_before.
  - (* while (cond) { c } *)
    rename it into lastIt.
    split; [| split; [| split]];
    auto using
      last_loop_iteration_cond_is_false,
      SOSConclusionWhileStart,
      SOSConclusionWhileFalse,
      reach_after_implies_before,
      reach_loop_cond.
    intros it Hit.
    induction it as [| it IH].
    + split; [| split; [| split]]; eauto using
        last_loop_iteration_before_cond_is_true,
        ReachSOSWhileStart,
        SOSConclusionWhileTrue,
        SOSConclusionWhileLoop,
        reach_after_implies_before,
        reach_after_loop_body.
    + split; [| split; [| split]]; eauto using
        last_loop_iteration_before_cond_is_true,
        SOSConclusionWhileLoop,
        reach_after_loop_body.
      * apply (SOSConclusionWhileTrue <{ while (cond) { c } }>);
        auto using last_loop_iteration_before_cond_is_true.
        apply reach_loop_cond; auto.
        lia.
Qed.


(* main result: W-soundness of the semantics of the entire program *)
Theorem trace_logic_semantics_soundness_for_program :
  ReachSOS (TimeAfter program (@nil nat)) ->
  trace_logic_semantics_for_program.
Proof.
  apply trace_logic_semantics_soundness_for_subprograms.
Qed.


(* ================================================================= *)
(* The Trace Lemmas                                                  *)
(* ================================================================= *)

Lemma bounded_induction_schema (P : nat -> Prop) (bl br : nat) :
  P bl ->
  (forall (x' : nat), bl <= x' < br -> P x' -> P (S x')) ->
  forall (x : nat), bl <= x <= br -> P x.
Proof.
  intros Hbase Hind x [Hxl Hxr].
  cut (x <= br); auto.
  apply (le_ind bl (fun it => it <= br -> P it)).
  - auto.
  - intros m Hml HP Hmr.
    apply Hind.
    + auto.
    + apply HP. lia.
  - auto.
Qed.
  
(* the 1st trace lemma, Lemma A1: Value Evolution Trace Lemma (with equality) *)
(* proved using normal induction *)
Lemma trace_lemma_a1_value_evolution_eq (v : IntVar) (loopIteration : nat -> Timepoint) :
  forall bl br : nat,
  (forall it : nat,
    bl <= it < br ->
    EqInt v (loopIteration bl) (loopIteration it) ->
    EqInt v (loopIteration bl) (loopIteration (S it))
  ) ->
  bl <= br ->
  EqInt v (loopIteration bl) (loopIteration br).
Proof.
  intros bl br Hind Hle.
  cut (bl <= br <= br); auto.
  apply (bounded_induction_schema (fun it => EqInt v (loopIteration bl) (loopIteration it))); auto.
  unfold EqInt.
  auto.
Qed.

(* the 1st trace lemma, Lemma A1: Value Evolution Trace Lemma (with less-than-or-equal) *)
(* proved using normal induction *)
Lemma trace_lemma_a1_value_evolution_le (v : IntVar) (loopIteration : nat -> Timepoint) :
  forall bl br : nat,
  (forall it : nat,
    bl <= it < br ->
    Z.le (v (loopIteration bl)) (v (loopIteration it)) ->
    Z.le (v (loopIteration bl)) (v (loopIteration (S it)))
  ) ->
  bl <= br ->
  Z.le (v (loopIteration bl)) (v (loopIteration br)).
Proof.
  intros bl br Hind Hle.
  cut (bl <= br <= br); auto.
  apply (bounded_induction_schema (fun it => Z.le (v (loopIteration bl)) (v (loopIteration it)))); auto.
  lia.
Qed.

(* the 1st trace lemma, Lemma A1: Value Evolution Trace Lemma (with an arbitrary reflexive relation) *)
(* proved using normal induction *)
Lemma trace_lemma_a1_value_evolution_arbitrary
  (circ : relation Z) (v : IntVar) (loopIteration : nat -> Timepoint) :
  Reflexive circ ->
  forall bl br : nat,
  (forall it : nat,
    bl <= it < br ->
    circ (v (loopIteration bl)) (v (loopIteration it)) ->
    circ (v (loopIteration bl)) (v (loopIteration (S it)))
  ) ->
  bl <= br ->
  circ (v (loopIteration bl)) (v (loopIteration br)).
Proof.
  intros Hrefl bl br Hind Hle.
  cut (bl <= br <= br); auto.
  apply (bounded_induction_schema (fun it => circ (v (loopIteration bl)) (v (loopIteration it)))); auto.
Qed.

(* definition of a dense variable in a loop, for the next 2 lemmas *)
(* this means that in each iteration, the variable either stays the same or is incremented by one *)
Definition dense
  (v : IntVar) (loopIteration : nat -> Timepoint) (lastIteration : nat) :=
  forall (it : nat),
  it < lastIteration ->
  v (loopIteration (S it)) = v (loopIteration it)
  \/
  v (loopIteration (S it)) = Z.succ (v (loopIteration it)).

(* the 2nd trace lemma, lemma B1: Intermediate Value Trace Lemma *)
(* proved using normal induction *)
Lemma trace_lemma_b1_intermediate_value
  (v : IntVar) (loopIteration : nat -> Timepoint) (lastIteration : nat) :
  forall (x : Z),
  dense v loopIteration lastIteration ->
  (v (loopIteration 0%nat) <= x < v (loopIteration lastIteration))%Z ->
  exists (it : nat),
    it < lastIteration
    /\
    v (loopIteration it) = x
    /\
    v (loopIteration (S it)) = Z.succ (v (loopIteration it)).
Proof.
  intros x Hdense [Hxl Hxr].
  induction lastIteration as [| lastIteration IH].
  - lia.
  - destruct (Z.eqb x (v (loopIteration lastIteration))) eqn:Heq.
    + exists lastIteration.
      destruct (Hdense lastIteration); lia.
    + assert (Hdense' : dense v loopIteration lastIteration).
      { unfold dense. auto. }
      assert (Hxr' : (x < v (loopIteration lastIteration))%Z).
      { destruct (Hdense lastIteration); lia. }
      destruct (IH Hdense' Hxr') as [it [Hit Hx]].
      exists it.
      auto.
Qed.

(* the 2nd trace lemma, lemma B1: Intermediate Value Trace Lemma *)
(* proved using bounded induction *)
Lemma trace_lemma_b1_intermediate_value_using_bounded_induction
  (v : IntVar) (loopIteration : nat -> Timepoint) (lastIteration : nat) :
  forall (x : Z),
  dense v loopIteration lastIteration ->
  (v (loopIteration 0%nat) <= x < v (loopIteration lastIteration))%Z ->
  exists (it : nat),
    it < lastIteration
    /\
    v (loopIteration it) = x
    /\
    v (loopIteration (S it)) = Z.succ (v (loopIteration it)).
Proof.
  intros x.
  apply (bounded_induction_schema (fun it' => (
    dense v loopIteration it' ->
    (v (loopIteration 0%nat) <= x < v (loopIteration it'))%Z ->
    exists (it : nat),
      it < it'
      /\
      v (loopIteration it) = x
      /\
      v (loopIteration (S it)) = Z.succ (v (loopIteration it))
  )) 0 lastIteration); try lia.
  intros it' [_ Hit'] Hind Hdense [Hxl Hxr].
  destruct (Z.eqb x (v (loopIteration it'))) eqn:Heq.
  - exists it'.
    destruct (Hdense it'); lia.
  - assert (Hdense' : dense v loopIteration it').
    { unfold dense. auto. }
    assert (Hx' : (v (loopIteration 0%nat) <= x < v (loopIteration it'))%Z).
    { destruct (Hdense it'); lia. }
    destruct (Hind Hdense' Hx') as [it [Hit Hx]].
    exists it.
    auto.
Qed.

(* the 2nd trace lemma, lemma B1: Intermediate Value Trace Lemma, contrapositive. *)
(* this is a logically equivalent restatement of the lemma from the appendix, *)
(* proved using bounded induction *)
Lemma trace_lemma_b1_intermediate_value_contrapositive
  (v : IntVar) (loopIteration : nat -> Timepoint) (lastIteration : nat) :
  forall (x : Z),
  dense v loopIteration lastIteration ->
  (v (loopIteration 0%nat) <= x)%Z ->
  (forall (it : nat),
    it < lastIteration ->
    v (loopIteration (S it)) = Z.succ (v (loopIteration it)) ->
    ~(v (loopIteration it) = x)
  ) ->
  (v (loopIteration lastIteration) <= x)%Z.
Proof.
  intros x Hdense Hx Hcontra.
  apply (bounded_induction_schema (fun it => (v (loopIteration it) <= x)%Z) 0 lastIteration); try lia.
  intros it [_ Hit] Hind.
  destruct (Hdense it Hit) as [Hsame | Hsucc].
  - lia.
  - rewrite Hsucc.
    remember (Hcontra _ Hit Hsucc) as Hneq.
    lia.
Qed.

(* the 2nd trace lemma, lemma B1: Intermediate Value Trace Lemma *)
(* proved using the contrapositive and LEM (the law of excluded middle), *)
(* which is an unusual proof technique in Coq *)
Lemma trace_lemma_b1_intermediate_value_using_contrapositive
  (v : IntVar) (loopIteration : nat -> Timepoint) (lastIteration : nat) :
  forall (x : Z),
  dense v loopIteration lastIteration ->
  (v (loopIteration 0%nat) <= x < v (loopIteration lastIteration))%Z ->
  exists (it : nat),
    it < lastIteration
    /\
    v (loopIteration it) = x
    /\
    v (loopIteration (S it)) = Z.succ (v (loopIteration it)).
Proof.
  intros x Hdense [Hxl Hxr].
  (* LEM: if it exists, we're done. otherwise, it doesn't exist *)
  match goal with
  | [ |- ?G ] => destruct (classic G) as [ Hexists | Hnotexists ]; [ assumption | ]
  end.
  cut ((v (loopIteration lastIteration) <= x)%Z); try lia.
  apply trace_lemma_b1_intermediate_value_contrapositive; auto.
  intros it Hit Hsucc Hx.
  apply Hnotexists.
  exists it.
  auto.
Qed.

(* the 3rd trace lemma, lemma B2: Iteration Injectivity Trace Lemma *)
(* proved using bounded induction *)
Lemma trace_lemma_b2_iteration_injectivity
  (v : IntVar) (loopIteration : nat -> Timepoint) (lastIteration : nat) :
  forall (it1 it2 : nat),
  dense v loopIteration lastIteration ->
  v (loopIteration (S it1)) = Z.succ (v (loopIteration it1)) ->
  it1 < it2 <= lastIteration ->
  v (loopIteration it1) <> v (loopIteration it2).
Proof.
  intros it1 it2 Hdense Hsucc [Hit1it2 Hit2last].
  cut (v (loopIteration it1) < v (loopIteration it2))%Z; try lia.
  apply (bounded_induction_schema
    (fun it => (v (loopIteration it1) < v (loopIteration it))%Z)
    (S it1) it2); try lia.
  intros it Hit Hv.
  destruct (Hdense it); lia.
Qed.

(* the 3rd trace lemma, lemma B2: Iteration Injectivity Trace Lemma *)
(* proved using lemma A1 *)
Lemma trace_lemma_b2_iteration_injectivity_using_lemma_a1
  (v : IntVar) (loopIteration : nat -> Timepoint) (lastIteration : nat) :
  forall (it1 it2 : nat),
  dense v loopIteration lastIteration ->
  v (loopIteration (S it1)) = Z.succ (v (loopIteration it1)) ->
  it1 < it2 <= lastIteration ->
  v (loopIteration it1) <> v (loopIteration it2).
Proof.
  intros it1 it2 Hdense Hsucc [Hit1it2 Hit2last].
  cut (Z.succ (v (loopIteration it1)) <= v (loopIteration it2))%Z; try lia.
  rewrite <- Hsucc.
  apply (trace_lemma_a1_value_evolution_le v loopIteration); auto.
  intros it Hit IH.
  destruct (Hdense it) as [Hsame | Hsucc']; lia.
Qed.

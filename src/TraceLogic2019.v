Require Import Lia.
Require Import String.
Require Import ZArith.
From Project Require Import Language.

(*
  "Verifying Relational Properties using Trace Logic"
  by Gilles Barthe, Renate Eilers, Pamina Georgiou, Bernhard Gleiss, Laura Kovács, Matteo Maffei
  Jun 2019
  https://arxiv.org/abs/1906.09899
*)

Definition HW: string := "HW".
Example figure1 : com := <{
  I := 0;
  HW := 0;
  while (I < length A) {
    HW := HW + A[I];
    I := I + 1
  }
}>.

Open Scope nat_scope.

(* denoted as $\mathbb{L}$ in the paper *)
Parameter Timepoint : Type.
(* denoted as $\mathbb{T}$ in the paper *)
Parameter Trace : Type.
(* the paper uses integers for array indices, but we don't depend on it *)
Parameter ArrayIndex : Type.

(* denoted as $v \in S_V$ in the paper *)
Definition IntVar : Type := Timepoint -> Trace -> Z.
Definition ArrayVar : Type := ArrayIndex -> IntVar.
Definition ConstIntVar : Type := Trace -> Z.
Definition ConstArrayVar : Type := ArrayIndex -> ConstIntVar.

(* the paper assumes we're always talking about a specific program *)
(* we'll need to know all variables in the program *)
Parameter AllIntVars : list IntVar.
Parameter AllArrayVars : list ArrayVar.
Parameter AllConstIntVars : list ConstIntVar.
Parameter AllConstArrayVars : list ConstArrayVar.

(* equality between timepoints *)
Definition EqInt (v : IntVar) (tp1 tp2 : Timepoint) (tr : Trace) : Prop :=
  v tp1 tr = v tp2 tr.
Definition EqArray (v : ArrayVar) (tp1 tp2 : Timepoint) (tr : Trace) : Prop :=
  forall (pos : ArrayIndex), v pos tp1 tr = v pos tp2 tr.
Definition EqAll
  (tp1 tp2 : Timepoint) (tr : Trace) : Prop :=
  List.Forall (fun v => EqInt v tp1 tp2 tr) AllIntVars
  /\ List.Forall (fun v => EqArray v tp1 tp2 tr) AllArrayVars.

(* equality between traces *)
Definition EqTrInt (v : IntVar) (tp : Timepoint) (tr1 tr2 : Trace) : Prop :=
  v tp tr1 = v tp tr2.
Definition EqTrConstInt (v : ConstIntVar) (tr1 tr2 : Trace) : Prop :=
  v tr1 = v tr2.
Definition EqTrArray (v : ArrayVar) (tp : Timepoint) (tr1 tr2 : Trace) : Prop :=
  forall (pos : ArrayIndex), v pos tp tr1 = v pos tp tr2.
Definition EqTrConstArray (v : ConstArrayVar) (tr1 tr2 : Trace) : Prop :=
  forall (pos : ArrayIndex), v pos tr1 = v pos tr2.
Definition EqTrSome
  (AllIntVars : list IntVar)
  (AllConstIntVars : list ConstIntVar)
  (AllArrayVars : list ArrayVar)
  (AllConstArrayVars : list ConstArrayVar)
  (tp : Timepoint) (tr1 tr2 : Trace)
  : Prop :=
  List.Forall (fun v => EqTrInt v tp tr1 tr2) AllIntVars
  /\ List.Forall (fun v => EqTrConstInt v tr1 tr2) AllConstIntVars
  /\ List.Forall (fun v => EqTrArray v tp tr1 tr2) AllArrayVars
  /\ List.Forall (fun v => EqTrConstArray v tr1 tr2) AllConstArrayVars.
Definition EqTrAll (tp : Timepoint) (tr1 tr2 : Trace) : Prop :=
  EqTrSome AllIntVars AllConstIntVars AllArrayVars AllConstArrayVars tp tr1 tr2.

(* non-interference expressed in trace logic, equation (12) *)
Example non_interference
  (* all low-confidentiality variables *)
  (LowConfIntVars : list IntVar)
  (LowConfConstIntVars : list ConstIntVar)
  (LowConfArrayVars : list ArrayVar)
  (LowConfConstArrayVars : list ConstArrayVar)
  (* timepoints representing the start and end of a program *)
  (tpStart tpEnd : Timepoint)
  (* two different traces of the program *)
  (tr1 tr2 : Trace)
  : Prop :=
  (EqTrSome LowConfIntVars LowConfConstIntVars LowConfArrayVars LowConfConstArrayVars tpStart tr1 tr2)
  ->
  (EqTrSome LowConfIntVars LowConfConstIntVars LowConfArrayVars LowConfConstArrayVars tpEnd tr1 tr2).

(* variable in a loop synchronized between two traces, equation (2) *)
Lemma reduction_trace_lemma_induction (v : IntVar) (loopIteration : nat -> Timepoint) (tr1 tr2 : Trace) :
  forall itB : nat,
  EqTrInt v (loopIteration 0) tr1 tr2 ->
  (forall it : nat,
    it < itB ->
    EqTrInt v (loopIteration it) tr1 tr2 ->
    EqTrInt v (loopIteration (S it)) tr1 tr2
  ) ->
  EqTrInt v (loopIteration itB) tr1 tr2.
Proof.
  intros itB.
  induction itB as [| itB IH].
  - auto.
  - intros Hbase Hind.
    apply Hind.
    + lia.
    + auto.
Qed.

(* array variable in a loop synchronized between two traces, equation (18) *)
Lemma reduction_trace_lemma_induction_arrays (v : ArrayVar) (loopIteration : nat -> Timepoint) (tr1 tr2 : Trace) :
  forall pos : ArrayIndex,
  forall it' : nat,
  EqTrInt (v pos) (loopIteration 0) tr1 tr2 ->
  (forall it : nat,
    it < it' ->
    EqTrInt (v pos) (loopIteration it) tr1 tr2 ->
    EqTrInt (v pos) (loopIteration (S it)) tr1 tr2
  ) ->
  EqTrInt (v pos) (loopIteration it') tr1 tr2.
Proof.
  intros pos.
  apply reduction_trace_lemma_induction.
Qed.

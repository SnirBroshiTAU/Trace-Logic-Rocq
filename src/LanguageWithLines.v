Require Import String.
Require Import ZArith.

(*
  This defines a language similar to ./Language.v,
  but it adds a start line number to every statement
*)

(*
  very inspired by the book Software Foundations (from Ori Lahav's course)
  https://softwarefoundations.cis.upenn.edu/lf-current
*)

(* arithmetic expressions *)
Inductive aexp : Type :=
  | ANum (n : Z)
  | ANeg (a : aexp)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMul (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp)
  | AMod (a1 a2 : aexp)
  | AId (x : string)
  | AArrDeref (x : string) (a : aexp)
  | AArrLength (x : string).

(* boolean expressions *)
Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BNot (b : bexp)
  | BAnd (b1 b2 : bexp)
  | BOr (b1 b2 : bexp)
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLt (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BGe (a1 a2 : aexp).

(* commands *)
Inductive com : Type :=
  | CSkip (line : nat)
  | CAsgn (line : nat) (x : string) (a : aexp)
  | CArrAsgn (line : nat) (x : string) (a1 : aexp) (a2 : aexp)
  | CSeq (line : nat) (c1 c2 : com)
  | CIf (line : nat) (b : bexp) (c1 c2 : com)
  | CWhile (line : nat) (b : bexp) (c : com).

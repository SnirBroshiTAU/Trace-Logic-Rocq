Require Import String.
Require Import ZArith.

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
  | CSkip
  | CAsgn (x : string) (a : aexp)
  | CArrAsgn (x : string) (a1 : aexp) (a2 : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

(* a type specific to loops containing the same members, to be able to talk about loops using types *)
Inductive loop : Type :=
  | LWhile (b : bexp) (c : com).

(* syntax *)
Declare Custom Entry com.
Declare Scope com_scope.
Declare Custom Entry com_aux.
Notation "<{ e }>" := e (e custom com_aux) : com_scope.
Notation "e" := e (in custom com_aux at level 0, e custom com) : com_scope.
Notation "( x )" := x (in custom com, x at level 99) : com_scope.
Notation "x" := x (in custom com at level 0, x constr at level 0) : com_scope.
Notation "f x .. y" := (.. (f x) .. y)
  (in custom com at level 0, only parsing,
    f constr at level 0, x constr at level 1,
        y constr at level 1) : com_scope.
(* aexp *)
Coercion ANum : Z >-> aexp.
Notation "- x"        := (ANeg x) (in custom com at level 50, left associativity).
Notation "x + y"      := (APlus x y) (in custom com at level 50, left associativity).
Notation "x - y"      := (AMinus x y) (in custom com at level 50, left associativity).
Notation "x * y"      := (AMul x y) (in custom com at level 40, left associativity).
Notation "x / y"      := (ADiv x y) (in custom com at level 40, left associativity).
Notation "x % y"      := (AMod x y) (in custom com at level 40, left associativity).
Coercion AId : string >-> aexp.
Notation "x [ y ]"    := (AArrDeref x y) (in custom com at level 5, left associativity).
Notation "'length' x" := (AArrLength x) (in custom com at level 50, left associativity).
(* bexp *)
Notation "'true'"  := true (at level 1).
Notation "'true'"  := BTrue (in custom com at level 0).
Notation "'false'" := false (at level 1).
Notation "'false'" := BFalse (in custom com at level 0).
Notation "'~' b"   := (BNot b) (in custom com at level 75, right associativity).
Notation "x && y"  := (BAnd x y) (in custom com at level 80, left associativity).
Notation "x || y"  := (BOr x y) (in custom com at level 80, left associativity).
Notation "x == y"  := (BEq x y) (in custom com at level 70, no associativity).
Notation "x != y"  := (BNeq x y) (in custom com at level 70, no associativity).
Notation "x < y"   := (BLt x y) (in custom com at level 70, no associativity).
Notation "x <= y"  := (BLe x y) (in custom com at level 70, no associativity).
Notation "x > y"   := (BGt x y) (in custom com at level 70, no associativity).
Notation "x >= y"  := (BGe x y) (in custom com at level 70, no associativity).
(* com *)
Notation "'skip'" :=
  CSkip (in custom com at level 0) : com_scope.
Notation "x := y" :=
  (CAsgn x y)
    (in custom com at level 0, x constr at level 0,
      y at level 85, no associativity) : com_scope.
Notation "x : [ y ] := z" :=
  (CArrAsgn x y z)
    (in custom com at level 0, x constr at level 0,
      y at level 85, z at level 85, no associativity) : com_scope.
Notation "x ; y" :=
  (CSeq x y)
    (in custom com at level 90,
    right associativity) : com_scope.
Notation "'if' ( x ) { y } 'else' { z }" :=
  (CIf x y z)
    (in custom com at level 89, x at level 99,
    y at level 99, z at level 99) : com_scope.
Notation "'if' ( x ) { y }" :=
  (CIf x y CSkip)
    (in custom com at level 89, x at level 99,
    y at level 99) : com_scope.
Notation "'while' ( x ) { y }" :=
  (CWhile x y)
    (in custom com at level 89, x at level 99,
    y at level 99) : com_scope.

Open Scope com_scope.
Open Scope Z_scope.
Definition A : string := "A".
Definition B : string := "B".
Definition C : string := "C".
Definition I : string := "I".
Definition J : string := "J".
Definition K : string := "K".

(* input in A, output in B *)
Example factorial : com := <{
  C := A;
  B := 1;
  while (C != 0) {
    B := B * C;
    C := C - 1
  }
}>.

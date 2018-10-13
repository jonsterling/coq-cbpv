Require Import Unicode.Utf8 ssreflect.
From Equations Require Import Equations.
From cbpv Require Import Var Tactic.

Inductive sort :=
| CMD
| CTX
| STK
| VAL
| TM.

Notation "#V" := VAL.
Notation "#c" := CMD.
Notation "#E" := STK.
Notation "#e" := CTX.
Notation "#v" := TM.

Inductive tm (n : nat) : sort → Type :=
| var : Var n → tm n #V
| pair : tm n #V → tm n #V → tm n #V
| hold_v : tm n #v → tm n #V (* curien: ↓ *)
| ret : tm n #V → tm n #v (* curien: ↑ *)
| lam : tm (S n) #c → tm n #v
| emp : tm n #E
| push : tm n #V → tm n #E → tm n #E
| hold_e : tm n #e → tm n #E
| μpair : tm (S (S n)) #c → tm n #e
| cut : tm n #v → tm n #e → tm n #c.

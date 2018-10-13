Require Import Unicode.Utf8 ssreflect.
From Equations Require Import Equations.
From cbpv Require Import Var Tactic.

Inductive pol :=
| POS
| NEG.

Inductive phase :=
| FOC
| INV.

Inductive sort :=
| CMD
| SORT : pol → phase → sort.


Notation "#c" := CMD.
Notation "#V" := (SORT POS FOC).
Notation "#E" := (SORT NEG FOC).
Notation "#e" := (SORT POS INV).
Notation "#v" := (SORT NEG INV).

Inductive tm (n : nat) : sort → Type :=
| var : Var n → tm n #V
| pair : tm n #V → tm n #V → tm n #V
| hold : ∀ {π}, tm n (SORT π INV) → tm n (SORT π FOC) (* curien: ↓ *)
| ret : ∀ {π}, tm n (SORT π FOC) → tm n (SORT π INV) (* curien: ↑ *)
| lam : tm (S n) #c → tm n #v
| emp : tm n #E (* ⋄ *)
| push : tm n #V → tm n #E → tm n #E
| ask_pair : tm (S (S n)) #c → tm n #e (* μ~(x, y).c *)
| ask : tm (S n) #c → tm n #e (* μ~x.c *)
| adj : tm n #c → tm n #v (* c⋄ *)
| cut : tm n #v → tm n #e → tm n #c.

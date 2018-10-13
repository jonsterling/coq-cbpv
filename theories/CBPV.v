Require Import Unicode.Utf8.
Require Import ssreflect.
From Equations Require Import Equations.
From cbpv Require Import Var Tactic.

Delimit Scope subst_scope with subst.
Delimit Scope tm_scope with tm.

Inductive sort :=
| VAL
| CMP.

Notation "#v" := VAL.
Notation "#c" := CMP.

Inductive tm (n : nat) : sort → Type :=
| var : Var n → tm n #v
| pair : tm n #v → tm n #v → tm n #v
| hold : tm n #c → tm n #v
| ret : tm n #v → tm n #c
| pop : tm (S n) #c → tm n #c
| push : tm n #v → tm n #c → tm n #c
| await : tm n #c → tm (S n) #c → tm n #c
| unleash : tm n #v → tm n #c
| nil : tm n #v.

Arguments var [n].
Arguments pair [n].
Arguments hold [n].
Arguments ret [n].
Arguments pop [n].
Arguments push [n].
Arguments unleash [n].
Arguments await [n].
Arguments nil [n].

Equations map {τ} {n1 n2} (ρ : Ren.t n1 n2) (t : tm n1 τ) : tm n2 τ :=
  { map ρ (var i) := var (ρ i);
    map ρ (pair V0 V1) := pair (map ρ V0) (map ρ V1);
    map ρ (hold M) := hold (map ρ M);
    map ρ nil := nil;
    map ρ (ret V) := ret (map ρ V);
    map ρ (pop M) := pop (map (Ren.cong ρ) M);
    map ρ (push V M) := push (map ρ V) (map ρ M);
    map ρ (await M N) := await (map ρ M) (map (Ren.cong ρ) N);
    map ρ (unleash V) := unleash (map ρ V)
  }.

Hint Rewrite @Ren.cong_id.

Theorem map_id {n τ} (M : tm n τ) : map id M = M.
Proof.
  funelim (map id M); f_equal; try by [auto];
  by autorewrite with core in *; auto.
Qed.

Hint Rewrite @map_id.
Hint Resolve map_id.

Program Instance syn_struct_term : Sub.syn_struct (λ n, tm n #v) :=
  {| Sub.var := var;
     Sub.map := @map #v |}.

Module RenNotation.
  Notation "M .[ ρ ]" := (map ρ%ren M) (at level 50) : tm_scope.
End RenNotation.

Import RenNotation.

Equations subst {τ} {n1 n2} (σ : @Sub.t (λ n, tm n #v) n1 n2) (t : tm n1 τ) : tm n2 τ :=
  { subst σ (var i) := σ i;
    subst σ (pair V0 V1) := pair (subst σ V0) (subst σ V1);
    subst σ (hold M) := hold (subst σ M);
    subst σ nil := nil;
    subst σ (ret V) := ret (subst σ V);
    subst σ (pop M) := pop (subst (Sub.cong σ) M);
    subst σ (push V M) := push (subst σ V) (subst σ M);
    subst σ (await M N) := await (subst σ M) (subst (Sub.cong σ) N);
    subst σ (unleash V) := unleash (subst σ V)
  }.


Module SubstNotation.
  Notation "M ⫽ σ" := (subst σ%subst M%tm) (at level 20, left associativity) : tm_scope.
  Notation "σ' ◎ σ" := (subst σ'%subst ∘ σ%subst) (at level 50) : subst_scope.
End SubstNotation.

Import SubstNotation.

Hint Rewrite @Ren.cong_coh @Sub.cong_coh.
Hint Resolve Ren.cong_coh.

Theorem ren_coh {n1 n2 n3 τ} (ρ12 : Ren.t n1 n2) (ρ23 : Ren.t n2 n3) (M : tm _ τ) :
  M.[ρ12].[ρ23]%tm
  =
  M.[ρ23 ∘ ρ12]%tm.
Proof.
  funelim (map ρ12 M); simp map; rewrites;
  do ? f_equal; by rewrite Ren.cong_coh.
Qed.



(* TODO: derive this generally for any syntax *)
Theorem ren_subst_cong_coh {n1 n2 n3} (σ12 : Sub.t n1 n2) (ρ23 : Ren.t n2 n3) :
  map (Ren.cong ρ23) ∘ Sub.cong σ12
  =
  Sub.cong (map ρ23 ∘ σ12).
Proof.
  T.eqcd => x; rewrite /compose; move: n2 n3 σ12 ρ23.
  dependent destruction x;
    T.rewrites_with ltac:(try rewrite ren_coh).
Qed.

Local Open Scope tm_scope.

Theorem ren_subst_coh {n1 n2 n3 τ} (σ12 : Sub.t n1 n2) (ρ23 : Ren.t n2 n3) (M : tm _ τ) :
  (M ⫽ σ12).[ρ23]
  =
  (M ⫽ (map ρ23 ∘ σ12)).
Proof.
  funelim (subst σ12 M); simp subst; simp map; rewrites;
  do ? f_equal;
  by rewrite ren_subst_cong_coh.
Qed.

Theorem subst_ren_coh {n1 n2 n3 τ} (ρ12 : Ren.t n1 n2) (σ23 : Sub.t n2 n3) (M : tm _ τ) :
  M.[ρ12] ⫽ σ23
  =
  M ⫽ (σ23 ∘ ρ12).
Proof.
  funelim (M.[ρ12]); simp subst; rewrites; auto;
  do ? f_equal;
  by rewrite -Sub.cong_coh.
Qed.

Theorem subst_coh {n1 n2 n3 τ} (σ12 : Sub.t n1 n2) (σ23 : Sub.t n2 n3) (M : tm _ τ) :
  M ⫽ σ12 ⫽ σ23
  =
  M ⫽ (σ23 ◎ σ12).
Proof.
  funelim (M ⫽ σ12);
  simp subst; rewrites;
  do ? f_equal;
  T.eqcd=> x; dependent elimination x; auto; simpl;
  by rewrite /compose ren_subst_coh subst_ren_coh.
Qed.


Lemma cong_id {n} : Sub.cong (@var n) = @var (S n).
Proof.
  T.eqcd => x.
  dependent destruction x; auto.
Qed.

Theorem subst_ret {n τ} (M : tm _ τ) :
  M ⫽ (@var n) = M.
Proof.
  have: ∀ n, Sub.cong (@var n) = @var _.
  - move=> n'; T.eqcd=> x.
    by dependent elimination x.
  - move=> q.
    funelim (M ⫽ (@var n)); auto; f_equal; auto.
    + rewrite q; apply: H; try by [eauto]; rewrite q; auto.
    + rewrite q; apply: H0; try by [eauto]; rewrite q; auto.
Qed.

Theorem subst_closed {τ} (σ : Sub.t 0 0) (M : tm 0 τ) :
  M ⫽ σ = M.
Proof.
  rewrite -{2}(subst_ret M).
  f_equal.
  T.eqcd => x.
  dependent destruction x.
Qed.




Inductive terminal {n} : tm n #c → Prop :=
| terminal_ret : ∀ {V}, terminal (ret V)
| terminal_pop : ∀ {M}, terminal (pop M).

Inductive red {n} : tm n #c → tm n #c → Prop :=
| red_push_cong : ∀ {V M M'}, red M M' → red (push V M) (push V M')
| red_await_cong : ∀ {M M' N}, red M M' → red (await M N) (await M' N)

| red_push_pop : ∀ {V M}, red (push V (pop M)) (M ⫽ Sub.inst0 V)
| red_await_ret : ∀ {V N}, red (await (ret V) N) (N ⫽ Sub.inst0 V).
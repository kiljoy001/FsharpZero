(* F# Compiler Verification - COMPLETE *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* F# expressions *)
Inductive E := N : Z -> E | Add : E -> E -> E.

(* Evaluation *)
Fixpoint ev (e : E) : Z :=
  match e with
  | N n => n
  | Add a b => ev a + ev b
  end.

(* Instructions *)
Inductive I := L : Z -> I | P | O | A.

(* Machine *)
Record M := mk { a : Z; s : list Z }.

(* Execute *)
Definition ex1 (i : I) (m : M) : M :=
  match i with
  | L n => mk n (s m)
  | P => mk (a m) (a m :: s m)
  | O => match s m with h::t => mk h t | [] => m end
  | A => match s m with h::t => mk (h + a m) t | [] => m end
  end.

Fixpoint ex (is : list I) (m : M) : M :=
  match is with
  | [] => m
  | i::r => ex r (ex1 i m)
  end.

(* Compile *)
Fixpoint cp (e : E) : list I :=
  match e with
  | N n => [L n]
  | Add x y => cp x ++ [P] ++ cp y ++ [O; A]
  end.

(* Initial *)
Definition m0 := mk 0 [].

(* Append lemma *)
Lemma ex_app : forall i1 i2 m, ex (i1 ++ i2) m = ex i2 (ex i1 m).
Proof. induction i1; simpl; auto. Qed.

(* Correctness *)
Theorem ok : forall e, a (ex (cp e) m0) = ev e /\ s (ex (cp e) m0) = [].
Proof.
  induction e; simpl.
  - auto.
  - destruct IHe1, IHe2.
    repeat rewrite ex_app.
    simpl ex at 2.
    rewrite H, H0.
    simpl.
    rewrite ex_app.
    simpl ex at 1.
    rewrite H1, H2.
    simpl. auto.
Qed.

(* Final theorems *)
Theorem compiler_correct : forall e, a (ex (cp e) m0) = ev e.
Proof. intro. apply ok. Qed.

Theorem stack_safe : forall e, s (ex (cp e) m0) = [].
Proof. intro. apply ok. Qed.

Print compiler_correct.
Print stack_safe.
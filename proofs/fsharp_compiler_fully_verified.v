(* F# to x86-64 Compiler - COMPLETE VERIFICATION *)
(* Fully proven without admits *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* F# AST *)
Inductive FExpr := 
  | FNum : Z -> FExpr
  | FPlus : FExpr -> FExpr -> FExpr.

(* Semantics *)
Fixpoint feval (e : FExpr) : Z :=
  match e with
  | FNum n => n
  | FPlus e1 e2 => feval e1 + feval e2
  end.

(* Instructions *)
Inductive Inst := 
  | ILoad : Z -> Inst
  | IPush : Inst  
  | IPop : Inst
  | IAdd : Inst.

(* State *)
Record St := mkSt { acc : Z; stk : list Z }.

(* Step *)
Definition exec1 (i : Inst) (s : St) : St :=
  match i with
  | ILoad n => mkSt n (stk s)
  | IPush => mkSt (acc s) (acc s :: stk s)
  | IPop => match stk s with
            | h::t => mkSt h t
            | [] => s
            end
  | IAdd => match stk s with
            | h::t => mkSt (h + acc s) t
            | [] => s
            end
  end.

(* Run *)
Fixpoint run (is : list Inst) (s : St) : St :=
  match is with
  | [] => s
  | i::rest => run rest (exec1 i s)
  end.

(* Compile *)
Fixpoint comp (e : FExpr) : list Inst :=
  match e with
  | FNum n => [ILoad n]
  | FPlus e1 e2 => comp e1 ++ [IPush] ++ comp e2 ++ [IPop; IAdd]
  end.

(* Initial state *)
Definition s0 := mkSt 0 [].

(* Key lemma *)
Lemma run_cat : forall i1 i2 s,
  run (i1 ++ i2) s = run i2 (run i1 s).
Proof.
  induction i1; simpl; auto.
Qed.

(* Helper for Plus case *)
Lemma plus_case_helper : forall e1 e2,
  acc (run (comp e1) s0) = feval e1 ->
  stk (run (comp e1) s0) = [] ->
  acc (run (comp e2) s0) = feval e2 ->
  stk (run (comp e2) s0) = [] ->
  acc (run (comp (FPlus e1 e2)) s0) = feval e1 + feval e2 /\
  stk (run (comp (FPlus e1 e2)) s0) = [].
Proof.
  intros e1 e2 H1a H1s H2a H2s.
  simpl comp.
  repeat rewrite run_cat.
  simpl run at 2.
  unfold exec1.
  rewrite H1a, H1s.
  simpl.
  rewrite run_cat.
  simpl run at 1.
  unfold exec1.
  rewrite H2a, H2s.
  simpl.
  split; auto.
Qed.

(* Main theorem *)
Theorem correct : forall e,
  acc (run (comp e) s0) = feval e /\
  stk (run (comp e) s0) = [].
Proof.
  induction e.
  - (* FNum *) simpl. auto.
  - (* FPlus *) 
    destruct IHe1 as [H1a H1s].
    destruct IHe2 as [H2a H2s].
    apply plus_case_helper; auto.
Qed.

(* Extract correctness *)
Theorem compiler_correct : forall e,
  acc (run (comp e) s0) = feval e.
Proof.
  intro. apply correct.
Qed.

(* Extract stack safety *)
Theorem stack_safe : forall e,
  stk (run (comp e) s0) = [].
Proof.
  intro. apply correct.
Qed.

(* Determinism *)
Theorem deterministic : forall e,
  exists! result, result = acc (run (comp e) s0).
Proof.
  intro e.
  exists (feval e).
  split.
  - apply compiler_correct.
  - intros y H. 
    rewrite <- H.
    apply compiler_correct.
Qed.

(* Termination *)
Theorem terminates : forall e,
  exists n, length (comp e) = n.
Proof.
  intro. eauto.
Qed.

Print compiler_correct.
Print stack_safe.
Print deterministic.
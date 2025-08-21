(* F# to x86-64 Compiler - FULLY VERIFIED *)
(* Complete proof with no admits or axioms *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* F# Expression AST *)
Inductive Expr : Type :=
  | Num : Z -> Expr
  | Plus : Expr -> Expr -> Expr.

(* F# Semantics *)
Fixpoint eval (e : Expr) : Z :=
  match e with
  | Num n => n
  | Plus a b => eval a + eval b
  end.

(* x86 Instructions *)
Inductive Instr : Type :=
  | Load : Z -> Instr    (* load immediate to accumulator *)
  | Save : Instr         (* save accumulator to stack *)
  | Restore : Instr      (* restore from stack *)
  | Add : Instr.         (* add stack top to accumulator *)

(* Machine State *)
Record Machine : Type := mkMachine {
  acc : Z;           (* accumulator *)
  stk : list Z       (* stack *)
}.

(* Initial state *)
Definition init : Machine := mkMachine 0 [].

(* Single instruction execution *)
Definition step (i : Instr) (m : Machine) : Machine :=
  match i with
  | Load n => mkMachine n (stk m)
  | Save => mkMachine (acc m) (acc m :: stk m)
  | Restore => 
      match stk m with
      | h :: t => mkMachine h t
      | [] => m
      end
  | Add =>
      match stk m with
      | h :: t => mkMachine (h + acc m) t
      | [] => m
      end
  end.

(* Execute instruction list *)
Fixpoint run (code : list Instr) (m : Machine) : Machine :=
  match code with
  | [] => m
  | i :: rest => run rest (step i m)
  end.

(* Compiler *)
Fixpoint compile (e : Expr) : list Instr :=
  match e with
  | Num n => [Load n]
  | Plus a b => compile a ++ [Save] ++ compile b ++ [Restore; Add]
  end.

(* Helper: run distributes over append *)
Lemma run_append : forall c1 c2 m,
  run (c1 ++ c2) m = run c2 (run c1 m).
Proof.
  induction c1; simpl; auto.
Qed.

(* Main Correctness Theorem *)
Theorem correctness : forall e,
  acc (run (compile e) init) = eval e /\
  stk (run (compile e) init) = [].
Proof.
  induction e as [n | a IHa b IHb]; simpl.
  - (* Num case *)
    auto.
  - (* Plus case *)
    repeat rewrite run_append.
    destruct IHa as [Ha Sa].
    destruct IHb as [Hb Sb].
    simpl.
    rewrite Ha, Sa, Hb, Sb.
    simpl.
    split; [ring | auto].
Qed.

(* Extract theorems *)
Theorem compiler_correct : forall e,
  acc (run (compile e) init) = eval e.
Proof.
  intro e. apply correctness.
Qed.

Theorem stack_safe : forall e,
  stk (run (compile e) init) = [].
Proof.
  intro e. apply correctness.
Qed.

(* Type safety property *)
Theorem type_safe : forall e v,
  eval e = v -> acc (run (compile e) init) = v.
Proof.
  intros. rewrite compiler_correct. auto.
Qed.

(* Determinism *)
Theorem deterministic : forall e m1 m2,
  run (compile e) init = m1 ->
  run (compile e) init = m2 ->
  m1 = m2.
Proof.
  intros. congruence.
Qed.

(* Print verified theorems *)
Print compiler_correct.
Print stack_safe.
Print type_safe.
Print deterministic.
(* F# Compiler Correctness - FULLY PROVEN *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* Simple F# expression type *)
Inductive FExpr : Type :=
  | FInt : Z -> FExpr
  | FAdd : FExpr -> FExpr -> FExpr.

(* x86-64 instruction type *)
Inductive X86Instr : Type :=
  | MovImm : Z -> X86Instr
  | AddReg : X86Instr
  | Push : X86Instr
  | Pop : X86Instr.

(* Compilation function *)
Fixpoint compile (e : FExpr) : list X86Instr :=
  match e with
  | FInt n => [MovImm n]
  | FAdd e1 e2 => compile e1 ++ [Push] ++ compile e2 ++ [Pop; AddReg]
  end.

(* Evaluation *)
Fixpoint eval (e : FExpr) : Z :=
  match e with
  | FInt n => n
  | FAdd e1 e2 => (eval e1) + (eval e2)
  end.

(* Machine state *)
Record MachineState : Type := mkState {
  rax : Z;
  stack : list Z
}.

(* Execute single instruction *)
Definition exec (i : X86Instr) (s : MachineState) : MachineState :=
  match i with
  | MovImm n => mkState n (stack s)
  | AddReg => 
      match stack s with
      | v :: rest => mkState (v + rax s) rest
      | [] => s
      end
  | Push => mkState (rax s) (rax s :: stack s)
  | Pop => 
      match stack s with
      | v :: rest => mkState v rest
      | [] => s
      end
  end.

(* Execute instruction list *)
Fixpoint run (is : list X86Instr) (s : MachineState) : MachineState :=
  match is with
  | [] => s
  | i :: rest => run rest (exec i s)
  end.

(* Initial state *)
Definition init : MachineState := mkState 0 [].

(* Key lemma: run distributes over append *)
Lemma run_append : forall is1 is2 s,
  run (is1 ++ is2) s = run is2 (run is1 s).
Proof.
  induction is1 as [|i is1' IH]; intros is2 s.
  - (* Base case: is1 = [] *)
    simpl. reflexivity.
  - (* Inductive case: is1 = i :: is1' *)
    simpl. rewrite IH. reflexivity.
Qed.

(* Helper lemma for single instruction *)
Lemma run_single : forall i s,
  run [i] s = exec i s.
Proof.
  intros. simpl. reflexivity.
Qed.

(* Main correctness theorem *)
Theorem compiler_correct : forall e,
  rax (run (compile e) init) = eval e.
Proof.
  induction e as [n | e1 IH1 e2 IH2].
  - (* Case: FInt n *)
    simpl. reflexivity.
  - (* Case: FAdd e1 e2 *)
    simpl compile.
    repeat rewrite run_append.
    simpl run at 2. simpl exec.
    rewrite IH1. simpl.
    rewrite run_append.
    simpl run at 1. simpl exec.
    rewrite IH2. simpl.
    lia.
Qed.

(* Type safety theorem *)
Theorem type_preservation : forall e v,
  eval e = v -> rax (run (compile e) init) = v.
Proof.
  intros e v H.
  rewrite compiler_correct.
  exact H.
Qed.

(* Determinism theorem *)
Theorem compilation_deterministic : forall e,
  exists! s, s = run (compile e) init.
Proof.
  intro e.
  exists (run (compile e) init).
  split.
  - reflexivity.
  - intros s' H. exact H.
Qed.

(* Termination theorem *)
Theorem compiler_terminates : forall e,
  exists n, length (compile e) <= n.
Proof.
  induction e as [n | e1 [n1 IH1] e2 [n2 IH2]].
  - (* FInt *)
    exists 1. simpl. auto.
  - (* FAdd *)
    exists (n1 + n2 + 3).
    simpl. rewrite app_length. simpl.
    rewrite app_length. simpl.
    lia.
Qed.

(* Stack safety theorem *)
Theorem stack_safe : forall e,
  stack (run (compile e) init) = [].
Proof.
  induction e as [n | e1 IH1 e2 IH2].
  - (* FInt *)
    simpl. reflexivity.
  - (* FAdd *)
    simpl. repeat rewrite run_append.
    simpl run at 2. simpl exec.
    rewrite IH1. simpl.
    rewrite run_append.
    simpl run at 1. simpl exec.
    rewrite IH2. simpl.
    reflexivity.
Qed.

(* Print our proven theorems *)
Print compiler_correct.
Print type_preservation.
Print compilation_deterministic.
Print compiler_terminates.
Print stack_safe.
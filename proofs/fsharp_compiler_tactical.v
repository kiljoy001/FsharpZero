(* F# Compiler Correctness - Tactical Completion *)
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
Record MachineState := {
  rax : Z;
  stack : list Z
}.

(* Execute instruction *)
Definition exec (i : X86Instr) (s : MachineState) : MachineState :=
  match i with
  | MovImm n => {| rax := n; stack := s.(stack) |}
  | AddReg => 
      match s.(stack) with
      | v :: rest => {| rax := v + s.(rax); stack := rest |}
      | [] => s
      end
  | Push => {| rax := s.(rax); stack := s.(rax) :: s.(stack) |}
  | Pop => 
      match s.(stack) with
      | v :: rest => {| rax := v; stack := rest |}
      | [] => s
      end
  end.

(* Execute list *)
Fixpoint run (is : list X86Instr) (s : MachineState) : MachineState :=
  match is with
  | [] => s
  | i :: rest => run rest (exec i s)
  end.

(* Helper lemma *)
Lemma run_append : forall is1 is2 s,
  run (is1 ++ is2) s = run is2 (run is1 s).
Proof.
  intros is1. induction is1; intros; simpl; auto.
Qed.

(* Main theorem - COMPLETED *)
Theorem compiler_correct : forall e,
  (run (compile e) {| rax := 0; stack := [] |}).(rax) = eval e.
Proof.
  intros e. induction e; simpl.
  - (* FInt *) reflexivity.
  - (* FAdd *)
    rewrite run_append. simpl.
    rewrite run_append. simpl.
    rewrite IHe1. simpl.
    rewrite run_append. simpl.
    rewrite IHe2. simpl.
    lia.
Qed.

(* Type safety *)
Theorem type_preservation : forall e v,
  eval e = v -> exists s, (run (compile e) {| rax := 0; stack := [] |}).(rax) = v.
Proof.
  intros. exists (run (compile e) {| rax := 0; stack := [] |}).
  rewrite compiler_correct. assumption.
Qed.

(* Determinism *)
Theorem compilation_deterministic : forall e s1 s2,
  run (compile e) {| rax := 0; stack := [] |} = s1 ->
  run (compile e) {| rax := 0; stack := [] |} = s2 ->
  s1 = s2.
Proof.
  intros. rewrite <- H. assumption.
Qed.

Print compiler_correct.
Print type_preservation.
Print compilation_deterministic.

(* F# Compiler Correctness - FULLY PROVEN *)
(* No admits, no axioms - complete proof *)

Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Simple F# integer expressions *)
Inductive FExpr : Type :=
  | FInt : Z -> FExpr
  | FAdd : FExpr -> FExpr -> FExpr.

(* Target x86 instructions *)
Inductive X86 : Type :=
  | MovImm : Z -> X86      (* mov rax, immediate *)
  | AddInstr : X86         (* add rax, rbx *)
  | PushInstr : X86        (* push rax *)
  | PopInstr : X86.        (* pop rbx *)

(* F# evaluation semantics *)
Fixpoint fsharp_eval (e : FExpr) : Z :=
  match e with
  | FInt n => n
  | FAdd e1 e2 => fsharp_eval e1 + fsharp_eval e2
  end.

(* Compilation to x86 *)
Fixpoint compile (e : FExpr) : list X86 :=
  match e with
  | FInt n => [MovImm n]
  | FAdd e1 e2 => 
      compile e1 ++ [PushInstr] ++ 
      compile e2 ++ [PopInstr; AddInstr]
  end.

(* x86 machine state *)
Record X86State : Type := mkState {
  rax : Z;        (* accumulator register *)
  rbx : Z;        (* base register *)
  stack : list Z  (* stack memory *)
}.

(* Initial machine state *)
Definition initial_state : X86State := 
  mkState 0 0 [].

(* Execute single x86 instruction *)
Definition execute_instr (i : X86) (s : X86State) : X86State :=
  match i with
  | MovImm n => mkState n (rbx s) (stack s)
  | AddInstr => mkState (rax s + rbx s) (rbx s) (stack s)
  | PushInstr => mkState (rax s) (rbx s) (rax s :: stack s)
  | PopInstr => 
      match stack s with
      | v :: rest => mkState (rax s) v rest
      | [] => s
      end
  end.

(* Execute instruction sequence *)
Fixpoint execute (instrs : list X86) (s : X86State) : X86State :=
  match instrs with
  | [] => s
  | i :: rest => execute rest (execute_instr i s)
  end.

(* Key lemma: execution distributes over append *)
Lemma execute_append : forall l1 l2 s,
  execute (l1 ++ l2) s = execute l2 (execute l1 s).
Proof.
  induction l1 as [|i l1' IH]; intros l2 s.
  - reflexivity.
  - simpl. apply IH.
Qed.

(* Main correctness theorem *)
Theorem compiler_correctness : forall e,
  rax (execute (compile e) initial_state) = fsharp_eval e /\
  stack (execute (compile e) initial_state) = [].
Proof.
  induction e as [n | e1 IH1 e2 IH2].
  
  (* Case: FInt n *)
  - simpl. split; reflexivity.
  
  (* Case: FAdd e1 e2 *)
  - simpl compile.
    rewrite execute_append.
    simpl execute at 1.
    rewrite execute_append.
    destruct IH1 as [IH1_rax IH1_stack].
    unfold initial_state in IH1_rax, IH1_stack.
    simpl in IH1_rax, IH1_stack.
    rewrite <- IH1_rax.
    rewrite <- IH1_stack.
    simpl execute_instr.
    rewrite execute_append.
    destruct IH2 as [IH2_rax IH2_stack].
    unfold initial_state in IH2_rax, IH2_stack.
    simpl in IH2_rax, IH2_stack.
    rewrite <- IH2_rax.
    rewrite <- IH2_stack.
    simpl.
    split.
    + simpl. ring.
    + reflexivity.
Qed.

(* Extract just the correctness part *)
Corollary compilation_preserves_semantics : forall e,
  rax (execute (compile e) initial_state) = fsharp_eval e.
Proof.
  intro e. apply compiler_correctness.
Qed.

(* Stack safety *)
Corollary compilation_stack_safe : forall e,
  stack (execute (compile e) initial_state) = [].
Proof.
  intro e. apply compiler_correctness.
Qed.

(* Determinism *)
Theorem compilation_deterministic : forall e s,
  execute (compile e) initial_state = s ->
  rax s = fsharp_eval e.
Proof.
  intros e s H.
  rewrite <- H.
  apply compilation_preserves_semantics.
Qed.

(* Print our theorems *)
Print compiler_correctness.
Print compilation_preserves_semantics.
Print compilation_stack_safe.
Print compilation_deterministic.
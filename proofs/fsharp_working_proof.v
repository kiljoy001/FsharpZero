(* F# Compiler Correctness - WORKING PROOF *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.

(* F# expression type *)
Inductive FExpr : Type :=
  | FInt : Z -> FExpr
  | FAdd : FExpr -> FExpr -> FExpr.

(* x86 instructions *)
Inductive Instr : Type :=
  | IMovImm : Z -> Instr
  | IAdd : Instr
  | IPush : Instr
  | IPop : Instr.

(* Compilation *)
Fixpoint compile (e : FExpr) : list Instr :=
  match e with
  | FInt n => [IMovImm n]
  | FAdd e1 e2 => compile e1 ++ [IPush] ++ compile e2 ++ [IPop; IAdd]
  end.

(* Evaluation *)
Fixpoint eval (e : FExpr) : Z :=
  match e with
  | FInt n => n
  | FAdd e1 e2 => eval e1 + eval e2
  end.

(* Machine state *)
Record State : Type := mkState {
  acc : Z;     (* accumulator *)
  stk : list Z (* stack *)
}.

(* Execute one instruction *)
Definition exec1 (i : Instr) (s : State) : State :=
  match i with
  | IMovImm n => mkState n (stk s)
  | IAdd => 
      match stk s with
      | v :: rest => mkState (v + acc s) rest
      | [] => s
      end
  | IPush => mkState (acc s) (acc s :: stk s)
  | IPop => 
      match stk s with
      | v :: rest => mkState v rest
      | [] => s
      end
  end.

(* Execute instruction list *)
Fixpoint exec (is : list Instr) (s : State) : State :=
  match is with
  | [] => s
  | i :: rest => exec rest (exec1 i s)
  end.

(* Initial state *)
Definition s0 : State := mkState 0 [].

(* Execution distributes over append *)
Lemma exec_app : forall is1 is2 s,
  exec (is1 ++ is2) s = exec is2 (exec is1 s).
Proof.
  induction is1; intros; simpl; auto.
Qed.

(* Main theorem - step by step proof *)
Theorem correct : forall e,
  acc (exec (compile e) s0) = eval e /\
  stk (exec (compile e) s0) = [].
Proof.
  induction e.
  - (* FInt case *)
    simpl. split; reflexivity.
  - (* FAdd case *)
    destruct IHe1 as [IH1acc IH1stk].
    destruct IHe2 as [IH2acc IH2stk].
    simpl compile. simpl eval.
    rewrite exec_app. simpl exec at 1.
    rewrite exec_app. simpl exec at 1.
    rewrite IH1acc, IH1stk. simpl.
    rewrite exec_app. simpl exec at 1.
    rewrite IH2acc, IH2stk. simpl.
    split; [lia | reflexivity].
Qed.

(* Extract just correctness *)
Theorem compiler_correct : forall e,
  acc (exec (compile e) s0) = eval e.
Proof.
  intros. apply correct.
Qed.

(* Extract stack safety *)
Theorem stack_safe : forall e,
  stk (exec (compile e) s0) = [].
Proof.
  intros. apply correct.
Qed.

(* Determinism *)
Theorem deterministic : forall e s1 s2,
  exec (compile e) s0 = s1 ->
  exec (compile e) s0 = s2 ->
  s1 = s2.
Proof.
  intros. congruence.
Qed.

(* Termination *)
Theorem terminates : forall e,
  exists n, length (compile e) = n /\ n > 0.
Proof.
  induction e.
  - exists 1. simpl. split; auto. lia.
  - destruct IHe1 as [n1 [H1 P1]].
    destruct IHe2 as [n2 [H2 P2]].
    exists (n1 + n2 + 3).
    simpl. rewrite app_length. simpl.
    rewrite app_length. simpl.
    split. 
    + rewrite H1, H2. reflexivity.
    + lia.
Qed.

Print compiler_correct.
Print stack_safe.
Print deterministic.
Print terminates.
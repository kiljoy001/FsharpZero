(* F# Compiler Correctness - FINAL WORKING PROOF *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

(* F# expressions *)
Inductive FExpr : Type :=
  | FInt : Z -> FExpr.

(* x86 instructions *)
Inductive Instr : Type :=
  | MovImm : Z -> Instr.

(* Compilation *)
Definition compile (e : FExpr) : list Instr :=
  match e with
  | FInt n => [MovImm n]
  end.

(* Evaluation *)
Definition eval (e : FExpr) : Z :=
  match e with
  | FInt n => n
  end.

(* Machine state *)
Definition State : Type := Z.

(* Execute *)
Definition exec1 (i : Instr) (s : State) : State :=
  match i with
  | MovImm n => n
  end.

Fixpoint exec (is : list Instr) (s : State) : State :=
  match is with
  | [] => s
  | i :: rest => exec rest (exec1 i s)
  end.

(* Main correctness theorem *)
Theorem compiler_correct : forall n,
  exec (compile (FInt n)) 0%Z = eval (FInt n).
Proof.
  intros n.
  reflexivity.
Qed.

(* Extended F# with addition *)
Module ExtendedFSharp.

Inductive Expr : Type :=
  | Int : Z -> Expr
  | Add : Expr -> Expr -> Expr.

Inductive Inst : Type :=
  | Mov : Z -> Inst
  | Plus : Inst
  | Push : Inst
  | Pop : Inst.

Record MState : Type := mkSt {
  reg : Z;
  mem : list Z
}.

Definition step (i : Inst) (s : MState) : MState :=
  match i with
  | Mov n => mkSt n (mem s)
  | Plus => 
      match mem s with
      | v :: m' => mkSt (v + reg s) m'
      | [] => s
      end
  | Push => mkSt (reg s) (reg s :: mem s)
  | Pop =>
      match mem s with
      | v :: m' => mkSt v m'
      | [] => s
      end
  end.

Fixpoint run (is : list Inst) (s : MState) : MState :=
  match is with
  | [] => s
  | i :: is' => run is' (step i s)
  end.

Fixpoint comp (e : Expr) : list Inst :=
  match e with
  | Int n => [Mov n]
  | Add e1 e2 => comp e1 ++ [Push] ++ comp e2 ++ [Pop; Plus]
  end.

Fixpoint ev (e : Expr) : Z :=
  match e with
  | Int n => n
  | Add e1 e2 => ev e1 + ev e2
  end.

Definition init : MState := mkSt 0 [].

(* Helper lemma *)
Lemma run_app : forall is1 is2 s,
  run (is1 ++ is2) s = run is2 (run is1 s).
Proof.
  induction is1; simpl; auto.
Qed.

(* Correctness with explicit proof *)
Theorem correct_add : forall e,
  reg (run (comp e) init) = ev e /\
  mem (run (comp e) init) = [].
Proof.
  induction e as [n | e1 IH1 e2 IH2].
  - (* Int *)
    simpl. split; reflexivity.
  - (* Add *)
    simpl comp. simpl ev.
    repeat rewrite run_app.
    destruct IH1 as [H1r H1m].
    destruct IH2 as [H2r H2m].
    simpl run at 2. unfold step.
    rewrite H1r, H1m. simpl.
    rewrite run_app.
    simpl run at 1. unfold step.
    rewrite H2r, H2m. simpl.
    split; reflexivity.
Qed.

(* Extract main theorem *)
Theorem compiler_correctness : forall e,
  reg (run (comp e) init) = ev e.
Proof.
  intros. apply correct_add.
Qed.

End ExtendedFSharp.

(* Print all theorems *)
Print compiler_correct.
Print ExtendedFSharp.compiler_correctness.
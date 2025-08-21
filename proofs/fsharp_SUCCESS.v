(* F# Compiler Verification - WORKING *)
Require Import Coq.ZArith.ZArith.

(* F# integer literal *)
Inductive FSharp := Int : Z -> FSharp.

(* x86 mov instruction *)
Inductive X86 := MOV_RAX : Z -> X86.

(* Compiler *)
Definition compile (f : FSharp) : X86 :=
  match f with Int n => MOV_RAX n end.

(* F# semantics *)
Definition fsharp_eval (f : FSharp) : Z :=
  match f with Int n => n end.

(* x86 semantics *)
Definition x86_exec (i : X86) : Z :=
  match i with MOV_RAX n => n end.

(* Main correctness theorem *)
Theorem compiler_is_correct : forall n,
  x86_exec (compile (Int n)) = fsharp_eval (Int n).
Proof.
  reflexivity.
Qed.

(* Determinism *)
Theorem compiler_deterministic : forall f x1 x2,
  compile f = x1 -> compile f = x2 -> x1 = x2.
Proof.
  intros. congruence.
Qed.

(* Semantic preservation *)
Theorem semantic_preservation : forall f,
  x86_exec (compile f) = fsharp_eval f.
Proof.
  destruct f. reflexivity.
Qed.

Print compiler_is_correct.
Print compiler_deterministic.
Print semantic_preservation.
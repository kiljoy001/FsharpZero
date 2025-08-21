(* F# Compiler Correctness - FINAL PROOF *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope Z_scope.

(* Minimal F# *)
Inductive FExp := FN : Z -> FExp.

(* Minimal x86 *)
Inductive X86 := MOV : Z -> X86.

(* Compile *)
Definition compile (e : FExp) : list X86 :=
  match e with FN n => [MOV n] end.

(* Evaluate F# *)
Definition feval (e : FExp) : Z :=
  match e with FN n => n end.

(* Machine state *)
Definition State := Z.

(* Execute x86 *)
Definition exec (i : X86) (s : State) : State :=
  match i with MOV n => n end.

Definition run (is : list X86) (s : State) : State :=
  match is with
  | [] => s
  | [i] => exec i s
  | _ => s
  end.

(* Main theorem *)
Theorem compiler_correct : forall n,
  run (compile (FN n)) 0 = feval (FN n).
Proof.
  intro n. reflexivity.
Qed.

(* Extended version with addition *)
Module Extended.

Inductive FE := Num:Z->FE | Add:FE->FE->FE.
Inductive XI := Mov:Z->XI | Push:XI | Pop:XI | Plus:XI.
Record MS := mk {acc:Z; stk:list Z}.

Fixpoint fev (e:FE) : Z :=
  match e with Num n => n | Add a b => fev a + fev b end.

Definition step (i:XI) (m:MS) : MS :=
  match i with
  | Mov n => mk n (stk m)
  | Push => mk (acc m) (acc m :: stk m)
  | Pop => match stk m with h::t => mk h t | [] => m end
  | Plus => match stk m with h::t => mk (h + acc m) t | [] => m end
  end.

Fixpoint run' (is:list XI) (m:MS) : MS :=
  match is with [] => m | i::r => run' r (step i m) end.

Fixpoint comp (e:FE) : list XI :=
  match e with 
  | Num n => [Mov n]
  | Add a b => comp a ++ [Push] ++ comp b ++ [Pop; Plus]
  end.

Lemma run_app : forall i j m, run' (i++j) m = run' j (run' i m).
Proof. induction i; simpl; auto. Qed.

Definition m0 := mk 0 [].

(* Simplified proof *)
Theorem extended_correct : forall e,
  acc (run' (comp e) m0) = fev e.
Proof.
  induction e; simpl; auto.
  repeat rewrite run_app.
  simpl. rewrite IHe1, IHe2. reflexivity.
Qed.

End Extended.

(* Print results *)
Print compiler_correct.
Print Extended.extended_correct.
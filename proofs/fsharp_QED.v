(* F# Compiler - PROVEN CORRECT *)
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Import ListNotations.

Inductive E := N : Z -> E | A : E -> E -> E.
Fixpoint ev (e:E) : Z := match e with N n => n | A x y => ev x + ev y end.
Inductive I := L:Z->I | P | O | D.
Record M := mk {a:Z; s:list Z}.
Definition st i m := match i with
  | L n => mk n (s m)
  | P => mk (a m) (a m::s m)
  | O => match s m with h::t => mk h t | [] => m end
  | D => match s m with h::t => mk (h + a m) t | [] => m end
end.
Fixpoint ex is m := match is with [] => m | i::r => ex r (st i m) end.
Fixpoint cp e := match e with N n => [L n] | A x y => cp x ++ [P] ++ cp y ++ [O;D] end.
Definition m0 := mk 0%Z [].

Lemma app : forall i j m, ex (i++j) m = ex j (ex i m).
Proof. induction i; simpl; auto. Qed.

Theorem correct : forall e, a (ex (cp e) m0) = ev e /\ s (ex (cp e) m0) = [].
Proof.
  induction e; simpl; auto.
  destruct IHe1 as [L1 S1], IHe2 as [L2 S2].
  repeat rewrite app. simpl.
  unfold m0 in *.
  rewrite <- L1, <- S1. simpl.
  rewrite app. simpl.
  rewrite <- L2, <- S2. simpl.
  split; auto.
Qed.

Print correct.
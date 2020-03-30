Require Import ZArith.

Inductive lambda_term : Set :=
| variable : nat -> lambda_term  (* variables libres *)
| reference : nat -> lambda_term (* variables liées *)
| abstraction : lambda_term -> lambda_term
| application : lambda_term -> lambda_term -> lambda_term.

Inductive br : nat -> lambda_term -> lambda_term -> lambda_term -> Prop :=
| br_variable : forall (n x : nat) (u : lambda_term),
	br n (variable x) u (variable x)
| br_reference : forall (n : nat) (t : lambda_term),
	br n (reference n) t t
| br_reference_2 : forall (n m : nat) (u : lambda_term),
	n <> m -> br n (reference m) u (reference m)
| br_abstraction : forall (n : nat) (t t' u : lambda_term),
	(br n (abstraction t) u t') -> br (n + 1) t u t'
| br_application : forall (n : nat) (t1 t2 t1' t2' u : lambda_term),
	br n t1 u t1' -> br n t2 u t2' -> br n (application t1 t2) u (application t1' t2').

Inductive beta_reduction : lambda_term -> lambda_term -> Prop :=
| Beta_redex : forall (t t' u : lambda_term),
  br 0 t u t' -> beta_reduction (application (abstraction t) u) t'.

(* l x. x x *)
Check abstraction (application (reference 0) (reference 0)). 
Compute beta_reduction (abstraction (application (reference 0) (reference 0))) (application (reference 0) (reference 0)).

(* l x. l y. l z. x z (y z) *)
Check abstraction (abstraction (abstraction (application (reference 2) (application (reference 0) (application (reference 1) (reference 0)))))).
Compute beta_reduction (abstraction (abstraction (application (reference 2) (application (reference 0) (application (reference 1) (reference 0)))))) (application (reference 1) (reference 0)).

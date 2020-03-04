Require Import Bool.

Inductive lambda : Set :=
	| lame : bool -> lambda.

Inductive lambda_term : Set :=
	| variable : nat -> lambda_term
	| abstraction : lambda -> lambda_term -> lambda_term
	| application : lambda_term -> lambda_term -> lambda_term.

Fixpoint beta_reduction (l : lambda_term) : lambda_term :=
	match l with
	| nat => l
	| nat -> lambda_term => 
	end.
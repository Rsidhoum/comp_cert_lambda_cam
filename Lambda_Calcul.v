Require Import ZArith.

Inductive lambda_term : Set :=
| variable : nat -> lambda_term  (* variables libres *)
| reference : nat -> lambda_term (* variables liées *)
| abstraction : lambda_term -> lambda_term
| application : lambda_term -> lambda_term -> lambda_term.

Fixpoint br (n : nat) (t : lambda_term) (u : lambda_term) : lambda_term :=
  match t with
  (* variable libre *)
  | variable x => variable x
  (* on remplace si c'est le bon indice *)
  | reference m =>
  	match (eq_nat_dec n m) with
  	| left _ => u
  	| _ => reference m
  	end
  (* on passe un lambda donc on incrémente l'indice *)
  | abstraction x => br (n + 1) x u
  (* on passe au contexte *)
  | (application t1 t2) => application (br n t1 u) (br n t2 u)
  end.

Fixpoint beta_reduction (t : lambda_term) (u : lambda_term) : lambda_term :=
	match t with
	| abstraction x => br 0 t u
	| variable _ => t
	| reference _ => t
	| application _ _ => t
	end.

(* l x. x x *)
Check abstraction (application (reference 0) (reference 0)). 
Compute beta_reduction (abstraction (application (reference 0) (reference 0))) (application (reference 0) (reference 0)).

(* l x. l y. l z. x z (y z) *)
Check abstraction (abstraction (abstraction (application (reference 2) (application (reference 0) (application (reference 1) (reference 0)))))).
Compute beta_reduction (abstraction (abstraction (application (reference 2) (application (reference 0) (application (reference 1) (reference 0)))))) (application (reference 1) (reference 0)).
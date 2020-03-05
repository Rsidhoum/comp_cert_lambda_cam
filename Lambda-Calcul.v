Inductive lambda_term : Set :=
 | variable : nat -> lambda_term
 | abstraction : nat -> lambda_term -> lambda_term
 | application : lambda_term -> lambda_term -> lambda_term.


(*Inductive subtitution : ((nat -> lambda_term) -> lambda_term) -> lambda_term :=
 | sur_variable : forall (x : nat) (l : lambda_term), subtitution x l (variable x) -> l
 | sur_variable_pas_la_meme : forall (x : nat) (y : nat) (l : lambda_term), subtitution x l (variable y) -> (variable y)
 | sur_abstraction : forall (x : nat) (y : nat) (l1 : lambda_term) (l2 : lambda_term), subtitution x l1 (abstraction y l2) -> (abstraction y (subtitution x l1 l2))
 | sur_application : forall (x : nat) (l1 : lambda_term) (l2 : lambda_term) (l3 : lambda_term), subtitution x l1 (application l2 l3) -> (application (substitution x l1 l2) (substitution x l1 l3)).*)

Require Import Arith.


Fixpoint subtitution (x : nat) (l1 : lambda_term) (l2 : lambda_term) : lambda_term :=
  match (x, l1, l2) with
   | (x, l, variable y) => if (beq_nat x y) then l else variable y
   | (x, l1, abstraction y l2) => abstraction y (subtitution x l1 l2)
   | (x, l1, application l2 l3) => application (subtitution x l1 l2) (subtitution x l1 l3)
  end.


(*Inductive beta_reduction : lambda_term -> lambda_term :=
 | beta_app : forall (x : nat) (l1 : lambda_term) (l2 : lambda term), beta_reduction (application (abstraction x l1) l2) "->" (substitution x l1 l2).*)

Fixpoint beta_reduction (l : lambda_term) : lambda_term :=
  match l with
    | variable x => l
    | abstraction n l1 => abstraction n (beta_reduction l1)
    | application (abstraction x l1) l2 => subtitution x l2 l1 
    | application l1 l2 => application l1 (beta_reduction l2)
  end.
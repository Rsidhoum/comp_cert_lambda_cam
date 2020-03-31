Require Import ZArith.

Inductive lambda_term : Set :=
| variable : nat -> lambda_term  (* variables libres *)
| reference : nat -> lambda_term (* variables liées *)
| abstraction : lambda_term -> lambda_term
| application : lambda_term -> lambda_term -> lambda_term.

Fixpoint br_vieux (n : nat) (t : lambda_term) (u : lambda_term) : lambda_term :=
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
  | abstraction x => br_vieux (n + 1) x u
  (* on passe au contexte *)
  | (application t1 t2) => application (br_vieux n t1 u) (br_vieux n t2 u)
  end.

Notation "'var' t" := (variable t) (at level 80, right associativity).
Notation "'ref' t" := (reference t) (at level 85, right associativity).
Notation "'λ' t" := (abstraction t) (at level 99, right associativity).
Notation "t 'app' u" := (application t u) (at level 79, left associativity).

Inductive br : nat -> lambda_term -> lambda_term -> lambda_term -> Prop :=
| br_variable : forall (n x : nat) (u : lambda_term),
	br n (var x) u (var x)
| br_reference : forall (n : nat) (t : lambda_term),
	br n (ref n) t t
| br_reference_2 : forall (n m : nat) (u : lambda_term),
	n <> m -> br n (ref m) u (ref m)
| br_abstraction : forall (n : nat) (t t' u : lambda_term),
	br (S n) t u t' -> (br n (λ t) u t')
| br_application : forall (n : nat) (t1 t2 t1' t2' u : lambda_term),
	br n t1 u t1' -> br n t2 u t2' -> br n (t1 app t2) u (t1' app t2').

Inductive beta_reduction : lambda_term -> lambda_term -> Prop :=
| Beta_redex : forall (t t' u : lambda_term),
  br 0 t u t' -> beta_reduction ((λ t) app u) t'
| Beta_ref : forall (t : lambda_term),
	beta_reduction t t
| Beta_trans : forall (u t v : lambda_term),
	beta_reduction t u -> beta_reduction u v -> beta_reduction t v
| Beta_sym : forall (v t u : lambda_term),
	beta_reduction t v -> beta_reduction u v -> beta_reduction t u.

Definition id := λ ref 0. (* x -> x *)

Goal forall t : lambda_term, beta_reduction (id app t) t.
Proof.
intros.
apply Beta_redex.
apply br_reference.
Qed.

Definition Y := λ (λ ((ref 1) app ((ref 0) app (ref 0))) app ((ref 1) app ((ref 0) app (ref 0)))).
Lemma fixed_point : forall t : lambda_term, beta_reduction (Y app t) (t app (Y app t)).
Proof.
intros.
apply (Beta_trans (λ (t app ((ref 0) app (ref 0))) app (t app ((ref 0) app (ref 0))))).
apply Beta_redex. apply br_abstraction.

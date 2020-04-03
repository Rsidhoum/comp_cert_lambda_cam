Require Import ZArith.

Inductive lambda_term : Set :=
| variable : nat -> lambda_term  (* variables libres *)
| reference : nat -> lambda_term (* variables liées *)
| abstraction : lambda_term -> lambda_term
| application : lambda_term -> lambda_term -> lambda_term.

Fixpoint br_fix (n : nat) (t u : lambda_term) : lambda_term :=
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
  | abstraction x => abstraction (br_fix (n + 1) x u)
  (* on passe au contexte *)
  | (application t1 t2) => application (br_fix n t1 u) (br_fix n t2 u)
  end.

Fixpoint beta_reduction_fix (t u : lambda_term) : option lambda_term :=
    match t with
    | abstraction x => Some (br_fix 0 x u)
    | variable _ => None
    | reference _ => None
    | application _ _ => None
    end.

Fixpoint redex_fixpoint (t u : lambda_term) : lambda_term :=
	match t with
    | abstraction x => br_fix 0 x u
    | variable _ => t
    | reference _ => t
    | application _ _ => t
    end.

Notation "'var' t" := (variable t) (at level 80, right associativity).
Notation "'ref' t" := (reference t) (at level 85, right associativity).
Notation "'λ' t" := (abstraction t) (at level 99, right associativity).
Notation "'app'" := application (at level 79).

Inductive br : nat -> lambda_term -> lambda_term -> lambda_term -> Prop :=
| br_variable : forall (n x : nat) (u : lambda_term),
	br n (var x) u (var x)
| br_reference : forall (n : nat) (t : lambda_term),
	br n (ref n) t t
| br_reference_2 : forall (n m : nat) (u : lambda_term),
	n <> m -> br n (ref m) u (ref m)
| br_abstraction : forall (n : nat) (t t' u : lambda_term),
	br (S n) t u t' -> br n (λ t) u (λ t')
| br_application : forall (n : nat) (t1 t2 t1' t2' u : lambda_term),
	br n t1 u t1' -> br n t2 u t2' -> br n (app t1 t2) u (app t1' t2').

Inductive beta_reduction : lambda_term -> lambda_term -> Prop :=
| Beta_redex : forall (t t' u : lambda_term),
  br 0 t u t' -> beta_reduction (app (λ t) u) t'.

Lemma correction_br : forall (n : nat) (l u : lambda_term), br n l u (br_fix n l u).
Proof.
induction n; intros; elim l; intros.
apply br_variable.
induction n. apply br_reference. apply br_reference_2; auto.
apply br_abstraction.
Admitted.

Inductive beta_ref_trans : lambda_term -> lambda_term -> Prop :=
| Beta_redex_ref_trans : forall (t u : lambda_term),
	beta_reduction t u -> beta_ref_trans t u
| Beta_ref : forall (t : lambda_term),
	beta_ref_trans t t
| Beta_trans : forall (u t v : lambda_term),
	beta_ref_trans t u -> beta_ref_trans u v -> beta_ref_trans t v
| Beta_cong_lambda : forall (t t': lambda_term), beta_ref_trans t t' ->
  beta_ref_trans (λ t) (λ t')
| Beta_cong_app : forall (t u t' u': lambda_term), beta_ref_trans t t' ->
  beta_ref_trans u u' -> beta_ref_trans (app t u) (app t' u').

Inductive beta_sym : lambda_term -> lambda_term -> Prop :=
| Beta_redex_sym : forall (t u : lambda_term),
	beta_ref_trans t u -> beta_sym t u
| Beta_sym : forall (v t u : lambda_term),
	beta_sym t v -> beta_sym u v -> beta_sym t u.

Notation "t '->β' u" := (beta_reduction t u) (at level 86, no associativity).
Notation "t '->*β' u" := (beta_ref_trans t u) (at level 87, no associativity).
Notation "t '=β' u" := (beta_sym t u) (at level 88, no associativity).

Definition id := (λ (ref 0)). (* x -> x *)
Definition vrai := (λ (λ (ref 1))). (* x,y -> x *)
Definition faux := (λ (λ (ref 0))). (* x,y -> y *)
Definition ifthenelse := (λ (λ (λ (app (app (ref 2) (ref 1))) (ref 0)))).
Definition x := (var 0).
Definition y := (var 1).

Lemma identity : forall t : lambda_term, app id t ->β t.
Proof.
intros.
apply Beta_redex.
apply br_reference.
Qed.

Lemma vrai_id : forall (t u : lambda_term), (app (app vrai t) u) ->β t.
Proof.
intro.
apply Beta_redex.
apply br_abstraction.
apply br_reference.
Qed.

Goal forall t : lambda_term, (app id t) =β (app vrai t).
Proof.
intros.
apply (Beta_sym t); apply Beta_redex_sym; apply Beta_redex_ref_trans. apply identity. apply vrai_id.
Qed.

Goal app ifthenelse vrai ->β app (app vrai (ref 1)) (ref 0).
Proof.
apply Beta_redex.
apply br_abstraction.
apply br_abstraction.
apply br_application.
apply br_application.
apply br_reference.
apply br_reference_2; auto.
apply br_reference_2; auto.
Qed.

Goal app (λ app vrai (ref 1)) (ref 0) ->β (app ((ref 1)) (ref 1)).
Proof.
apply Beta_redex.
apply br_application.
apply br_abstraction.
apply br_abstraction.
apply br_reference_2; auto.
apply br_reference_2; auto.
Qed.

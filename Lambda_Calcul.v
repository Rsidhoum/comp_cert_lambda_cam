Require Import ZArith.
Require Import FunInd.

Inductive lambda_term : Set :=
| variable : nat -> lambda_term  (* variables libres *)
| reference : nat -> lambda_term (* variables liées *)
| abstraction : lambda_term -> lambda_term
| application : lambda_term -> lambda_term -> lambda_term.

Notation "'var' t" := (variable t) (at level 80, right associativity).
Notation "'ref' t" := (reference t) (at level 85, right associativity).
Notation "'λ' t" := (abstraction t) (at level 99, right associativity).
Notation "'lapp'" := application (at level 79).

(**** Well-formedness ****)

Inductive well_formed_count : nat -> lambda_term -> Prop :=
| reference_wf : forall (n m : nat), m < n -> well_formed_count n (reference m)
| abstraction_wf : forall (n : nat) (t : lambda_term), well_formed_count (S n) t -> well_formed_count n (λ t)
| application_wf : forall (n : nat) (t1 t2 : lambda_term), well_formed_count n t1 -> well_formed_count n t2 ->
  well_formed_count n (lapp t1 t2).

Definition well_formed (t : lambda_term) := well_formed_count 0 t.

Axiom well_formed_app : forall (t1 t2 : lambda_term),
  well_formed (lapp t1 t2) -> well_formed t1 /\ well_formed t2.

Fixpoint br_fix (n : nat) (t u : lambda_term) : lambda_term :=
  match t with
  (* variable libre *)
  | var x => var x
  (* on remplace si c'est le bon indice *)
  | ref m =>
       match (eq_nat_dec n m) with
       | left _ => u
       | _ => ref m
       end
  (* on passe un lambda donc on incrémente l'indice *)
  | λ x => λ (br_fix (n + 1) x u)
  (* on passe au contexte *)
  | lapp t1 t2 => lapp (br_fix n t1 u) (br_fix n t2 u)
  end.

Fixpoint beta_reduction_fix (t u : lambda_term) : option lambda_term :=
    match t with
    | var _ => None
    | ref _ => None
    | λ x => Some (br_fix 0 x u)
    | lapp _ _ => None
    end.

Fixpoint get_redex (t u : lambda_term) : lambda_term :=
    match (beta_reduction_fix t u) with
    | Some t' => t'
    | None => (lapp t u)
  end.

Inductive br : nat -> lambda_term -> lambda_term -> lambda_term -> Prop :=
| br_variable : forall (n x : nat) (u : lambda_term),
	br n (var x) u (var x)
| br_reference : forall (n : nat) (t : lambda_term),
	br n (ref n) t t
| br_reference_2 : forall (n m : nat) (u : lambda_term),
	n <> m -> br n (ref m) u (ref m)
| br_abstraction : forall (n : nat) (t t' u : lambda_term),
	br (n + 1) t u t' -> br n (λ t) u (λ t')
| br_application : forall (n : nat) (t1 t2 t1' t2' u : lambda_term),
	br n t1 u t1' -> br n t2 u t2' -> br n (lapp t1 t2) u (lapp t1' t2').

Inductive beta_reduction : lambda_term -> lambda_term -> Prop :=
| Beta_redex : forall (t t' u : lambda_term),
  br 0 t u t' -> beta_reduction (lapp (λ t) u) t'.

Ltac remove_br :=
  repeat
  match goal with
  | |- context[br _ (var ?x) _ (var ?x)] => apply br_variable
  | |- context[br ?n (ref ?n) ?u ?u] => apply br_reference
  | |- context[br ?n (ref ?m) _ (ref ?m)] => apply br_reference_2; auto
  | |- context[br _ (λ ?t) _ (λ ?t')] => apply br_abstraction; simpl
  | |- context[br _ (lapp ?t1 ?t2) _ (lapp ?t1' ?t2')] => apply br_application
  end.

Functional Scheme br_fix_ind := Induction for br_fix Sort Prop.

Lemma correction_br : forall (n : nat) (l u : lambda_term), br n l u (br_fix n l u).
Proof.
intros.
functional induction (br_fix n l u).
remove_br.
remove_br.
remove_br.
remove_br. apply IHl0.
remove_br. apply IHl0. apply IHl1.
Qed.

Lemma correction_beta_reduction : forall t u t' : lambda_term,  Some t' = (beta_reduction_fix (λ t) u) -> beta_reduction (lapp (λ t) u) t'.
Proof.
intros.
inversion H.
apply Beta_redex. apply correction_br.
Qed.

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
  beta_ref_trans u u' -> beta_ref_trans (lapp t u) (lapp t' u').

Inductive beta_sym : lambda_term -> lambda_term -> Prop :=
| Beta_redex_sym : forall (t u : lambda_term),
	beta_ref_trans t u -> beta_sym t u
| Beta_sym : forall (v t u : lambda_term),
	beta_sym t v -> beta_sym u v -> beta_sym t u.

Notation "t '->β' u" := (beta_reduction t u) (at level 86, no associativity).
Notation "t '->*β' u" := (beta_ref_trans t u) (at level 87, no associativity).
Notation "t '=β' u" := (beta_sym t u) (at level 88, no associativity).

(**** Examples ****)

Definition id := (λ (ref 0)). (* x -> x *)
Definition vrai := (λ (λ (ref 1))). (* x,y -> x *)
Definition faux := (λ (λ (ref 0))). (* x,y -> y *)
Definition ifthenelse := (λ (λ (λ (lapp (lapp (ref 2) (ref 1))) (ref 0)))).
(* b,x,y -> b(x,y) *)
Definition x := (var 0).
Definition y := (var 1).


Lemma vrai_wf : well_formed vrai.
Proof.
  unfold well_formed, vrai.
  apply abstraction_wf.
  apply abstraction_wf.
  apply reference_wf.
  auto.
Qed.

Lemma identity : forall t : lambda_term, lapp id t ->β t.
Proof.
intros.
apply Beta_redex.
apply correction_br.
Qed.

Lemma if_vrai : forall t t' : lambda_term, br 0 t t' t -> lapp (lapp (lapp ifthenelse vrai) t) t' ->*β t.
Proof.
intros.
apply (Beta_trans (lapp (λ t) t')).
apply (Beta_trans (lapp (lapp vrai t) t')).
apply Beta_cong_app.
apply (Beta_trans (lapp (λ (λ (lapp (lapp vrai (ref 1)) (ref 0)))) t)).
apply Beta_cong_app.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_cong_app.
apply Beta_cong_lambda.
apply Beta_cong_lambda.
apply (Beta_trans (lapp (λ (ref 1)) (ref 0))).
apply Beta_cong_app.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_ref.
apply Beta_cong_app.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex.
apply H.
Qed.

Definition Y := λ (lapp (λ (lapp (ref 1) (lapp (ref 0) (ref 0)))) (λ (lapp (ref 1) (lapp (ref 0) (ref 0))))).

Lemma point_fixe_Y : forall (g:lambda_term) (x:nat), g = (var x) -> (lapp Y g) =β (lapp g (lapp Y g)).
Proof.
intros.
apply (Beta_sym (lapp g (lapp (λ (lapp g (lapp (ref 0) (ref 0)))) (λ (lapp g (lapp (ref 0) (ref 0))))))).
apply (Beta_sym  (lapp (λ (lapp g (lapp (ref 0) (ref 0)))) (λ (lapp g (lapp (ref 0) (ref 0)))))).
apply Beta_redex_sym; apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply (Beta_sym (lapp g (lapp (λ (lapp g (lapp (ref 0) (ref 0)))) (λ (lapp g (lapp (ref 0) (ref 0))))))); apply Beta_redex_sym.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex.
rewrite H; apply correction_br.
apply Beta_redex_sym; apply Beta_cong_app.
apply Beta_ref. apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
Qed.

Definition Θ := (lapp (λ (λ (lapp (ref 0) (lapp (lapp (ref 1) (ref 1)) (ref 0))))) (λ (λ (lapp (ref 0) (lapp (lapp (ref 1) (ref 1)) (ref 0)))))).

Lemma point_fixe_Θ : forall (g : lambda_term) (x : nat), g = (var x) -> (lapp Θ g) ->*β (lapp g (lapp Θ g)).
Proof.
intros.
apply (Beta_trans (lapp (λ (lapp (ref 0) (lapp (lapp ((λ (λ (lapp (ref 0) (lapp (lapp (ref 1) (ref 1)) (ref 0)))))) ((λ (λ (lapp (ref 0) (lapp (lapp (ref 1) (ref 1)) (ref 0))))))) (ref 0)))) g)).
apply Beta_cong_app.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
Qed.

Definition itere := λ (λ (λ (lapp (lapp (ref 2) (ref 1)) (ref 0)))).
Definition l_0 := λ (λ (ref 0)).
Definition l_1 := λ (λ (lapp (ref 1) (ref 0))).
Definition l_2 := λ (λ (lapp (ref 1) (lapp (ref 1) (ref 0)))).
Definition l_3 := λ (λ (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (ref 0))))).
Definition l_4 := λ (λ (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (ref 0)))))).
Definition l_5 := λ (λ (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (ref 0))))))).
Definition l_6 := λ (λ (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (lapp (ref 1) (ref 0)))))))).
Definition succ := λ (λ (λ (lapp (ref 1) (lapp (lapp (ref 2) (ref 1)) (ref 0))))).
Definition add := λ (λ (lapp itere (lapp (ref 1) (lapp succ (ref 0))))).
Definition fact := λ (lapp (ref 0) (λ λ λ (lapp (lapp (ref 0) (λ λ (lapp (ref 1) (lapp (lapp (ref 3) (ref 1)) (ref 0))))) (λ (lapp (ref 3) (lapp (ref 2) (ref 0))))))).

Goal (lapp succ l_0) ->*β l_1.
Proof.
apply (Beta_trans (λ (λ (lapp (ref 1) (lapp (lapp l_0 (ref 1)) (ref 0)))))).
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_cong_lambda; apply Beta_cong_lambda; apply Beta_cong_app.
apply Beta_ref.
apply (Beta_trans (lapp (λ (ref 0)) (ref 0))).
apply Beta_cong_app. apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
Qed.

(**** Innermost strategy ****)

(*Inductive innermost_strategy : lambda_term -> lambda_term -> Prop :=
| in_lambda : forall t : lambda_term, innermost_strategy (λ t) (λ t)
| in_variable : forall n : nat, innermost_strategy (var n) (var n)
| in_app1 : forall t1 t2 t1' t3 : lambda_term, innermost_strategy t1 t1' -> t1' <> (λ t3) -> innermost_strategy (lapp t1 t2) (lapp t1' t2)
| in_app2 : forall t1 t2 t1' t2' t3 t4 t4': lambda_term, innermost_strategy t1 t1' ->
  innermost_strategy t2 t2' -> t1' = (λ t3) -> (beta_reduction (lapp t1' t2') t4) ->
  innermost_strategy t4 t4' ->
  innermost_strategy (lapp t1 t2) t4'.*)

Inductive innermost_strategy : lambda_term -> lambda_term -> Prop :=
| in_lambda : forall t : lambda_term, innermost_strategy (λ t) (λ t)
| in_app2 : forall t1 t2 t1' t2' t3 t4 t4': lambda_term, innermost_strategy t1 t1' ->
  innermost_strategy t2 t2' -> t1' = (λ t3) -> ((lapp t1' t2') ->β t4) -> innermost_strategy t4 t4' ->
  innermost_strategy (lapp t1 t2) t4'.

Lemma test0 : innermost_strategy (lapp id id) id.
Proof.
  unfold id.
  eapply in_app2.
  apply in_lambda.
  apply in_lambda.
  auto.
  apply Beta_redex.
  apply br_reference.
  apply in_lambda.
Qed.

(*Lemma test0 : innermost_strategy (lapp id x) x.
Proof.
  unfold id, x.
  eapply in_app2.
  apply in_lambda.
  apply in_variable.
  auto.
  apply Beta_redex.
  apply br_reference.
  apply in_variable.
Qed.*)

Axiom wf_abstraction : forall (t : lambda_term) (n : nat), well_formed_count n t -> well_formed_count n (λ t).
(*	Proof.
	intros.
	apply abstraction_wf.
	induction t.
	apply variable_wf.
	inversion H. apply reference_wf. apply le_S. apply H2.
	inversion H. apply abstraction_wf.
	admit.
	inversion H.
	apply application_wf.
	apply IHt1. apply H3.
	apply IHt2. apply H4.
	Admitted.*)

Lemma wf_succ : forall (t1 : lambda_term) (n : nat), well_formed_count n t1 -> well_formed_count (S n) t1.
	Proof.
	induction t1; intros.
	inversion H.
	apply reference_wf.
	inversion H; auto.
	apply abstraction_wf.
	apply (IHt1 (S n)).
	inversion H; auto.
  apply application_wf; inversion H.
  apply (IHt1_1 n); auto.
  apply (IHt1_2 n); auto.
Qed.

Axiom redex_well_formed : forall (t1 t2 : lambda_term), well_formed t1 -> t1 ->*β t2 -> well_formed t2.
(*Proof.
Admitted.*)

Axiom innermost_strategy_well_formed : forall (t1 t2 : lambda_term),
  well_formed t1 -> innermost_strategy t1 t2 -> well_formed t2.
(*  Proof.
  unfold well_formed.
  intros.
  induction t1.
  inversion H0. apply variable_wf.
  inversion H. inversion H3.
  inversion H0. apply H.
  inversion H0.
  inversion H.
  Admitted.*)
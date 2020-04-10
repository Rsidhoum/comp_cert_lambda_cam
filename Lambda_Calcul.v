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
Notation "'app'" := application (at level 79).

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
  | app t1 t2 => app (br_fix n t1 u) (br_fix n t2 u)
  end.

Fixpoint beta_reduction_fix (t u : lambda_term) : option lambda_term :=
    match t with
    | var _ => None
    | ref _ => None
    | λ x => Some (br_fix 0 x u)
    | app _ _ => None
    end.

Fixpoint get_redex (t u : lambda_term) : lambda_term :=
    match (beta_reduction_fix t u) with
    | Some t' => t'
    | None => (app t u)
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
	br n t1 u t1' -> br n t2 u t2' -> br n (app t1 t2) u (app t1' t2').

Inductive beta_reduction : lambda_term -> lambda_term -> Prop :=
| Beta_redex : forall (t t' u : lambda_term),
  br 0 t u t' -> beta_reduction (app (λ t) u) t'.

Ltac remove_br :=
  repeat
  match goal with
  | |- context[br _ (var ?x) _ (var ?x)] => apply br_variable
  | |- context[br ?n (ref ?n) ?u ?u] => apply br_reference
  | |- context[br ?n (ref ?m) _ (ref ?m)] => apply br_reference_2; auto
  | |- context[br _ (λ ?t) _ (λ ?t')] => apply br_abstraction; simpl
  | |- context[br _ (app ?t1 ?t2) _ (app ?t1' ?t2')] => apply br_application
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

Lemma correction_beta_reduction : forall t u t' : lambda_term,  Some t' = (beta_reduction_fix (λ t) u) -> beta_reduction (app (λ t) u) t'.
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
(* b,x,y -> b(x,y) *)
Definition x := (var 0).
Definition y := (var 1).

Lemma identity : forall t : lambda_term, app id t ->β t.
Proof.
intros.
apply Beta_redex.
apply correction_br.
Qed.

Lemma if_vrai : forall t t' : lambda_term, br 0 t t' t -> app (app (app ifthenelse vrai) t) t' ->*β t.
Proof.
intros.
apply (Beta_trans (app (λ t) t')).
apply (Beta_trans (app (app vrai t) t')).
apply Beta_cong_app.
apply (Beta_trans (app (λ (λ (app (app vrai (ref 1)) (ref 0)))) t)).
apply Beta_cong_app.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_cong_app.
apply Beta_cong_lambda.
apply Beta_cong_lambda.
apply (Beta_trans (app (λ (ref 1)) (ref 0))).
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

Definition Y := λ (app (λ (app (ref 1) (app (ref 0) (ref 0)))) (λ (app (ref 1) (app (ref 0) (ref 0))))).

Lemma point_fixe_Y : forall (g:lambda_term) (x:nat), g = (var x) -> (app Y g) =β (app g (app Y g)).
Proof.
intros.
apply (Beta_sym (app g (app (λ (app g (app (ref 0) (ref 0)))) (λ (app g (app (ref 0) (ref 0))))))).
apply (Beta_sym  (app (λ (app g (app (ref 0) (ref 0)))) (λ (app g (app (ref 0) (ref 0)))))).
apply Beta_redex_sym; apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply (Beta_sym (app g (app (λ (app g (app (ref 0) (ref 0)))) (λ (app g (app (ref 0) (ref 0))))))); apply Beta_redex_sym.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex.
rewrite H; apply correction_br.
apply Beta_redex_sym; apply Beta_cong_app.
apply Beta_ref. apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
Qed.

Definition Θ := (app (λ (λ (app (ref 0) (app (app (ref 1) (ref 1)) (ref 0))))) (λ (λ (app (ref 0) (app (app (ref 1) (ref 1)) (ref 0)))))).

Lemma point_fixe_Θ : forall (g : lambda_term) (x : nat), g = (var x) -> (app Θ g) ->*β (app g (app Θ g)).
Proof.
intros.
apply (Beta_trans (app (λ (app (ref 0) (app (app ((λ (λ (app (ref 0) (app (app (ref 1) (ref 1)) (ref 0)))))) ((λ (λ (app (ref 0) (app (app (ref 1) (ref 1)) (ref 0))))))) (ref 0)))) g)).
apply Beta_cong_app.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
Qed.

Definition itere := λ (λ (λ (app (app (ref 2) (ref 1)) (ref 0)))).
Definition l_0 := λ (λ (ref 0)).
Definition l_1 := λ (λ (app (ref 1) (ref 0))).
Definition l_2 := λ (λ (app (ref 1) (app (ref 1) (ref 0)))).
Definition l_3 := λ (λ (app (ref 1) (app (ref 1) (app (ref 1) (ref 0))))).
Definition l_4 := λ (λ (app (ref 1) (app (ref 1) (app (ref 1) (app (ref 1) (ref 0)))))).
Definition l_5 := λ (λ (app (ref 1) (app (ref 1) (app (ref 1) (app (ref 1) (app (ref 1) (ref 0))))))).
Definition l_6 := λ (λ (app (ref 1) (app (ref 1) (app (ref 1) (app (ref 1) (app (ref 1) (app (ref 1) (ref 0)))))))).
Definition succ := λ (λ (λ (app (ref 1) (app (app (ref 2) (ref 1)) (ref 0))))).
Definition add := λ (λ (app itere (app (ref 1) (app succ (ref 0))))).
Definition fact := λ (app (ref 0) (λ λ λ (app (app (ref 0) (λ λ (app (ref 1) (app (app (ref 3) (ref 1)) (ref 0))))) (λ (app (ref 3) (app (ref 2) (ref 0))))))).

Goal (app succ l_0) ->*β l_1.
Proof.
apply (Beta_trans (λ (λ (app (ref 1) (app (app l_0 (ref 1)) (ref 0)))))).
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_cong_lambda; apply Beta_cong_lambda; apply Beta_cong_app.
apply Beta_ref.
apply (Beta_trans (app (λ (ref 0)) (ref 0))).
apply Beta_cong_app. apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
apply Beta_ref.
apply Beta_redex_ref_trans; apply Beta_redex; apply correction_br.
Qed.

Goal (app fact l_3) =β l_6.
Proof.
apply Beta_sym with (get_redex fact l_3); simpl.
apply Beta_redex_sym; apply Beta_redex_ref_trans; apply correction_beta_reduction; reflexivity.
apply Beta_sym with l_6; try (apply Beta_redex_sym; apply Beta_ref).
apply Beta_sym with (get_redex l_3
(λ λ λ (app)
           ((app) (ref 0)
              (λ λ (app) (ref 1) ((app) ((app) (ref 3) (ref 1)) (ref 0))))
           (λ (app) (ref 3) ((app) (ref 2) (ref 0))))
); simpl.
apply Beta_redex_sym; apply Beta_redex_ref_trans; apply correction_beta_reduction; reflexivity.
apply Beta_sym with l_6; try (apply Beta_redex_sym; apply Beta_ref).
apply Beta_sym with
(λ (app)
     (λ λ λ (app)
              ((app) (ref 0)
                 (λ λ (app) (ref 1) ((app) ((app) (ref 3) (ref 1)) (ref 0))))
              (λ (app) (ref 3) ((app) (ref 2) (ref 0))))
     ((app)
        (λ λ λ (app)
                 ((app) (ref 0)
                    (λ λ (app) (ref 1)
                           ((app) ((app) (ref 3) (ref 1)) (ref 0))))
                 (λ (app) (ref 3) ((app) (ref 2) (ref 0))))
                 (get_redex (λ λ λ (app)
                    ((app) (ref 0)
                       (λ λ (app) (ref 1)
                              ((app) ((app) (ref 3) (ref 1)) (ref 0))))
                    (λ (app) (ref 3) ((app) (ref 2) (ref 0))))
                    (ref 0)))); simpl.

apply Beta_redex_sym; apply Beta_cong_lambda; apply Beta_cong_app; try apply Beta_ref. apply Beta_cong_app; try apply Beta_ref.
apply Beta_redex_ref_trans; apply correction_beta_reduction; reflexivity.
apply Beta_sym with l_6; try (apply Beta_redex_sym; apply Beta_ref).
apply Beta_sym with
(λ (app)
     (λ λ λ (app)
              ((app) (ref 0)
                 (λ λ (app) (ref 1) ((app) ((app) (ref 3) (ref 1)) (ref 0))))
              (λ (app) (ref 3) ((app) (ref 2) (ref 0))))
              (get_redex
              (λ λ λ (app)
                 ((app) (ref 0)
                    (λ λ (app) (ref 1)
                           ((app) ((app) (ref 3) (ref 1)) (ref 0))))
                 (λ (app) (ref 3) ((app) (ref 2) (ref 0))))
              (λ λ (app)
               ((app) (ref 0)
                  (λ λ (app) (ref 1) ((app) ((app) (ref 3) (ref 1)) (ref 0))))
               (λ (app) (ref 0) ((app) (ref 2) (ref 0)))))); simpl.

apply Beta_redex_sym; apply Beta_cong_lambda; apply Beta_cong_app; try apply Beta_ref.
apply Beta_redex_ref_trans; apply correction_beta_reduction; reflexivity.
apply Beta_sym with l_6; try (apply Beta_redex_sym; apply Beta_ref).
apply Beta_sym with
(λ (app)
     (λ λ λ (app)
              ((app) (ref 0)
                 (λ λ (app) (ref 1) ((app) ((app) (ref 3) (ref 1)) (ref 0))))
              (λ (app) (ref 3) ((app) (ref 2) (ref 0))))
     (λ λ (app)
            ((app) (ref 0)
               (λ λ (app) (ref 1) ((app) ((app) (ref 3) (ref 1)) (ref 0))))
               (get_redex  (λ λ (app)
                        ((app) (ref 0)
                           (λ λ (app) (ref 1)
                                  ((app) ((app) (ref 3) (ref 1)) (ref 0))))
                        (λ (app) (ref 0) ((app) (ref 2) (ref 0))))
((app) (ref 2) (ref 0))))); simpl.
apply Beta_redex_sym; apply Beta_cong_lambda; apply Beta_cong_app; try apply Beta_ref.
repeat apply Beta_cong_lambda. apply Beta_cong_app; try apply Beta_ref. apply Beta_cong_lambda; apply Beta_cong_app.
Admitted.

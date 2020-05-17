Load "CAM".
Load "Lambda_Calcul".

Notation "'appl'" := (app lambda_term).
Notation "'consl'" := (cons lambda_term).
Notation "'constantel'" := (constante lambda_term).
Notation "'curl'" := (cur lambda_term).
Notation "'fstl'" := (fst lambda_term).
Notation "'pairel'" := (paire lambda_term).
Notation "'pushl'" := (push lambda_term).
Notation "'quotel'" := (quote lambda_term).
Notation "'sndl'" := (snd lambda_term).
Notation "'stackl'" := (stack lambda_term).
Notation "'swapl'" := (swap lambda_term).

Fixpoint acc (n : nat) : (code lambda_term) :=
  match n with
  | 0 => sndl :: nil
  | S m => fstl :: (acc m)
  end.

(*Fixpoint traduction (t : lambda_term) : option (code lambda_term) :=
match t with
| variable n => Some ((quotel (variable n))::nil)
| ref n => Some (acc n)
| λ u =>
    match traduction u with
    | Some C => Some ((curl C)::nil)
    | _ => None
  end
|application u v =>
    match (traduction u,traduction v) with
    | (Some C, Some C1) => Some (pushl :: C ++ swapl::nil ++ C1 ++ appl::nil)
    | (_, _) => None
  end
end.*)

Fixpoint traduction (t : lambda_term) : code lambda_term :=
match t with
| var n => (quotel (variable n))::nil
| ref n => acc n
| λ u => (curl (traduction u))::nil
| lapp u v => (pushl :: (traduction u) ++ swapl::nil ++ (traduction v) ++ appl::nil)
end.

Functional Scheme traduction_ind := Induction for traduction Sort Prop.

Lemma correction_lambda : forall (t1 t2 : lambda_term),
  (innermost_strategy t1 t2) -> forall (c2 : code lambda_term) (s : stack_element lambda_term),
  (well_formed t1) -> traduction t2 = ((curl c2)::nil) ->
  cam_reduction_ref_trans lambda_term (s::nil) (traduction t1) ((avec_code lambda_term c2 s)::nil) nil.
	Proof.
	do 3 intro.
	elim H.
	simpl.
	intros.
	inversion H1.
	rewrite H3.
	simplification_cam.
	simpl.
	intros.
	inversion H1.
	simpl.
	intros.
	inversion H6.

	simpl.
	intros.

	simpl.
	intros.
	rewrite H1.
	simplification_cam.
  Focus 3.
  simpl.
  intros.


	
	rewrite H1 in H2.
	rewrite H2.
	simplification_cam.
	simpl.
	intros.
	inversion H2.
	simpl.
	intros.
	inversion H7.
	simpl.
	intros.
	apply H8.
	2: apply H10.
	rewrite <- H9.
	rewrite H5 in H6.
	
	
	
	
	
	
	
	
	
	
	intros.
	elim H.
	
	inversion H. rewrite <-H2 in H0. rewrite <-H3 in H1.
	functional induction (traduction (λ t)); try discriminate.
	induction n; discriminate.
	inversion_clear H0. inversion_clear H1. simplification_cam.
	rewrite <-H2 in H0. rewrite <-H3 in H1. inversion_clear H0. inversion_clear H1.
	rewrite <-H6 in H1. inversion H1. destruct (traduction t1'); destruct (traduction t2'); discriminate.
	rewrite <-H7 in H0. inversion H0. destruct (traduction t0); destruct (traduction t3); try discriminate. inversion_clear H10.
	
	
	Abort.

Lemma correction_var: forall (t1 t2 : lambda_term) (n : nat) (c1 : code lambda_term)
  (s : stack_element lambda_term),
  (innermost_strategy_bis t1 t2) -> traduction t1 = Some c1 -> traduction t2 = Some ((quotel (variable n))::nil)
  -> cam_reduction_ref_trans lambda_term (s::nil) c1 ((constante lambda_term (var n))::nil) nil.
Abort.

Lemma correction_app: forall (t1 t2 : lambda_term) (c1 C C1 c' : code lambda_term)
  (s : stack_element lambda_term) (s' : stackl),
  (innermost_strategy_bis t1 t2) -> traduction t1 = Some c1 ->
  traduction t2 = Some (pushl :: C ++ swapl::nil ++ C1 ++ appl::nil) ->
  cam_reduction_ref_trans lambda_term (s::nil) C s' c' -> c' <> nil ->
  cam_reduction_ref_trans lambda_term (s::nil) c1 s' (c' ++ (pushl :: C ++ swapl::nil ++ C1 ++ appl::nil)).

var
lambda
(f t1 t2 ... tn)
==> (((f t1) t2) ... tn)
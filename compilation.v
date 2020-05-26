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

Fixpoint traduction (t : lambda_term) : code lambda_term :=
match t with
| var n => (quotel (variable n))::nil
| ref n => acc n
| λ u => (curl (traduction u))::nil
| lapp u v => (pushl :: (traduction u) ++ swapl::nil ++ (traduction v) ++ appl::nil)
end.

Functional Scheme traduction_ind := Induction for traduction Sort Prop.

Definition ne_stack (s : stack lambda_term) :=
  exists (e : stack_element lambda_term), exists (tl : stack lambda_term), s = e :: tl.

(**** New version of the soundness ****)

Lemma correction : forall (ti tf : lambda_term), (innermost_strategy ti tf) ->
  forall (ci cf : code lambda_term) (si : stack lambda_term), ne_stack si -> (well_formed ti) ->
  ci = traduction ti -> cf = traduction tf -> exists sf : stack lambda_term,
    ne_stack sf /\
    cam_reduction_ref_trans lambda_term si (traduction ti) sf nil /\
    cam_reduction_ref_trans lambda_term si (traduction tf) sf nil.
Proof.
  do 3 intro.
  elim H.

  (* Case of λ *)

  intros.
  simpl.
  elim H0; intros.
  elim H4; clear H4; intros.
  exists ((avec_code lambda_term (traduction t) x0)::x1).
  split.
  unfold ne_stack.
  exists (avec_code lambda_term (traduction t) x0).
  exists x1; auto.
  rewrite H4.
  split; simplification_cam.

  (* Case of application *)

	intros.
	simpl.
	elim H8; intros; elim H12; intros; rewrite H13.
  elim (well_formed_app _ _ H9); intros.
	assert (well_formed t4). apply redex_well_formed with (lapp t1' t2'). apply application_wf. apply  innermost_strategy_well_formed with t1. apply H14. apply H0. apply innermost_strategy_well_formed with t2. apply H15. apply H2. apply Beta_redex_ref_trans. apply H5.
	elim (H1 (traduction t1) (traduction t1') (x0::x0::x1)); clear H1; intros; auto;
	  [idtac | unfold ne_stack; exists x0; exists (x0 :: x1); auto].
	elim H1; clear H1; intros.
	elim H1; clear H1; intros.
	elim H17; clear H17; intros.
	clear H9 H12.
	rewrite H4 in H18.
	simpl in H18.
	elim (stack_two lambda_term x0 x0 x1 x2 (traduction t3) nil H18); intros.
	elim H9; clear H9; intros.
	elim H9; clear H9; intros.
	rewrite 
	elim (H3 (traduction t2) (traduction t2') (x5::x4::x6)); clear H3; intros; auto;
	  [idtac | unfold ne_stack; exists x5; exists (x4::x6); auto].
	elim H3; clear H3; intros.
	elim H3; clear H3; intros.
	elim H12; clear H12; intros.
  rewrite H4 in H5.
  elim (beta_cam t3 t2' t4 si H8 H5); intros.
  elim H20; clear H20; intros.
  elim H20; clear H20; intros.
  elim H21; clear H21; intros.
  simpl in H21.
  elim (H7 (traduction t4) (traduction t4') si H8 H16); clear H7; intros; auto.
  elim H7; clear H7; intros.
  elim H7; clear H7; intros.
  elim H23; clear H23; intros.
  exists x11.
  exists x12.
  rewrite H13 in H23, H24.
  split; auto.
  split; auto.
  cut (cam_reduction_ref_trans lambda_term si
    (pushl :: traduction t1 ++ swapl :: traduction t2 ++ appl :: nil) x9 x10).
  intro.
  generalize (equality _ _ _ _ _ H8 H22 H25); intro.
  rewrite <- H26; assumption.
  rewrite H13.
  simplification_cam.
  apply reduc_trans with x2 (x3 ++ swapl :: traduction t2 ++ appl :: nil).
  Focus 2.
  rewrite H9.





(**** Old version of the soundness ***)

Axiom beta_cam : forall (t u t' : lambda_term) (si : stack lambda_term), ne_stack si ->
  (lapp (λ t) u) ->β t' -> 
  exists sf : stack lambda_term, exists c : code lambda_term,
    ne_stack sf /\
    cam_reduction_ref_trans lambda_term si (traduction (lapp (λ t) u)) sf c /\
    cam_reduction_ref_trans lambda_term si (traduction t') sf c.

Axiom equality : forall (si sf : stack lambda_term) (c c' cf : code lambda_term), ne_stack si ->
  cam_reduction_ref_trans lambda_term si c sf cf -> cam_reduction_ref_trans lambda_term si c' sf cf -> c = c'.

Lemma correction : forall (ti tf : lambda_term), (innermost_strategy ti tf) ->
  forall (ci cf : code lambda_term) (si : stack lambda_term), ne_stack si -> (well_formed ti) ->
  ci = traduction ti -> cf = traduction tf -> exists sf : stack lambda_term, exists c : code lambda_term,
    ne_stack sf /\
    cam_reduction_ref_trans lambda_term si (traduction ti) sf c /\
    cam_reduction_ref_trans lambda_term si (traduction tf) sf c.
Proof.
  do 3 intro.
  elim H.
  intros.
  exists si.
  exists (traduction (λ t)).
  split.
  apply H0.
  rewrite <-H2.
  split; simplification_cam.
  intros.
  exists si.
  exists (traduction (var n)).
  split.
  apply H0.
  split; simplification_cam.
  
  (* Cas application avec tête non λ *)
  intros.
  simpl.
  elim H3; intros; elim H7; intros; rewrite H8.
  elim (well_formed_app _ _ H4); intros.
  elim (H1 (traduction t1) (traduction t1') (x0 :: x0 :: x1)); intros; auto;
    [ idtac | unfold ne_stack; exists x0; exists (x0 :: x1); auto].
  elim H11; clear H11; intros; elim H11; clear H11; intros; elim H12; clear H12; intros.
  exists x2. exists (x3 ++ swapl :: traduction t2 ++ appl :: nil).
  split. apply H11.
  split.
  faire_une_etape.
  elim H12; clear H12; intros. elim H12; clear H12; intros;
  simpl; simplification_cam; rewrite H12; try apply reduc_ref. 
  cut (((C0 ++ C1 ++ swapl :: traduction t2 ++ appl :: nil) = ((C0 ++ C1) ++ swapl :: traduction t2 ++ appl :: nil))).
  intros. rewrite H14. apply reduc_ref.
  elim C0. simpl. reflexivity. intros. simpl. rewrite H14. reflexivity.
  apply reduc_ref.
  apply reduc_trans with S' (C' ++ swapl :: traduction t2 ++ appl :: nil).
  apply H14. apply H16.
  faire_une_etape.
  elim H13; clear H13; intros. elim H13; clear H13; intros;
  simpl; simplification_cam; rewrite H13; try apply reduc_ref. 
  cut (((C0 ++ C1 ++ swapl :: traduction t2 ++ appl :: nil) = ((C0 ++ C1) ++ swapl :: traduction t2 ++ appl :: nil))).
  intros. rewrite H14. apply reduc_ref.
  elim C0. simpl. reflexivity. intros. simpl. rewrite H14. reflexivity.
  apply reduc_ref.
  apply reduc_trans with S' (C' ++ swapl :: traduction t2 ++ appl :: nil).
  apply H14. apply H16.
	
	(* Cas application avec tête λ *)
	intros.
	simpl.
	elim H8; intros; elim H12; intros; rewrite H13.
	elim (well_formed_app _ _ H9); intros.
	assert (well_formed t4). apply redex_well_formed with (lapp t1' t2'). apply application_wf. apply  innermost_strategy_well_formed with t1. apply H14. apply H0. apply innermost_strategy_well_formed with t2. apply H15. apply H2. apply Beta_redex_ref_trans. apply H5.
	elim (H1 (traduction t1) (traduction t1') (x0::x0::x1)); clear H1; intros; auto;
	  [idtac | unfold ne_stack; exists x0; exists (x0 :: x1); auto].
	elim H1; clear H1; intros.
	elim H1; clear H1; intros.
	elim H17; clear H17; intros.
	clear H9 H12.
	rewrite H4 in H18.
	simpl in H18.
	elim (stack_two lambda_term x0 x0 x1 x2 (traduction t3) nil x3 H18); intros.
	elim H9; clear H9; intros.
	elim H9; clear H9; intros.
	elim (H3 (traduction t2) (traduction t2') (x5::x4::x6)); clear H3; intros; auto;
	  [idtac | unfold ne_stack; exists x5; exists (x4::x6); auto].
	elim H3; clear H3; intros.
	elim H3; clear H3; intros.
	elim H12; clear H12; intros.
  rewrite H4 in H5.
  elim (beta_cam t3 t2' t4 si H8 H5); intros.
  elim H20; clear H20; intros.
  elim H20; clear H20; intros.
  elim H21; clear H21; intros.
  simpl in H21.
  elim (H7 (traduction t4) (traduction t4') si H8 H16); clear H7; intros; auto.
  elim H7; clear H7; intros.
  elim H7; clear H7; intros.
  elim H23; clear H23; intros.
  exists x11.
  exists x12.
  rewrite H13 in H23, H24.
  split; auto.
  split; auto.
  cut (cam_reduction_ref_trans lambda_term si
    (pushl :: traduction t1 ++ swapl :: traduction t2 ++ appl :: nil) x9 x10).
  intro.
  generalize (equality _ _ _ _ _ H8 H22 H25); intro.
  rewrite <- H26; assumption.
  rewrite H13.
  simplification_cam.
  apply reduc_trans with x2 (x3 ++ swapl :: traduction t2 ++ appl :: nil).
  Focus 2.
  rewrite H9.
  






































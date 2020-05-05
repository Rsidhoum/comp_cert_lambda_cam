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

Fixpoint traduction (t : lambda_term) : option (code lambda_term) :=
match t with
|variable n => Some ((quotel (variable n))::nil)
|ref n => Some (acc n)
|abstraction u =>
    match traduction u with
    | Some C => Some ((curl C)::nil)
    | _ => None
  end
|application u v =>
    match (traduction u,traduction v) with
    | (Some C, Some C1) => Some (pushl :: C ++ swapl::nil ++ C1 ++ appl::nil)
    | (_, _) => None
  end
end.
Functional Scheme traduction_ind := Induction for traduction Sort Prop.

Lemma correction : forall (t1 t2 t': lambda_term) (c c' : code lambda_term) (s : stack_element lambda_term), traduction (lapp (λ t1) t2) = Some c -> traduction t' = Some c' -> innermost_strategy (lapp (λ t1) t2) t' -> cam_reduction_ref_trans lambda_term (s::nil) c ((avec_code lambda_term c' s)::nil) nil.
Proof.
intros.
inversion_clear H1. functional induction (traduction (lapp (λ t1) t2)); functional induction (traduction t'); inversion H2.
cut (c = (pushl :: C ++ swapl :: nil ++ C1 ++ appl :: nil)). cut (c' = (quotel (var n) :: nil)). intros. rewrite H6. rewrite H7.

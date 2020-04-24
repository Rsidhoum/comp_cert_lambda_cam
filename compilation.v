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
    | (Some C, Some C1) => Some (pushl::(curl C)::swapl::nil ++ C1 ++ appl::nil)
    | (_, _) => None
  end
end.

Definition empty_stack := (constantel (var 0))::nil.

Lemma correction : forall (t t' : lambda_term) (c1 c2 : code lambda_term), t ->β t' -> traduction t = Some c1 -> traduction t' = Some c2 -> exists S : stackl, cam_reduction_ref_trans lambda_term empty_stack c1 S c2.

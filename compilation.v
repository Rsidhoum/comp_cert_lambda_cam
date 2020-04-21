Load "CAM".
Load "Lambda_Calcul".

Fixpoint traduction (t : lambda_term) : option (code lambda_term) :=
match t with
|variable n => Some ((quote lambda_term (variable n))::nil)
|ref n => Some ((app lambda_term)::nil)  (*en attendant*)
|abstraction u => match traduction u with
    |Some C => Some ((cur lambda_term C)::nil)
    | _ => None
    end
|application u v => match u with
    |abstraction x => match (traduction x, traduction v) with 
        |(Some C, Some C1) => Some (((push lambda_term)::C1)++((cons lambda_term)::C))
        | (_, _) => None
        end
    | _ => None
    end
end.

Notation "'constantel'" := (constante lambda_term).
Notation "'pairel'" := (paire lambda_term).
Notation "'quotel'" := (quote lambda_term).
Notation "'consl'" := (cons lambda_term).
Notation "'appl'" := (app lambda_term).
Definition empty_stack := (constantel (var 0))::nil.

Goal forall c1 c2 : code lambda_term, traduction (lapp id (var 1)) = Some c1 -> traduction (var 1) = Some c2 -> cam_reduction_ref_trans lambda_term empty_stack c1 empty_stack c2.
Proof.
intros.
inversion H; inversion H0.
apply reduc_trans with
((constantel (var 0))::(constantel (var 0))::nil)
((quotel (var 1)) :: consl :: (appl) :: nil).
apply reduc_cas_base; remove_simple_cam_reduc.
apply reduc_trans with
((constantel (var 1)) :: (constantel (var 0))::nil)
(consl :: appl :: nil).
apply reduc_cas_base; remove_simple_cam_reduc.

Lemma correction : forall (t t' : lambda_term) (c1 c2 : code lambda_term), t ->β t' -> traduction t = Some c1 -> traduction t' = Some c2 -> cam_reduction_ref_trans lambda_term empty_stack c1 empty_stack c2.

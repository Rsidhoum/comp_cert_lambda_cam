Load "Bureau/TER/CAM".
Load "Bureau/TER/Lambda_calcul".

(*Notation "lpush" := (push lambda_term).*)



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


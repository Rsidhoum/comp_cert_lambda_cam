Inductive code_element (A : Set) : Set :=
|fst : code_element A
|snd : code_element A
|quote : A -> code_element A
|cur : (list (code_element A)) -> code_element A
|push : code_element A
|swap : code_element A
|cons : code_element A
|app : code_element A.

Definition code (A : Set) := (list (code_element A)).

Inductive stack_element (A : Set) : Set :=
|constante: A -> stack_element A
|paire: stack_element A -> stack_element A -> stack_element A (* (s, t) : (paire s t)*)
|avec_code: code A -> stack_element A -> stack_element A. (* (C:s) : (avec_code C s)*)

Definition stack (A : Set) := (list (stack_element A)).

Inductive cam_reduction (A : Set) : (stack A) -> (code A) -> (stack A) -> (code A) -> Prop :=
| reduc_fst : reduction_fst : forall (s t : stack_element) (S S': stack) (C : code),
    S' = (s::S) -> cam_reduction ((paire s t)::S) (fst::C) S' C
| reduc_snd : forall (s t : stack_element) (S : stack) (C : code),
    cam_reduction ((paire s t)::S) (fst::C) (t::S) C
| reduc_quote : forall (s : stack_element) (S : stack) (C : code) (n : nat),
    cam_reduction (s::S) ((quote n)::C) (-La nième constante-::S) C
| reduc_cur : forall (s : stack_element) (S : stack) (C C1 : code), 
  cam_reduction (s::S) ((cur C)::C1) (avec_code C s)::S) C1
| reduc_push : forall (s : stack_element) (S : stack) (C:code), 
    cam_reduction (s::S) (push::C) (s::s::S) C
| reduc_swap : forall (s t : stack_element) (S : stack) (C:code), 
    cam_reduction (t::s::S) (swap::C) (s::t::S) C
| reduc_cons : forall (s t : stack_element) (S : stack) (C:code), 
    cam_reduction (t::s::S) (cons::C) ((paire s t)::S) C
| reduc_app : forall (s t : stack_element) (S : stack) (C C1 : code), 
    cam_reduction (t::(avec_code C s)::S) (app::C1) ((paire s t)::S) C::C1.
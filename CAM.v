Inductive code_element : Set :=
|fst : code_element
|snd : code_element
|quote : nat -> code_element
|cur : (list code_element) -> code_element (*Soit dans le futur: code -> code_element*)
|push : code_element
|swap : code_element
|cons : code_element
|app : code_element.

Definition code := (list code_element).

Inductive stack_element : Set :=
|vide : stack_element (* () : (vide)*)
|simple : stack_element -> stack_element (* s : (simple s)*)
|paire: stack_element -> stack_element -> stack_element (* (s, t) : (paire s t)*)
|avec_code: code -> stack_element -> stack_element. (* (C:s) : (avec_code C s)*)

Definition stack1 := (list stack_element).
Definition stack2 := (list code).

Inductive cam_reduction : stack -> code -> stack -> code -> Prop :=
| reduc_fst : reduction_fst : forall (s t : stack_element) (S : stack) (C : code), 
    cam_reduction ((paire s t)::S) (fst::C) (s::S) C
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
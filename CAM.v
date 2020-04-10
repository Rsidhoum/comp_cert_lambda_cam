Open Scope list_scope.

Inductive code_element (A : Set) : Set :=
|fst : (code_element A)
|snd : (code_element A)
|quote : A -> (code_element A)
|cur : (list (code_element A)) -> (code_element A)
|push : (code_element A)
|swap : (code_element A)
|cons : (code_element A)
|app : (code_element A).

Definition code (A : Set) := (list (code_element A)).

Inductive stack_element (A : Set) : Set :=
|constante: A -> (stack_element A)
|paire: (stack_element A) -> (stack_element A) -> (stack_element A) (* (s, t) : (paire s t)*)
|avec_code: (code A) -> (stack_element A) -> (stack_element A). (* (C:s) : (avec_code C s)*)

Definition stack (A : Set) := (list (stack_element A)).

Inductive cam_reduction (A : Set) : (stack A) -> (code A) -> (stack A) -> (code A) -> Prop :=
| reduc_fst : forall (s t : (stack_element A)) (S S' : (stack A)) (C : (code A)),
		S' = (s::S) -> (cam_reduction A) (((paire A) s t)::S) ((fst A)::C) S' C
| reduc_snd : forall (s t : (stack_element A)) (S S' : (stack A)) (C : (code A)),
		S' = (t::S) -> (cam_reduction A) (((paire A) s t)::S) ((snd A)::C) S' C
| reduc_quote : forall (s : (stack_element A)) (S S' : (stack A)) (C : (code A)) (c : A),
		S' = (((constante A) c)::S) -> (cam_reduction A) (s::S) (((quote A) c)::C) S' C
| reduc_cur : forall (s : (stack_element A)) (S S' : (stack A)) (C C1 : (code A)),
		S' = (((avec_code A) C s)::S) -> (cam_reduction A) (s::S) (((cur A) C)::C1) S' C1
| reduc_push : forall (s : (stack_element A)) (S S' : (stack A)) (C C' :(code A)), 
		S' = (s::s::S) -> (cam_reduction A) (s::S) ((push A)::C) S' C
| reduc_swap : forall (s t : (stack_element A)) (S S' : (stack A)) (C:(code A)), 
		S' = (s::t::S) -> (cam_reduction A) (t::s::S) ((swap A)::C) S' C
| reduc_cons : forall (s t : (stack_element A)) (S S' : (stack A)) (C:(code A)), 
		S' = (((paire A) s t)::S) -> (cam_reduction A) (t::s::S) ((cons A)::C) S' C
| reduc_app : forall (s t : (stack_element A)) (S S' : (stack A)) (C C1 : (code A)), 
		S' = (((paire A) s t)::S) -> (cam_reduction A) (t::((avec_code A) C s)::S) ((app A)::C1) S' (C++C1) (*Ici faut-il aussi remplacer (C++C1) par C' et mettre quelque chose de similaire à S'*).

Inductive cam_reduction_ref_trans (A : Set) : (stack A) -> (code A) -> (stack A) -> (code A) -> Prop :=
| reduc_cas_base : forall (S S' : (stack A)) (C C' : (code A)),
	(cam_reduction A) S C S' C' -> (cam_reduction_ref_trans A) S C S' C'
| reduc_ref : forall (S : (stack A)) (C : (code A)),
	(cam_reduction_ref_trans A) S C S C
| reduc_trans : forall (S S' S'' : (stack A)) (C C' C'' :(code A)),
	(cam_reduction_ref_trans A) S C S' C' -> (cam_reduction_ref_trans A) S' C' S'' C'' -> (cam_reduction_ref_trans A) S C S'' C''.

Ltac remove_simple_cam_reduc :=
  repeat
  match goal with
  | |- context[cam_reduction ?A (paire ?A ?s ?t::?S) (fst ?A::?C) (?s::?S) ?C] => apply reduc_fst;trivial
  | |- context[cam_reduction ?A (paire ?A ?s ?t::?S) (snd ?A::?C) (?t::?S) ?C] => apply reduc_snd;trivial
  | |- context[cam_reduction ?A (?s::?S) (quote ?A ?c::?C) ((constante ?A ?c)::?S) ?C] => apply reduc_quote;trivial
  | |- context[cam_reduction ?A (?s::?S) ((cur ?A ?C)::?C1) (avec_code ?A ?C ?s::?S) ?C1] => apply reduc_cur;trivial
  | |- context[cam_reduction ?A (?s::?S) (push ?A::?C) (?s::?s::?S) ?C] => apply reduc_push;trivial;trivial
  | |- context[cam_reduction ?A (?s::?t::?S) (swap ?A::?C) (?t::?s::?S) ?C] => apply reduc_swap;trivial
  | |- context[cam_reduction ?A (?s::?t::?S) (cons ?A::?C) (paire ?A ?t ?s::?S) ?C] => apply reduc_cons;trivial
  | |- context[cam_reduction _ ( _::(avec_code _ _ _)::_) (app _::_) ((paire _ _ _)::_) _] => apply reduc_app;trivial
end.

(*s.S | push;(quote 0);C -> 0.s.S | C*)
Lemma pourAjoutZero :
	forall (S : (stack nat)) (C : (code nat)) (s : (stack_element nat)), 
	(cam_reduction_ref_trans nat) (s::S) ((push nat)::((quote nat) 0)::C) (((constante nat) 0)::s::S) C.
Proof.
intros.
apply reduc_trans with (s::s::S) (((quote nat) 0)::C); apply reduc_cas_base.
remove_simple_cam_reduc.
remove_simple_cam_reduc.
Qed.

(*s.t.S | (cur push;fst;swap;snd;swap);swap;app;C -> s.t.S | C*)
Lemma pourFonctionInutile :
	forall (S : (stack nat)) (C : (code nat)) (s t : (stack_element nat)),
	(cam_reduction_ref_trans nat) (s::t::S) (((cur nat) ((push nat)::(fst nat)::(swap nat)::(snd nat)::(swap nat)::nil))::(swap nat)::(app nat)::C) (s::t::S) C.
Proof.
intros.
apply reduc_trans with (((avec_code nat) ((push nat)::(fst nat)::(swap nat)::(snd nat)::(swap nat)::nil) s)::t::S) ((swap nat)::(app nat)::C).
apply reduc_cas_base.
remove_simple_cam_reduc.
apply reduc_trans with (t::((avec_code nat) ((push nat)::(fst nat)::(swap nat)::(snd nat)::(swap nat)::nil) s)::S) ((app nat)::C).
apply reduc_cas_base.
remove_simple_cam_reduc.
apply reduc_trans with (((paire nat) s t)::S) ((push nat)::(fst nat)::(swap nat)::(snd nat)::(swap nat)::C).
apply reduc_cas_base.
remove_simple_cam_reduc.
remove_simple_cam_reduc.
apply reduc_trans with (((paire nat) s t)::((paire nat) s t)::S) ((fst nat)::(swap nat)::(snd nat)::(swap nat)::C).
apply reduc_cas_base.
remove_simple_cam_reduc.
apply reduc_trans with (s::((paire nat) s t)::S) ((swap nat)::(snd nat)::(swap nat)::C).
apply reduc_cas_base.
remove_simple_cam_reduc.
apply reduc_trans with (((paire nat) s t)::s::S) ((snd nat)::(swap nat)::C).
apply reduc_cas_base.
remove_simple_cam_reduc.
apply reduc_trans with (t::s::S) ((swap nat)::C).
apply reduc_cas_base.
remove_simple_cam_reduc.
apply reduc_trans with (s::t::S) C.
apply reduc_cas_base.
remove_simple_cam_reduc.
apply reduc_ref.
Qed.

Fixpoint exec (A : Set) (S : stack A)  (C : code A) {C}: ((stack A) * (code A)) :=
	match (S, C) with
	| (S', nil) => (S', nil)
	| (((paire _ s t) :: S'), ((fst _) :: C')) => exec A (s :: S') C'
	| (((paire _ s t) :: S'), ((snd _) :: C')) => exec A (t :: S') C'
	| ((s :: S'), ((quote _ c) :: C')) => exec A ((constante A c) :: S') C'
	| ((s :: S'), ((cur _ C') :: C1)) => exec A (((avec_code A) C' s) :: S') C1
	| ((s :: S'), ((push _) :: C')) => exec A (s :: s :: S') C'
	| ((s :: t :: S'),  ((swap _) :: C')) => exec A (t :: s :: S') C'
	| ((t :: s :: S'), ((cons _) :: C')) => exec A ((paire A s t) :: S') C'
	| ((t :: (avec_code _ C' s) :: S'), ((app _) :: C1)) => exec A (((paire A) s t) :: S') (C'++C1)
	| (_, _) => (S, C)
end.
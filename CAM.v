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
		S' = (((paire A) s t)::S) -> (cam_reduction A) (t::((avec_code A) C s)::S) ((app A)::C1) S' (C++C1).

Inductive cam_reduction_ref_trans (A : Set) : (stack A) -> (code A) -> (stack A) -> (code A) -> Prop :=
| reduc_cas_base : forall (S S' : (stack A)) (C C' : (code A)),
	(cam_reduction A) S C S' C' -> (cam_reduction_ref_trans A) S C S' C'
| reduc_ref : forall (S : (stack A)) (C : (code A)),
	(cam_reduction_ref_trans A) S C S C
| reduc_trans : forall (S S' S'' : (stack A)) (C C' C'' :(code A)),
	(cam_reduction_ref_trans A) S C S' C' -> (cam_reduction_ref_trans A) S' C' S'' C'' -> (cam_reduction_ref_trans A) S C S'' C''.

Ltac remove_simple_cam_reduc :=
  try repeat
  apply reduc_fst || apply reduc_snd || apply reduc_quote || apply reduc_cur || apply reduc_push || apply reduc_swap || apply reduc_cons || apply reduc_app || trivial.

Ltac faire_trans :=
	match goal with
	| |- context[cam_reduction_ref_trans ?A ((paire ?A ?s ?t)::?S) ((fst ?A)::?C) _ _] 
		=> apply reduc_trans with (s::S) C
	| |- context[cam_reduction_ref_trans ?A ((paire ?A ?s ?t)::?S) ((snd ?A)::?C) _ _] 
		=> apply reduc_trans with (t::S) C
	| |- context[cam_reduction_ref_trans ?A (?s::?S) ((quote ?A ?c)::?C) _ _] 
		=> apply reduc_trans with ((constante A c)::S) C
	| |- context[cam_reduction_ref_trans ?A (?s::?S) ((cur ?A ?C)::?C1) _ _] 
		=> apply reduc_trans with ((avec_code A C s)::S) C1
	| |- context[cam_reduction_ref_trans ?A (?s::?S) ((push ?A)::?C) _ _] 
		=> apply reduc_trans with (s::s::S) C
	| |- context[cam_reduction_ref_trans ?A (?t::?s::?S) ((swap ?A)::?C) _ _] 
		=> apply reduc_trans with (s::t::S) C
	| |- context[cam_reduction_ref_trans ?A (?t::?s::?S) ((cons ?A)::?C) _ _] 
		=> apply reduc_trans with ((paire A s t)::S) C
	| |- context[cam_reduction_ref_trans ?A (?t::(avec_code ?A ?C ?s)::?S) ((app ?A)::?C1) _ _] 
		=> apply reduc_trans with ((paire A s t)::S) (C++C1);simpl
end.

Ltac faire_une_etape :=
	faire_trans;
	only 1 : [> apply reduc_cas_base;
	remove_simple_cam_reduc].
	
Ltac simplification_cam :=
	try repeat
	apply reduc_ref || faire_une_etape.
	
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
simplification_cam.
Qed.

Axiom stack_two : forall (A : Set) (a b : stack_element A) (tl s : stack A) (c tc : code A),
  cam_reduction_ref_trans A (a::b::tl) ((cur A c)::tc) s nil ->
  exists (a' : stack_element A), exists (b' : stack_element A), exists (tl' : stack A), s = a'::b'::tl'.






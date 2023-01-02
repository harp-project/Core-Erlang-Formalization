From CoreErlang.FrameStack Require Export Frames.
From CoreErlang Require Export Exceptions Auxiliaries Matching.

Import ListNotations.

Lemma Lit_eqb_eq : forall l1 l2, Lit_beq l1 l2 = true <-> l1 = l2.
Proof.
  split; intros.
  * now apply internal_Lit_dec_bl.
  * now apply internal_Lit_dec_lb. 
Qed.

Lemma Lit_eqb_refl : forall l, Lit_beq l l = true.
Proof.
  intro. rewrite Lit_eqb_eq. reflexivity.
Qed.


Definition convert_to_closlist (l : list (nat * nat * Exp)) : (list Val) :=
  map (fun '(id,vc,e) => (VClos l id vc e)) l.

Definition create_result (ident : FrameIdent) (vl : list Val)
  : Redex :=
match ident with
| IValues => RValSeq vl
| ITuple => RValSeq [VTuple vl]
| IMap => RValSeq [VMap (make_val_map (deflatten_list vl))]
| ICall f => fst (eval f f vl []) (*side effects!!! *)
| IPrimOp f => fst (eval f f vl []) (* side effects !!!!*)
| IApp (VClos ext id vars e) =>
  if Nat.eqb vars (length vl)
  then RExp (e.[list_subst vl idsubst])
  else RExc (badarity (VClos ext id vars e))
| IApp v => RExc (badfun v)
end.

Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).
Inductive step : FrameStack -> Redex -> FrameStack -> Redex -> Prop :=
(**  Reduction rules *)

(** Cooling: single value *)
| cool_value v xs:
  ⟨ xs, `v ⟩ --> ⟨ xs, RValSeq [v] ⟩

(************************************************)
(* heating should be separate for all complex expressions (to be
   syntax-driven).
   Only the intermediate and last steps can be extracted: *)
| step_params xs ident (el : list Exp) (vl : list Val) (v : Val) (e : Exp):
  ⟨FParams ident vl (e :: el) :: xs, RValSeq [v]⟩ -->
  ⟨FParams ident (vl ++ [v]) el :: xs, e⟩

(* technical rule to avoid duplication for 0 subexpressions : *)
| step_params_0 xs ident e el vl:
  ⟨FParams ident vl (e::el) ::xs, RBox⟩ --> ⟨FParams ident vl el :: xs, e⟩

(* 0 subexpression in complex expressions: *)
| cool_params_0 xs ident (vl : list Val) (res : Redex) : 
  res = create_result ident vl ->
  ⟨FParams ident vl [] ::xs, RBox⟩ --> ⟨xs, res⟩

| cool_params xs ident (vl : list Val) (v : Val) (res : Redex):
  res = create_result ident (vl ++ [v]) ->
  ⟨FParams ident vl [] :: xs, RValSeq [v]⟩ --> ⟨xs, res⟩

(************************************************)
(* Heating constructs with list subexpressions: *)
| heat_values (el : list Exp) (xs : list Frame):
  ⟨ xs, EValues el ⟩ --> ⟨ (FParams IValues [] el)::xs, RBox ⟩

| heat_tuple (el : list Exp) (xs : list Frame):
  ⟨ xs, ETuple el ⟩ --> ⟨ (FParams ITuple [] el)::xs, RBox ⟩

| heat_map (el : list (Exp * Exp)) (xs : list Frame):
  ⟨ xs, EMap el ⟩ --> ⟨ (FParams IMap [] (flatten_list el))::xs, RBox ⟩

| heat_call (el : list Exp) (xs : list Frame) f:
  ⟨ xs, ECall f el ⟩ --> ⟨ (FParams (ICall f) [] el)::xs, RBox ⟩

| heat_primop (el : list Exp) (xs : list Frame) f:
  ⟨ xs, EPrimOp f el ⟩ --> ⟨ (FParams (IPrimOp f) [] el)::xs, RBox ⟩

| heat_app2 (el : list Exp) (xs : list Frame) (v : Val):
  ⟨ FApp1 el :: xs, RValSeq [v] ⟩ --> ⟨ (FParams (IApp v) [] el)::xs, RBox ⟩

(************************************************)
(**  List *)
(**  Cooling *)

| cool_cons_1 (hd : Exp) (tl : Val) xs :
  ⟨ (FCons1 hd)::xs, RValSeq [tl] ⟩ --> ⟨ (FCons2 tl)::xs, RExp hd ⟩

| cool_cons_2 (hd tl : Val) xs :
  ⟨ (FCons2 tl)::xs, RValSeq [hd] ⟩ --> ⟨ xs, RValSeq [VCons hd tl] ⟩

(**  Heating *)
| heat_cons (hd tl : Exp) xs :
  ⟨ xs, ECons hd tl ⟩ --> ⟨ (FCons1 hd)::xs, RExp tl ⟩

(**  Let *)
(**  Cooling *)
| cool_let l e2 vs xs :
  length vs = l ->
  ⟨ (FLet l e2)::xs, RValSeq vs ⟩ --> ⟨ xs, RExp (e2.[ list_subst vs idsubst ]) ⟩

(**  Heating *)
| heat_let l e1 e2 xs :
  ⟨ xs, ELet l e1 e2 ⟩ --> ⟨ (FLet l e2)::xs, RExp e1 ⟩

(**  Seq *)
(**  Cooling *)
| cool_seq e2 v xs :
  ⟨ (FSeq e2)::xs, RValSeq [v] ⟩ --> ⟨ xs, RExp e2 ⟩
(**  Heating *)
| heat_seq e1 e2 xs :
  ⟨ xs, ESeq e1 e2 ⟩ --> ⟨ (FSeq e2)::xs, RExp e1 ⟩


(**  Fun *)
(**  Cooling *)
| cool_fun e vl xs :
  ⟨ xs, EFun vl e ⟩ --> ⟨ xs, RValSeq [ VClos [] 0 vl e ] ⟩
  (* TODO : id <> 0 usually *)


(**  Case *)
(**  Heating *)
| heat_Case e l xs:
  ⟨ xs, ECase e l ⟩ --> ⟨ (FCase1 l)::xs, RExp e ⟩

(**  Cooling *)
(* reduction started or it is already ongoing, the first pattern matched,
   e1 the guard needs to be evaluated. vs' (the result of the pattern
   matching is stored in the frame) *)
| step_case_match lp e1 e2 l vs vs' xs :
  match_pattern_list lp vs = Some vs' ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs ⟩ -->
  ⟨ (FCase2 vs lp e2 l vs')::xs, RExp (e1.[list_subst vs' idsubst]) ⟩

(* reduction started or it is already ongoing, the first pattern doesn't 
   match, so we check the next pattern *)
| step_case_not_match lp e1 e2 l vs xs :
  match_pattern_list lp vs = None ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs ⟩ --> ⟨ (FCase1 l)::xs, RValSeq vs ⟩

(* reduction is ongoing, the pattern matched, and the guard is true, thus 
   the reduction continues inside the given clause *)
| step_case_true vs lp e' l vs' xs :
  ⟨ (FCase2 vs lp e' l vs')::xs, RValSeq [ VLit (Atom "true") ] ⟩ --> ⟨ xs, RExp (e'.[list_subst vs' idsubst]) ⟩

(* reduction is ongoing, the pattern matched, and the guard is false, thus
   we check the next pattern. *)
| step_case_false vs lp' e' l vs' xs :
  ⟨ (FCase2 vs lp' e' l vs')::xs, RValSeq [ VLit (Atom "false") ] ⟩ --> ⟨ (FCase1 l)::xs, RValSeq vs ⟩

(** Exceptions *)
| cool_case_empty vs xs:
  ⟨ (FCase1 [])::xs, RValSeq vs ⟩ --> ⟨ xs, RExc if_clause ⟩

(**  LetRec *)
(**  Cooling *)
(**  Heating *)
| heat_LetRec l e lc xs :
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc ->
  (* TODO: for now the funids are 0 coded in *)
  ⟨ xs, ELetRec l e ⟩ --> ⟨ xs, RExp e.[list_subst lc idsubst] ⟩


(**  Try *)
(**  Cooling *)
| cool_Try_ok vl1 e2 vl2 e3 vs xs:
  vl1 = length vs ->
  ⟨ (FTry vl1 e2 vl2 e3)::xs, RValSeq vs ⟩ --> ⟨ xs, RExp e2.[ list_subst vs idsubst ] ⟩
| cool_Try_err vl1 e2 e3 class reason details xs:
  (* in Core Erlang exceptions always have 3 parts *)
  ⟨ (FTry vl1 e2 3 e3)::xs, RExc (class, reason, details) ⟩ -->
  ⟨ xs, RExp e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] ⟩
(**  Heating *)
| heat_Try e1 vl1 e2 vl2 e3 xs :
  ⟨ xs, ETry e1 vl1 e2 vl2 e3 ⟩ --> ⟨ (FTry vl1 e2 vl2 e3)::xs, RExp e1 ⟩
  
(** Exceptions *)
(** Propogation *)
| propogate_Exception F exc xs :
  (forall vl1 e2 vl2 e3, (FTry vl1 e2 vl2 e3) <> F) ->
  ⟨ F::xs, RExc exc ⟩ --> ⟨ xs, RExc exc ⟩
  (* TODO: details could be appended here to the stack trace *)

where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').


Reserved Notation "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> Redex -> nat -> FrameStack -> Redex -> Prop :=
| step_refl fs e : ⟨ fs, e ⟩ -[ 0 ]-> ⟨ fs, e ⟩
| step_trans fs e fs' e' fs'' e'' k:
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -[ k ]-> ⟨fs'', e''⟩
  ->
  ⟨ fs, e ⟩ -[S k]-> ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" := (step_rt fs e k fs' e').

Inductive is_result : Redex -> Prop :=
| exception_is_result ex : is_result (RExc ex)
| valseq_is_result vs : is_result (RValSeq vs).

Definition step_any (fs : FrameStack) (e : Redex) (r : Redex) : Prop :=
  exists k res, is_result res /\ ⟨fs, e⟩ -[k]-> ⟨[], res⟩.
Notation "⟨ fs , e ⟩ -->* v" := (step_any fs e v) (at level 50).

(**
  This file defines the frame stack semantics of Core Erlang.
*)

From CoreErlang.FrameStack Require Export Frames.
From CoreErlang Require Export Auxiliaries Matching.

Import ListNotations.

(* Note: for simplicity, this semantics allows guards to evaluate
   to exceptions, which is not allowed in normal Core Erlang. *)
Reserved Notation "⟨ fs , e ⟩ -⌊ l ⌋->ₗ ⟨ fs' , e' ⟩" (at level 0).
Inductive step : FrameStack -> Redex -> option SideEffect -> FrameStack -> Redex -> Prop :=
(**  Reduction rules *)

(** Cooling: single value *)
| cool_value v xs:
  VALCLOSED v -> (* to filter out variables *)
  ⟨ xs, ˝v ⟩ -⌊None⌋->ₗ ⟨ xs, RValSeq [v] ⟩

(************************************************)
(* heating should be separate for all complex expressions (to be
   syntax-driven).
   Only the intermediate and last steps can be extracted: *)
| eval_step_params xs ident (el : list Exp) (vl : list Val) (v : Val) (e : Exp):
  ⟨FParams ident vl (e :: el) :: xs, RValSeq [v]⟩ -⌊None⌋->ₗ
  ⟨FParams ident (vl ++ [v]) el :: xs, e⟩

(* technical rule to avoid duplication for 0 subexpressions : *)
| eval_step_params_0 xs ident e el vl:
  ident <> IMap ->
  ⟨FParams ident vl (e::el) ::xs, RBox⟩ -⌊None⌋->ₗ ⟨FParams ident vl el :: xs, e⟩

(* 0 subexpression in complex expressions: *)
| eval_cool_params_0 xs ident (vl : list Val) (res : Redex) (l : option SideEffect) : 
  ident <> IMap ->
  Some (res, l) = create_result ident vl -> (* TODO: side effects *)
  ⟨FParams ident vl [] ::xs, RBox⟩ -⌊l⌋->ₗ ⟨xs, res⟩

| eval_cool_params xs ident (vl : list Val) (v : Val) (res : Redex) (l : option SideEffect):
  Some (res, l) = create_result ident (vl ++ [v]) ->(* TODO: side effects *)
  ⟨FParams ident vl [] :: xs, RValSeq [v]⟩ -⌊l⌋->ₗ ⟨xs, res⟩

(************************************************)
(* Heating constructs with list subexpressions: *)
| eval_heat_values (el : list Exp) (xs : list Frame):
  ⟨ xs, EValues el ⟩ -⌊None⌋->ₗ ⟨ (FParams IValues [] el)::xs, RBox ⟩

| eval_heat_tuple (el : list Exp) (xs : list Frame):
  ⟨ xs, ETuple el ⟩ -⌊None⌋->ₗ ⟨ (FParams ITuple [] el)::xs, RBox ⟩

(* This is handled separately, to satisfy the invariant in FCLOSED for maps *)
| eval_heat_map_0 (xs : list Frame):
  ⟨ xs, EMap [] ⟩ -⌊None⌋->ₗ ⟨ xs, RValSeq [VMap []] ⟩

| eval_heat_map (e1 e2 : Exp) (el : list (Exp * Exp)) (xs : list Frame):
  ⟨ xs, EMap ((e1, e2) :: el) ⟩ -⌊None⌋->ₗ
  ⟨ (FParams IMap [] (e2 :: flatten_list el))::xs, e1 ⟩

| eval_heat_call_mod (el : list Exp) (xs : list Frame) (m f : Exp) :
  ⟨ xs, ECall m f el ⟩ -⌊None⌋->ₗ ⟨ FCallMod f el :: xs, m ⟩

| eval_heat_call_fun (el : list Exp) (xs : list Frame) (v : Val) (f : Exp) :
  ⟨ FCallMod f el :: xs, RValSeq [v] ⟩ -⌊None⌋->ₗ ⟨ FCallFun v el :: xs, f ⟩

| eval_heat_call_params (el : list Exp) (xs : list Frame) (m f : Val):
  ⟨ FCallFun m el :: xs, RValSeq [f] ⟩ -⌊None⌋->ₗ ⟨ (FParams (ICall m f) [] el)::xs, RBox ⟩

| eval_heat_primop (el : list Exp) (xs : list Frame) f:
  ⟨ xs, EPrimOp f el ⟩ -⌊None⌋->ₗ ⟨ (FParams (IPrimOp f) [] el)::xs, RBox ⟩

| eval_heat_app2 (el : list Exp) (xs : list Frame) (v : Val):
  ⟨ FApp1 el :: xs, RValSeq [v] ⟩ -⌊None⌋->ₗ ⟨ (FParams (IApp v) [] el)::xs, RBox ⟩

(************************************************)
(**  App *)
| eval_heat_app xs e l:
  ⟨xs, EApp e l⟩ -⌊None⌋->ₗ ⟨FApp1 l :: xs, e⟩ 
(**  List *)
(**  Cooling *)

| eval_cool_cons_1 (hd : Exp) (tl : Val) xs :
  ⟨ (FCons1 hd)::xs, RValSeq [tl] ⟩ -⌊None⌋->ₗ ⟨ (FCons2 tl)::xs, RExp hd ⟩

| eval_cool_cons_2 (hd tl : Val) xs :
  ⟨ (FCons2 tl)::xs, RValSeq [hd] ⟩ -⌊None⌋->ₗ ⟨ xs, RValSeq [VCons hd tl] ⟩

(**  Heating *)
| eval_heat_cons (hd tl : Exp) xs :
  ⟨ xs, ECons hd tl ⟩ -⌊None⌋->ₗ ⟨ (FCons1 hd)::xs, RExp tl ⟩

(**  Let *)
(**  Cooling *)
| eval_cool_let l e2 vs xs :
  length vs = l ->
  ⟨ (FLet l e2)::xs, RValSeq vs ⟩ -⌊None⌋->ₗ ⟨ xs, RExp (e2.[ list_subst vs idsubst ]) ⟩

(**  Heating *)
| eval_heat_let l e1 e2 xs :
  ⟨ xs, ELet l e1 e2 ⟩ -⌊None⌋->ₗ ⟨ (FLet l e2)::xs, RExp e1 ⟩

(**  Seq *)
(**  Cooling *)
| eval_cool_seq e2 v xs :
  ⟨ (FSeq e2)::xs, RValSeq [v] ⟩ -⌊None⌋->ₗ ⟨ xs, RExp e2 ⟩
(**  Heating *)
| eval_heat_seq e1 e2 xs :
  ⟨ xs, ESeq e1 e2 ⟩ -⌊None⌋->ₗ ⟨ (FSeq e2)::xs, RExp e1 ⟩


(**  Fun *)
(**  Cooling *)
| eval_cool_fun e vl xs :
  ⟨ xs, EFun vl e ⟩ -⌊None⌋->ₗ ⟨ xs, RValSeq [ VClos [] 0 vl e ] ⟩
  (* TODO : id <> 0 usually *)


(**  Case *)
(**  Heating *)
| eval_heat_case e l xs:
  ⟨ xs, ECase e l ⟩ -⌊None⌋->ₗ ⟨ (FCase1 l)::xs, RExp e ⟩

(**  Cooling *)
(* reduction started or it is already ongoing, the first pattern matched,
   e1 the guard needs to be evaluated. vs' (the result of the pattern
   matching is stored in the frame) *)
| eval_step_case_match lp e1 e2 l vs vs' xs :
  match_pattern_list lp vs = Some vs' ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs ⟩ -⌊None⌋->ₗ
  ⟨ (FCase2 vs e2.[list_subst vs' idsubst] l)::xs, RExp (e1.[list_subst vs' idsubst]) ⟩

(* reduction started or it is already ongoing, the first pattern doesn't 
   match, so we check the next pattern *)
| eval_step_case_not_match lp e1 e2 l vs xs :
  match_pattern_list lp vs = None ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs ⟩ -⌊None⌋->ₗ
  ⟨ (FCase1 l)::xs, RValSeq vs ⟩

(* reduction is ongoing, the pattern matched, and the guard is true, thus 
   the reduction continues inside the given clause *)
| eval_step_case_true vs e' l xs :
  ⟨ (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "true") ] ⟩ -⌊None⌋->ₗ 
  ⟨ xs, RExp e' ⟩

(* reduction is ongoing, the pattern matched, and the guard is false, thus
   we check the next pattern. *)
| eval_step_case_false vs e' l xs :
  ⟨ (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "false") ] ⟩ -⌊None⌋->ₗ ⟨ (FCase1 l)::xs, RValSeq vs ⟩

(** Exceptions *)
| eval_cool_case_empty vs xs:
  ⟨ (FCase1 [])::xs, RValSeq vs ⟩ -⌊None⌋->ₗ ⟨ xs, RExc if_clause ⟩

(**  LetRec *)
(**  Cooling *)
(**  Heating *)
| eval_heat_letrec l e lc xs :
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc ->
  (* TODO: for now the funids are 0 coded in *)
  ⟨ xs, ELetRec l e ⟩ -⌊None⌋->ₗ ⟨ xs, RExp e.[list_subst lc idsubst] ⟩


(**  Try *)
(**  Cooling *)
| eval_cool_try_ok vl1 e2 vl2 e3 vs xs:
  vl1 = length vs ->
  ⟨ (FTry vl1 e2 vl2 e3)::xs, RValSeq vs ⟩ -⌊None⌋->ₗ ⟨ xs, RExp e2.[ list_subst vs idsubst ] ⟩
| eval_cool_try_err vl1 e2 e3 class reason details xs:
  (* in Core Erlang exceptions always have 3 parts *)
  ⟨ (FTry vl1 e2 3 e3)::xs, RExc (class, reason, details) ⟩ -⌊None⌋->ₗ
  ⟨ xs, RExp e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] ⟩
(**  Heating *)
| eval_heat_try e1 vl1 e2 vl2 e3 xs :
  ⟨ xs, ETry e1 vl1 e2 vl2 e3 ⟩ -⌊None⌋->ₗ ⟨ (FTry vl1 e2 vl2 e3)::xs, RExp e1 ⟩
  
(** Exceptions *)
(** Propogation *)
| eval_prop_exc F exc xs :
  isPropagatable F = true ->
  ⟨ F::xs, RExc exc ⟩ -⌊None⌋->ₗ ⟨ xs, RExc exc ⟩
  (* TODO: details could be appended here to the stack trace *)

where "⟨ fs , e ⟩ -⌊ l ⌋->ₗ ⟨ fs' , e' ⟩" := (step fs e l fs' e').


Reserved Notation "⟨ fs , e ⟩ -[ k , l ]->ₗ ⟨ fs' , e' ⟩" (at level 0).
Inductive step_rt : FrameStack -> Redex -> nat -> list SideEffect -> FrameStack -> Redex -> Prop :=
| step_refl fs e : ⟨ fs, e ⟩ -[ 0, [] ]->ₗ ⟨ fs, e ⟩
| step_trans fs e fs' e' fs'' e'' k l l' s:
  ⟨ fs, e ⟩ -⌊s⌋->ₗ ⟨ fs', e'⟩ ->
  ⟨fs', e'⟩ -[ k , l ]->ₗ ⟨fs'', e''⟩ ->
  l' = match s with | None => l | Some s' => s' :: l end
  ->
  ⟨ fs, e ⟩ -[S k, l' ]->ₗ ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k , l ]->ₗ ⟨ fs' , e' ⟩" := (step_rt fs e k l fs' e').

Definition step_any_non_terminal
  (fs : FrameStack) (e : Redex) (l: list SideEffect) (fs' : FrameStack) (e': Redex) : Prop :=
  exists k, ⟨fs, e⟩ -[k, l]->ₗ ⟨fs', e'⟩.
Notation "⟨ fs , e ⟩ -[ l ]->ₗ* ⟨ fs' , e' ⟩" := (step_any_non_terminal fs e l fs' e') (at level 0).

Definition step_any (fs : FrameStack) (e : Redex) (r : Redex) : Prop :=
  exists k l, is_result r /\ ⟨fs, e⟩ -[k, l]->ₗ ⟨[], r⟩.
Notation "⟨ fs , e ⟩ -->ₗ* v" := (step_any fs e v) (at level 0, v at level 50).

Local Lemma test_precedence : ⟨ [], ˝VNil ⟩ -->ₗ* RValSeq [VNil].
Abort.

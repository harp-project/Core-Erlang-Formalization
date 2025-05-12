(**
  This file contains the inductive definition for (frame stack) termination of Core
  Erlang expressions. It is equivalent to the termination expressed with the
  semantics in `SubstSemanticsLabeled.v`.
*)

From CoreErlang.FrameStack Require Export SubstSemanticsLabeled.

Import ListNotations.

(** This property holds true if a |fs, e| configuration terminates in k steps with l sideeffects. *)
Definition terminates_in_k_l_sem (fs : FrameStack) (e : Redex) (k : nat) (l : list SideEffect)
  : Prop :=
  exists (res : Redex), is_result res /\ ⟨fs, e⟩ -[k , l]-> ⟨[], res⟩.


(** A more practical way to define termination in k steps *)
Reserved Notation "| fs , e | l – k ↓" (at level 80).
Inductive terminates_in_k : FrameStack -> Redex -> SideEffectList -> nat -> Prop :=

(** Cooling: single value *)
| cool_value v xs l k :
  VALCLOSED v ->
  | xs, RValSeq [v] | l – k ↓
->
  | xs, ˝v | l – S k ↓

(************************************************)
(* heating should be separate for all complex expressions (to be
   syntax-driven).
   Only the intermediate and last steps can be extracted: *)
| step_params xs ident (el : list Exp) (vl : list Val) (v : Val) (e : Exp) l k:
  | FParams ident (vl ++ [v]) el :: xs, e | l – k ↓
->
  | FParams ident vl (e :: el) :: xs, RValSeq [v] | l – S k ↓

(* technical rule to avoid duplication for 0 subexpressions : *)
| step_params_0 xs ident e (el : list Exp) vl l k:
  ident <> IMap ->
  |FParams ident vl el :: xs, RExp e| l – k ↓
->
  |FParams ident vl (e::el) ::xs, RBox| l – S k ↓

(* 0 subexpression in complex expressions: *)
| cool_params_0 xs ident (vl : list Val) (res : Redex) (l: option SideEffect) ls k: 
  ident <> IMap ->
  Some (res, l) = create_result ident vl -> (* TODO side effects *)
  |xs, res| ls – k ↓
->
  |FParams ident vl [] ::xs, RBox| ls – S k ↓

| cool_params xs ident (vl : list Val) (v : Val) (res : Redex) (l : option SideEffect) ls k:
  Some (res, l) = create_result ident (vl ++ [v]) -> (* TODO side effects *)
  |xs, res| ls – k ↓
->
  |FParams ident vl [] :: xs, RValSeq [v]| ls – S k ↓

(************************************************)
(* Heating constructs with list subexpressions: *)
| heat_values (el : list Exp) (xs : list Frame) l k:
  | (FParams IValues [] el)::xs, RBox | l – k ↓
->
  | xs, EValues el | l – S k ↓

| heat_tuple (el : list Exp) (xs : list Frame) l k:
  | (FParams ITuple [] el)::xs, RBox | l – k ↓ 
->
  | xs, ETuple el | l – S k ↓

(* This is handled separately, to satisfy the invariant in FCLOSED for maps *)
| heat_map_0 (xs : list Frame) l k:
  | xs, RValSeq [VMap []] | l – k ↓ 
->
  | xs, EMap [] | l – S k ↓

| heat_map (e1 e2 : Exp) (el : list (Exp * Exp)) (xs : list Frame) l k:
  | (FParams IMap [] (e2 :: flatten_list el))::xs, e1 | l – k ↓ 
->
  | xs, EMap ((e1, e2) :: el) | l – S k ↓

| heat_call_mod (el : list Exp) (xs : list Frame) (m f : Exp) l k :
  | FCallMod f el :: xs, m | l – k ↓
->
  | xs, ECall m f el | l – S k ↓

| heat_call_fun (el : list Exp) (xs : list Frame) (v : Val) (f : Exp) l k :
  | FCallFun v el :: xs, f | l – k ↓
->
  | FCallMod f el :: xs, RValSeq [v] | l – S k ↓

| heat_call_params (el : list Exp) (xs : list Frame) (m f : Val) l k:
  | (FParams (ICall m f) [] el)::xs, RBox | l – k ↓
->
  | FCallFun m el :: xs, RValSeq [f] | l – S k ↓

| heat_primop (el : list Exp) (xs : list Frame) f l k:
  | (FParams (IPrimOp f) [] el)::xs, RBox | l – k ↓ 
->
  | xs, EPrimOp f el | l – S k ↓

| heat_app2 (el : list Exp) (xs : list Frame) (v : Val) l k:
  | (FParams (IApp v) [] el)::xs, RBox | l – k ↓ 
->
  | FApp1 el :: xs, RValSeq [v] | l – S k ↓

(************************************************)
(**  App *)
| heat_app xs e l ls k:
  |FApp1 l :: xs, RExp e| ls – k ↓ 
->
  |xs, EApp e l| ls – S k ↓
(**  List *)
(**  Cooling *)

| cool_cons_1 (hd : Exp) (tl : Val) xs l k :
  | (FCons2 tl)::xs, RExp hd | l – k ↓ 
->
  | (FCons1 hd)::xs, RValSeq [tl] | l – S k ↓

| cool_cons_2 (hd tl : Val) xs l k:
  | xs, RValSeq [VCons hd tl] | l – k ↓ 
->
  | (FCons2 tl)::xs, RValSeq [hd] | l – S k ↓

(**  Heating *)
| heat_cons (hd tl : Exp) xs l k:
  | (FCons1 hd)::xs, RExp tl | l – k ↓ 
->
  | xs, ECons hd tl | l – S k ↓

(**  Let *)
(**  Cooling *)
| cool_let l e2 vs xs ls k:
  length vs = l ->
  | xs, RExp (e2.[ list_subst vs idsubst ]) | ls – k ↓ 
->
  | (FLet l e2)::xs, RValSeq vs | ls – S k ↓

(**  Heating *)
| heat_let l e1 e2 xs ls k:
  | (FLet l e2)::xs, RExp e1 | ls – k ↓ 
->
  | xs, ELet l e1 e2 | ls – S k ↓

(**  Seq *)
(**  Cooling *)
| cool_seq e2 v xs l k:
  | xs, RExp e2 | l – k ↓ 
->
  | (FSeq e2)::xs, RValSeq [v] | l – S k ↓
(**  Heating *)
| heat_seq e1 e2 xs l k:
  | (FSeq e2)::xs, RExp e1 | l – k ↓ 
->
  | xs, ESeq e1 e2 | l – S k ↓


(**  Fun *)
(**  Cooling *)
| cool_fun e vl xs l k:
  | xs, RValSeq [ VClos [] 0 vl e ] | l – k ↓ 
->
  | xs, EFun vl e | l – S k ↓
  (* TODO : id <> 0 usually *)


(**  Case *)
(**  Heating *)
| heat_case e l xs ls k:
  | (FCase1 l)::xs, RExp e | ls – k ↓ 
->
  | xs, ECase e l | ls – S k ↓

(**  Cooling *)
(* reduction started or it is already ongoing, the first pattern matched,
   e1 the guard needs to be evaluated. vs' (the result of the pattern
   matching is stored in the frame) *)
| step_case_match lp e1 e2 l vs vs' xs ls k:
  match_pattern_list lp vs = Some vs' ->
  | (FCase2 vs e2.[list_subst vs' idsubst] l)::xs, RExp (e1.[list_subst vs' idsubst]) | ls – k ↓
->
  | (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs | ls – S k ↓
(* reduction started or it is already ongoing, the first pattern doesn't 
   match, so we check the next pattern *)
| step_case_not_match lp e1 e2 l vs xs ls k:
  match_pattern_list lp vs = None ->
  | (FCase1 l)::xs, RValSeq vs | ls – k ↓ 
->
  | (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs | ls – S k ↓

(* reduction is ongoing, the pattern matched, and the guard is true, thus 
   the reduction continues inside the given clause *)
| step_case_true vs e' l xs ls k:
  | xs, RExp e' | ls – k ↓ 
->
  | (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "true") ] | ls – S k ↓

(* reduction is ongoing, the pattern matched, and the guard is false, thus
   we check the next pattern. *)
| step_case_false vs e' l xs k ls:
  | (FCase1 l)::xs, RValSeq vs | ls – k ↓ 
->
  | (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "false") ] | ls – S k ↓

(** Exceptions *)
| cool_case_empty vs xs l k:
  | xs, RExc if_clause | l – k ↓ 
->
  | (FCase1 [])::xs, RValSeq vs | l – S k ↓

(**  LetRec *)
(**  Cooling *)
(**  Heating *)
| heat_letrec l e lc xs ls k:
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc ->
  (* TODO: for now the funids are 0 coded in *)
  | xs, RExp e.[list_subst lc idsubst] | ls – k ↓ 
->
  | xs, ELetRec l e | ls – S k ↓


(**  Try *)
(**  Cooling *)
| cool_try_ok vl1 e2 vl2 e3 vs xs l k:
  vl1 = length vs ->
  | xs, RExp e2.[ list_subst vs idsubst ] | l – k ↓ 
->
  | (FTry vl1 e2 vl2 e3)::xs, RValSeq vs | l – S k ↓
| cool_try_err vl1 e2 e3 class reason details xs l k:
  (* in Core Erlang exceptions always have 3 parts *)
  | xs, RExp e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] | l – k ↓
->
  | (FTry vl1 e2 3 e3)::xs, RExc (class, reason, details) | l – S k ↓
(**  Heating *)
| heat_try e1 vl1 e2 vl2 e3 xs l k:
  | (FTry vl1 e2 vl2 e3)::xs, RExp e1 | l – k ↓ 
->
  | xs, ETry e1 vl1 e2 vl2 e3 | l – S k ↓
  
(** Exceptions *)
(** Propogation *)
| prop_exc F exc xs l k:
  isPropagatable F = true ->
  | xs, RExc exc | l – k ↓ 
->
  | F::xs, RExc exc | l – S k ↓
  (* TODO: details could be appended here to the stack trace *)

(** Ends *)
| term_fin v l :
  is_result v -> | [] , v | l – 0 ↓ 
where "| fs , e | l – k ↓" := (terminates_in_k fs e l k).

Definition terminates (fs : FrameStack) (e : Redex) (l : list SideEffect) :=
  exists n, | fs, e | l – n ↓.
Notation "| fs , e | l ↓" := (terminates fs e) (at level 80).


Ltac inv_term :=
  match goal with
  | [H : | _, _ | _ – _ ↓ |- _] => inv H
  end.
Ltac deriv :=
  match goal with
  | [H : ?i < length _ |- _] => simpl in *; inv H; auto; try lia
  | [H : ?i <= length _ |- _] => simpl in *; inv H;  auto; try lia
  | [H : | _, _ | _ ↓ |- _] => inv H; try inv_val
  | [H : | _ :: _, RValSeq _ | _ ↓ |- _] => inv H; try inv_val
  | [H : | _ :: _, RExc _ | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RExp (EExp _) | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RExp (VVal _) | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RBox | _ ↓ |- _] => inv H; try inv_val
  end.

Tactic Notation "change" "clock" "to" constr(num) :=
  match goal with
  | |- | _, _ | _ – ?k ↓ => replace k with num by lia
  end.

Theorem inf_diverges :
  forall n Fs l, ~|Fs, inf| l – n↓.
Proof.
  intros. intro. induction n using Wf_nat.lt_wf_ind.
  inv H. 2: inv H1.
  * simpl in *. inv H7. inv H5. 2: { inv H. } inv H3. inv H7.
    cbn in H5. inv H5.
    unfold inf in H0. specialize (H0 (1 + k) ltac:(lia)).
    apply H0. econstructor. reflexivity. cbn. assumption.
Qed.

From CoreErlang.FrameStack Require Export
  Termination.

Theorem labeled_termination :
 forall fs e l n ,
  | fs, e | l – n ↓ ->
  | fs, e | n ↓.
Proof.
  intros fs e l n H.
  induction H; econstructor; eassumption.
Qed.

Theorem labeled_termination_2 :
 forall fs e l n ,
  | fs, e | l – n ↓ ->
  | fs, e | n ↓.
Proof.
  intros fs e l n H.
  induction H; econstructor; try assumption; try destruct ident.
  all: try now (cbn in H0; cbn; inv H0; try unfold not in H; reflexivity).
  all: try now (cbn in H0; unfold not in H; inv H0; assumption).
  * cbn in H. cbn. inv H. 


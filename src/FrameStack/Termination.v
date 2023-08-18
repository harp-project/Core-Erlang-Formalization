From CoreErlang.FrameStack Require Export SubstSemantics.

Import ListNotations.

(** This property holds true if a |fs, e| configuration terminates in k steps. *)
Definition terminates_in_k_sem (fs : FrameStack) (e : Redex) (k : nat)
  : Prop :=
  exists (res : Redex), is_result res /\ ⟨fs, e⟩ -[k]-> ⟨[], res⟩.


(** A more practical way to define termination in k steps *)
Reserved Notation "| fs , e | k ↓" (at level 80).
Inductive terminates_in_k : FrameStack -> Redex -> nat -> Prop :=

(** Cooling: single value *)
| cool_value v xs k :
  VALCLOSED v ->
  | xs, RValSeq [v] | k ↓
->
  | xs, `v | S k ↓

(************************************************)
(* heating should be separate for all complex expressions (to be
   syntax-driven).
   Only the intermediate and last steps can be extracted: *)
| step_params xs ident (el : list Exp) (vl : list Val) (v : Val) (e : Exp) k:
  | FParams ident (vl ++ [v]) el :: xs, e | k ↓
->
  | FParams ident vl (e :: el) :: xs, RValSeq [v] | S k ↓

(* technical rule to avoid duplication for 0 subexpressions : *)
| step_params_0 xs ident e (el : list Exp) vl k:
  ident <> IMap ->
  |FParams ident vl el :: xs, RExp e| k ↓
->
  |FParams ident vl (e::el) ::xs, RBox| S k ↓

(* 0 subexpression in complex expressions: *)
| cool_params_0 xs ident (vl : list Val) (res : Redex) (eff' : SideEffectList) k: 
  ident <> IMap ->
  Some (res, eff') = create_result ident vl [] -> (* TODO side effects *)
  |xs, res| k ↓
->
  |FParams ident vl [] ::xs, RBox| S k ↓

| cool_params xs ident (vl : list Val) (v : Val) (res : Redex) (eff' : SideEffectList) k:
  Some (res, eff') = create_result ident (vl ++ [v]) [] -> (* TODO side effects *)
  |xs, res| k ↓
->
  |FParams ident vl [] :: xs, RValSeq [v]| S k ↓

(************************************************)
(* Heating constructs with list subexpressions: *)
| heat_values (el : list Exp) (xs : list Frame) k:
  | (FParams IValues [] el)::xs, RBox | k ↓
->
  | xs, EValues el | S k ↓

| heat_tuple (el : list Exp) (xs : list Frame) k:
  | (FParams ITuple [] el)::xs, RBox | k ↓ 
->
  | xs, ETuple el | S k ↓

(* This is handled separately, to satisfy the invariant in FCLOSED for maps *)
| heat_map_0 (xs : list Frame) k:
  | xs, RValSeq [VMap []] | k ↓ 
->
  | xs, EMap [] | S k ↓

| heat_map (e1 e2 : Exp) (el : list (Exp * Exp)) (xs : list Frame) k:
  | (FParams IMap [] (e2 :: flatten_list el))::xs, e1 | k ↓ 
->
  | xs, EMap ((e1, e2) :: el) | S k ↓

| heat_call_mod (el : list Exp) (xs : list Frame) (m f : Exp) k :
  | FCallMod f el :: xs, m | k ↓
->
  | xs, ECall m f el | S k ↓

| heat_call_fun (el : list Exp) (xs : list Frame) (v : Val) (f : Exp) k :
  | FCallFun v el :: xs, f | k ↓
->
  | FCallMod f el :: xs, RValSeq [v] | S k ↓

| heat_call_params (el : list Exp) (xs : list Frame) (m f : Val) k:
  | (FParams (ICall m f) [] el)::xs, RBox | k ↓
->
  | FCallFun m el :: xs, RValSeq [f] | S k ↓

| heat_primop (el : list Exp) (xs : list Frame) f k:
  | (FParams (IPrimOp f) [] el)::xs, RBox | k ↓ 
->
  | xs, EPrimOp f el | S k ↓

| heat_app2 (el : list Exp) (xs : list Frame) (v : Val) k:
  | (FParams (IApp v) [] el)::xs, RBox | k ↓ 
->
  | FApp1 el :: xs, RValSeq [v] | S k ↓

(************************************************)
(**  App *)
| heat_app xs e l k:
  |FApp1 l :: xs, RExp e|  k ↓ 
->
  |xs, EApp e l| S k ↓
(**  List *)
(**  Cooling *)

| cool_cons_1 (hd : Exp) (tl : Val) xs k :
  | (FCons2 tl)::xs, RExp hd | k ↓ 
->
  | (FCons1 hd)::xs, RValSeq [tl] | S k ↓

| cool_cons_2 (hd tl : Val) xs k:
  | xs, RValSeq [VCons hd tl] | k ↓ 
->
  | (FCons2 tl)::xs, RValSeq [hd] | S k ↓

(**  Heating *)
| heat_cons (hd tl : Exp) xs k:
  | (FCons1 hd)::xs, RExp tl | k ↓ 
->
  | xs, ECons hd tl | S k ↓

(**  Let *)
(**  Cooling *)
| cool_let l e2 vs xs k:
  length vs = l ->
  | xs, RExp (e2.[ list_subst vs idsubst ]) | k ↓ 
->
  | (FLet l e2)::xs, RValSeq vs | S k ↓

(**  Heating *)
| heat_let l e1 e2 xs k:
  | (FLet l e2)::xs, RExp e1 | k ↓ 
->
  | xs, ELet l e1 e2 | S k ↓

(**  Seq *)
(**  Cooling *)
| cool_seq e2 v xs k:
  | xs, RExp e2 | k ↓ 
->
  | (FSeq e2)::xs, RValSeq [v] | S k ↓
(**  Heating *)
| heat_seq e1 e2 xs k:
  | (FSeq e2)::xs, RExp e1 | k ↓ 
->
  | xs, ESeq e1 e2 | S k ↓


(**  Fun *)
(**  Cooling *)
| cool_fun e vl xs k:
  | xs, RValSeq [ VClos [] 0 vl e ] | k ↓ 
->
  | xs, EFun vl e | S k ↓
  (* TODO : id <> 0 usually *)


(**  Case *)
(**  Heating *)
| heat_case e l xs k:
  | (FCase1 l)::xs, RExp e | k ↓ 
->
  | xs, ECase e l | S k ↓

(**  Cooling *)
(* reduction started or it is already ongoing, the first pattern matched,
   e1 the guard needs to be evaluated. vs' (the result of the pattern
   matching is stored in the frame) *)
| step_case_match lp e1 e2 l vs vs' xs k:
  match_pattern_list lp vs = Some vs' ->
  | (FCase2 vs e2.[list_subst vs' idsubst] l)::xs, RExp (e1.[list_subst vs' idsubst]) | k ↓
->
  | (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs | S k ↓
(* reduction started or it is already ongoing, the first pattern doesn't 
   match, so we check the next pattern *)
| step_case_not_match lp e1 e2 l vs xs k:
  match_pattern_list lp vs = None ->
  | (FCase1 l)::xs, RValSeq vs | k ↓ 
->
  | (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs | S k ↓

(* reduction is ongoing, the pattern matched, and the guard is true, thus 
   the reduction continues inside the given clause *)
| step_case_true vs e' l xs k:
  | xs, RExp e' | k ↓ 
->
  | (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "true") ] | S k ↓

(* reduction is ongoing, the pattern matched, and the guard is false, thus
   we check the next pattern. *)
| step_case_false vs e' l xs k:
  | (FCase1 l)::xs, RValSeq vs | k ↓ 
->
  | (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "false") ] | S k ↓

(** Exceptions *)
| cool_case_empty vs xs k:
  | xs, RExc if_clause | k ↓ 
->
  | (FCase1 [])::xs, RValSeq vs | S k ↓

(**  LetRec *)
(**  Cooling *)
(**  Heating *)
| heat_letrec l e lc xs k:
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc ->
  (* TODO: for now the funids are 0 coded in *)
  | xs, RExp e.[list_subst lc idsubst] | k ↓ 
->
  | xs, ELetRec l e | S k ↓


(**  Try *)
(**  Cooling *)
| cool_try_ok vl1 e2 vl2 e3 vs xs k:
  vl1 = length vs ->
  | xs, RExp e2.[ list_subst vs idsubst ] | k ↓ 
->
  | (FTry vl1 e2 vl2 e3)::xs, RValSeq vs | S k ↓
| cool_try_err vl1 e2 e3 class reason details xs k:
  (* in Core Erlang exceptions always have 3 parts *)
  | xs, RExp e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] | k ↓
->
  | (FTry vl1 e2 3 e3)::xs, RExc (class, reason, details) | S k ↓
(**  Heating *)
| heat_try e1 vl1 e2 vl2 e3 xs k:
  | (FTry vl1 e2 vl2 e3)::xs, RExp e1 | k ↓ 
->
  | xs, ETry e1 vl1 e2 vl2 e3 | S k ↓
  
(** Exceptions *)
(** Propogation *)
| prop_exc F exc xs k:
  isPropagatable F = true ->
  | xs, RExc exc | k ↓ 
->
  | F::xs, RExc exc | S k ↓
  (* TODO: details could be appended here to the stack trace *)

(** Ends *)
| term_fin v :
  is_result v -> | [] , v | 0 ↓ 
where "| fs , e | k ↓" := (terminates_in_k fs e k).

Definition terminates (fs : FrameStack) (e : Redex) :=
  exists n, | fs, e | n ↓.
Notation "| fs , e | ↓" := (terminates fs e) (at level 80).


Ltac inv_term :=
  match goal with
  | [H : | _, _ | _ ↓ |- _] => inv H
  end.
Ltac deriv :=
  match goal with
  | [H : ?i < length _ |- _] => simpl in *; inv H; auto; try lia
  | [H : ?i <= length _ |- _] => simpl in *; inv H;  auto; try lia
  | [H : | _, _ | ↓ |- _] => inv H; try inv_val
  | [H : | _ :: _, RValSeq _ | _ ↓ |- _] => inv H; try inv_val
  | [H : | _ :: _, RExc _ | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RExp (EExp _) | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RExp (VVal _) | _ ↓ |- _] => inv H; try inv_val
  | [H : | _, RBox | _ ↓ |- _] => inv H; try inv_val
  end.

Tactic Notation "change" "clock" "to" constr(num) :=
  match goal with
  | |- | _, _ | ?k ↓ => replace k with num by lia
  end.

Theorem inf_diverges :
  forall n Fs, ~|Fs, inf| n↓.
Proof.
  intros. intro. induction n using Wf_nat.lt_wf_ind.
  inv H. 2: inv H1.
  * simpl in *. inv H6. inv H4. 2: { inv H. } inv H3. inv H6.
    cbn in H5. inv H5.
    unfold inf in H0. specialize (H0 (1 + k) ltac:(lia)).
    apply H0. econstructor. reflexivity. cbn. assumption.
Qed.


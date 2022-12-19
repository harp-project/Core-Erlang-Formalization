Require Export SubstSemantics.

Import ListNotations.

(** This property holds true if a ⟨fs, e⟩ configuration terminates. So it reaches a point with an empty FrameStack *)
Definition terminates_sem (fs : FrameStack) (e : ProgResult) : Prop :=
  exists v, ⟨fs, e⟩ -->* v.

(** This property holds true if a ⟨fs, e⟩ configuration terminates in k steps. So it reaches a point with an empty FrameStack in k steps *)
Definition terminates_in_k_sem (fs : FrameStack) (e : ProgResult) (k : nat) : Prop :=
  (*
  (exists v, ⟨fs, e⟩ -[k]-> ⟨ [], ValSeqRes v⟩)
  \/
  (exists exc, ⟨fs, e⟩ -[k]-> ⟨ [], ExcRes exc⟩).
  *)
  (exists r, ⟨fs, e⟩ -[k]-> ⟨ [], r⟩ /\ ((exists v, r = ValSeqRes v) \/ (exists exc, r = ExcRes exc)))
  .

(* TODO: is this needed? *)
(*Open Scope nat_scope. *)

(** A more practical way to define termination in k steps *)
Reserved Notation "| fs , e | k ↓" (at level 80).
Inductive terminates_in_k : FrameStack -> ProgResult -> nat -> Prop :=

(** Ends *)
| term_fin_val vs :
  | [] , ValSeqRes vs | 0 ↓
| term_fin_exc exc :
  | [] , ExcRes exc | 0 ↓


(** Value ExpRess**)
(**  Cooling *)
| term_cool_value v k fs:
  | fs , ValSeqRes [v] | k ↓
  ->
  | fs , ExpRes (Val v) | (S k) ↓


(**  Values *)
(**  Cooling *)
| term_cool_Values_empty k fs :
  | fs , ValSeqRes [] | k ↓
  ->
  | fs , ExpRes (Exp (EValues [])) | (S k) ↓

| term_cool_Values_1 vl e el v k fs :
  | (FValues (vl++[v]) el)::fs , ExpRes e | k ↓
  ->
  | (FValues vl (e::el))::fs , ValSeqRes [v] | (S k) ↓

| term_cool_Values_2 vl v k fs :
  | fs , ValSeqRes (vl++[v]) | k ↓
  ->
  | (FValues vl [])::fs , ValSeqRes [v] | (S k) ↓

(**  Heating *)
| term_heat_Values e el k fs:
  | (FValues [] el)::fs , ExpRes e | k ↓
  ->
  | fs , ExpRes (Exp (EValues (e::el))) | (S k) ↓


(**  Cons *)
(**  Cooling *)
| term_cool_Cons_1 hd tl k fs :
  | (FCons2 tl)::fs , ExpRes hd | k ↓
  ->
  | (FCons1 hd)::fs , ValSeqRes [tl] | (S k) ↓

| term_cool_Cons_2 hd tl k fs :
  | fs ,ValSeqRes [VCons hd tl] | k ↓
  ->
  | (FCons2 tl)::fs , ValSeqRes [hd] | (S k) ↓

(**  Heating *)
| term_heat_Cons hd tl k fs :
  | (FCons1 hd)::fs , ExpRes tl | k ↓
  ->
  | fs , ExpRes (Exp (ECons hd tl)) | (S k) ↓


(**  Tuple *)
(**  Cooling *)
| term_cool_Tuple_empty k fs :
  | fs , ValSeqRes [ VTuple [] ] | k ↓
  ->
  | fs , ExpRes (Exp (ETuple [])) | (S k) ↓

| term_cool_Tuple_1 vl e el v k fs :
  | (FTuple (vl++[v]) el)::fs , ExpRes e | k ↓
  ->
  | (FTuple vl (e::el))::fs , ValSeqRes [v] | (S k) ↓

| term_cool_Tuple_2 vl v k fs :
  | fs , ValSeqRes [ VTuple (vl++[v]) ] | k ↓
  ->
  | (FTuple vl [])::fs , ValSeqRes [v] | (S k) ↓

(**  Heating *)
| term_heat_Tuple e el k xs:
  | (FTuple [] el)::xs , ExpRes e | k ↓
  ->
  | xs , ExpRes (Exp (ETuple (e::el))) | (S k) ↓


(**  Map *)
(**  Cooling *)
| term_cool_Map_empty k fs :
    | fs , ValSeqRes [ VMap [] ] | k ↓
  ->
  | fs , ExpRes (Exp (EMap [])) | (S k) ↓

| term_cool_Map_1  vl sn fs el k xs :
  | (FMap2 vl fs el)::xs , ExpRes sn | k ↓
  ->
  | (FMap1 vl sn el)::xs , ValSeqRes [fs] | (S k) ↓

| term_cool_Map_2  vl fs sn fs' sn' el k xs :
  | (FMap1 (vl++[(fs,sn)]) sn' el)::xs , ExpRes fs' | k ↓
  ->
  | (FMap2 vl fs ((fs',sn')::el))::xs , ValSeqRes [sn] | (S k) ↓

| term_cool_Map_3  vl fs sn k xs :
  | xs , ValSeqRes [ VMap (vl++[(fs,sn)]) ] | k ↓
  ->
  | (FMap2 vl fs [])::xs , ValSeqRes [sn] | (S k) ↓

(**  Heating *)
| term_heat_Map fs sn el k xs :
  | (FMap1 [] sn el)::xs , ExpRes fs | k ↓
  ->
  | xs , ExpRes (Exp (EMap ((fs,sn)::el))) | (S k) ↓


(**  PrimOp *) (* "inl res" is a ValueExpRes*)
(**  Cooling *)
| term_cool_PrimOp_empty f k xs res eff :
  eval f [] [] = (inl res, eff) ->
  | xs , ValSeqRes res | k ↓
  ->
  | xs , ExpRes(Exp (EPrimOp f [])) | (S k) ↓

| term_cool_PrimOp_1 f vl e el v k xs :
  | (FPrimOp f (vl++[v]) el)::xs , ExpRes e | k ↓
  ->
  | (FPrimOp f vl (e::el))::xs , ValSeqRes [v] | (S k) ↓

| term_cool_PrimOp_2 f vl v k xs res eff :
  eval f (vl++[v]) [] = (inl res, eff) ->
  | xs , ValSeqRes res | k ↓
  ->
  | (FPrimOp f vl [])::xs , ValSeqRes [v] | (S k) ↓

(**  Heating *)
| term_heat_PrimOp f e el k xs :
  | (FPrimOp f [] el)::xs , ExpRes e | k ↓
  ->
  | xs , ExpRes (Exp (EPrimOp f (e::el))) | (S k) ↓

(** Exceptions *)
| term_err_PrimOp_1 f k xs exc eff : (* in this case there were no parameters to evaluate *)
  eval f [] [] = (inr exc, eff) ->
  | xs , ExcRes exc | k ↓
  ->
  | xs , ExpRes (Exp (EPrimOp f [])) | (S k) ↓

| term_err_PrimOp_2 f vl v k xs exc eff : (* there were parameters *)
  eval f (vl++[v]) [] = (inr exc, eff) ->
  | xs , ExcRes exc | k ↓
  ->
  | (FPrimOp f vl [])::xs , ValSeqRes [v] | (S k) ↓


(**  Let *)
(**  Cooling *)
| term_cool_Let l e2 vs k xs :
  length vs = l ->
  | xs , ExpRes (e2.[ list_subst vs idsubst ]) | k ↓
  ->
  | (FLet l e2)::xs , ValSeqRes vs | (S k) ↓
(**  Heating *)
| term_heat_Let l e1 e2 k xs :
  | (FLet l e2)::xs , ExpRes e1 | k ↓
  ->
  | xs , ExpRes (Exp (ELet l e1 e2)) | (S k) ↓


(**  Seq *)
(**  Cooling *)
| term_cool_Seq e2 v k xs :
  | xs , ExpRes e2 | k ↓
  ->
  | (FSeq e2)::xs , ValSeqRes [v] | (S k) ↓
(**  Heating *)
| term_heat_Seq e1 e2 k xs :
  | (FSeq e2)::xs , ExpRes e1 | k ↓
  ->
  | xs , ExpRes (Exp (ESeq e1 e2)) | (S k) ↓


(**  Fun *)
(**  Cooling *)
| term_cool_fun e vl k xs :
  | xs , ValSeqRes [ VClos [] 0 vl e ] | k ↓        (*TODO : id not 0*)
  ->
  | xs , ExpRes (Exp (EFun vl e)) | (S k) ↓


(**  Call *)
(**  Cooling *)
| term_cool_Call_empty f k xs res eff :
  eval f [] [] = (inl res, eff) ->
  | xs , ValSeqRes res | k ↓
  ->
  | xs , ExpRes (Exp (ECall f [])) | (S k) ↓

| term_cool_Call_1 f vl e el v k xs :
  | (FCall f (vl++[v]) el)::xs , ExpRes e | k ↓
  ->
  | (FCall f vl (e::el))::xs , ValSeqRes [v] | (S k) ↓

| term_cool_Call_2 f vl v k xs res eff :
  eval f (vl++[v]) [] = (inl res, eff) ->
  | xs , ValSeqRes res | k ↓
  ->
  | (FCall f vl [])::xs , ValSeqRes [v] | (S k) ↓

(**  Heating *)
| term_heat_Call f e el k xs :
  | (FCall f [] el)::xs , ExpRes e | k ↓
  ->
  | xs , ExpRes (Exp (ECall f (e::el))) | (S k) ↓

(** Exceptions *)
| term_err_Call_1 f exc eff k xs : (* in this case there were no parameters to evaluate *)
  eval f [] [] = (inr exc, eff) ->
  | xs , ExcRes exc | k ↓
  ->
  | xs , ExpRes (Exp (ECall f [])) | (S k) ↓

| term_err_Call_2 f v vl exc eff k xs : (* there were parameters *)
  eval f (vl++[v]) [] = (inr exc, eff) ->
  | xs , ExcRes exc | k ↓
  ->
  | (FCall f vl [])::xs , ValSeqRes [v] | (S k) ↓


(**  App *) (* in "EApp e el" e needs to evaluate to a VClos but it will only be checked when el is done *)
(**  Cooling *)
| term_cool_App_empty vl' ext id e k xs :
  convert_to_closlist ext = vl' ->
  | xs , ExpRes e.[list_subst (vl') idsubst] | k ↓
  ->
  | (FApp1 [])::xs , ValSeqRes [(VClos ext id 0 e)] | (S k) ↓

| term_cool_App_1 e el v k xs :
  | (FApp2 v [] el)::xs , ExpRes e | k ↓
  ->
  | (FApp1 (e::el))::xs , ValSeqRes [v] | (S k) ↓

| term_cool_App_2a v' vl e el v k xs :
  | (FApp2 v' (vl++[v]) el)::xs , ExpRes e | k ↓
  ->
  | (FApp2 v' vl (e::el))::xs , ValSeqRes [v] | (S k) ↓

| term_cool_App_2b vl' ext id vc e' vl v k xs :
  vc = (length (vl) + 1) ->
  convert_to_closlist ext = vl' ->
  | xs , ExpRes (e'.[list_subst (vl'++(vl++[v])) idsubst]) | k ↓
  ->
  | (FApp2 (VClos ext id vc e') vl [])::xs , ValSeqRes [v] | (S k) ↓

(**  Heating *)
| term_heat_App e el k xs :
  | (FApp1 el)::xs , ExpRes e | k ↓
  ->
  | xs , ExpRes (Exp (EApp e el)) | (S k) ↓

(** Exceptions *) (*TODO badarity FApp1 version*)
| term_err_App_badariry_1 ext id vc e k xs :
  vc <> 0 ->
  | xs , ExcRes (badarity (VClos ext id vc e)) | k ↓
  ->
  | (FApp1 [])::xs , ValSeqRes [(VClos ext id vc e)] | (S k) ↓

| term_err_App_badariry_2 ext id vc e' vl k xs v :
  vc <> (length (vl) + 1) ->
  | xs , ExcRes (badarity (VClos ext id vc e')) | k ↓
  ->
  | (FApp2 (VClos ext id vc e') vl [])::xs , ValSeqRes [v] | (S k) ↓

| term_err_App_noclos_1 v k xs : (* when it had no other expressions to evalate ([] case) *)
  (forall ext id vc e, v <> (VClos ext id vc e)) ->
  | xs , ExcRes (badfun v) | k ↓
  ->
  | (FApp1 [])::xs , ValSeqRes [v] | (S k) ↓

| term_err_App_noclos_2 v' vl v k xs : (* when it had expressions to evaluate *)
  (forall ext id vc e', v' <> (VClos ext id vc e')) ->
  | xs , ExcRes (badfun v') | k ↓
  ->
  | (FApp2 v' vl [])::xs , ValSeqRes [v] | (S k) ↓


(**  Case *)
(**  Cooling *)
| term_cool_Case_1m lp e1 e2 l vs vs' k xs :
  match_pattern_list lp vs = Some vs' ->
  | (FCase2 vs lp e2 l vs')::xs , ExpRes (e1.[list_subst (vs') idsubst]) | k ↓
  ->
  | (FCase1 ((lp,e1,e2)::l))::xs , ValSeqRes vs | (S k) ↓

| term_cool_Case_1nm lp e1 e2 l vs k xs :
  match_pattern_list lp vs = None ->
  | (FCase1 l)::xs , ValSeqRes vs | k ↓
  ->
  | (FCase1 ((lp,e1,e2)::l))::xs , ValSeqRes vs | (S k) ↓

| term_cool_Case_2mt vs lp e' l vs' k xs :
  | xs , ExpRes (e'.[list_subst (vs') idsubst]) | k ↓
  ->
  | (FCase2 vs lp e' l vs')::xs , ValSeqRes [ VLit (Atom "true") ] | (S k) ↓

| term_cool_Case_2mf vs lp' e' l vs' k xs :
  | (FCase1 l)::xs , ValSeqRes vs | k ↓
  ->
  | (FCase2 vs lp' e' l vs')::xs , ValSeqRes [ VLit (Atom "false") ] | (S k) ↓

(**  Heating *)
| term_heat_Case e l k xs:
  | (FCase1 l)::xs , ExpRes e | k ↓
  ->
  | xs , ExpRes (Exp (ECase e l)) | (S k) ↓

(** Exceptions *)
| term_err_Case_empty vs k xs:
  | xs , ExcRes if_clause | k ↓
  ->
  | (FCase1 [])::xs , ValSeqRes vs | (S k) ↓


(**  LetRec *)
(**  Heating *)
| term_heat_LetRec l e lc k xs :
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc -> (*TODO: for now the funids are 0 coded in *)
  | xs , ExpRes e.[list_subst (lc) idsubst] | k ↓
  ->
  | xs , ExpRes (Exp (ELetRec l e)) | (S k) ↓


(**  Try *)
(**  Cooling *)
| term_cool_Try_ok vl1 e2 vl2 e3 vs k xs:
  vl1 = length vs ->
  | xs , ExpRes e2.[ list_subst vs idsubst ] | k ↓
  ->
  | (FTry vl1 e2 vl2 e3)::xs , ValSeqRes vs | (S k) ↓

| term_cool_Try_err vl1 e2 e3 class reason details k xs:  (* in CErlang exceptions always have 3 part*)
  | xs , ExpRes e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] | k ↓
  ->
  | (FTry vl1 e2 3 e3)::xs , ExcRes (class, reason, details) | (S k) ↓

(**  Heating *)
| term_heat_Try e1 vl1 e2 vl2 e3 k xs :
  | (FTry vl1 e2 vl2 e3)::xs , ExpRes e1 | k ↓
  ->
  | xs , ExpRes (Exp (ETry e1 vl1 e2 vl2 e3)) | (S k) ↓


(** Exceptions *)
(** Propogation *)
| term_propogate_Exception frame exc k xs :
  (forall vl1 e2 vl2 e3 , (FTry vl1 e2 vl2 e3) <> frame)->
  | xs , ExcRes exc | k ↓
  ->
  | (frame)::xs , ExcRes exc | (S k) ↓

where "| fs , e | k ↓" := (terminates_in_k fs e k).

(** A more practical way to define termination *)
Definition terminates (fs : FrameStack) (e : ProgResult) := exists n, | fs, e | n ↓.
Notation "| fs , e | ↓" := (terminates fs e) (at level 80).


Theorem terminates_in_k_eq_terminates_in_k_sem :
  forall k e fs, terminates_in_k_sem fs e k <-> | fs, e | k ↓.
Proof.
  
  intros. split; revert e fs.
  * induction k.
    - intros. destruct H. destruct H. inversion H. subst. destruct H0.
      + destruct H0. subst. constructor.
      + destruct H0. subst. constructor.
    - intros. destruct H. destruct H. inversion H. subst. specialize (IHk e' fs').
      (* pose proof (conj H5 H0). Check ex_intro. apply ex_intro with (x := x) in H1. *)
      assert (terminates_in_k_sem fs' e' k).
      {
        unfold terminates_in_k_sem. exists x. split; auto.
      }
      specialize (IHk H1). clear H H0 H5 H1. inversion H2; subst.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + eapply term_cool_PrimOp_empty.
        ** exact H.
        ** auto.
      + constructor. auto.
      + econstructor.
        ** exact H.
        ** auto.
      + constructor. auto.
      + eapply term_err_PrimOp_1.
        ** exact H.
        ** auto.
      + eapply term_err_PrimOp_2.
        ** exact H.
        ** auto.
      + constructor.
        ** auto.
        ** auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + eapply term_cool_Call_empty.
        ** exact H.
        ** auto.
      + eapply term_cool_Call_1. auto.
      + eapply term_cool_Call_2.
        ** exact H.
        ** auto.
      + constructor. auto.
      + eapply term_err_Call_1.
        ** exact H.
        ** auto.
      + eapply term_err_Call_2.
        ** exact H.
        ** auto.
      + Check term_cool_App_empty. apply (term_cool_App_empty (convert_to_closlist ext)).
        ** auto.
        ** auto.
      + constructor. auto.
      + constructor. auto.
      + Check term_cool_App_2b. apply (term_cool_App_2b (convert_to_closlist ext)).
        ** auto.
        ** auto.
        ** auto.
      + constructor. auto.
      + apply (term_err_App_badariry_1).
        ** auto.
        ** auto.
      + apply term_err_App_badariry_2.
        ** auto.
        ** auto.
      + apply term_err_App_noclos_1.
        ** auto.
        ** auto.
      + apply term_err_App_noclos_2.
        ** auto.
        ** auto.
      + eapply term_cool_Case_1m.
        ** exact H.
        ** auto.
      + apply term_cool_Case_1nm.
        ** auto.
        ** auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + constructor. auto.
      + Check term_heat_LetRec. eapply (term_heat_LetRec _ _ (convert_to_closlist (map (fun '(x0, y) => (0, x0, y)) l))).
        ** auto.
        ** auto.
      + eapply term_cool_Try_ok.
        ** auto.
        ** auto.
      + constructor. auto.
      + constructor. auto.
      + eapply term_propogate_Exception.
        ** auto.
        ** auto.
  * intros. induction H.
    - unfold terminates_in_k_sem. exists (ValSeqRes vs). split.
      + constructor.
      + left. exists vs. auto.
    - unfold terminates_in_k_sem. exists (ExcRes exc). split.
      + constructor.
      + right. exists exc. auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x.
      split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** econstructor. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** econstructor. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** eapply err_PrimOp_1. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** eapply err_PrimOp_2. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** constructor. auto.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** eapply cool_Call_empty. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** eapply cool_Call_2. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** eapply err_Call_1. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** eapply err_Call_2. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** eapply cool_App_empty. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H2. exists x. split.
      + econstructor.
        ** constructor.
           -- auto.
           -- exact H0.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** constructor. auto.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** apply err_App_badariry_2. auto.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** constructor. auto.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** constructor. auto.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** apply cool_Case_1m. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** apply cool_Case_1nm. auto.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** constructor. exact H.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** constructor. auto.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H0. exists x. split.
      + econstructor.
        ** constructor.
        ** auto.
      + auto.
    - unfold terminates_in_k_sem. destruct IHterminates_in_k. destruct H1. exists x. split.
      + econstructor.
        ** constructor. auto.
        ** auto.
      + auto.
Qed.






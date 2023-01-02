Require Export Frames.
Require Export Exceptions.
Require Export Auxiliaries.

Import ListNotations.

Definition lit_eqb (l1 l2 : Literal) : bool :=
match l1, l2 with
 | Atom s, Atom s2 => String.eqb s s2
 | Integer z , Integer z2  => Z.eqb z z2
 | _     , _       => false
end.

Lemma lit_eqb_eq : forall l1 l2, lit_eqb l1 l2 = true <-> l1 = l2.
Proof.
  destruct l1, l2; split; intros; subst; auto; simpl in H; try congruence.
  * apply eqb_eq in H. now inversion H.
  * inversion H. subst. simpl. now rewrite eqb_refl.
  * apply Z.eqb_eq in H. now inversion H.
  * inversion H. subst. simpl. now rewrite Z.eqb_refl.
Qed.

Lemma lit_eqb_refl : forall l, lit_eqb l l = true.
Proof.
  intro. rewrite lit_eqb_eq. reflexivity.
Qed.


Definition convert_to_closlist (l : list (nat * nat * Expression)) : (list ValueExpression) :=
map (fun '(id,vc,e) => (VClos l id vc e)) l.


Inductive ProgResult : Type :=
| ExpRes (e : Expression) (* RExp *) (* Expression *)
| ValSeqRes (vs : list ValueExpression) (* RValSeq *) (* ValueSequence *)
| ExcRes (e : Exception) (* RExc *) (* Exception *)
.

Reserved Notation "'PROG' Γ ⊢ e" (at level 69, no associativity).
Inductive ProgResultScope : ProgResult -> nat -> Prop :=
| expScope Γ e : EXP Γ ⊢ e -> PROG Γ ⊢ (ExpRes e)
| excScope Γ class reason details : VAL Γ ⊢ reason -> VAL Γ ⊢ details
                                    -> PROG Γ ⊢ (ExcRes (class,reason,details))
| valSeqScope Γ vl : (forall i, i < (length vl) -> VAL Γ ⊢ (nth i vl (VNil))) -> PROG Γ ⊢ (ValSeqRes vl)
where "'PROG' Γ ⊢ e" := (ProgResultScope e Γ).

Notation "'PROGCLOSED' v" := (PROG 0 ⊢ v) (at level 5).


(* Definition list_subst (l : list ValueExpression) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l. *)

Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).

Inductive step : FrameStack -> ProgResult -> FrameStack -> ProgResult -> Prop :=
(**  Reduction rules *)

(** Value Expressions**)
(**  Cooling *)
| cool_value v xs:
  ⟨ xs, ExpRes (Val v) ⟩ --> ⟨ xs, ValSeqRes [v] ⟩


(**  Values *)
(**  Cooling *)
| cool_Values_empty xs :
  ⟨ xs, ExpRes (Exp (EValues [])) ⟩ --> ⟨ xs, ValSeqRes [] ⟩
| cool_Values_1 vl e el v xs :
  ⟨ (FValues vl (e::el))::xs, ValSeqRes [v]⟩ --> ⟨ (FValues (vl++[v]) el)::xs, ExpRes e ⟩
| cool_Values_2 vl v xs :
  ⟨ (FValues vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ValSeqRes (vl++[v]) ⟩
(**  Heating *)
| heat_Values e el xs:
  ⟨ xs, ExpRes (Exp (EValues (e::el))) ⟩ --> ⟨ (FValues [] el)::xs, ExpRes e ⟩


(**  Cons *)
(**  Cooling *)
| cool_Cons_1 hd tl xs :
  ⟨ (FCons1 hd)::xs, ValSeqRes [tl] ⟩ --> ⟨ (FCons2 tl)::xs, ExpRes hd ⟩
| cool_Cons_2 hd tl xs :
  ⟨ (FCons2 tl)::xs, ValSeqRes [hd] ⟩ --> ⟨ xs, ValSeqRes [VCons hd tl] ⟩
(**  Heating *)
| heat_Cons hd tl xs :
  ⟨ xs, ExpRes (Exp (ECons hd tl)) ⟩ --> ⟨ (FCons1 hd)::xs, ExpRes tl ⟩

(**  Tuple *)
(**  Cooling *)
| cool_Tuple_empty xs :
  ⟨ xs, ExpRes (Exp (ETuple [])) ⟩ --> ⟨ xs, ValSeqRes [ VTuple [] ] ⟩
| cool_Tuple_1 vl e el v xs :
  ⟨ (FTuple vl (e::el))::xs, ValSeqRes [v] ⟩ --> ⟨ (FTuple (vl++[v]) el)::xs, ExpRes e ⟩
| cool_Tuple_2 vl v xs :
  ⟨ (FTuple vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ValSeqRes [ VTuple (vl++[v]) ] ⟩
(**  Heating *)
| heat_Tuple e el xs:
  ⟨ xs, ExpRes (Exp (ETuple (e::el))) ⟩ --> ⟨ (FTuple [] el)::xs, ExpRes e ⟩


(**  Map *)
(**  Cooling *)
| cool_Map_empty xs :
  ⟨ xs, ExpRes (Exp (EMap [])) ⟩ --> ⟨ xs, ValSeqRes [ VMap [] ] ⟩
| cool_Map_1  vl sn fs el xs :
  ⟨ (FMap1 vl sn el)::xs, ValSeqRes [fs] ⟩ --> ⟨ (FMap2 vl fs el)::xs, ExpRes sn ⟩
| cool_Map_2  vl fs sn fs' sn' el xs :
  ⟨ (FMap2 vl fs ((fs',sn')::el))::xs, ValSeqRes [sn] ⟩ --> ⟨ (FMap1 (vl++[(fs,sn)]) sn' el)::xs, ExpRes fs' ⟩
| cool_Map_3  vl fs sn xs :
  ⟨ (FMap2 vl fs [])::xs, ValSeqRes [sn] ⟩ --> ⟨ xs, ValSeqRes [ VMap (vl++[(fs,sn)]) ] ⟩
(**  Heating *)
| heat_Map fs sn el xs :
  ⟨ xs, ExpRes (Exp (EMap ((fs,sn)::el))) ⟩ --> ⟨ (FMap1 [] sn el)::xs, ExpRes fs ⟩


(**  PrimOp *) (*TODO: Auxiliaries *) (* "inl res" is a ValueExpression*)
(*TODO: Auxiliaries.ValueSequence -> list ValueExpression, is this conversion ok?*)
(**  Cooling *)
| cool_PrimOp_empty f xs res eff :
  eval f [] [] = (inl res, eff) ->
  ⟨ xs, ExpRes (Exp (EPrimOp f [])) ⟩ --> ⟨ xs, ValSeqRes res ⟩
| cool_PrimOp_1 f vl e el v xs :
  ⟨ (FPrimOp f vl (e::el))::xs, ValSeqRes [v] ⟩ --> ⟨ (FPrimOp f (vl++[v]) el)::xs, ExpRes e ⟩
| cool_PrimOp_2 f vl v xs res eff :
  eval f (vl++[v]) [] = (inl res, eff) ->
  ⟨ (FPrimOp f vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ValSeqRes res ⟩
(**  Heating *)
| heat_PrimOp f e el xs :
  ⟨ xs, ExpRes (Exp (EPrimOp f (e::el))) ⟩ --> ⟨ (FPrimOp f [] el)::xs, ExpRes e ⟩
(** Exceptions *)
| err_PrimOp_1 f xs exc eff : (* in this case there were no parameters to evaluate *)
  eval f [] [] = (inr exc, eff) ->
  ⟨ xs, ExpRes (Exp (EPrimOp f [])) ⟩ --> ⟨ xs, ExcRes exc ⟩
| err_PrimOp_2 f vl v xs exc eff : (* there were parameters *)
  eval f (vl++[v]) [] = (inr exc, eff) ->
  ⟨ (FPrimOp f vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ExcRes exc ⟩

(**  Let *)
(**  Cooling *)
| cool_Let l e2 vs xs :
  length vs = l ->
  ⟨ (FLet l e2)::xs, ValSeqRes vs ⟩ --> ⟨ xs, ExpRes (e2.[ list_subst vs idsubst ]) ⟩
(**  Heating *)
| heat_Let l e1 e2 xs :
  ⟨ xs, ExpRes (Exp (ELet l e1 e2)) ⟩ --> ⟨ (FLet l e2)::xs, ExpRes e1 ⟩


(**  Seq *)
(**  Cooling *)
| cool_Seq e2 v xs :
  ⟨ (FSeq e2)::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ExpRes e2 ⟩
(**  Heating *)
| heat_Seq e1 e2 xs :
  ⟨ xs, ExpRes (Exp (ESeq e1 e2)) ⟩ --> ⟨ (FSeq e2)::xs, ExpRes e1 ⟩


(**  Fun *)
(**  Cooling *)
| cool_fun e vl xs :
  ⟨ xs, ExpRes (Exp (EFun vl e)) ⟩ --> ⟨ xs, ValSeqRes [ VClos [] 0 vl e ] ⟩ (*TODO : id not 0*)


(**  Call *)
(**  Cooling *)
| cool_Call_empty f xs res eff :
  eval f [] [] = (inl res, eff) ->
  ⟨ xs, ExpRes (Exp (ECall f [])) ⟩ --> ⟨ xs, ValSeqRes res ⟩
| cool_Call_1 f vl e el v xs :
  ⟨ (FCall f vl (e::el))::xs, ValSeqRes [v] ⟩ --> ⟨ (FCall f (vl++[v]) el)::xs, ExpRes e ⟩
| cool_Call_2 f vl v xs res eff :
  eval f (vl++[v]) [] = (inl res, eff) ->
  ⟨ (FCall f vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ValSeqRes res ⟩
(**  Heating *)
| heat_Call f e el xs :
  ⟨ xs, ExpRes (Exp (ECall f (e::el))) ⟩ --> ⟨ (FCall f [] el)::xs, ExpRes e ⟩
(** Exceptions *)
| err_Call_1 f exc eff xs : (* in this case there were no parameters to evaluate *)
  eval f [] [] = (inr exc, eff) ->
  ⟨ xs, ExpRes (Exp (ECall f [])) ⟩ --> ⟨ xs, ExcRes exc ⟩
| err_Call_2 f v vl exc eff xs : (* there were parameters *)
  eval f (vl++[v]) [] = (inr exc, eff) ->
  ⟨ (FCall f vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ExcRes exc ⟩

(**  App *) (* On paper *) (* in "EApp e el" e needs to evaluate to a VClos but it will only be checked when el is done *)
(**  Cooling *) (*TODO: empty FApp1 *)
| cool_App_empty vl' ext id e xs :
  convert_to_closlist ext = vl' ->
  ⟨ (FApp1 [])::xs, ValSeqRes [(VClos ext id 0 e)] ⟩ --> ⟨ xs, ExpRes e.[list_subst (vl') idsubst] ⟩
| cool_App_1 e el v xs :
  ⟨ (FApp1 (e::el))::xs, ValSeqRes [v] ⟩ --> ⟨ (FApp2 v [] el)::xs, ExpRes e ⟩
| cool_App_2a v' vl e el v xs :
  ⟨ (FApp2 v' vl (e::el))::xs, ValSeqRes [v] ⟩ --> ⟨ (FApp2 v' (vl++[v]) el)::xs, ExpRes e ⟩
| cool_App_2b vl' ext id vc e' vl v xs :
  vc = (length (vl) + 1) ->
  convert_to_closlist ext = vl' ->
  ⟨ (FApp2 (VClos ext id vc e') vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ExpRes (e'.[list_subst (vl'++(vl++[v])) idsubst]) ⟩
(**  Heating *)
| heat_App e el xs :
  ⟨ xs, ExpRes (Exp (EApp e el)) ⟩ --> ⟨ (FApp1 el)::xs, ExpRes e ⟩
(** Exceptions *) (*TODO badarity FApp1 version*)
| err_App_badariry_1 ext id vc e xs :
  vc <> 0 ->
  ⟨ (FApp1 [])::xs, ValSeqRes [(VClos ext id vc e)] ⟩ --> ⟨ xs, ExcRes (badarity (VClos ext id vc e)) ⟩
| err_App_badariry_2 ext id vc e' vl xs v :
  vc <> (length (vl) + 1) ->
  ⟨ (FApp2 (VClos ext id vc e') vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ExcRes (badarity (VClos ext id vc e')) ⟩
| err_App_noclos_1 v xs : (* when it had no other expressions to evalate ([] case) *)
  (forall ext id vc e, v <> (VClos ext id vc e)) ->
  ⟨ (FApp1 [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ExcRes (badfun v) ⟩
| err_App_noclos_2 v' vl v xs : (* when it had expressions to evaluate *)
  (forall ext id vc e', v' <> (VClos ext id vc e')) ->
  ⟨ (FApp2 v' vl [])::xs, ValSeqRes [v] ⟩ --> ⟨ xs, ExcRes (badfun v') ⟩


(**  Case *)
(**  Cooling *)
(* eval started or ongoing, the first pattern matched, e1 the guard needs to be evaluated *)
| cool_Case_1m lp e1 e2 l vs vs' xs :
  match_pattern_list lp vs = Some vs' ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, ValSeqRes vs ⟩ --> ⟨ (FCase2 vs lp e2 l vs')::xs, ExpRes (e1.[list_subst (vs') idsubst]) ⟩
(* eval started or ongoing, the first pattern doesn't match, so case jumps to the next option where the pattern needs to match first. *)
| cool_Case_1nm lp e1 e2 l vs xs :
  match_pattern_list lp vs = None ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, ValSeqRes vs ⟩ --> ⟨ (FCase1 l)::xs, ValSeqRes vs ⟩
(* eval ongoing, the last pattern matched, the guard is true, so case ends*)
| cool_Case_2mt vs lp e' l vs' xs :
  ⟨ (FCase2 vs lp e' l vs')::xs, ValSeqRes [ VLit (Atom "true") ] ⟩ --> ⟨ xs, ExpRes (e'.[list_subst (vs') idsubst]) ⟩
(* eval ongoing, the last pattern matched, the guard is false, so case jumps to the next option where the pattern needs to match first. *)
| cool_Case_2mf vs lp' e' l vs' xs :
  ⟨ (FCase2 vs lp' e' l vs')::xs, ValSeqRes [ VLit (Atom "false") ] ⟩ --> ⟨ (FCase1 l)::xs, ValSeqRes vs ⟩
(**  Heating *)
| heat_Case e l xs:
  ⟨ xs, ExpRes (Exp (ECase e l)) ⟩ --> ⟨ (FCase1 l)::xs, ExpRes e ⟩
(** Exceptions *)
| err_Case_empty vs xs:
  ⟨ (FCase1 [])::xs, ValSeqRes vs ⟩ --> ⟨ xs, ExcRes if_clause ⟩

(**  LetRec *)
(**  Cooling *)
(**  Heating *)
| heat_LetRec l e lc xs :
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc -> (*TODO: for now the funids are 0 coded in *)
  ⟨ xs, ExpRes (Exp (ELetRec l e)) ⟩ --> ⟨ xs, ExpRes e.[list_subst (lc) idsubst] ⟩


(**  Try *)
(**  Cooling *)
| cool_Try_ok vl1 e2 vl2 e3 vs xs:
  vl1 = length vs ->
  ⟨ (FTry vl1 e2 vl2 e3)::xs, ValSeqRes vs ⟩ --> ⟨ xs, ExpRes e2.[ list_subst vs idsubst ] ⟩
| cool_Try_err vl1 e2 e3 class reason details xs:  (* in CErlang exceptions always have 3 part*)
  ⟨ (FTry vl1 e2 3 e3)::xs, ExcRes (class, reason, details) ⟩ --> ⟨ xs, ExpRes e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] ⟩
(**  Heating *)
| heat_Try e1 vl1 e2 vl2 e3 xs :
  ⟨ xs, ExpRes (Exp (ETry e1 vl1 e2 vl2 e3)) ⟩ --> ⟨ (FTry vl1 e2 vl2 e3)::xs, ExpRes e1 ⟩
  
(** Exceptions *)
(** Propogation *)
| propogate_Exception frame exc xs :
  (forall vl1 e2 vl2 e3 , (FTry vl1 e2 vl2 e3) <> frame)->
  ⟨ (frame)::xs, ExcRes exc ⟩ --> ⟨ xs, ExcRes exc ⟩


where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').



Reserved Notation "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" (at level 50).
Inductive step_rt : FrameStack -> ProgResult -> nat -> FrameStack -> ProgResult -> Prop :=
| step_refl fs e : ⟨ fs, e ⟩ -[ 0 ]-> ⟨ fs, e ⟩
| step_trans fs e fs' e' fs'' e'' k:
  ⟨ fs, e ⟩ --> ⟨ fs', e'⟩ -> ⟨fs', e'⟩ -[ k ]-> ⟨fs'', e''⟩
  ->
  ⟨ fs, e ⟩ -[S k]-> ⟨fs'', e''⟩
where "⟨ fs , e ⟩ -[ k ]-> ⟨ fs' , e' ⟩" := (step_rt fs e k fs' e').



Definition step_any (fs : FrameStack) (e : ProgResult) (r : ProgResult) : Prop :=
  (exists k v, r = ValSeqRes v /\ ⟨fs, e⟩ -[k]-> ⟨[], ValSeqRes v⟩)
  \/
  (exists k ex, r = ExcRes ex /\ ⟨fs, e⟩ -[k]-> ⟨[], ExcRes ex⟩).

Notation "⟨ fs , e ⟩ -->* v" := (step_any fs e v) (at level 50).





(*
Reserved Notation "⟨ fs , e ⟩ -->* v" (at level 50).
Inductive step_any : FrameStack -> ProgResult -> ProgResult -> Prop :=

| valseq_res    fs e r k v  :
  r = ValueSequence v ->
  ⟨fs, e⟩ -[k]-> ⟨[], ValueSequence v⟩
  ->
  ⟨ fs , e ⟩ -->* r

| exception_res fs e r k ex :
  r = Exception ex ->
  ⟨fs, e⟩ -[k]-> ⟨[], Exception ex⟩
  ->
  ⟨ fs , e ⟩ -->* r

where "⟨ fs , e ⟩ -->* r" := (step_any fs e r).
*)



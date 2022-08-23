Require Export Frames.
Require Export Exceptions.
Require Export Auxiliaries.

Import ListNotations.
Import Auxiliaries.

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

Fixpoint match_pattern (p : Pattern) (e : ValueExpression) : option (list ValueExpression) :=
match p with
| PVar => Some [e]
(* | PPid x => match e with
            | EPid p => if Nat.eqb p x then Some [] else None
            | _      => None
            end *)
| PNil => match e with
          | VNil => Some []
          | _    => None
          end
| PLit l0 => match e with
             | VLit l => if lit_eqb l l0 then Some [] else None
             | _      => None
             end
| PCons p1 p2 => 
  match e with
  | VCons v1 v2 =>
    match match_pattern p1 v1, match_pattern p2 v2 with
    | Some l1, Some l2 => Some (l1 ++ l2)
    | _      , _       => None
    end
  | _           => None
  end
| PTuple pl => match e with
              | VTuple vl =>
                       (fix match_and_bind_elements pl vl :=
                        match pl with
                        | [] => 
                            match vl with
                            | [] => Some []
                            | _ => None
                            end
                        | p::ps => 
                            match vl with
                            | v::vs => 
                                match (match_pattern p v) with
                                | Some vl1 => 
                                    match (match_and_bind_elements ps vs) with
                                    | Some vl2 => Some (vl1 ++ vl2)
                                    | _        => None
                                    end
                                | _ => None
                                end
                            | _ => None
                            end 
                        end) pl vl
              | _ => None
              end
| PMap pl => match e with
              | VMap vl => (fix match_and_bind_elements pl vl :=
                          match pl with
                          | [] => 
                              match vl with
                              | []  => Some []
                              | _   => None
                              end
                          | (p1,p2)::ps => 
                              match vl with
                              | (v1,v2)::vs =>
                                  match (match_pattern p1 v1), (match_pattern p2 v2) with
                                  | Some vl1, Some vl1' =>
                                      match (match_and_bind_elements ps vs) with
                                      | Some vl2  => Some (vl1 ++ vl1' ++ vl2)
                                      | _         => None
                                      end
                                  | _, _ => None
                                  end
                              | _ => None
                              end
                          end) pl vl
              | _  => None
              end
end.

Compute (match_pattern (PTuple []) (VTuple []) ).
Compute (match_pattern (PTuple [PNil]) (VTuple [VNil]) ).
Compute (match_pattern (PTuple [PNil]) (VTuple [VVar 1]) ).
Compute (match_pattern (PTuple [PVar]) (VTuple [VNil]) ).
Compute (match_pattern (PTuple [PVar]) (VTuple [VVar 1]) ).
Compute (match_pattern (PTuple [PVar; PNil]) (VTuple [VVar 1; VNil]) ).
Compute (match_pattern (PTuple [PVar; PVar]) (VTuple [VVar 1; VVar 2]) ).
Compute (match_pattern (PTuple [PVar; PVar]) (VTuple [VVar 1; VNil]) ).
Compute (match_pattern (PTuple [PVar; PNil]) (VTuple [VVar 1; VVar 2]) ).
Compute (match_pattern (PTuple [PNil; PVar]) (VTuple [VVar 1; VVar 2]) ).
Compute (match_pattern (PTuple [PNil; PVar]) (VTuple [VNil; VVar 2]) ).

Compute (match_pattern (PMap [])            (VMap []) ).
Compute (match_pattern (PMap [(PNil,PNil)]) (VMap [(VNil,VNil)]) ).

Compute (match_pattern (PMap [(PVar,PNil)]) (VMap [(VNil,VNil)]) ).
Compute (match_pattern (PMap [(PNil,PVar)]) (VMap [(VNil,VNil)]) ).
Compute (match_pattern (PMap [(PNil,PNil)]) (VMap [(VVar 1,VNil)]) ).
Compute (match_pattern (PMap [(PNil,PNil)]) (VMap [(VNil,VVar 2)]) ).

Compute (match_pattern (PMap [(PVar,PVar)]) (VMap [(VNil,VNil)]) ).
Compute (match_pattern (PMap [(PVar,PNil)]) (VMap [(VVar 1,VNil)]) ).
Compute (match_pattern (PMap [(PVar,PNil)]) (VMap [(VNil,VVar 2)]) ).
Compute (match_pattern (PMap [(PNil,PVar)]) (VMap [(VVar 1,VNil)]) ).
Compute (match_pattern (PMap [(PNil,PVar)]) (VMap [(VNil,VVar 2)]) ).
Compute (match_pattern (PMap [(PNil,PNil)]) (VMap [(VVar 1,VVar 2)]) ).

Compute (match_pattern (PMap [(PVar,PVar)]) (VMap [(VVar 1,VNil)]) ).
Compute (match_pattern (PMap [(PVar,PVar)]) (VMap [(VNil,VVar 2)]) ).
Compute (match_pattern (PMap [(PVar,PNil)]) (VMap [(VVar 1,VVar 2)]) ).
Compute (match_pattern (PMap [(PNil,PVar)]) (VMap [(VVar 1,VVar 2)]) ).
Compute (match_pattern (PMap [(PVar,PVar)]) (VMap [(VVar 1,VVar 2)]) ).

Fixpoint match_pattern_list (pl : list Pattern) (vl : list ValueExpression) : option (list ValueExpression) :=
match pl,vl with
  | (p::ps), (v::vs) => match match_pattern p v with
                        | Some vs' => match match_pattern_list ps vs with
                                      | Some vs'' => Some (vs'++vs'')
                                      | None      => None
                                      end
                        | None => None
                        end
  | [], [] => Some []
  | _, _ => None
end.


Definition convert_to_closlist (l : list (nat * nat * Expression)) : (list ValueExpression) :=
map (fun '(id,vc,e) => (VClos l id vc e)) l.


(* TODO (ValueSequence + Exception) -> Prog Result *)

Inductive ProgResult : Type :=
| Expression (e : Expression) (* RExp *)
| ValueSequence (vs : list ValueExpression) (* RValSeq *)
| Exception (e : Exception) (* RExc *)
.


Definition list_subst (l : list ValueExpression) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.

Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).

Inductive step : FrameStack -> ProgResult -> FrameStack -> ProgResult -> Prop :=
(**  Reduction rules *)

(** Value Expressions**)
(**  Cooling *)
| cool_value v xs:
  ⟨ xs, Expression (Val v) ⟩ --> ⟨ xs, ValueSequence [v] ⟩


(**  Values *)
(**  Cooling *)
| cool_Values_empty xs :
  ⟨ xs, Expression (Exp (EValues [])) ⟩ --> ⟨ xs, ValueSequence [] ⟩
| cool_Values_1 vl e el v xs :
  ⟨ (FValues vl (e::el))::xs, ValueSequence [v]⟩ --> ⟨ (FValues (vl++[v]) el)::xs, Expression e ⟩
| cool_Values_2 vl v xs :
  ⟨ (FValues vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, ValueSequence (vl++[v]) ⟩
(**  Heating *)
| heat_Values e el xs:
  ⟨ xs, Expression (Exp (EValues (e::el))) ⟩ --> ⟨ (FValues [] el)::xs, Expression e ⟩


(**  Cons *)
(**  Cooling *)
| cool_Cons_1 hd tl xs :
  ⟨ (FCons1 hd)::xs, ValueSequence [tl] ⟩ --> ⟨ (FCons2 tl)::xs, Expression hd ⟩
| cool_Cons_2 hd tl xs :
  ⟨ (FCons2 tl)::xs, ValueSequence [hd] ⟩ --> ⟨ xs, ValueSequence [VCons hd tl] ⟩
(**  Heating *)
| heat_Cons hd tl xs :
  ⟨ xs, Expression (Exp (ECons hd tl)) ⟩ --> ⟨ (FCons1 hd)::xs, Expression tl ⟩

(**  Tuple *)
(**  Cooling *)
| cool_Tuple_empty xs :
  ⟨ xs, Expression (Exp (ETuple [])) ⟩ --> ⟨ xs, ValueSequence [ VTuple [] ] ⟩
| cool_Tuple_1 vl e el v xs :
  ⟨ (FTuple vl (e::el))::xs, ValueSequence [v] ⟩ --> ⟨ (FTuple (vl++[v]) el)::xs, Expression e ⟩
| cool_Tuple_2 vl v xs :
  ⟨ (FTuple vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, ValueSequence [ VTuple (vl++[v]) ] ⟩
(**  Heating *)
| heat_Tuple e el xs:
  ⟨ xs, Expression (Exp (ETuple (e::el))) ⟩ --> ⟨ (FTuple [] el)::xs, Expression e ⟩


(**  Map *)
(**  Cooling *)
| cool_Map_empty xs :
  ⟨ xs, Expression (Exp (EMap [])) ⟩ --> ⟨ xs, ValueSequence [ VMap [] ] ⟩
| cool_Map_1  vl sn fs el xs :
  ⟨ (FMap1 vl sn el)::xs, ValueSequence [fs] ⟩ --> ⟨ (FMap2 vl fs el)::xs, Expression sn ⟩
| cool_Map_2  vl fs sn fs' sn' el xs :
  ⟨ (FMap2 vl fs ((fs',sn')::el))::xs, ValueSequence [sn] ⟩ --> ⟨ (FMap1 (vl++[(fs,sn)]) sn' el)::xs, Expression fs' ⟩
| cool_Map_3  vl fs sn xs :
  ⟨ (FMap2 vl fs [])::xs, ValueSequence [sn] ⟩ --> ⟨ xs, ValueSequence [ VMap (vl++[(fs,sn)]) ] ⟩
(**  Heating *)
| heat_Map fs sn el xs :
  ⟨ xs, Expression (Exp (EMap ((fs,sn)::el))) ⟩ --> ⟨ (FMap1 [] sn el)::xs, Expression fs ⟩


(**  PrimOp *) (*TODO: Auxiliaries *) (* "inl res" is a ValueExpression*)
(*TODO: Auxiliaries.ValueSequence -> list ValueExpression, is this conversion ok?*)
(**  Cooling *)
| cool_PrimOp_empty f xs res eff :
  eval f [] [] = (inl res, eff) ->
  ⟨ xs, Expression(Exp (EPrimOp f [])) ⟩ --> ⟨ xs, ValueSequence res ⟩
| cool_PrimOp_1 f vl e el v xs :
  ⟨ (FPrimOp f vl (e::el))::xs, ValueSequence [v] ⟩ --> ⟨ (FPrimOp f (vl++[v]) el)::xs, Expression e ⟩
| cool_PrimOp_2 f vl v xs res eff :
  eval f (vl++[v]) [] = (inl res, eff) ->
  ⟨ (FPrimOp f vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, ValueSequence res ⟩
(**  Heating *)
| heat_PrimOp f e el xs :
  ⟨ xs, Expression (Exp (EPrimOp f (e::el))) ⟩ --> ⟨ (FPrimOp f [] el)::xs, Expression e ⟩
(** Exceptions *)
| err_PrimOp_1 f xs exc eff : (* in this case there were no parameters to evaluate *)
  eval f [] [] = (inr exc, eff) ->
  ⟨ xs, Expression(Exp (EPrimOp f [])) ⟩ --> ⟨ xs, Exception exc ⟩
| err_PrimOp_2 f vl v xs exc eff : (* there were parameters *)
  eval f (vl++[v]) [] = (inr exc, eff) ->
  ⟨ (FPrimOp f vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, Exception exc ⟩

(**  Let *)
(**  Cooling *)
| cool_Let l e2 vs xs :
  length vs = l ->
  ⟨ (FLet l e2)::xs, ValueSequence vs ⟩ --> ⟨ xs, Expression (e2.[ list_subst vs idsubst ]) ⟩ (* TODO: e2.[ ? ] *)
(**  Heating *)
| heat_Let l e1 e2 xs :
  ⟨ xs, Expression(Exp (ELet l e1 e2)) ⟩ --> ⟨ (FLet l e2)::xs, Expression e1 ⟩


(**  Seq *)
(**  Cooling *)
| cool_Seq e2 v xs :
  ⟨ (FSeq e2)::xs, ValueSequence [v] ⟩ --> ⟨ xs, Expression e2 ⟩
(**  Heating *)
| heat_Seq e1 e2 xs :
  ⟨ xs, Expression (Exp (ESeq e1 e2)) ⟩ --> ⟨ (FSeq e2)::xs, Expression e1 ⟩
  
(**  Fun *)
(**  Cooling *)
| cool_fun e vl xs :
  ⟨ xs, Expression (Exp (EFun vl e)) ⟩ --> ⟨ xs, ValueSequence [ VClos [] 0 vl e ] ⟩ (*TODO : id not 0*)


(**  Call *) (*TODO : will be the same as PrimOp, use the eval from the Auxilieries*)
(**  Cooling *)
| cool_Call_empty f xs res eff :
  eval f [] [] = (inl res, eff) ->
  ⟨ xs, Expression (Exp (ECall f [])) ⟩ --> ⟨ xs, ValueSequence res ⟩
| cool_Call_1 f vl e el v xs :
  ⟨ (FCall f vl (e::el))::xs, ValueSequence [v] ⟩ --> ⟨ (FCall f (vl++[v]) el)::xs, Expression e ⟩
| cool_Call_2 f vl v xs res eff :
  eval f (vl++[v]) [] = (inl res, eff) ->
  ⟨ (FCall f vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, ValueSequence res ⟩
(**  Heating *)
| heat_Call f e el xs :
  ⟨ xs, Expression (Exp (ECall f (e::el))) ⟩ --> ⟨ (FCall f [] el)::xs, Expression e ⟩
(** Exceptions *)
| err_Call_1 f exc eff xs : (* in this case there were no parameters to evaluate *)
  eval f [] [] = (inr exc, eff) ->
  ⟨ xs, Expression (Exp (ECall f [])) ⟩ --> ⟨ xs, Exception exc ⟩
| err_Call_2 f v vl exc eff xs : (* there were parameters *)
  eval f (vl++[v]) [] = (inr exc, eff) ->
  ⟨ (FCall f vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, Exception exc ⟩

(**  App *) (* On paper *) (* in "EApp e el" e needs to evaluate to a VClos but it will only be checked when el is done *)
(**  Cooling *) (*TODO: empty FApp1 *) (* TODO: vc = length vl, when to evaluate? *)
| cool_App_empty vl' ext id e xs :
  convert_to_closlist ext = vl' ->
  ⟨ (FApp1 [])::xs, ValueSequence [(VClos ext id 0 e)] ⟩ --> ⟨ xs, Expression e.[list_subst (vl') idsubst] ⟩
| cool_App_1 e el v xs :
  ⟨ (FApp1 (e::el))::xs, ValueSequence [v] ⟩ --> ⟨ (FApp2 v [] el)::xs, Expression e ⟩
| cool_App_2a v' vl e el v xs :
  ⟨ (FApp2 v' vl (e::el))::xs, ValueSequence [v] ⟩ --> ⟨ (FApp2 v' (vl++[v]) el)::xs, Expression e ⟩
| cool_App_2b vl' ext id vc e' vl v xs :
  vc = (length (vl) + 1) ->
  convert_to_closlist ext = vl' ->
  ⟨ (FApp2 (VClos ext id vc e') vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, Expression (e'.[list_subst (vl'++(vl++[v])) idsubst]) ⟩
(**  Heating *)
| heat_App e el xs :
  ⟨ xs, Expression (Exp (EApp e el)) ⟩ --> ⟨ (FApp1 el)::xs, Expression e ⟩
(** Exceptions *) (*TODO badarity FApp1 version*)
| err_App_badariry ext id vc e' vl xs v :
  vc <> (length (vl) + 1) ->
  ⟨ (FApp2 (VClos ext id vc e') vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, Exception (badarity (VClos ext id vc e')) ⟩
| err_App_noclos_1 v xs : (* when it had no other expressions to evalate ([] case) *)
  (forall ext id vc e, v <> (VClos ext id vc e)) ->
  ⟨ (FApp1 [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, Exception (badfun v) ⟩
| err_App_noclos_2 v' vl v xs : (* when it had expressions to evaluate *)
  (forall ext id vc e', v' <> (VClos ext id vc e')) ->
  ⟨ (FApp2 v' vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, Exception (badfun v') ⟩


(**  Case *)
(**  Cooling *)
(* eval started or ongoing, the first pattern matched, e1 the guard needs to be evaluated *)
| cool_Case_1m lp e1 e2 l vs vs' xs :
  match_pattern_list lp vs = Some vs' ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, ValueSequence vs ⟩ --> ⟨ (FCase2 vs lp e2 l vs')::xs, Expression (e1.[list_subst (vs') idsubst]) ⟩
(* eval started or ongoing, the first pattern doesn't match, so case jumps to the next option where the pattern needs to match first. *)
| cool_Case_1nm lp e1 e2 l vs xs :
  match_pattern_list lp vs = None ->
  ⟨ (FCase1 ((lp,e1,e2)::l))::xs, ValueSequence vs ⟩ --> ⟨ (FCase1 l)::xs, ValueSequence vs ⟩
(* eval ongoing, the last pattern matched, the guard is true, so case ends*)
| cool_Case_2mt vs lp e' l vs' xs :
  ⟨ (FCase2 vs lp e' l vs')::xs, ValueSequence [ VLit (Atom "true") ] ⟩ --> ⟨ xs, Expression (e'.[list_subst (vs') idsubst]) ⟩
(* eval ongoing, the last pattern matched, the guard is false, so case jumps to the next option where the pattern needs to match first. *)
| cool_Case_2mf vs lp' e' l vs' xs :
  ⟨ (FCase2 vs lp' e' l vs')::xs, ValueSequence [ VLit (Atom "false") ] ⟩ --> ⟨ (FCase1 l)::xs, ValueSequence vs ⟩
(**  Heating *)
| heat_Case e l xs:
  ⟨ xs, Expression (Exp (ECase e l)) ⟩ --> ⟨ (FCase1 l)::xs, Expression e ⟩
(** Exceptions *)
| err_Case_empty vs xs:
  ⟨ (FCase1 [])::xs, ValueSequence vs ⟩ --> ⟨ xs, Exception if_clause ⟩

(**  LetRec *)
(**  Cooling *)
(**  Heating *)
| heat_LetRec l e lc xs :
  convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) = lc -> (*TODO: for now the funids are 0 coded in *)
  ⟨ xs, Expression (Exp (ELetRec l e)) ⟩ --> ⟨ xs, Expression e.[list_subst (lc) idsubst] ⟩


(**  Try *)
(**  Cooling *)
| cool_Try_ok vl1 e2 vl2 e3 vs xs:
  vl1 = length vs ->
  ⟨ (FTry vl1 e2 vl2 e3)::xs, ValueSequence vs ⟩ --> ⟨ xs, Expression e2.[ list_subst vs idsubst ] ⟩
| cool_Try_err vl1 e2 e3 class reason details xs:  (* in CErlang exceptions always have 3 part*)
  ⟨ (FTry vl1 e2 3 e3)::xs, Exception (class, reason, details) ⟩ --> ⟨ xs, Expression e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] ⟩
(**  Heating *)
| heat_Try e1 vl1 e2 vl2 e3 xs :
  ⟨ xs, Expression (Exp (ETry e1 vl1 e2 vl2 e3)) ⟩ --> ⟨ (FTry vl1 e2 vl2 e3)::xs, Expression e1 ⟩
  
(** Exceptions *)
(** Propogation *)
| propogate_Exception frame e xs :
  (forall vl1 e2 vl2 e3 , (FTry vl1 e2 vl2 e3) <> frame)->
  ⟨ (frame)::xs, Exception e ⟩ --> ⟨ xs, Exception e ⟩


where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').


Theorem semmantics_rules_determinism :
  forall fs fs1 fs2 e e1 e2,
  ⟨ fs , e ⟩ --> ⟨ fs1 , e1 ⟩ ->
  ⟨ fs , e ⟩ --> ⟨ fs2 , e2 ⟩
  -> (fs1 = fs2 /\ e1 = e2).
Proof.
intros. inversion H; subst; inversion H0; auto; subst.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H8. inversion H8. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H8. inversion H8. subst. auto.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H8. inversion H8. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H8. inversion H8. subst. auto.
* auto.
* specialize (H3 ext id 0 e0). congruence.
* auto.
* congruence.
* specialize (H7 ext id (Datatypes.length vl + 1) e'). congruence.
* congruence.
* specialize (H8 ext id vc e'). congruence.
* specialize (H1 ext id 0 e). congruence.
* specialize (H1 ext id (Datatypes.length vl + 1) e'). congruence.
* specialize (H1 ext id vc e'). congruence.
* rewrite H1 in H10. inversion H10. subst. auto.
* rewrite H1 in H10. inversion H10.
* rewrite H1 in H10. inversion H10.
* auto.
* specialize (H6 vl1 e0 3 e3). congruence.
* specialize (H1 vl1 e1 3 e3). congruence.
Qed.







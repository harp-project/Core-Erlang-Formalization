Require Export Frames.

Import ListNotations.

(*
Fixpoint match_pattern (p : Pattern) (e : Expression) : Prop :=
match p with
| PVar v => match e with
            | Val (VVar v') => match_pattern p e
            | _             => False
            end
| PLit l => False
| PCons hd tl => False
| PTuple l => False
| PMap l => False
| PNil => False
end.
*)

Definition list_subst (l : list ValueExpression) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.

Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).

Inductive step : FrameStack -> Expression -> FrameStack -> Expression -> Prop :=
(**  Reduction rules *)

(**  Values *)
(**  Cooling *)
| cool_Values_empty xs :
  ⟨ xs, Exp (EValues []) ⟩ --> ⟨ xs, Val (VValues []) ⟩
| cool_Values_1 vl e el v xs :
  ⟨ (FValues vl (e::el))::xs, Val v⟩ --> ⟨ (FValues (vl++[v]) el)::xs, e ⟩
| cool_Values_2 vl v xs :
  ⟨ (FValues vl [])::xs, Val v ⟩ --> ⟨ xs, Val (VValues (vl++[v])) ⟩
(**  Heating *)
| heat_Values e el xs:
  ⟨ xs, Exp (EValues (e::el)) ⟩ --> ⟨ (FValues [] el)::xs, e ⟩

(**  Cons *)
(**  Cooling *)
| cool_Cons_1 hd tl xs :
  ⟨ (FCons1 hd)::xs, Val tl ⟩ --> ⟨ (FCons2 tl)::xs, hd ⟩
| cool_Cons_2 hd tl xs :
  ⟨ (FCons2 tl)::xs, Val hd ⟩ --> ⟨ xs, Val (VCons hd tl) ⟩
(**  Heating *)
| heat_Cons hd tl xs :
  ⟨ xs, Exp (ECons hd tl) ⟩ --> ⟨ (FCons1 hd)::xs, tl ⟩

(**  Tuple *)
(**  Cooling *)
| cool_Tuple_empty xs :
  ⟨ xs, Exp (ETuple []) ⟩ --> ⟨ xs, Val (VTuple []) ⟩ (* Is this deterministic? *)
| cool_Tuple_1 vl e el v xs :
  ⟨ (FTuple vl (e::el))::xs, Val v⟩ --> ⟨ (FTuple (vl++[v]) el)::xs, e ⟩
| cool_Tuple_2 vl v xs :
  ⟨ (FTuple vl [])::xs, Val v ⟩ --> ⟨ xs, Val (VTuple (vl++[v])) ⟩
(**  Heating *)
| heat_Tuple e el xs:
  ⟨ xs, Exp (ETuple (e::el)) ⟩ --> ⟨ (FTuple [] el)::xs, e ⟩

(**  Map *)
(**  Cooling *)
| cool_Map_empty xs :
  ⟨ xs, Exp (EMap []) ⟩ --> ⟨ xs, Val (VMap []) ⟩
| cool_Map_1  vl sn fs el xs :
  ⟨ (FMap1 vl sn el)::xs, Val fs ⟩ --> ⟨ (FMap2 vl fs el)::xs, sn ⟩
| cool_Map_2  vl fs sn fs' sn' el xs :
  ⟨ (FMap2 vl fs ((fs',sn')::el))::xs, Val sn ⟩ --> ⟨ (FMap1 (vl++[(fs,sn)]) sn' el)::xs, fs' ⟩
| cool_Map_3  vl fs sn xs :
  ⟨ (FMap2 vl fs [])::xs, Val sn ⟩ --> ⟨ xs, Val (VMap (vl++[(fs,sn)])) ⟩
(**  Heating *)
| heat_Map fs sn el xs :
  ⟨ xs, Exp (EMap ((fs,sn)::el)) ⟩ --> ⟨ (FMap1 [] sn el)::xs, fs ⟩

(**  PrimOp *)
(**  Cooling *)
| cool_PrimOp_empty f v xs :
  ⟨ xs, Exp (EPrimOp f []) ⟩ --> ⟨ xs, Val VNil ⟩ (*TODO: VNil is a placeholder needs f(), but how?*)
| cool_PrimOp_1  xs :
  ⟨ (FPrimOp f vl (e::el))::xs, Val v ⟩ --> ⟨ (FPrimOp f (vl++[v]) el)::xs, e ⟩
| cool_PrimOp_2  xs :
  ⟨ (FPrimOp f vl [])::xs, Val v ⟩ --> ⟨ xs, Val VNil ⟩ (*TODO: VNil is a placeholder needs f(vl,v), but how?*)
(**  Heating *)
| heat_PrimOp f e el xs :
  ⟨ xs, Exp (EPrimOp f (e::el)) ⟩ --> ⟨ (FPrimOp f [] el)::xs, e ⟩

(**  Let *)
(**  Cooling *)
| cool_Let_a l e2 v xs :
  length vl = l ->
  ⟨ (FLet l e2)::xs, Val (VValues vl) ⟩ --> ⟨ xs, e2.[ list_subst vl idsubst ] ⟩ (* TODO: e2.[ ? ] *)
| cool_Let_b e2 v xs :
  (forall vl, v <> (VValues vl)) ->
  ⟨ (FLet 1 e2)::xs, Val v ⟩ --> ⟨ xs, e2.[ v /] ⟩
(**  Heating *)
| heat_Let l e1 e2 xs :
  ⟨ xs, Exp (ELet l e1 e2) ⟩ --> ⟨ (FLet l e2)::xs, e1 ⟩

(**  Seq *)
(**  Cooling *)
| cool_Seq e2 v xs :
  ⟨ (FSeq e2)::xs, Val v ⟩ --> ⟨ xs, e2 ⟩ (* TODO: e2.[ ? ]*)
(**  Heating *)
| heat_Seq e1 e2 xs :
  ⟨ xs, Exp (ESeq e1 e2) ⟩ --> ⟨ (FSeq e2)::xs, e1 ⟩

where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').

(*
| red_app_start v hd tl xs (H : VALCLOSED v):
  ⟨ (FApp1 (hd::tl))::xs, v ⟩ --> ⟨ (FApp2 v tl [])::xs, hd⟩
*)
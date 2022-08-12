Require Export Frames.
Require Export Exceptions.

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

(*
(**  PrimOp *) (*TODO: Auxiliaries *)
(**  Cooling *)
| cool_PrimOp_empty f xs :
  ⟨ xs, Expression(Exp (EPrimOp f [])) ⟩ --> ⟨ xs, ValueSequence [VNil] ⟩ (*TODO: VNil is a placeholder needs f(), but how?*)
| cool_PrimOp_1 f vl e el v xs :
  ⟨ (FPrimOp f vl (e::el))::xs, ValueSequence [v] ⟩ --> ⟨ (FPrimOp f (vl++[v]) el)::xs, Expression e ⟩
| cool_PrimOp_2 f vl v xs :
  ⟨ (FPrimOp f vl [])::xs, ValueSequence [v] ⟩ --> ⟨ xs, ValueSequence [VNil] ⟩ (*TODO: VNil is a placeholder needs f(vl,v), but how?*)
(**  Heating *)
| heat_PrimOp f e el xs :
  ⟨ xs, Expression (Exp (EPrimOp f (e::el))) ⟩ --> ⟨ (FPrimOp f [] el)::xs, Expression e ⟩
*)

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
(**  Heating *)

(**  App *) (* On paper *)
(**  Cooling *)
(**  Heating *)

(**  Case *) (*ok*)
(**  Cooling *)
(**  Heating *)

(**  LetRec *)
(**  Cooling *)
(**  Heating *)

(**  Try *)
(**  Cooling *)
(**  Heating *)

where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').

(*
| red_app_start v hd tl xs (H : VALCLOSED v):
  ⟨ (FApp1 (hd::tl))::xs, v ⟩ --> ⟨ (FApp2 v tl [])::xs, hd⟩
*)
(**
  This file contains the syntax and scope for evaluation frames.
 *)
From CoreErlang Require Export ScopingLemmas Maps Matching Auxiliaries.

Import ListNotations.
Import Notations.

(** FrameStack *)
(** Based on [Pitts' work](https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf) *)

(**
  To avoid duplication of semantic rules for language elements using lists of
  expressions as parameters, we use parameter list frames, with identifiers.
*)
Inductive FrameIdent :=
| IValues               (* value sequence *)
| ITuple                (* tuple *)
| IMap                  (* map (keys and values flattened) *)
| IBin                  (* binary construction *)
| ICall (m f : Val)     (* call of m:f, after evaluating m and f *)
| IPrimOp (f : string)  (* primitive operation f *)
| IApp (v : Val).       (* application of v, after evaluating v *)

(** Evaluation frames: expressions with a hole (□), in which the currently
    evaluated subexpression's result is placed. *)
Inductive Frame : Set :=
| FCons1 (hd : Exp) (* [e1 | □] *)
| FCons2 (tl : Val) (* [□ | v2] *)
| FParams (ident : FrameIdent) (vl : list Val) (el : list Exp) (* (v₁, ..., vₖ, □, eₖ₊₂, ..., eₙ) *)
| FApp1 (l : list Exp)  (* apply □(e₁, ..., eₙ) *)
| FCallMod (f : Exp) (l : list Exp) (* call □:f(e₁, ..., eₙ) *)
| FCallFun (m : Val) (l : list Exp) (* call v:□(e₁, ..., eₙ) *)
| FCase1 (l : list ((list Pat) * Exp * Exp)) (* case □ of l *)
| FCase2   (lv : list Val)
           (ex : Exp)
           (le : list ((list Pat) * Exp * Exp))
  (* the guard of a clause is being evaluated (□): if it is true, the body
     `ex` is evaluated, otherwise matching continues with the values `lv` and
     the remaining clauses `le` (see `plug_f`) *)
| FLet   (l : nat) (e : Exp) (* let <x₁, ..., xₙ> = □ in e *)
| FSeq   (e : Exp)           (* do □ e *)
| FTry (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)
  (* try □ of <x₁, ..., xₙ> -> e₂ catch <xₙ₊₁, ..., xₙ₊ₘ> -> e₃ *)
| FSeg1 (size : Exp) (unit : nat) (type : BinType) (sign : BinSign) (endian : BinEnd)
   (* #<□>{size, unit, type, [sign, endian]} *)
| FSeg2 (val : Val) (unit : nat) (type : BinType) (sign : BinSign) (endian : BinEnd)
   (* #<val>{□, unit, type, [sign, endian]} *)
.

(** Closedness of frame identifiers and frames: all of their subexpressions
    and values are closed (except for the bodies of binders, which are scoped
    in the number of variables bound). *)
Inductive ICLOSED : FrameIdent -> Prop :=
| iclosed_values : ICLOSED IValues
| iclosed_tuple : ICLOSED ITuple
| iclosed_map : ICLOSED IMap
| iclosed_app v : VALCLOSED v -> ICLOSED (IApp v)
| iclosed_call m f : VALCLOSED m -> VALCLOSED f -> ICLOSED (ICall m f)
| iclosed_primop f : ICLOSED (IPrimOp f)
| iclosed_bin : ICLOSED IBin.

Inductive FCLOSED : Frame -> Prop :=
| fclosed_cons1 e : EXPCLOSED e -> FCLOSED (FCons1 e)
| fclosed_cons2 v : VALCLOSED v -> FCLOSED (FCons2 v)
| fclosed_params ident vl el :
  ICLOSED ident ->
  Forall (fun v => VALCLOSED v) vl ->
  Forall (fun e => EXPCLOSED e) el
->
  FCLOSED (FParams ident vl el)
| fclosed_app1 l : Forall (fun e => EXPCLOSED e) l -> FCLOSED (FApp1 l)
| fclosed_callmod f l : EXPCLOSED f -> Forall (fun e => EXPCLOSED e) l -> FCLOSED (FCallMod f l)
| fclosed_callfun m l : VALCLOSED m -> Forall (fun e => EXPCLOSED e) l -> FCLOSED (FCallFun m l)
| fclosed_case1 l : 
  Forall (fun '(pl, g, b) => Forall (PatScoped 0) pl /\ EXP PatListVars pl ⊢ g /\ EXP PatListVars pl ⊢ b) l
->
  FCLOSED (FCase1 l)
| fclosed_case2 vl e rest :
  Forall (fun v => VALCLOSED v) vl ->
  EXPCLOSED e ->
  Forall (fun '(pl, g, b) => Forall (PatScoped 0) pl /\ EXP PatListVars pl ⊢ g /\ EXP PatListVars pl ⊢ b) rest
->
  FCLOSED (FCase2 vl e rest)
| fclosed_let vars e : EXP vars ⊢ e -> FCLOSED (FLet vars e)
| fclosed_seq e : EXPCLOSED e -> FCLOSED (FSeq e)
| fclosed_try vars1 vars2 e2 e3 :
  EXP vars1 ⊢ e2 -> EXP vars2 ⊢ e3
->
  FCLOSED (FTry vars1 e2 vars2 e3)
| fclosed_seg1 size unit type sign endian :
  EXPCLOSED size
->
  FCLOSED (FSeg1 size unit type sign endian)
| fclosed_seg2 val unit type sign endian :
  VALCLOSED val
->
  FCLOSED (FSeg2 val unit type sign endian)
.

(** The expression of a parameter list frame with the given identifier and
    (sub)expressions. *)
Definition to_Exp (ident : FrameIdent) (l : list Exp) : Exp :=
match ident with
| IValues => EValues l
| ITuple => ETuple l
| IMap => EMap (deflatten_list l)
| IApp v => EApp (˝v) l
| ICall m f => ECall (˝m) (˝f) l
| IPrimOp f => EPrimOp f l
| IBin => EBin l
end.

(** Plugging an expression into the hole of a frame. *)
Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FCons1 hd   => °(ECons hd e)
 | FCons2 tl   => °(ECons e (˝tl))
 | FParams ident vl el => to_Exp ident (map VVal vl ++ [e] ++ el)
 | FApp1 l      => °(EApp e l)
 | FCallMod f l => °(ECall e f l)
 | FCallFun m l => °(ECall (˝m) e l)
 | FCase1 l     => °(ECase e l)
 | FCase2 lv ex le =>
   (** This is basically an if-then-else translation from Erlang: *)
   °(ECase (°EValues []) [([], e, ex);
                        ([], ˝ttrue, °ECase (°EValues (map VVal lv)) le)])
   (** We chose this approach, since frames have to satisfy an implicit
       invariant: their □ has to be substituted by closed expressions.
       This way, ˝e˝ is handled as closed, since the corresponding pattern
       does not include variables. *)
 | FLet l ex            => °(ELet l e ex)
 | FSeq ex              => °(ESeq e ex)
 | FTry vl1 e2 vl2 e3   => °(ETry e vl1 e2 vl2 e3)
 | FSeg1 size unit type sign endian => ESeg (Build_Segment e size unit type sign endian)
 | FSeg2 val unit type sign endian  => ESeg (Build_Segment (˝val) e unit type sign endian)
end.

(** Frame stacks (the continuation of the evaluation), and their closedness. *)
Definition FrameStack := list Frame.

Definition FSCLOSED (fs : FrameStack) := Forall FCLOSED fs.

(** Frame invariants:
   - Since maps have an even number of subexpressions (suppose its n),
     map frames should include an odd number of values and evaluable
     expressions (namely, n - 1), since there is a single expression
     currently being evaluated.

*)
Definition FrameWf (f : Frame) : Prop :=
match f with
 | FParams ident vl el =>
   (ident = IMap -> exists n, length el + length vl = 1 + 2 * n)
 | _ => True
end.



#[global]
Hint Constructors ICLOSED : core.

(** `destruct_frame_scope` inverts one closedness hypothesis of a frame (stack)
    of a known shape; `destruct_scopes` deconstructs all frame and redex
    scoping hypotheses. *)
Ltac destruct_frame_scope :=
  match goal with
  | [H : FSCLOSED (_ :: _) |- _] => inversion H; subst; clear H
  | [H : FSCLOSED [] |- _] => clear H
  | [H : FCLOSED (FCons1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCons2 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FParams _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FApp1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCallFun _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCallMod _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase2 _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FLet _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FSeq _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FTry _ _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FSeg1 _ _ _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FSeg2 _ _ _ _ _) |- _] => inversion H; subst; clear H
  end.

Ltac destruct_scopes :=
  repeat destruct_frame_scope;
  repeat destruct_redex_scope.

(** `scope_solver` tries to prove scoping and closedness goals (of
    expressions, values, patterns, redexes and frames) by applying the
    constructors, splitting index bounds, and loosening the scopes of
    hypotheses. *)
Ltac scope_solver_step :=
  match goal with 
  | |- EXP _ ⊢ _ => constructor; simpl; auto
  | |- PAT _ ⊢ _ => constructor; simpl; auto
  | |- VAL _ ⊢ _ => constructor; simpl; auto
  | |- RED _ ⊢ _ => constructor; simpl; auto
  | |- NVAL _ ⊢ _ => constructor; simpl; auto
  | |- ICLOSED _ => constructor; simpl; auto
  | |- forall i, i < _ -> _ => simpl; intros
  | |- Forall FCLOSED _ => constructor; simpl
  | |- Forall (fun v => VAL _ ⊢ v) _ => constructor; simpl
  | |- Forall (fun v => EXP _ ⊢ v) _ => constructor; simpl
  | |- Forall _ _ => constructor; simpl
  | |- _ /\ _ => split
  | |- FSCLOSED _ => constructor; simpl
  | |- FCLOSED _ => constructor; simpl
  | [H : ?i < S _ |- _] => inv H; simpl in *; auto; try lia
  | [H : ?i <= S _ |- _] => inv H; simpl in *; auto; try lia
  | [H : EXP ?n1 ⊢ ?e |- EXP ?n2 ⊢ ?e] => try now (eapply (loosen_scope_exp n2 n1 ltac:(lia)) in H)
  | [H : PAT ?n1 ⊢ ?e |- PAT ?n2 ⊢ ?e] => try now (eapply (loosen_scope_pat n2 n1 ltac:(lia)) in H)
  | [H : VAL ?n1 ⊢ ?e |- VAL ?n2 ⊢ ?e] => try now (eapply (loosen_scope_val n2 n1 ltac:(lia)) in H)
  | [H : NVAL ?n1 ⊢ ?e |- NVAL ?n2 ⊢ ?e] => try now (eapply (loosen_scope_nonval n2 n1 ltac:(lia)) in H)
  end.
Ltac scope_solver := repeat scope_solver_step; try lia.

(** The diverging program `inf` is scoped in any context. *)
Lemma inf_scope :
  forall Γ, NVAL Γ ⊢ inf.
Proof.
  intros. unfold inf. scope_solver.
Qed.

#[global]
Hint Resolve inf_scope : core.

Opaque inf.

(** Concatenates the evaluated segments of a binary construction (which are
    bitstrings). Fails if an element is not a bitstring. *)
Fixpoint construct_bitstring (l : list Val) : option bvn :=
match l with
| [] => Some bvn_empty
| (VBitstring bits) :: rest =>
    match construct_bitstring rest with
    | Some restbits => Some (bvn_app bits restbits)
    | None          => None
    end
| _ => None
end.

(**
  To avoid duplication of semantic rules for language elements using lists of
  expressions as parameters, we use parameter list frames, with identifiers.
  The result of evaluating a given identifier is defined below:
*)
Definition create_result (ident : FrameIdent) (vl : list Val)
  : option (Redex * option SideEffect) :=
match ident with
| IValues => Some (RValSeq vl, None)
| ITuple => Some (RValSeq [VTuple vl], None)
| IMap => Some (RValSeq [VMap (make_val_map (deflatten_list vl))], None)
| ICall m f => match m, f with
               | VLit (Atom module), VLit (Atom func) =>
                  eval module func vl
               (* Calls with non-atom module or function names raise
                  `badarg` (as `erlang:apply/3` does) *)
               | _, _ => Some (RExc (badarg (VTuple [VLit "apply"%string; m; f; meta_to_cons vl])), None)
               end
| IPrimOp f => primop_eval f vl
| IApp (VClos ext id vars e) =>
  if Nat.eqb vars (length vl)
  then Some (RExp (e.[list_subst (convert_to_closlist ext ++ vl) idsubst]), None)
  else Some (RExc (badarity (VClos ext id vars e) (meta_to_cons vl)), None)
| IApp v => Some (RExc (badfun v), None)
| IBin => match construct_bitstring vl with
          | Some val => Some (RValSeq [VBitstring val], None)
          | None => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple vl])), None) (* TODO: not faithful completely *)
          end
end.

(** Decidable equality of frame identifiers. *)
Proposition FrameIdent_eq_dec :
  forall id1 id2 : FrameIdent, {id1 = id2} + {id1 <> id2}.
Proof.
  decide equality; try apply string_dec.
  all: apply Val_eq_dec.
Defined.

(** Exceptions propagate through every frame, except `try` frames, which
    catch them. *)
Definition isPropagatable (f : Frame) : bool :=
match f with
 | FTry _ _ _ _ => false
 | _ => true
end.


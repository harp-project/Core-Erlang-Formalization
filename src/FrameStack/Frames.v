Require Export ScopingLemmas Maps.

Import ListNotations.

(** FrameStack *)
(** Based on Pitts' work: https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf *)
(*
Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Exp) (l1 l2 : list Exp) (* apply v(v₁, v₂, ... vᵢ₋₁, □, eᵢ₊₁, ..., eₙ) *)
| FLet (v : Var) (e2 : Exp) (* let v = □ in e2 *)
| FPlus1 (e2 : Exp) (* □ + e2 *)
| FPlus2 (v : Exp) (* (p : is_value v) *) (* v + □ *)
| FCase (p : Pat) (e2 e3 : Exp) (* if □ then e2 else e3 *)
| FCons1 (e1 : Exp) (* [e1 | □] *)
| FCons2 (v2 : Exp) (* [□ | v2] *).
*)

(* It is an inductive to have the "FParams" name *)
(* This frame is used to handle parameter lists in a unified way to avoid
  duplication *)
Inductive ParamFrame : Set :=
| FParams : list Val -> list Exp -> ParamFrame. (* v₁, v₂, ... vᵢ₋₁, □, eᵢ₊₁, ..., eₙ *)

Inductive Frame : Set :=
| FValues (l : ParamFrame)
| FCons1 (hd : Exp) (* [e1 | □] *)
| FCons2 (tl : Val) (* [□ | v2] *)
| FTuple (l : ParamFrame)
| FMap (l : ParamFrame) (* maps are tricky: the list of pairs is flattened with `flatten_list`, which can be reversed by `deflatten_list` *)
| FCall   (f : string) (l : ParamFrame)
| FPrimOp (f : string) (l : ParamFrame)
| FApp1 (l : list Exp)
| FApp2 (v : Val) (l : ParamFrame)
| FCase1 (l : list ((list Pat) * Exp * Exp))
| FCase2   (lv : list Val)
           (lp : list Pat)
           (ex : Exp)
           (le : list ((list Pat) * Exp * Exp))
           (lvp : list Val)
           (* the result of the pattern matching, only needed in the reduction rules *)
(* ECase v ((lp, _, ex), ..., (lp, e, e)) *)
(* FCase2_p means that the pattern matching was not done yet so the current guard Exp (referenced by "_" or called the hole) does not need to be evaluated yet. *)
(* FCase2_g means that the last pattern matched so the current guard needs to be evaluated, so tha guard Exp does not need to be evaluated yet. *)

| FLet   (l : nat) (e : Exp) (* let <x₁, ..., xₙ> = □ in e *)
| FSeq   (e : Exp)           (* do □ e *)
| FTry (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)
  (* try □ of <x₁, ..., xₙ> -> e₂ catch <xₙ₊₁, ..., xₙ₊ₘ> -> e₃ *)
.

Definition closed_ParamFrame (F : ParamFrame) : Prop :=
match F with
| FParams vl el => Forall (fun v => VALCLOSED v) vl /\
                   Forall (fun e => EXPCLOSED e) el
end.

Definition lengthParamFrame (F : ParamFrame) : nat :=
match F with
| FParams vl el => S (length vl + length el) (* there is a box in the list! *)
end.

Inductive FCLOSED : Frame -> Prop :=
| wf_values l : closed_ParamFrame l -> FCLOSED (FValues l)
| wf_cons1 e : EXPCLOSED e -> FCLOSED (FCons1 e)
| wf_cons2 v : VALCLOSED v -> FCLOSED (FCons2 v)
| wf_tuple l : closed_ParamFrame l -> FCLOSED (FTuple l)
| wf_map l : 
  (exists n, lengthParamFrame l = 2 * n) ->
  closed_ParamFrame l
->
  FCLOSED (FMap l)
| wf_call f l : closed_ParamFrame l -> FCLOSED (FCall f l)
| wf_primop f l : closed_ParamFrame l -> FCLOSED (FPrimOp f l)
| wf_app1 l : Forall (fun e => EXPCLOSED e) l -> FCLOSED (FApp1 l)
| wf_app2 v l : VALCLOSED v -> closed_ParamFrame l -> FCLOSED (FApp2 v l)
| wf_case1 l : 
  (forall i : nat,
  i < Datatypes.length l ->
  EXP PatListScope (nth i (map (fst >>> fst) l) [])
  ⊢ nth i (map (fst >>> snd) l) (` VNil)) ->
  (forall i : nat,
        i < Datatypes.length l ->
        EXP PatListScope (nth i (map (fst >>> fst) l) [])
        ⊢ nth i (map snd l) (` VNil))
->  
  FCLOSED (FCase1 l)
| wf_case2 vl pl e rest lvp :
  Forall (fun v => VALCLOSED v) vl ->
  Forall (fun v => VALCLOSED v) lvp (* Necessary if the frame is used out of context *) ->
  VAL PatListScope pl ⊢ e ->
  (forall i : nat,
  i < Datatypes.length rest ->
  EXP PatListScope (nth i (map (fst >>> fst) rest) [])
  ⊢ nth i (map (fst >>> snd) rest) (` VNil)) ->
  (forall i : nat,
        i < Datatypes.length rest ->
        EXP PatListScope (nth i (map (fst >>> fst) rest) [])
        ⊢ nth i (map snd rest) (` VNil))
->
  FCLOSED (FCase2 vl pl e rest lvp)
| wf_let vars e : EXP vars ⊢ e -> FCLOSED (FLet vars e)
| wf_seq e : EXPCLOSED e -> FCLOSED (FSeq e)
| wf_try vars1 vars2 e2 e3 :
  EXP vars1 ⊢ e2 -> EXP vars2 ⊢ e3
->
  FCLOSED (FTry vars1 e2 vars2 e3)
.

Definition plug_params (F : ParamFrame) (e : Exp) : list Exp :=
match F with
| FParams vl el => map VVal vl ++ [e] ++ el
end.

Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FValues l   => °(EValues (plug_params l e))
 | FCons1 hd   => °(ECons hd e)
 | FCons2 tl   => °(ECons e (`tl))
 | FTuple l    => °(ETuple (plug_params l e))
 | FMap l      => °(EMap (deflatten_list (plug_params l e)))
 | FCall f l   => °(ECall f (plug_params l e))
 | FPrimOp f l => °(EPrimOp f (plug_params l e))
 | FApp1 l     => °(EApp e l)
 | FApp2 v l   => °(EApp (`v) (plug_params l e))
 | FCase1 l    => °(ECase e l)
 | FCase2 lv lp ex le lvp =>
   °(ECase (°EValues (map VVal lv)) ([(lp,e,ex)] ++ le))
 (*| FCase2 v lp ex le lv => (* lv only carries information needed in the evaluation of ex *)
        Exp (ECase (Val v) ((cons (lp,e,ex) nil) ++ le))*)
 (*| FCase2_g v lp ex le =>
        Exp (ECase (Val v) ((cons (lp,e,ex) nil) ++ le)) *)

 | FLet l ex            => °(ELet l e ex)
 | FSeq ex              => °(ESeq e ex)
 | FTry vl1 e2 vl2 e3   => °(ETry e vl1 e2 vl2 e3)
end.

Definition FrameStack := list Frame.

Definition FSCLOSED (fs : FrameStack) := Forall FCLOSED fs.


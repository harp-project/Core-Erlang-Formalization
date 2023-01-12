From CoreErlang Require Export ScopingLemmas Maps Matching.

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

Inductive FrameIdent :=
| IValues
| ITuple
| IMap
| ICall (f : string)
| IPrimOp (f : string)
| IApp (v : Val).

Inductive Frame : Set :=
| FCons1 (hd : Exp) (* [e1 | □] *)
| FCons2 (tl : Val) (* [□ | v2] *)
| FParams (ident : FrameIdent) (vl : list Val) (el : list Exp)
| FApp1 (l : list Exp)
| FCase1 (l : list ((list Pat) * Exp * Exp))
(* | FCase2   (lv : list Val)
           (lp : list Pat)
           (ex : Exp)
           (le : list ((list Pat) * Exp * Exp))
           (lvp : list Val) *)
           (* the result of the pattern matching, only needed in the reduction rules
         ^---- Not a good solution, because if this frame is used outside
               of a bigger context, lvp is not known to be the result of
               the pattern matching *)
| FCase2   (lv : list Val)
           (lp : list Pat)
           (ex : Exp)
           (le : list ((list Pat) * Exp * Exp))
| FLet   (l : nat) (e : Exp) (* let <x₁, ..., xₙ> = □ in e *)
| FSeq   (e : Exp)           (* do □ e *)
| FTry (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp)
  (* try □ of <x₁, ..., xₙ> -> e₂ catch <xₙ₊₁, ..., xₙ₊ₘ> -> e₃ *)
.

Inductive ICLOSED : FrameIdent -> Prop :=
| iclosed_values : ICLOSED IValues
| iclosed_tuple : ICLOSED ITuple
| iclosed_map : ICLOSED IMap
| iclosed_app v : VALCLOSED v -> ICLOSED (IApp v)
| iclosed_call f : ICLOSED (ICall f)
| iclosed_primop f : ICLOSED (IPrimOp f).

Inductive FCLOSED : Frame -> Prop :=
| fclosed_cons1 e : EXPCLOSED e -> FCLOSED (FCons1 e)
| fclosed_cons2 v : VALCLOSED v -> FCLOSED (FCons2 v)
| fclosed_params ident vl el :
  ICLOSED ident ->
  Forall (fun v => VALCLOSED v) vl ->
  Forall (fun e => EXPCLOSED e) el ->
  (* map invariant (even with this, the semantics of maps is a bit tricky) *)
  (ident = IMap -> exists n, length el + length vl = 1 + 2 * n)
  (* without this, we cannot be sure that the lists of expressions
     and values build up a map correctly (after applying `deflatten_list`) *)
->
  FCLOSED (FParams ident vl el)
| fclosed_app1 l : Forall (fun e => EXPCLOSED e) l -> FCLOSED (FApp1 l)
| fclosed_case1 l : 
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
| fclosed_case2 vl pl e rest :
  Forall (fun v => VALCLOSED v) vl ->
  (* Forall (fun v => VALCLOSED v) lvp (* Necessary if the frame is used out of context *) -> *)
  EXP PatListScope pl ⊢ e ->
  (exists vs, match_pattern_list pl vl = Some vs) -> (* frame invariant! *)
  (forall i : nat,
  i < Datatypes.length rest ->
  EXP PatListScope (nth i (map (fst >>> fst) rest) [])
  ⊢ nth i (map (fst >>> snd) rest) (` VNil)) ->
  (forall i : nat,
        i < Datatypes.length rest ->
        EXP PatListScope (nth i (map (fst >>> fst) rest) [])
        ⊢ nth i (map snd rest) (` VNil))
->
  FCLOSED (FCase2 vl pl e rest)
| fclosed_let vars e : EXP vars ⊢ e -> FCLOSED (FLet vars e)
| fclosed_seq e : EXPCLOSED e -> FCLOSED (FSeq e)
| fclosed_try vars1 vars2 e2 e3 :
  EXP vars1 ⊢ e2 -> EXP vars2 ⊢ e3
->
  FCLOSED (FTry vars1 e2 vars2 e3)
.

Definition to_Exp (ident : FrameIdent) (l : list Exp) : Exp :=
match ident with
| IValues => EValues l
| ITuple => ETuple l
| IMap => EMap (deflatten_list l)
| IApp v => EApp (`v) l
| ICall f => ECall f l
| IPrimOp f => EPrimOp f l
end.

Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FCons1 hd   => °(ECons hd e)
 | FCons2 tl   => °(ECons e (`tl))
 (* | FValues l   => °(EValues (plug_params l e))
 | FTuple l    => °(ETuple (plug_params l e))
 | FMap l      => °(EMap (deflatten_list (plug_params l e)))
 | FCall f l   => °(ECall f (plug_params l e))
 | FPrimOp f l => °(EPrimOp f (plug_params l e))
 | FApp2 v l   => °(EApp (`v) (plug_params l e)) *)
 | FParams ident vl el => to_Exp ident (map VVal vl ++ [e] ++ el)
 | FApp1 l     => °(EApp e l)
 | FCase1 l    => °(ECase e l)
 | FCase2 lv lp ex le =>
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

#[global]
Hint Constructors ICLOSED : core.

Ltac destruct_frame_scope :=
  match goal with
  | [H : FSCLOSED (_ :: _) |- _] => inversion H; subst; clear H
  | [H : FSCLOSED [] |- _] => clear H
  | [H : FCLOSED (FCons1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCons2 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FParams _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FApp1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase1 _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FCase2 _ _ _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FLet _ _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FSeq _) |- _] => inversion H; subst; clear H
  | [H : FCLOSED (FTry _ _ _ _) |- _] => inversion H; subst; clear H
  end.

Ltac destruct_scopes :=
  repeat destruct_frame_scope;
  repeat destruct_redex_scope.

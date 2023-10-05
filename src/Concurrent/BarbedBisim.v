From CoreErlang Require Export Concurrent.InductiveNodeSemantics
                               Concurrent.ProcessSemantics
                               FrameStack.CTX.

Import ListNotations.


Definition Srel (a b : Signal) :=
match a, b with
 | SMessage e, SMessage e' => forall n, Vrel n e e' /\ Vrel n e' e
 | SExit r b, SExit r' b' => b = b' /\ forall n, Vrel n r r' /\ Vrel n r' r
 | SLink, SLink => True
 | SUnlink, SUnlink => True
 | _, _ => False
end.

Fixpoint usedPidsExp (e : Exp) : list PID :=
match e with
 | VVal e => usedPidsVal e
 | EExp e => usedPidsNonVal e
end
with usedPidsVal (v : Val) : list PID :=
match v with
 | VNil => []
 | VLit l => []
 | VPid p => [p]
 | VCons hd tl => usedPidsVal hd ++ usedPidsVal tl
 | VTuple l => fold_right (fun x acc => usedPidsVal x ++ acc) [] l
 | VMap l =>
   fold_right (fun x acc => usedPidsVal x.1 ++ usedPidsVal x.2 ++ acc) [] l
 | VVar n => []
 | VFunId n => []
 | VClos ext id params e => 
   fold_right (fun x acc => usedPidsExp (snd x) ++ acc) (usedPidsExp e) ext
end

with usedPidsNonVal (n : NonVal) : list PID :=
match n with
 | EFun vl e => usedPidsExp e
 | EValues el => fold_right (fun x acc => usedPidsExp x ++ acc) [] el
 | ECons hd tl => usedPidsExp hd ++ usedPidsExp tl
 | ETuple l => fold_right (fun x acc => usedPidsExp x ++ acc) [] l
 | EMap l =>
   fold_right (fun x acc => usedPidsExp x.1 ++ usedPidsExp x.2 ++ acc) [] l
 | ECall m f l => fold_right (fun x acc => usedPidsExp x ++ acc)
                             (usedPidsExp m ++ usedPidsExp f) l
 | EPrimOp f l => fold_right (fun x acc => usedPidsExp x ++ acc) [] l
 | EApp exp l => fold_right (fun x acc => usedPidsExp x ++ acc) (usedPidsExp exp) l
 | ECase e l => fold_right (fun x acc => usedPidsExp x.1.2 ++ usedPidsExp x.2 ++ acc) (usedPidsExp e) l
 | ELet l e1 e2 => usedPidsExp e1 ++ usedPidsExp e2
 | ESeq e1 e2 => usedPidsExp e1 ++ usedPidsExp e2
 | ELetRec l e => fold_right (fun x acc => usedPidsExp x.2 ++ acc) (usedPidsExp e) l
 | ETry e1 vl1 e2 vl2 e3 => usedPidsExp e1 ++ usedPidsExp e2 ++ usedPidsExp e3
end.

Definition usedPidsRed (r : Redex) : list PID :=
match r with
 | RExp e => usedPidsExp e
 | RValSeq vs => fold_right (fun x acc => usedPidsVal x ++ acc) [] vs
 | RExc e => usedPidsVal e.1.2 ++ usedPidsVal e.2
 | RBox => []
end.

Definition usedPidsIdent (i : FrameIdent) : list PID :=
match i with
 | IValues => []
 | ITuple => []
 | IMap => []
 | ICall m f => usedPidsVal m ++ usedPidsVal f
 | IPrimOp f => []
 | IApp v => usedPidsVal v
end.

Definition usedPidsFrame (f : Frame) : list PID :=
match f with
 | FCons1 hd => usedPidsExp hd
 | FCons2 tl => usedPidsVal tl
 | FParams ident vl el => usedPidsIdent ident ++
                          fold_right (fun x acc => usedPidsVal x ++ acc) [] vl ++
                          fold_right (fun x acc => usedPidsExp x ++ acc) [] el
 | FApp1 l => fold_right (fun x acc => usedPidsExp x ++ acc) [] l
 | FCallMod f l => fold_right (fun x acc => usedPidsExp x ++ acc) (usedPidsExp f) l
 | FCallFun m l => fold_right (fun x acc => usedPidsExp x ++ acc) (usedPidsVal m) l
 | FCase1 l => fold_right (fun x acc => usedPidsExp x.1.2 ++ usedPidsExp x.2 ++ acc)
                          [] l
 | FCase2 lv ex le =>
   fold_right (fun x acc => usedPidsVal x ++ acc) [] lv ++
   fold_right (fun x acc => usedPidsExp x.1.2 ++ usedPidsExp x.2 ++ acc)
              (usedPidsExp ex) le
 | FLet l e => usedPidsExp e
 | FSeq e => usedPidsExp e
 | FTry vl1 e2 vl2 e3 => usedPidsExp e2 ++ usedPidsExp e3
end.

Definition usedPidsStack (fs : FrameStack) : list PID :=
  fold_right (fun x acc => usedPidsFrame x ++ acc) [] fs.

Definition usedPidsProc (p : Process) : list PID :=
match p with
| inl (fs, r, mb, links, flag) => 
    usedPidsStack fs ++
    usedPidsRed r ++
    links ++
    fold_right (fun x acc => usedPidsVal x ++ acc) [] mb.1 ++
    fold_right (fun x acc => usedPidsVal x ++ acc) [] mb.2
| inr links => (* TODO: should links should be considered? - Probably *)
    fold_right (fun x acc => x.1::usedPidsVal x.2 ++ acc) [] links
end.

Definition isUsed (ι : PID) (Π : ProcessPool) : Prop :=
  exists ι' p, Π ι' = Some p /\ In ι (usedPidsProc p).

Definition isUnTaken (ι : PID) (Π : ProcessPool) : Prop :=
  Π ι = None /\ isUsed ι Π.

Definition preCompatibleNodes (n1 n2 : Node) : Prop :=
  forall ι, isUnTaken ι n1.2 -> n2.2 ι = None.

Definition symClos {T : Type} (R : T -> T -> Prop) : T -> T -> Prop :=
  fun t1 t2 => R t1 t2 /\ R t2 t1.


Theorem asd :
  forall n n' a ι, n -[a | ι]ₙ-> n' ->
    forall ι', ~isUnTaken ι' n.2 -> ~isUnTaken ι' n'.2.
Proof.
  intros. inv H; unfold symClos, preCompatibleNodes.
Qed.
 *)

Theorem reduction_preserves_compatibility :
  forall n1 n2, preCompatibleNodes n1 n2 ->
    forall n1' n2' l l',
      Forall (fun x => ~isUnTaken x n1.2) (PIDsOf l) ->
      Forall (fun x => ~isUnTaken x n2.2) (PIDsOf l') ->
      n1 -[l]ₙ->* n1' ->
      n2 -[l']ₙ->* n2' ->
        preCompatibleNodes n1' n2'.
Proof.
  intros.
Qed.


Definition relatedNodes (U : list PID) (S : Node -> Node -> Prop) n1 n2 :=
  symClos preCompatibleNodes n1 n2 ->
    S n1 n2 ->
    (forall n1' a ι,
      Forall (fun x => ~isUnTaken x n2.2) (PIDsOf [(a, ι)]) ->
      n1 -[a | ι]ₙ-> n1' ->
        exists n2' l,
          Forall (fun x => ~isUnTaken x n1.2) (PIDsOf l) ->
          n2 -[l]ₙ->* n2' /\
      S n1' n2') /\
    (forall source dest,
      ~In dest U ->
      exists source' l n2',
      n2 -[l]ₙ->* n2' /\
      list_biforall Srel (n1.1 source dest) (n2'.1 source' dest)).

Definition barbedSim (U : list PID) (S : Node -> Node -> Prop) :=
  forall n1 n2,
    relatedNodes U S n1 n2.

Definition barbedBisim (U : list PID) (S : Node -> Node -> Prop) :=
  forall n1 n2,
    symClos (relatedNodes U S) n1 n2.





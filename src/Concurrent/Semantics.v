(* This part of the work is based on https://dl.acm.org/doi/10.1145/3123569.3123576 *)
From CoreErlang.FrameStack Require Export SubstSemantics.
Require Export Coq.Sorting.Permutation.
Require Export Coq.Classes.EquivDec.

Import ListNotations.

(* mailbox: [old msg₁, old msg₁, ...] ++ 
            current msg₁ :: [new msg₁, new msg₂, ...] *)
Definition Mailbox : Set := list Val * list Val.
Definition Process : Set := FrameStack * Redex * Mailbox.

Notation "x '.1'" := (fst x) (at level 20, left associativity).
Notation "x '.2'" := (snd x) (at level 20, left associativity).

Definition removeMessage (m : Mailbox) : option Mailbox :=
  match m with
  | (m1, msg :: m2) => Some (m1 ++ m2, [])
  | _ => None
  end.

(* in Core Erlang, this function returns a flag and a message, if there is
   a current message *)
Definition peekMessage (m : Mailbox) : option Val :=
  match m with
  | (m1, msg :: m2) => Some msg
  | _ => None
  end.

(* TODO: Check C implementation, how this exactly works *)
Definition recvNext (m : Mailbox) : Mailbox :=
  match m with
  | (m1, msg :: m2) => (m1 ++ [msg], m2)
  | (m1, [])        => (m1         , [])
  end.

Definition mailboxPush (m : Mailbox) (msg : Val) : Mailbox :=
  (m.1, m.2 ++ [msg]).

(* Since OTP 24.0, receive-s are syntactic sugars *)
Definition EReceive l e :=
  ELetRec [(0, 
     °ELet 2 (EPrimOp "recv_peek_message" [])
       (ECase (`VFunId (0, 0)) [
         ([PLit (Atom "true")], `ttrue, °ECase (`VVar 1) (l ++
           [([PVar], `ttrue, °ESeq (EPrimOp "recv_next" [])
                                 (EApp (`VFunId (3, 0)) [])
           )]));
         ([PLit (Atom "false")], `ttrue,
           °ELet 1 (EPrimOp "recv_wait_timeout" [])
              (ECase (`VVar 0)
                [([PLit (Atom "true")], `ttrue, e); (* TODO: timeout *)
                 ([PLit (Atom "false")], `ttrue, °EApp (`VFunId (3, 0)) [])
                ]
              )
         )
       ])
    )]
    (EApp (`VFunId (0, 0)) []).

Inductive Action : Set :=
| ASend (p : PID) (t : Val)
| AReceive (t : Val)
| AArrive (t : Val)
| ASelf (ι : PID)
| ASpawn (ι : PID) (t1 t2 : Exp) (* evaluate apply t1(t2) in a new proc. *)
| AInternal
| AExit.

(* Fixpoint find_clause (vs : list Val) (c : list (list Pat * Exp * Exp)) :
  option (Exp * Exp) :=
match c with
| [] => None
| (ps, g, e)::xs => match match_pattern_list ps vs with
                     | None => find_clause vs xs
                     | Some l => Some (g.[list_subst l idsubst],
                                       e.[list_subst l idsubst])
                    end
end.

Fixpoint receive (m : Mailbox) (c : list (list Pat * Exp * Exp)) : option (Exp * Exp) :=
match m with
| [] => None
| m::ms => match find_clause [m] c with (* NOTE: this is the point where
                                                 it is required that there
                                                 is only one pattern in the
                                                 clauses of receive *)
           | Some res => Some res
           | None => receive ms c
           end
end. *)

(*
  if a `receive` is evaluated:
  1) try the first message against the clauses
    a) if it matches one, evaluate its guard
    b) if the guard is true, go to step 2)
    c) if the guard is false, or the message did not match, save the message
       into a separate cell, then evaluate `receive` with step 1), second message
  2) remove the current message from the mailbox, re-build the mailbox with
     the first part retrieved from the separate cell, and the second is the
     current mailbox
*)

(* Definition pop (v : Val) (m : Mailbox) := removeFirst Exp_eq_dec v m.
Definition etherPop := removeFirst (prod_eqdec Nat.eq_dec Exp_eq_dec). *)

(* TODO: move this to Auxiliaries.v, and refactor eval_length *)
Fixpoint len (l : Val) : option nat :=
match l with
| VNil => Some 0
| VCons v1 v2 => match len v2 with
                 | Some n2 => Some (S n2)
                 | _ => None
                 end
| _ => None
end.

(* TODO: move this to Auxiliaries.v, and refactor eval_list_tuple *)
Fixpoint mk_list (l : Val) : option (list Val) :=
match l with
| VNil => Some []
| VCons v1 v2 => match mk_list v2 with
                 | Some l => Some (v1 :: l)
                 | _ => None
                 end
| _ => None
end.

Reserved Notation "p -⌈ a ⌉-> p'" (at level 50).
Inductive processLocalSemantics : Process -> Action -> Process -> Prop :=
| p_local fs e fs' e' mb :
  ⟨fs, e⟩ --> ⟨fs', e'⟩
->
  (fs, e, mb) -⌈ AInternal ⌉-> (fs', e', mb)

| p_send_local1 fs e ι mb :
  (fs, ESend ι e, mb) -⌈ AInternal ⌉-> (FSend1 e :: fs, ι, mb)
| p_send_local2 fs e v mb : VALCLOSED v ->
  (FSend1 e :: fs, v, mb) -⌈ AInternal ⌉-> (FSend2 v :: fs, e, mb)
| p_spawn_local1 fs e ι mb :
  (fs, ESpawn ι e, mb) -⌈ AInternal ⌉-> (FSpawn1 e :: fs, ι, mb)
| p_spawn_local2 fs e v mb : VALCLOSED v ->
  (FSpawn1 e :: fs, v, mb) -⌈ AInternal ⌉-> (FSpawn2 v :: fs, e, mb)


| p_arrive mb mb' fs e v : VALCLOSED v -> mb' = mb ++ [v] ->
  (fs, e, mb) -⌈ AArrive v ⌉-> (fs, e, mb')

| p_send ι v mb fs : VALCLOSED v ->
  (FSend2 (EPid ι) :: fs, v, mb) -⌈ ASend ι v ⌉-> (fs, v, mb)

| p_self ι fs mb :
  ( fs, ESelf, mb ) -⌈ ASelf ι ⌉-> ( fs, EPid ι, mb )

| p_spawn ι fs mb vl e l:
  Some (length vl) = len l -> VALCLOSED l ->
  (FSpawn2 (EFun vl e) :: fs, l, mb) -⌈ASpawn ι (EFun vl e) l⌉-> (fs, EPid ι, mb)

| p_receive mb l fs e m mb' bindings :
  receive mb l = Some (m, e, bindings) -> mb' = pop m mb
->
  (fs, EReceive l, mb) -⌈ AReceive m ⌉-> (fs, e.[list_subst bindings idsubst], mb')

where "p -⌈ a ⌉-> p'" := (processLocalSemantics p a p').

Inductive LabelStar {A B : Type} (r : A -> B -> A -> Prop) : A -> nat -> list B -> A -> Prop :=
| lsrefl x : LabelStar r x 0 [] x
| lsstep x l ls y z k : r x l y -> LabelStar r y k ls z -> LabelStar r x (S k) (l::ls) z.

Notation "x -⌈ k | xs ⌉-> y" := (LabelStar processLocalSemantics x k xs y) (at level 50).

(******************************************************************************)
(****************************   NODES  ****************************************)
(******************************************************************************)

Definition GlobalMailbox : Set := list (PID * Exp).
Definition ProcessPool : Set := (PID -> option Process).
Definition Node : Set := GlobalMailbox * ProcessPool.

Definition nullpool : ProcessPool := fun ι => None.
Definition update (pid : PID) (p : option Process) (n : ProcessPool) :=
  fun ι => if Nat.eq_dec pid ι then p else n ι.
Definition par (pid : PID) (proc: Process) (n : ProcessPool) : ProcessPool :=
  update pid (Some proc) n.

Notation "pid : p |||| n" := (par pid p n) (at level 30, right associativity).
Notation "n -- pid" := (update pid None n) (at level 31, left associativity).
Lemma update_same : forall ι p p' Π, update ι p (update ι p' Π) = update ι p Π.
Proof.
  intros. unfold update. extensionality ι'.
  break_match_goal; auto.
Qed.
Corollary par_same :  forall ι p p' Π, ι : p |||| ι : p' |||| Π = ι : p |||| Π.
Proof.
  intros. apply update_same.
Qed.

Lemma update_swap : forall ι ι' p p' Π, ι <> ι' ->
   update ι p (update ι' p' Π) = update ι' p' (update ι p Π).
Proof.
  intros. unfold update. extensionality ι''.
  break_match_goal; auto.
  subst. break_match_goal; auto. congruence.
Qed.
Corollary par_swap :  forall ι ι' p p' Π, ι <> ι' ->
   ι : p |||| ι' : p' |||| Π = ι' : p' |||| ι : p |||| Π.
Proof.
  intros. now apply update_swap.
Qed.

Reserved Notation "n -[ a | ι ]ₙ-> n'" (at level 50).
Inductive nodeSemantics : Node -> Action -> PID -> Node -> Prop :=
| n_send p p' ether prs (ι ι' : PID) t :
  p -⌈ASend ι' t⌉-> p'
->
  (ether, ι : p |||| prs) -[ASend ι' t | ι]ₙ->  (ether ++ [(ι', t)], ι : p' |||| prs)

(** This leads to the loss of determinism: *)
| n_arrive ι p p' ether prs t:
  In (ι, t) ether ->
  p -⌈AArrive t⌉-> p' ->
  (ether, ι : p |||| prs) -[AArrive t | ι]ₙ-> (etherPop (ι, t) ether,
                                            ι : p' |||| prs)

| n_other p p' a Π (ι : PID) ether:
  p -⌈a⌉-> p' ->
  (a = AInternal \/ a = ASelf ι \/ (exists t, a = AReceive t))
->
   (ether, ι : p |||| Π) -[a| ι]ₙ-> (ether, ι : p' |||| Π)

| n_spawn Π p p' v1 v2 l ι ι' ether:
  mk_list v2 = Some l -> (ι : p |||| Π) ι' = None ->
  p -⌈ASpawn ι' v1 v2⌉-> p'
->
  (ether, ι : p |||| Π) -[ASpawn ι' v1 v2 | ι]ₙ-> (ether, ι' : ([], EApp v1 l, []) |||| ι : p' |||| Π)

| n_terminate ether v mb ι Π :
  VALCLOSED v ->
  (ether, ι : ([], v, mb) |||| Π) -[AExit | ι]ₙ-> (ether, Π -- ι)

(* | nsend1 p p' q q' Π (ι ι' : PID) t :
  p -⌈ASend ι' t⌉-> p' -> q -⌈AArrive t⌉-> q' -> ι <> ι'
->
  ι : p |||| ι' : q |||| Π -[ASend ι' t | ι]ₙ-> ι : p' |||| ι' : q' |||| Π

| nsend2 p p' p'' t (ι : PID) Π :
  p -⌈ASend ι t⌉-> p' -> p' -⌈AArrive t⌉-> p'' (** two transitions, because this is atomic! *)
->
   ι : p |||| Π  -[ASend ι t | ι]ₙ->  ι : p'' |||| Π 

| nsend3 p p' (ι ι' : PID) Π t :
  p -⌈ASend ι' t⌉-> p' -> (ι : p |||| Π) ι = None
->
  ι : p |||| Π -[ASend ι' t | ι]ₙ-> ι : p' |||| Π *)
(* | nreceive p p' t Π (ι : PID) :
  p -⌈AReceive t⌉-> p'
->
   ι : p |||| Π -[AReceive t | ι]ₙ-> ι : p' |||| Π

| ninternal p p' Π (ι : PID) :
  p -⌈AInternal⌉-> p'
->
   ι : p |||| Π -[AInternal | ι]ₙ-> ι : p' |||| Π

| nself p p' Π ι:
  p -⌈ASelf ι⌉-> p'
->
  ι : p |||| Π -[ASelf ι | ι]ₙ-> ι : p' |||| Π *)

(* *)
where "n -[ a | ι ]ₙ-> n'" := (nodeSemantics n a ι n').

(*
Fixpoint Pat_eqb (p1 p2 : Pat) : bool :=
match p1, p2 with
 | PLit l, PLit l2 => Z.eqb l l2
 | PPid p, PPid p2 => p =? p2
 | PVar, PVar => true
 | PNil, PNil => true
 | PCons p1 p2, PCons p12 p22 => Pat_eqb p1 p12 && Pat_eqb p2 p22
 | _, _ => false
end.

Fixpoint list_eqb {A} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| x::xs, y::ys => eq x y && list_eqb eq xs ys
| _, _ => false
end.

Fixpoint Exp_eqb (e1 e2 : Exp) : bool :=
match e1, e2 with
 | ELit l, ELit l2 => Z.eqb l l2
 | EPid p, EPid p2 => p =? p2
 | EVar n, EVar n2 => n =? n2
 | EFunId n, EFunId n2 => n =? n2
 | EFun vl e, EFun vl2 e2 => list_eqb String.eqb vl vl2 && Exp_eqb e e2
 | EApp exp l, EApp exp2 l2 => Exp_eqb exp exp2 && list_eqb Exp_eqb l l2
 | ELet v e1 e2, ELet v2 e12 e22 => Exp_eqb e1 e12 && Exp_eqb e12 e22
 | ELetRec f vl b e, ELetRec f2 vl2 b2 e2 => _
 | EPlus e1 e2, EPlus e12 e22 => _
 | ECase e0 p e1 e2, ECase e02 p2 e12 e22 => _
 | ECons e1 e2, ECons e12 e22 => _
 | ENil, ENil => true
 | VCons e1 e2, VCons e12 e22 => _
 | ESend p e, ESend p2 e2 => _
 | EReceive l, EReceive l2 => _
 | _, _ => false
end. *)
(* 
Fixpoint list_eq_Node (l : list (PID * Process)) (n : Node) : Prop :=
match l with
| [] => True
| (p, pr)::xs => find p n = Some pr /\ list_eq_Node xs n
end.

Definition equivalent (n1 n2 : Node) : Prop :=
match n1 with
| {| this := x; sorted := y |} => length n2 = length x /\ list_eq_Node x n2
end. *)

(* #[export] Instance processEq : Equiv Process := eq. *)

Reserved Notation "n -[ k | l ]ₙ->* n'" (at level 50).
Inductive closureNodeSem : Node -> nat -> list (Action * PID) -> Node -> Prop :=
| n_refl n (* n'  *): (* Permutation n n' -> *) n -[ 0 | [] ]ₙ->* n (* ' *)
| n_trans n n' n'' k l a ι:
  n -[a|ι]ₙ-> n' -> n' -[k|l]ₙ->* n''
->
  n -[S k | (a,ι)::l]ₙ->* n''
where "n -[ k | l ]ₙ->* n'" := (closureNodeSem n k l n').

Theorem closureNodeSem_trans :
  forall n n' k l, n -[k | l]ₙ->* n' -> forall n'' k' l', n' -[k'|l']ₙ->* n''
->
  n -[k + k' | l ++ l']ₙ->* n''.
Proof.
  intros n n' k l D1. induction D1; intros; simpl.
  * exact H.
  * eapply n_trans. exact H.
    eapply IHD1 in H0. exact H0.
Qed.

(*
  0 -[ 1 + 1 ]-> 1
  1 -[ 2 ]-> 3
  2 -[ 3 ]-> 3
  3 : 2 + 3 == 5
*)
Goal exists acts k,
  ([], 0 : ([], ESend (EPid 1) (EPlus (ELit 1) (ELit 1)), []) ||||
       1 : ([], EReceive [(PVar, ESend (EPid 3) (EVar 0))], []) ||||
       2 : ([], ESend (EPid 3) (ELit 3), []) ||||
       3 : ([], EReceive [(PVar, EReceive [(PVar, EPlus (EVar 0) (EVar 1))])], []) |||| nullpool)
  -[ k | acts ]ₙ->*
  ([], 0 : ([], ELit 2, []) ||||
       1 : ([], ELit 2, []) ||||
       2 : ([], ELit 3, []) ||||
       3 : ([], ELit 5, []) |||| nullpool).
Proof.
  eexists. exists 21.
  (* Some steps with 0 *)
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_send_local1. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_send_local2. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    constructor. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.

  rewrite par_swap with (ι' := 2). rewrite par_swap with (ι' := 2). 2-3: lia.

  (* Some steps with 2 *)
  eapply n_trans. eapply n_other with (ι := 2).
    apply p_send_local1. auto.
  eapply n_trans. eapply n_other with (ι := 2).
    apply p_send_local2. constructor. auto.

  rewrite par_swap with (ι' := 3). rewrite par_swap with (ι' := 3). 2-3: lia.

  eapply n_trans. eapply n_send with (ι := 2) (ι' := 3).
    constructor. constructor.
  simpl.

  rewrite par_swap with (ι' := 3). 2: lia.
  eapply n_trans. apply n_arrive. 
    constructor. reflexivity. repeat constructor.
  cbn. break_match_goal. 2: congruence.

  rewrite par_swap with (ι' := 0). rewrite par_swap with (ι' := 0). 2-3: lia.

  (* Again with 0 *)
  eapply n_trans. eapply n_other with (ι := 0).
  constructor. constructor. auto.

  rewrite par_swap with (ι' := 1). rewrite par_swap with (ι' := 1). 2-3: lia.

  eapply n_trans. eapply n_send with (ι := 0) (ι' := 1).
  constructor. constructor. simpl.

  rewrite par_swap with (ι' := 1). 2: lia.
  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
  cbn. break_match_goal. 2: congruence.

  (* Now with 1 *)
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_receive; try reflexivity. right. right. eexists. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_send_local1. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_send_local2. constructor. auto.

  cbn. break_match_goal. 2: congruence.
  rewrite par_swap with (ι' := 3). 2: lia.

  eapply n_trans. eapply n_send with (ι := 1) (ι' := 3).
    constructor. constructor. simpl.

  rewrite par_swap with (ι' := 3). 2: lia.

  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
    cbn. break_match_goal. 2: congruence.

  (* Mailbox processing for 3 *)
  eapply n_trans. eapply n_other with (ι := 3).
    apply p_receive; try reflexivity. right. right. eexists. auto. cbn.
  break_match_goal. 2: congruence.
  eapply n_trans. eapply n_other with (ι := 3).
    apply p_receive; try reflexivity. right. right. eexists. auto.
    cbn. break_match_goal. 2: congruence.

  eapply n_trans. eapply n_other with (ι := 3).
    constructor. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 3).
    constructor. constructor. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 3).
    constructor. constructor. auto.

  rewrite par_swap with (ι' := 0). rewrite par_swap with (ι' := 0).
  rewrite par_swap with (ι' := 1). rewrite par_swap with (ι' := 2).

  apply n_refl.
  all: lia.
Qed.

(*

let X = spawn(fun() -> receive X -> X ! self() end end, [])
  in let Y = X ! self()
    in receive X -> X end

*)
Goal exists acts k,
  ([], 0 : ([], ELet "X"%string (ESpawn (EFun [] (EReceive [(PVar, ESend (EVar 0) ESelf)]
                                            )) ENil)
             (ELet "Y"%string (ESend (EVar 0) ESelf)
                 (EReceive [(PVar, EVar 0)]))
                  , [])
  |||| nullpool)
  -[ k | acts ]ₙ->*
  ([], 0 : ([], EPid 1, []) ||||
       1 : ([], EPid 1, []) |||| nullpool).
Proof.
  eexists. exists 21.
  eapply n_trans. eapply n_other with (ι := 0).
    do 2 constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_spawn_local1. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_spawn_local2. do 2 constructor. intros.
    inversion H; subst; cbn. 2: inversion H1. repeat constructor.
    auto.
  eapply n_trans. eapply n_spawn with (ι := 0) (ι' := 1); simpl. 2: reflexivity.
    2: constructor. all: simpl; auto. constructor.

  rewrite par_swap with (ι' := 0). 2: lia.

  eapply n_trans. eapply n_other with (ι := 0).
    do 3 constructor. auto.

  rewrite par_swap with (ι' := 1). 2: lia.

  eapply n_trans. eapply n_other with (ι := 1).
    repeat constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    repeat constructor. simpl. auto.

  rewrite par_swap with (ι' := 0). 2: lia.

  simpl.
  eapply n_trans. eapply n_other with (ι := 0).
    repeat constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_send_local1. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_send_local2. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_self. auto.
  eapply n_trans. eapply n_send with (ι := 0) (ι' := 1).
    constructor. constructor. simpl.
  eapply n_trans. eapply n_other with (ι := 0); cbn; try reflexivity.
    repeat constructor. simpl. auto.

  rewrite par_swap with (ι' := 1). 2: lia.

  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
  cbn. break_match_goal. 2: congruence.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_receive; auto; try reflexivity. right. right. eexists. auto.
  simpl.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_send_local1. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_send_local2. constructor. auto.
  eapply n_trans. eapply n_other with (ι := 1).
    apply p_self. auto.
  eapply n_trans. eapply n_send with (ι := 1) (ι' := 0).
    constructor. constructor. simpl.

  rewrite par_swap with (ι' := 0). 2: lia.

  eapply n_trans. apply n_arrive.
    constructor. reflexivity. repeat constructor.
  eapply n_trans. eapply n_other with (ι := 0).
    apply p_receive; auto. reflexivity. right. right. eexists. auto. cbn.
  break_match_goal. 2: congruence.
  cbn. break_match_goal. 2: congruence.
  break_match_goal. 2: congruence.
  apply n_refl.
Qed.

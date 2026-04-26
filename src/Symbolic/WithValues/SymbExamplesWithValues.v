From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Symbolic.WithValues Require Import SymbPreconditions.
From CoreErlang.Symbolic.WithValues Require Import SymbTacticsWithValues.

From CoreErlang.Interpreter Require Import StepFunctions Equivalences.
From CoreErlang.Symbolic Require Import SymbTheorems.
From CoreErlang.Symbolic Require Import SymbTactics.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

 Definition reverse (lst acc : Exp) : Exp :=
   ELetRec [(2,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar],  (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °EApp (˝VFunId (2, 2)) [˝VVar 1; °ECons (˝VVar 0) (˝VVar 4)]);  (* reverse(T, [H|Acc]) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VVar 2)])]  (* return Acc *)
   (EApp (˝VFunId (0, 2)) [lst; acc]).

Fixpoint reverseMetaHelp (y : Val) (acc : Val) :=
  match y with
    | VCons hd tl => reverseMetaHelp tl (VCons hd acc)
    | VNil => acc
    | _ => VNil
  end.

Ltac2 contains_match2 () :=
  lazy_match! goal with
  | [_:_ |- context[match ?v with _ => _ end]] => print (of_constr v)
  | [_:_ |- _] => fail
  end.

Theorem reverse_identity: 
  forall (n : Z) (l : Val), (0 <= n)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\
    VALCLOSED l ->
   exists (y : Val),
   ⟨ [], reverse (reverse (˝l) (˝VNil)) (˝VNil) ⟩ -->* RValSeq [y] /\ y = l.
Proof.
  (* solve_symbolically n ; l. *)
Admitted.

Lemma Z_is_S_n:
  forall (p: positive), exists (n: nat), (Z.to_nat (Z.pos p)) = S n.
Proof.
  intros.
  rewrite (Z2Nat.inj_pos p).
  pose (Pos2Nat.is_pos p).

  destruct l.
  + exists 0. reflexivity.
  + exists m. reflexivity.
Qed.

Theorem reverse_is_correct: 
  forall (n : Z) (m : Z) (l : Val) (lh : Val), (0 <= n)%Z /\ (0 <= m)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\  isWellFormedList_n (Z.to_nat m) lh /\
    VALCLOSED l /\ VALCLOSED lh ->
   exists (y : Val),
   ⟨ [], (reverse (˝l) (˝lh)) ⟩ -->* RValSeq [y] /\ y = reverseMetaHelp l lh.
Proof.
  (* intros.
  eexists.
  split.
  2: reflexivity.
  econstructor.
  split.
  auto.

  econstructor.
  econstructor.
  simpl.
  unfold convert_to_closlist.
  simpl.
  reflexivity.
  unfold list_subst.
  simpl.

  pose H as precond.
  recut_preconds ().
  solve_substitutions ().
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  econstructor.
  discriminate.
  econstructor.
  econstructor.
  econstructor.
  econstructor.

  econstructor.
  econstructor.

  simpl.
  clear_fresh_hyps ().
  clear precond.
  assert (0 <= n)%Z by ltac1:(lia).
  revert H.
  revert m l lh.

  apply Zlt_0_ind with (x := n).
  2: exact H0.
  clear H0 n;
  intro n.
  intro IH.
  intro Heq.
  intros m l lh.
  intro precond.
  
  destruct n.

  3: ltac1:(nia).

  2: {
    recut_preconds ().
    pose (Z_is_S_n p).
    destruct e.
    rewrite H in _PrecondVal1.
    simpl in _PrecondVal1.
    destruct l; try ltac1:(nia).


    econstructor.
    econstructor.
    simpl.
    reflexivity.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    econstructor.
    simpl.
    econstructor.
    econstructor.
    remember (VClos
[(0, 2,
° ECase (˝ VVar 1)
[([PCons PVar PVar], ˝ VLit "true"%string,
° EApp (˝ VFunId (2, 2))
[˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]);
([PNil], ˝ VLit "true"%string, ˝ VVar 2)])] 0 2
(° ECase (˝ VVar 1)
[([PCons PVar PVar], ˝ VLit "true"%string,
° EApp (˝ VFunId (2, 2))
[˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]);
([PNil], ˝ VLit "true"%string, ˝ VVar 2)])) as RevClose.


    simpl.
    solve_substitutions ().

    econstructor.

    econstructor.
    admit.

  }
  admit. *)

  solve_symbolically n , m ; l lh.
  all: ltac1:(scope_solver_v1).
Qed.

Fixpoint sumMeta (v : Val) : Z :=
  match v with
    | VNil => 0%Z
    | VCons (VLit (Integer i)) tl => i + sumMeta tl
    | _ => 0
  end.

Definition sum (lst acc : Exp) : Exp :=
   ELetRec [(2,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar], (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °ELet 1 (ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 0; ˝VVar 4])  (* NewAcc = 0 H = 1, T= 2,fun = 3, List =4, Acc =5 *)
           (EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 0]));  (* sum(T, NewAcc) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VVar 2)])]  (* return Acc *)
   (EApp (˝VFunId (0, 2)) [lst; acc]).


(*TODO: can we determine the functions operation? e.g. not just summing the elements but mapping (fun x => 2 * x + 1) on it?*)
(*TODO: probably a proof hint is much more viable: what parameter is the induction on? What is its terminating function?
What function is applied to the additional parameters?*)

Theorem sum_is_correct:
  forall (n : Z) (m : Z) (l : Val),
    (0 <= n)%Z /\
    isWellFormedNumberList_n (Z.to_nat n) l /\
    VALCLOSED l ->
    exists (y : Z),
    ⟨ [], (sum (˝l) (˝VLit m)) ⟩ -->* RValSeq [VLit y] /\ (y = sumMeta l + m)%Z.
Proof.
  solve_symbolically n , m ; l.
  assumption.
Qed.

Fixpoint lengthMeta (v : Val) : Z :=
  match v with
    | VNil => 0%Z
    | VCons hd tl => 1 + lengthMeta tl
    | _ => 0
  end.

Definition length (lst : Exp) : Exp :=
   ELetRec [(1,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar], (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °ELet 1 (EApp (˝VFunId (2, 1)) [˝VVar 1])
            (ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VLit 1%Z; ˝VVar 0])  (* NewAcc = 0 H = 1, T= 2,fun = 3, List =4, Acc =5 *));  (* sum(T, NewAcc) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VLit 0%Z)])]  (* return Acc *)
   (EApp (˝VFunId (0, 1)) [lst]).

Theorem length_is_correct:
  forall (n : Z) (l : Val),
    (0 <= n)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\
    VALCLOSED l ->
    exists (y : Z),
    ⟨ [], (length (˝l)) ⟩ -->* RValSeq [VLit y] /\ (y = lengthMeta l)%Z.
Proof.

  (* intros.
  assert (0 <= n)%Z by ltac1:(lia).
  revert H.
  revert l.

  apply Zlt_0_ind with (x := n).
  2: exact H0.
  clear H0 n.
  intros n IH Heq l precond.

  eexists.
  split.
  2: reflexivity.

  econstructor.
  split.
  auto.

  econstructor.
  econstructor.

  simpl.

  reflexivity.
  simpl.
  recut_preconds ().
  solve_substitutions ().

  destruct n.
  3: ltac1:(nia).

  2: {
      pose (Z_is_S_n p).
      destruct e.
      rewrite H in _PrecondVal0.
      simpl in _PrecondVal0.
      destruct l; try(ltac1:(nia)).

      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      discriminate.

      econstructor.
      econstructor.
      econstructor.
      econstructor.
      reflexivity.

      econstructor.
      simpl.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      reflexivity.
      simpl.
      (*Mathc_succes*)

      econstructor.
      econstructor.
      econstructor.
      econstructor.
      (*itt van meg a PCaseTrue*)

      econstructor.
      econstructor.
      (*Itt van meg az SLet*)
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      econstructor.
      (*Itt kerül be az app(CLOS_LEN) a stackbe*)

      econstructor.
      econstructor.
      discriminate.
      (*itt kerül vissza t a redexbe, innen kell a lemma a last param eval-ról*)

      econstructor.
      econstructor.
      econstructor.
      econstructor.
      reflexivity.
      simpl.
      econstructor.
      econstructor.
      
  } *)



  solve_symbolically n ; l.  
  assumption.
Qed.



Fixpoint prodMeta (v : Val) : Z :=
  match v with
    | VNil => 1%Z
    | VCons (VLit (Integer i)) tl => i * prodMeta tl
    | _ => 0
  end.

Definition prod (lst acc : Exp) : Exp :=
   ELetRec [(2,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar], (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °ELet 1 (ECall (˝VLit "erlang"%string) (˝VLit "*"%string) [˝VVar 0; ˝VVar 4])  (* NewAcc = 0 H = 1, T= 2,fun = 3, List =4, Acc =5 *)
           (EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 0]));  (* sum(T, NewAcc) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VVar 2)])]  (* return Acc *)
   (EApp (˝VFunId (0, 2)) [lst; acc]).

Theorem prod_is_correct:
  forall (n : Z) (m : Z) (l : Val),
    (0 <= n)%Z /\
    isWellFormedNumberList_n (Z.to_nat n) l /\
    VALCLOSED l ->
    exists (y : Z),
    ⟨ [], (prod (˝l) (˝VLit m)) ⟩ -->* RValSeq [VLit y] /\ (y = prodMeta l * m)%Z.
Proof.
  solve_symbolically n , m ; l.
  assumption.
Qed.


Fixpoint sumPlusOneMeta (v : Val) : Z :=
  match v with
    | VNil => 0%Z
    | VCons (VLit (Integer i)) tl => (i + 1) + sumPlusOneMeta tl
    | _ => 0
  end.

Definition sumPlusOne (lst acc : Exp) : Exp :=
   ELetRec [(2,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar], (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °ELet 1 (ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 0; ˝VVar 4])  (* NewAcc = 0 H = 1, T= 2,fun = 3, List =4, Acc =5 *)
           (°ELet 1 (ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 0; ˝VLit 1%Z]) 
            (EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 0])));  (* sum(T, NewAcc) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VVar 2)])]  (* return Acc *)
   (EApp (˝VFunId (0, 2)) [lst; acc]).

Theorem sumPlusOne_is_correct:
  forall (n : Z) (m : Z) (l : Val),
    (0 <= n)%Z /\
    isWellFormedNumberList_n (Z.to_nat n) l /\
    VALCLOSED l ->
    exists (y : Z),
    ⟨ [], (sumPlusOne (˝l) (˝VLit m)) ⟩ -->* RValSeq [VLit y] /\ (y = sumPlusOneMeta l + m)%Z.
Proof.
  solve_symbolically n , m ; l.
  assumption.
Qed.

Compute map (fun x => S x) [1 ; 2 ; 3].

Fixpoint mapPlusOneMeta l :=
match l with
| VNil => VNil
| (VCons (VLit (Integer i)) tl) => VCons (VLit (Integer (i + 1))) (mapPlusOneMeta tl)
| _ => VLit (Atom "error"%string)
end.

Compute mapPlusOneMeta (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 5%Z) VNil))).

Definition map_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 2) [˝VVar 0])) ((°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause"%string; ˝VLit "_5"%string;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).


(** Test map - inputs: ['FUN',[1,2]] *)
Goal forall (n : Z) (l : Val),
  (0 <= n)%Z /\
  isWellFormedNumberList_n (Z.to_nat n) l /\ VALCLOSED l -> exists y : Val,
  ⟨[], map_2 (°EFun 1 (°ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 0; ˝VLit (Integer 1%Z)])) (˝l)⟩
   -->* RValSeq [y] /\ y = mapPlusOneMeta l.
Proof.
 solve_symbolically n ; l.
 assumption.
 reflexivity.
Qed.







Fixpoint sublist_3Meta (L : Val) (s len : Z) :=
match L, s, len with
  | VNil, _, _ => VNil
  | _, _, 0%Z => VNil
  | (VCons hd tl), 1%Z, len => VCons hd (sublist_3Meta tl 1 (len - 1))
  | (VCons hd tl), (Z.pos p), len => sublist_3Meta tl (Z.pos p - 1) len
  | _, _, _ => VLit (Atom "error")
end.

Compute sublist_3Meta (VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VCons (VLit 5%Z) (VCons (VLit 6%Z) (VNil))))))) 1 5.

Definition sublist_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     (°ECase (EValues [˝VVar 1 ; ˝VVar 2 ; ˝VVar 3])
      [
      ([PNil ; PVar ; PVar], 
        ˝ttrue, 
        ˝VNil); (*case ([], Start, Len)*)
      ([PVar ; PVar ; (PLit (Integer 0%Z))], 
        ˝ttrue, 
        ˝VNil); (*case (List, Start, 0)*)
      ([(PCons PVar PVar) ; (PLit (Integer 1%Z)) ; PVar], (*0 = Head, 1 = Tail , 2 = Len; 3 = letrec, 4 = List, 5 = Start, 6 = Len*)
        ˝ttrue, 
        (°ELet 1 ((°ECall (˝VLit "erlang"%string) (˝VLit "-"%string) [˝VVar 2; ˝VLit (Integer 1%Z)])) (*0 = Len - 1 , 1 = Head, 2 = Tail , 3 = Len; 4 = letrec, 5 = List, 6 = Start, 7 = Len*)
          ((°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 2; ˝VLit (Integer 1%Z); ˝VVar 0])) (*0 = letrec(Tail, 1, Len - 1), 1 = Len - 1 , 2 = Head, 3 = Tail , 4 = Len; 5 = letrec, 6 = List, 7 = Start, 8 = Len*)
            ((°ECons (˝VVar 2) (˝VVar 0))))))); (*case ([H | T], 1, Len)*)
      ([(PCons PVar PVar); PVar ; PVar], (*0 = Head, 1 = Tail, 2 = Start , 3 = Len; 4 = letrec, 5 = List, 6 = Start, 7 = Len*)
        (°ECall (˝VLit "erlang"%string) (˝VLit ">"%string) [˝VVar 2; ˝VLit (Integer 1%Z)]), 
        (°ELet 1 ((°ECall (˝VLit "erlang"%string) (˝VLit "-"%string) [˝VVar 2; ˝VLit (Integer 1%Z)])) (*0 = Start - 1 , 1 = Head, 2 = Tail, 3 = Start , 4 = Len; 5 = letrec, 6 = List, 7 = Start, 8 = Len*)
          ((°EApp (˝VFunId (5, 3)) [˝VVar 2; ˝VVar 0; ˝VVar 4])))); (*case ([H | T], Start, Len) where Start > 1*)
      ([PVar ; PVar ; PVar],
        ˝ttrue, 
        °EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause"%string;˝VVar 0;˝VVar 1;˝VVar 2])])]))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Theorem sublist_3_is_correct:
  forall (n : Z) (m : Z) (t : Z) (l : Val),
    (0 <= n)%Z /\ (1 <= m)%Z /\
    (isWellFormedList_n (Z.to_nat n) l) /\
    VALCLOSED l ->
    exists (y : Val),
    ⟨ [], (sublist_3 (˝l) (˝VLit m) (˝VLit t)) ⟩ -->* RValSeq [y] /\ (y = sublist_3Meta l m t).
Proof.
  solve_symbolically n , m t ; l.

  6: {
    simpl in IHStripped.

    destruct ((t =? 0)%Z).
    {
      simpl.
      ltac1:(stepThousand).
      exists 0.
      reflexivity.
    }
    {
      simpl.
      destruct (m =? 1)%Z.
      {
        simpl.
        solve_substitutions ().
      }
      {

      }
    }
  }

  7: {
    destruct m.
    all: try ltac1:(nia).
    simpl.
    destruct p0.
  }
   
Admitted.



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

Theorem reverse_is_correct: 
  forall (n : Z) (m : Z) (l : Val) (lh : Val), (0 <= n)%Z /\ (0 <= m)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\  isWellFormedList_n (Z.to_nat m) lh /\
    VALCLOSED l /\ VALCLOSED lh ->
   exists (y : Val),
   ⟨ [], (reverse (˝l) (˝lh)) ⟩ -->* RValSeq [y] /\ y = reverseMetaHelp l lh.
Proof.
  solve_symbolically n , m ; l lh.
  all: ltac1:(scope_solver_v1).
Qed.

(*----------------------*)

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


(*Note: can we determine the functions operation? e.g. not just summing the elements but mapping (fun x => 2 * x + 1) on it?*)
(*Note: probably a proof hint is much more viable: what parameter is the induction on? What is its terminating function?
What function is applied to the additional parameters?*)
(*Note: Commutativity and associativity of addittion over Z needs to be applied manually*)
Theorem sum_is_correct:
  forall (n : Z) (m : Z) (l : Val),
    (0 <= n)%Z /\
    isWellFormedNumberList_n (Z.to_nat n) l /\
    VALCLOSED l ->
    exists (y : Z),
    ⟨ [], (sum (˝l) (˝VLit m)) ⟩ -->* RValSeq [VLit y] /\ (y = sumMeta l + m)%Z.
Proof.
  solve_symbolically n , m ; l.

  6: {
     solve_substitutions ().
     ltac1:(lia).
  }
  4,5: solve_substitutions (); assumption.
  3: {
    solve_substitutions ().
    assert (Z.to_nat (Z.pos p - 1) = n1) by ltac1:(lia).
    rewrite <- H in _PrecondVal0.
    exact _PrecondVal0.
  }
  1,2: ltac1:(lia).
Qed.

Fixpoint lengthMeta (v : Val) : Z :=
  match v with
    | VNil => 0%Z
    | VCons hd tl => 1 + lengthMeta tl
    | _ => 0
  end.

Definition length_1 (lst : Exp) : Exp :=
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
    ⟨ [], (length_1 (˝l)) ⟩ -->* RValSeq [VLit y] /\ (y = lengthMeta l)%Z.
Proof.
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

  6: solve_substitutions (); ltac1:(lia).
  4,5: solve_substitutions (); assumption.
  3: {
    solve_substitutions ().
    assert (Z.to_nat (Z.pos p - 1) = n1) by ltac1:(lia).
    rewrite <- H in _PrecondVal0.
    exact _PrecondVal0.
  }
  1,2: ltac1:(lia).
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
  6: {
     solve_substitutions ().
     ltac1:(lia).
  }
  4,5: solve_substitutions (); assumption.
  3: {
    solve_substitutions ().
    assert (Z.to_nat (Z.pos p - 1) = n1) by ltac1:(lia).
    rewrite <- H in _PrecondVal0.
    exact _PrecondVal0.
  }
  1,2: ltac1:(lia).
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
  6: {
     solve_substitutions ().
  }
  4,5: solve_substitutions (); assumption.
  3: {
    solve_substitutions ().
    assert (Z.to_nat (Z.pos p - 1) = n1) by ltac1:(lia).
    rewrite <- H in _PrecondVal0.
    exact _PrecondVal0.
  }
  1,2: ltac1:(lia).
Qed.

Fixpoint sublist_3Meta (L : Val) (s len : Z) :=
match L, s, len with
  | VNil, _, _ => VNil
  | _, _, 0%Z => VNil
  | (VCons hd tl), 1%Z, len => VCons hd (sublist_3Meta tl 1 (len - 1))
  | (VCons hd tl), (Z.pos p), len => sublist_3Meta tl (Z.pos p - 1) len
  | _, _, _ => VLit (Atom "error")
end.

(* Compute sublist_3Meta (VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VCons (VLit 5%Z) (VCons (VLit 6%Z) (VNil))))))) 1 5. *)

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

(*Needs lot of additional destructs*)
Theorem sublist_3_is_correct:
  forall (n : Z) (m : Z) (t : Z) (l : Val),
    (0 <= n)%Z /\ (1 <= m)%Z /\
    (isWellFormedList_n (Z.to_nat n) l) /\
    VALCLOSED l ->
    exists (y : Val),
    ⟨ [], (sublist_3 (˝l) (˝VLit m) (˝VLit t)) ⟩ -->* RValSeq [y] /\ (y = sublist_3Meta l m t).
Proof.
  (* solve_symbolically n , m t ; l. *)
Admitted.


Definition zip_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (EValues [˝VVar 1 ; ˝VVar 2])
      [([PNil ; PVar],  
        ˝ttrue, 
        ˝VNil);
      ([PVar ; PNil],  
        ˝ttrue,
        ˝VNil);
      ([(PCons PVar PVar); (PCons PVar PVar)], ˝ttrue,
        (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 1; ˝VVar 3])) 
          ((°ECons ((°ETuple [˝VVar 1;˝VVar 3])) (˝VVar 0)))))
        ])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition unzip_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],   
        ˝ttrue, 
        (°ETuple [˝VNil;˝VNil]));
      ([(PCons (PTuple [PVar; PVar]) PVar)],   
        ˝ttrue, 
        (°ECase ((°EApp (˝VFunId (3, 1)) [˝VVar 2])) 
          [([(PTuple [PVar;PVar])],   
            ˝ttrue, 
          (°ETuple [(°ECons (˝VVar 2) (˝VVar 0));(°ECons (˝VVar 3) (˝VVar 1))]))
          ]))
      ])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition zipClose := ((VClos [(0, 2, ° ECase (° EValues [˝ VVar 1; ˝ VVar 2]) [([PNil; PVar], ˝ VLit "true"%string, ˝ VNil); ([PVar; PNil], ˝ VLit "true"%string, ˝ VNil); ([PCons PVar PVar; PCons PVar PVar], ˝ VLit "true"%string, ° ELet 1 (° EApp (˝ VFunId (4, 2)) [˝ VVar 1; ˝ VVar 3]) (° ECons (° ETuple [˝ VVar 1; ˝ VVar 3])
(˝ VVar 0)))])] 0 2
(° ECase (° EValues [˝ VVar 1; ˝ VVar 2]) [([PNil; PVar], ˝ VLit "true"%string, ˝ VNil); ([PVar; PNil], ˝ VLit "true"%string, ˝ VNil); ([PCons PVar PVar; PCons PVar PVar], ˝ VLit "true"%string, ° ELet 1 (° EApp (˝ VFunId (4, 2)) [˝ VVar 1; ˝ VVar 3]) (° ECons (° ETuple [˝ VVar 1; ˝ VVar 3]) (˝ VVar 0)))]))).

Definition unZipClose := ((VClos [(0, 1, ° ECase (˝ VVar 1) [([PNil], ˝ VLit "true"%string, ° ETuple [˝ VNil; ˝ VNil]); ([PCons (PTuple [PVar; PVar]) PVar], ˝ VLit "true"%string, ° ECase (° EApp (˝ VFunId (3, 1)) [˝ VVar 2]) [([PTuple [PVar; PVar]], ˝ VLit "true"%string, ° ETuple [° ECons (˝ VVar 2) (˝ VVar 0); ° ECons (˝ VVar 3)
(˝ VVar 1)])])])] 0 1
(° ECase (˝ VVar 1) [([PNil], ˝ VLit "true"%string, ° ETuple [˝ VNil; ˝ VNil]); ([PCons (PTuple [PVar; PVar]) PVar], ˝ VLit "true"%string, ° ECase (° EApp (˝ VFunId (3, 1)) [˝ VVar 2]) [([PTuple [PVar; PVar]], ˝ VLit "true"%string, ° ETuple [° ECons (˝ VVar 2) (˝ VVar 0); ° ECons (˝ VVar 3) (˝ VVar 1)])])]))).


Lemma zip_terminates_as_a_tupleList : forall (n : Z) (xs ys : Val), 
(0 <= n)%Z /\ isWellFormedList_n (Z.to_nat n) xs /\ isWellFormedList_n (Z.to_nat n) ys /\ VALCLOSED xs /\ VALCLOSED ys -> 
exists y, ((⟨ [], (zip_2 (˝ xs) (˝ ys)) ⟩ -->* RValSeq [y]) /\ isWellFormed2TupleList_n (Z.to_nat n) y).
Proof.
  solve_symbolically n ; xs ys.

  1-2: assumption.
  solve_substitutions ().
  assert (Z.to_nat (Z.pos p - 1) = n1) by ltac1:(lia).
  rewrite H in IHPost.
  exact IHPost.
Qed.

Lemma unzip_terminates : forall (n : Z) (xs : Val), (0 <= n)%Z /\ isWellFormed2TupleList_n (Z.to_nat n) xs /\ VALCLOSED xs -> 
exists (y1 y2 : Val), (⟨ [], (unzip_1 (˝ xs)) ⟩ -->* RValSeq [VTuple [y1 ; y2]] ) /\ isWellFormedList_n (Z.to_nat n) y1 /\ isWellFormedList_n (Z.to_nat n) y2.
Proof.
  solve_symbolically n ; xs.

  6: {
    fold unZipClose.

    solve_substitutions ().
    
    
    1-3: inversion H3;pose (H1 0) as vClosed;
        simpl in vClosed; apply vClosed; auto.
    1-3: inversion H3;pose (H1 1) as vClosed;
        simpl in vClosed; apply vClosed; auto.


    destruct IHStripped as [IHRes2 IHTemp].
    destruct IHTemp as [IHExp IHPost].
    let ih_exp_t := Control.hyp @IHExp in
    pose (frame_indep_core_func _ _ _ _ $ih_exp_t) as IHExp_fic.
    simpl in IHExp_fic.

    eexists.
    eexists.
    
    eapply maxKTransitive'.
 
    let iHExp_fic_t := Control.hyp @IHExp_fic in
    apply $iHExp_fic_t.

    ltac1:(stepThousand).
    split.

    exists 0.
    solve_substitutions ().

    inversion H3.
    assert (Z.to_nat (Z.pos p - 1) = n1) by ltac1:(lia).
    rewrite <- H2.
    exact IHPost.
  }
  4-5: assumption.
  3: {
    assert (Z.to_nat (Z.pos p - 1) = n1) by ltac1:(lia).

    rewrite <- H  in _PrecondVal0.
    exact _PrecondVal0.
  }
  1-2: ltac1:(lia).
Qed.


Fixpoint zip {A B : Set} (a : list A) (b : list B) :=
match a, b with
| nil, _ => nil
| _, nil => nil
| (cons a atl), (cons b btl) => (a , b) :: (zip atl btl)
end.

Fixpoint unzip {A B : Set} (a : list (A * B)) :=
match a with
| nil => (nil , nil)
| cons (a, b) tl => let (fst, snd) := unzip tl in (a :: fst, b :: snd)
end.

Compute (zip [1;2;3] [4;5;6]).
Compute unzip (zip [1;2;3] [4;5;6]).
Compute unzip (zip [1;2;3] [4;5;6;7]).

Compute unzip [(1,2) ; (3,4); (5,6)].
Compute zip (fst (unzip [(1,2) ; (3,4); (5,6)])) (snd (unzip [(1,2) ; (3,4); (5,6)])).

Theorem rocq_unzip_is_rocq_zip_inverse :
  forall (A B : Set) (a : list A) (b : list B),
  0 <= length a /\ length a = length b ->
  unzip (zip a b) = (a , b).
Proof.
  intros.
  revert H.
  revert b.
  induction a.
  intros.
  simpl.
  inversion H.
  simpl in H1.
  destruct b.
  reflexivity.
  inversion H1.


  intros.
  destruct b.
  inversion H.
  simpl in H1.
  inversion H1.
  simpl.
  specialize (IHa b0).
  rewrite IHa.
  reflexivity.
  simpl in H.
  ltac1:(lia).
Qed.

Fixpoint metaZip (xs ys : Val) :=
match xs , ys with
| VCons _ _ , VNil => VNil
| VNil , VCons _ _ => VNil 
| VCons xh xtl , VCons yh ytl => VCons (VTuple [xh ; yh]) (metaZip xtl ytl)
| VNil , VNil => VNil
| _ , _ => VLit (Atom "error"%string)
end.

Fixpoint metaUnzip (xs : Val) :=
match xs with
| VNil => VTuple [VNil ; VNil]
| VCons (VTuple [a ; b]) tl => let rec := metaUnzip tl in 
                                          match rec with
                                          | VTuple [fs ; sn] => VTuple [VCons a fs ; VCons b sn]
                                          | _ => VLit (Atom "error"%string)
                                          end
| _ => VLit (Atom "error"%string)
end.

(*Call by name evaluation strategy with the ASSUMPTION, that the function close is side-effect and exception free!*)
(*Future work:
defining the call by name semantics and proving conditions when it is equivalent to the call by value semantics of core erlang*)
Parameter zip_call_by_name_eval : forall n (x y xs ys res : Val), isWellFormedList_n n xs /\ isWellFormedList_n n ys /\ VALCLOSED xs /\ VALCLOSED ys -> 
(exists n, sequentialStepMaxK [FParams (IApp zipClose) [xs ; ys] []] RBox n = ([], RValSeq [res])) ->
(exists n, sequentialStepMaxK [FParams (IApp zipClose) [xs ; ys] [] ; FLet 1 (° ECons (° (ETuple [˝x ; ˝y])) (˝ VVar 0))] RBox n = ([], RValSeq [VCons (VTuple [x ; y]) res])).

Parameter unZip_call_by_name_eval : forall n (a b resFst resSnd xs : Val), isWellFormed2TupleList_n n xs /\ VALCLOSED xs -> 
(exists n, sequentialStepMaxK [FParams (IApp unZipClose) [xs] []] RBox n = ([], RValSeq [VTuple [resFst ; resSnd]])) ->
(exists n, sequentialStepMaxK [FParams (IApp unZipClose) [xs] [];  
  FCase1 [([PTuple [PVar; PVar]], ˝ VLit "true"%string,
    ° ETuple [
      ° ECons (˝a) (˝ VVar 0);
      ° ECons (˝b) (˝ VVar 1)])]] RBox n 
= ([], RValSeq [VTuple [VCons a resFst ; VCons b resSnd]])).

(*We can still reason about the validity of this, since zip and unzip are SPECIFIC function closures.*)
(*The generality is highly doubtable, since the "second" function could just throw the result of the first one*)
(*Future work: Can it be determined that this kind of lazy evaluation is true for any two (or more) closures which satisfy some criteria, like
- effect-freeness, true usage of previous function results (doesn't just ignore the previous closures), etc. *)
(*When trying to compute zip and unzip individually, we need the structural information of unzip's input, i. e. it is the zipped tuple list created
from the inputs of zip.*)
Parameter zip_unzip_call_by_name_eval : forall n (x y xs ys : Val), isWellFormedList_n n xs /\ isWellFormedList_n n ys /\ VALCLOSED xs /\ VALCLOSED ys -> 
(exists n, sequentialStepMaxK [FParams (IApp zipClose) [xs ; ys] []; FParams (IApp unZipClose) [] []] RBox n = ([], RValSeq [VTuple [xs ; ys]])) ->
(exists n, sequentialStepMaxK [FParams (IApp zipClose) [xs ; ys] []; 
                               FLet 1 (° ECons (° (ETuple [˝x ; ˝y])) (˝ VVar 0));
                               FParams (IApp unZipClose) [] []] RBox n 
  = ([], RValSeq [VTuple [VCons x xs ; VCons y ys]])).
Theorem unzip_is_zip_inverse: 
  forall (n : Z) (l : Val) (lh : Val), (0 <= n)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\  isWellFormedList_n (Z.to_nat n) lh /\
    VALCLOSED l /\ VALCLOSED lh ->
    exists (y2 : Val), 
    ⟨ [], (unzip_1 (zip_2 (˝l) (˝lh))) ⟩ -->* RValSeq [y2] /\ y2 = VTuple [l ; lh].
Proof.
  solve_symbolically n ; l lh.

  11: {

    solve_substitutions ().
    
    pose (zip_unzip_call_by_name_eval n1 &l1 lh1 &l2 lh2) as Lazy_eval.
    eexists.
    
    2: reflexivity.
    eapply Lazy_eval.
    
     
    split.
    assumption.
    split.
    assumption.
    split.
    assumption.
    assumption.
    
    unfold zipClose.
    unfold unZipClose.
    
    destruct IHStripped as [IHExp IHPost].
    rewrite IHPost in IHExp.
    exact IHExp.
   }
   5-10: assumption.
   3: {
    pose (Nat2Z.id n1) as n1ToZ.
    rewrite <- n1ToZ in _PrecondVal0.
    exact _PrecondVal0.
   }
   3: {
    pose (Nat2Z.id n1) as n1ToZ.
    rewrite <- n1ToZ in _PrecondVal1.
    exact _PrecondVal1.
   }
   1-2: (ltac1:(lia)).
Qed.



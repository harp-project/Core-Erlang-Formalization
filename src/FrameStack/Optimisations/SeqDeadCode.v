From CoreErlang.FrameStack Require Import SubstSemanticsLemmas
                                          CIU
                                          CTX
                                          Compatibility.

Import ListNotations.

Definition is_exit_bif (modu func : string) (n : nat) : bool :=
match convert_string_to_code (modu, func) with
| BThrow | BExit => Nat.eqb n 1
| BError => Nat.eqb n 1 || Nat.eqb n 2
| _ => false
end.

Definition is_safe (modu func : string) (n : nat) : bool :=
match convert_string_to_code (modu, func) with
| BEq | BTypeEq | BNeq | BTypeNeq
| BLe | BLt | BGe | BGt           => Nat.eqb n 2
(**)
| BIsAtom | BIsNumber | BIsBoolean | BIsInteger => Nat.eqb n 1
(* TODO: rest of the bifs in erl_bifs.erl *)
| _ => false
end.

Fixpoint will_fail (e : Exp) : bool :=
match e with
| ELet _ e1 e2 => will_fail e1 || will_fail e2
| EPrimOp name _  => match convert_primop_to_code name with
                     | PMatchFail => true
                     | _ => false
                     end
| ECall (VVal (VLit (Atom modu))) (VVal (VLit (Atom func))) args =>
   is_exit_bif modu func (length args)
| _ => false
end.

Fixpoint is_safe_simple (e : Exp) : bool :=
match e with
| VVal (VLit _) => true
| VVal (VFunId _) => false
| VVal (VVar _) => true
| EExp (ECons e1 e2) => is_safe_simple e1 && is_safe_simple e2
| EExp (ETuple l) => forallb is_safe_simple l
| EExp (ECall (VVal (VLit (Atom modu))) (VVal (VLit (Atom func))) args) =>
  is_safe modu func (length args) (* TODO: missing parts *)
| _ => false
end.

Fixpoint seq_elim (e : Exp) : Exp :=
(*   match fuel with
  | O => e  (* out of fuel: return original expression unchanged *)
  | S => *)
    match e with
    | VVal v => VVal v
    | EExp nv =>
      match nv with
      | EFun vl body =>
          EExp (EFun vl (seq_elim body))
      | EValues l =>
          EExp (EValues (map (fun x => seq_elim x) l))
      | ECons hd tl =>
          EExp (ECons (seq_elim hd) (seq_elim tl))
      | ETuple l =>
          EExp (ETuple (map (fun x => seq_elim x) l))
      | EMap l =>
          EExp (EMap (map (fun '(a,b) => (seq_elim a, seq_elim b)) l))
      | ECall m f l =>
          EExp (ECall (seq_elim m) (seq_elim f) (map (fun x => seq_elim x) l))
      | EPrimOp fn l =>
          EExp (EPrimOp fn (map (fun x => seq_elim x) l))
      | EApp e0 l =>
          EExp (EApp (seq_elim e0) (map (fun x => seq_elim x) l))
      | ECase e0 branches =>
          let e0' := seq_elim e0 in
          let branches' := map (fun '(p,g,b) => (p, seq_elim g, seq_elim b)) branches in
          EExp (ECase e0' branches')
      | ELet n e1 e2 =>
          EExp (ELet n (seq_elim e1) (seq_elim e2))
      | ESeq e1 e2 =>
          (* First fold the left part *)
          let e1' := seq_elim e1 in
          let e2' := seq_elim e2 in
            if will_fail e1' then e1'
            else
              match is_safe_simple e1', is_safe_simple e2' with
              | true, _      => e2'
              | false, true  => e1'
              | false, false => ESeq e1' e2'
              end
      | ELetRec l ebody =>
          let l' := map (fun '(n, e0) => (n, seq_elim e0)) l in
          EExp (ELetRec l' (seq_elim ebody))
      | ETry e1 vl1 e2 vl2 e3 =>
          EExp (ETry (seq_elim e1) vl1 (seq_elim e2) vl2 (seq_elim e3))
      end
    end
(*   end *).

Fixpoint size_val (v : Val) : nat :=
  match v with
  | VNil => 1
  | VLit _ => 1
  | VPid _ => 1
  | VCons hd tl => 1 + size_val hd + size_val tl
  | VTuple l => 1 + fold_left (fun acc v => acc + size_val v) l 0
  | VMap pairs => 1 + fold_left (fun acc '(a,b) => acc + size_val a + size_val b) pairs 0
  | VVar _ => 1
  | VFunId _ => 1
  | VClos ext _ _ e => 1 + fold_left (fun acc '(_,_,e0) => acc + size_exp e0) ext 0 + size_exp e
  end
with size_exp (e : Exp) : nat :=
  match e with
  | VVal v => 1 + size_val v
  | EExp nv => 1 + size_nonval nv
  end
with size_nonval (nv : NonVal) : nat :=
  match nv with
    | EFun _ e => size_exp e
    | EValues l => fold_left (fun acc e => acc + size_exp e) l 0
    | ECons hd tl => size_exp hd + size_exp tl
    | ETuple l => fold_left (fun acc e => acc + size_exp e) l 0
    | EMap l => fold_left (fun acc '(a,b) => acc + size_exp a + size_exp b) l 0
    | ECall m f l => size_exp m + size_exp f + fold_left (fun acc e => acc + size_exp e) l 0
    | EPrimOp _ l => fold_left (fun acc e => acc + size_exp e) l 0
    | EApp e l => size_exp e + fold_left (fun acc e => acc + size_exp e) l 0
    | ECase e branches => size_exp e + fold_left (fun acc '(_,g,b) => acc + size_exp g + size_exp b) branches 0
    | ELet _ e1 e2 => size_exp e1 + size_exp e2
    | ESeq e1 e2 => size_exp e1 + size_exp e2
    | ELetRec l e => fold_left (fun acc '(_,e0) => acc + size_exp e0) l 0 + size_exp e
    | ETry e1 _ e2 _ e3 => size_exp e1 + size_exp e2 + size_exp e3
  end.

Lemma closed_seq_elim Γ e :
  EXP Γ ⊢ e -> EXP Γ ⊢ (seq_elim e).
Proof.
Admitted.

Lemma will_fail_exception :
  forall e, will_fail e ->
    exists exc, ⟨[], e⟩ -->* RExc exc.
Proof.
  
Admitted.

Require Import SubstSemanticsLabeled.
Lemma is_safe_simple_no_effects: 
  forall e, is_safe_simple e ->
    exists vs, ⟨[], e⟩  -[ [] ]->ₗ* ⟨[], RValSeq vs⟩.
Proof.
  
Admitted.

Lemma eval_seq_optim_1 :
  forall e1 e2 res,
   ⟨ [], (° ESeq e1 e2)⟩ -->* res ->
   ⟨ [], (if will_fail (seq_elim e1)
   then seq_elim e1
   else
    if is_safe_simple (seq_elim e1)
    then seq_elim e2
    else
     if is_safe_simple (seq_elim e2)
     then seq_elim e1
     else ° ESeq (seq_elim e1) (seq_elim e2)) ⟩ -->* res.
Proof.

Admitted.

Lemma eval_seq_optim_2 :
  forall e1 e2 res,
   ⟨ [], (if will_fail (seq_elim e1)
   then seq_elim e1
   else
    if is_safe_simple (seq_elim e1)
    then seq_elim e2
    else
     if is_safe_simple (seq_elim e2)
     then seq_elim e1
     else ° ESeq (seq_elim e1) (seq_elim e2)) ⟩ -->* res
     ->
      ⟨ [], (° ESeq e1 e2)⟩ -->* res.
Proof.

Admitted.

Theorem seq_optim Γ (e : Exp) :
  EXP Γ ⊢ e ->
  CIU_open Γ e (seq_elim e).
Proof.
  remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H Γ.
  induction n using lt_wf_ind. destruct e; simpl; intros.
  { apply CIU_iff_Rrel. auto. }
  pose proof CIU_IsPreCtxRel as CONG.
  destruct e; simpl.
  * apply CONG; auto.
    - by destruct_scopes.
    - apply closed_seq_elim. by destruct_scopes.
    - eapply H. 2: reflexivity. 2: by destruct_scopes.
      simpl in H0. lia.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * split. 2: split.
    - apply -> subst_preserves_scope_red. 2: exact H2. scope_solver.
    - apply -> subst_preserves_scope_red. 2: exact H2.
      repeat case_match.
      1-3: constructor; apply closed_seq_elim; by destruct_scopes.
      do 3 constructor;
      destruct_scopes;
      by apply closed_seq_elim.
    - intros. destruct H4.
      simpl in *.

  * admit.
  * admit.
Admitted.

Theorem seq_optim (e : Exp) :
  EXPCLOSED e ->
  CIU (seq_elim e) e.
Proof.

Qed.


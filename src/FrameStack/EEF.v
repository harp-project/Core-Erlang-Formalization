From CoreErlang.FrameStack Require Export Frames SubstSemantics.
From CoreErlang Require Export Auxiliaries Matching.
From CoreErlang.Concurrent Require Export ProcessSemantics.

Import ListNotations.
Import Coq.Lists.List.

Fixpoint Exp_eqb_strict (e1 e2 : Exp) : bool :=
  match e1, e2 with
  | VVal a, VVal a' => Val_eqb_strict a a'
  | EExp (EValues l), EExp (EValues l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') 
                                 (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EFun vl e), EExp (EFun vl' e') => Nat.eqb vl vl' && Exp_eqb_strict e e'
  | EExp (ECons hd tl), EExp (ECons hd' tl') => Exp_eqb_strict hd hd' && Exp_eqb_strict tl tl'
  | EExp (ETuple l), EExp (ETuple l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (ECall m f l), EExp (ECall m' f' l') => Exp_eqb_strict f f' && Exp_eqb_strict m m' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EPrimOp f l), EExp (EPrimOp f' l') => String.eqb f f' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EApp exp l), EExp (EApp exp' l') => Exp_eqb_strict exp exp' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (ECase e l), EExp (ECase e' l') => Exp_eqb_strict e e' 
      && Nat.eqb (length l) (length l') 
      && (fix blist l l' := match l, l' with
        | [], [] => true
        | (pl,y,z)::xs, (pl',y',z')::xs' => andb (
          (fix blist l l' := match l, l' with
          | [], [] => true
          | x::xs, x'::xs' => andb (Pat_eqb x x') (blist xs xs')
          | _, _ => false
          end) pl pl') 
          (andb (Exp_eqb_strict y y') (andb (Exp_eqb_strict z z') (blist xs xs')))
                                           | _, _ => false
                                           end) l l' 
  | EExp (ELet l e1 e2), EExp (ELet l' e1' e2') => 
      Nat.eqb l l' && Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2'
  | EExp (ESeq e1 e2), EExp (ESeq e1' e2') => andb (Exp_eqb_strict e1 e1') (Exp_eqb_strict e2 e2')
  | EExp (ELetRec l e), EExp (ELetRec l' e') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Nat.eqb x x') (andb (Exp_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l' && Exp_eqb_strict e e'
  | EExp (EMap l), EExp (EMap l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Exp_eqb_strict x x') (andb (Exp_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l'
  | EExp (ETry e1 vl1 e2 vl2 e3), EExp (ETry e1' vl1' e2' vl2' e3') => 
      Nat.eqb vl1 vl1' && Nat.eqb vl2 vl2' &&
      Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2' && Exp_eqb_strict e3 e3'
  | _, _ => false
  end
with Val_eqb_strict (v1 v2 : Val) : bool :=
  match v1, v2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Lit_beq l l'
  | VPid p, VPid p' => Nat.eqb p p'
  | VCons hd tl, VCons hd' tl' => Val_eqb_strict hd hd' && Val_eqb_strict tl tl'
  | VTuple l, VTuple l' => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Val_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | VMap l, VMap l' => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Val_eqb_strict x x') (andb (Val_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l'
  | VVar v, VVar v' => Nat.eqb v v'
  | VFunId v, VFunId v' => funid_eqb v v'
  | VClos ext id vc e, VClos ext' id' vc' e' => 
      Nat.eqb id id' && Nat.eqb vc vc' && Exp_eqb_strict e e' &&
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (n1,n2,e)::xs, (n1',n2',e')::xs' => 
        andb (Exp_eqb_strict e e') (andb (Nat.eqb n1 n1') (andb (Nat.eqb n2 n2') (blist xs xs')))
        | _, _ => false
        end) ext ext'
  | _, _ => false
  end.

Compute Val_eqb_strict (VPid 2) (VPid 3).
Compute Val_eqb (VPid 2) (VPid 3).

Open Scope string_scope.

Theorem Val_eqb_strict_eq: forall v1 v2, Val_eqb_strict v1 v2 = true <-> v1 = v2.
Proof.

Admitted.

Fixpoint valclosed_func (v : Val) : bool :=
  match v with
    (* scoped_nil *)
    | VNil => true
    
    (* scoped_lit *)
    | VLit _ => true
    
    (* scoped_pid *)
    | VPid _ => true
    
    (* scoped_var *)
    | VVar _ => false
    
    (* scoped_funId *)
    | VFunId _ => false
    
    (* scoped_vtuple *)
    | VTuple l => (fix tuple_f (li : list Val) : bool :=
                    match li with
                    | [] => true
                    | x :: xs => andb (valclosed_func x) (tuple_f xs)
                    end) l
    
    (* scoped_vcons *)
    | VCons hd tl => (valclosed_func hd) && (valclosed_func tl)
    
    (* scoped_vmap *)
    | VMap l => (fix tuple_f (li : list (Val * Val)) : bool :=
                    match li with
                    | [] => true
                    | (x1, x2) :: xs => andb (valclosed_func x1) (andb (valclosed_func x2) (tuple_f xs))
                    end) l
    
    (* scoped_vclos *)
    (* TODO *)
    
    | _ => false
  end.

Theorem valclosed_equiv: forall (v : Val), VALCLOSED v <-> valclosed_func v = true.
Proof.

Admitted.

Fixpoint valscoped_func (n : nat) (v : Val) : bool :=
  match v with
    (* scoped_nil *)
    | VNil => true
    
    (* scoped_lit *)
    | VLit _ => true
    
    (* scoped_pid *)
    | VPid _ => true
    
    (* scoped_var *)
    | VVar v => v <? n
    
    (* scoped_funId *)
    | VFunId fi => fst fi <? n
    
    (* scoped_vtuple *)
    | VTuple l => (fix tuple_f (li : list Val) : bool :=
                    match li with
                    | [] => true
                    | x :: xs => andb (valscoped_func n x) (tuple_f xs)
                    end) l
    
    (* scoped_vcons *)
    | VCons hd tl => (valscoped_func n hd) && (valscoped_func n tl)
    
    (* scoped_vmap *)
    | VMap l => (fix tuple_f (li : list (Val * Val)) : bool :=
                 match li with
                 | [] => true
                 | (x1, x2) :: xs => 
                     andb (valscoped_func n x1) (andb (valscoped_func n x2) (tuple_f xs))
                 end) l
    
    (* scoped_vclos *)
    (* TODO *)
    
    | _ => false
    end.

Theorem valscoped_equiv: forall (n : nat) (v : Val), ValScoped n v <-> valscoped_func n v = true.
Proof.
  intros. split.
  * intro. induction H; simpl; try reflexivity.
    + rewrite Nat.ltb_lt. assumption.
    + rewrite Nat.ltb_lt. assumption.
    + clear H. specialize (H0 0). admit.
    + rewrite IHValScoped1. rewrite IHValScoped2. reflexivity.
    + admit.
    + admit.
  * intro. admit.
Admitted.

Definition valclosed_func' (v : Val) : bool := valscoped_func 0 v.

Locate "˝".


Definition step_func : FrameStack -> Redex -> option (FrameStack * Redex) :=
  fun fs r =>
    match r with
      (* cool_value *)
      | ˝v => match valclosed_func v with
              | true => Some (fs, RValSeq [v])
              | _ => None
              end
      
      | RValSeq vs =>
          match fs with
          (* eval_cool_let *)
          | (FLet l e2)::xs => match length vs =? l with
                               | true => Some ( xs, RExp (e2.[ list_subst vs idsubst ]) )
                               | _ => None
                               end
          
          (* eval_step_case_match and eval_step_case_not_match *)
          | (FCase1 ((lp,e1,e2)::l))::xs => 
            match match_pattern_list lp vs with
            | Some vs' => 
                Some ((FCase2 vs e2.[list_subst vs' idsubst] l)::xs, 
                RExp (e1.[list_subst vs' idsubst]) )
            | None => Some ( (FCase1 l)::xs, RValSeq vs )
            end
          
          (* eval_cool_case_empty *)
          | (FCase1 [])::xs => Some ( xs, RExc if_clause )
          
          (* eval_cool_try_ok *)
          | (FTry vl1 e2 _ e3)::xs => match vl1 =? length vs with
                                      | true => Some ( xs, RExp e2.[ list_subst vs idsubst ] )
                                      | _ => None
                                      end
      
      (* | RValSeq [v] => *)
          (* eval_step_params *)
          | FParams ident vl (e :: el) :: xs => 
              match vs with
              | [v] => Some (FParams ident (vl ++ [v]) el :: xs , RExp e)
              | _ => None
              end
          
          (* eval_cool_params *)
          | FParams ident vl [] ::xs => 
              match vs with
              | [v] => match create_result ident (vl ++ [v]) with
                       | Some (res, l) => Some (xs, res)
                       | None => None
                       end
              | _ => None
              end
          
          (* eval_heat_call_fun *)
          | FCallMod f el :: xs => 
              match vs with
              | [v] => Some ( FCallFun v el :: xs, RExp f )
              | _ => None
              end
          
          (* eval_heat_call_params *)
          | FCallFun m el :: xs => 
              match vs with
              | [v] => Some ( (FParams (ICall m v) [] el)::xs, RBox )
              | _ => None
              end
          
          (* eval_heat_app2 *)
          | FApp1 el :: xs => 
              match vs with
              | [v] => Some ( (FParams (IApp v) [] el)::xs, RBox )
              | _ => None
              end
          
          (* eval_cool_cons_1 *)
          | (FCons1 hd )::xs => 
              match vs with
              | [v] => Some ( (FCons2 v)::xs, RExp hd )
              | _ => None
              end
          
          (* eval_cool_cons_2 *)
          | (FCons2 tl)::xs => 
              match vs with 
              | [v] => Some ( xs, RValSeq [VCons v tl] )
              | _ => None
              end
          
          (* eval_cool_seq *)
          | (FSeq e2)::xs => 
              match vs with
              | [v] => Some ( xs, RExp e2 )
              | _ => None
              end
          
          (* eval_step_case_true and eval_step_case_false *)
          | (FCase2 vs' e' l)::xs => 
              match vs with
              | [VLit (Atom "true")] => Some ( xs, RExp e' )
              | [VLit (Atom "false")] => Some ((FCase1 l)::xs, RValSeq vs' )
              | _ => None
              end
          
          | _ => None
          end
      
      (* eval_heat_values *)
      | EValues el => Some ((FParams IValues [] el)::fs , RBox)
      
      (* eval_heat_tuple *)
      | ETuple el => Some ((FParams ITuple [] el)::fs, RBox )
    
      (* eval_heat_map_0 *)
      | EMap [] => Some (fs, RValSeq [VMap []] )
      
      (* eval_heat_map *)
      | EMap ((e1, e2) :: el) =>
          Some ((FParams IMap [] (e2 :: flatten_list el))::fs, RExp e1 )
          
      (* eval_heat_call_mod *)
      | ECall m f el => Some ( FCallMod f el :: fs, RExp m )
      
      (* eval_heat_primop *)
      | EPrimOp f el => Some ( (FParams (IPrimOp f) [] el)::fs, RBox )
      
      (* eval_heat_app *)
      | EApp e l => Some (FApp1 l :: fs, RExp e)
      
      (* eval_heat_cons *)
      | ECons hd tl => Some ( (FCons1 hd)::fs, RExp tl )
      
      (* eval_heat_let *)
      | ELet l e1 e2 => Some ( (FLet l e2)::fs, RExp e1 )
      
      (* eval_heat_seq *)
      | ESeq e1 e2 => Some ( (FSeq e2)::fs, RExp e1 )

      (* eval_cool_fun *)
      | EFun vl e => Some (fs, RValSeq [ VClos [] 0 vl e ])

      (* eval_heat_case *)
      | ECase e l => Some ( (FCase1 l)::fs, RExp e )
      
      (* eval_heat_letrec *)
      | ELetRec l e => let lc := convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) in
                           Some (fs, RExp e.[list_subst lc idsubst] )
      
      (* eval_heat_try *)
      | ETry e1 vl1 e2 vl2 e3 => Some ( (FTry vl1 e2 vl2 e3)::fs, RExp e1 )
      
      | RBox => match fs with
                (* eval_step_params_0 *)
                | FParams ident vl (e::el) ::xs => match ident with
                                              | IMap => None
                                              | _ => Some (FParams ident vl el :: xs, RExp e)
                                              end
                (* eval_cool_params_0 *)
                | FParams ident vl [] ::xs => match ident with
                                              | IMap => None
                                              | _ => match create_result ident vl with
                                                     | Some (res, l) => Some (xs, res)
                                                     | None => None
                                                     end
                                              end
                | _ => None
                end
      
      | RExc (class, reason, details) =>
          (* eval_cool_try_err *)
          match fs with
          | (FTry vl1 e2 3 e3)::xs =>
              Some ( xs, RExp e3.[ 
                list_subst [exclass_to_value class; reason; details] idsubst ] )
          
          (* eval_prop_exc *)
          | F::xs => match isPropagatable F with
                     | true => Some ( xs, RExc (class, reason, details) )
                     | _ => None
                     end
          
          | _ => None
          end
    end.

Print step_func.

Theorem step_equiv: forall fs fs' e e', 
    ⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩ <-> step_func fs e = Some (fs', e').
Proof.
  intros. split.
  * intro. inversion H; try auto; unfold step_func.
    + apply valclosed_equiv in H0. rewrite H0. reflexivity.
    + destruct ident; try reflexivity. congruence.
    + rewrite <- H1. destruct ident; try reflexivity. congruence.
    + rewrite <- H0. reflexivity.
    + rewrite H0. rewrite Nat.eqb_refl. reflexivity.
    + rewrite H0. reflexivity.
    + rewrite H0. reflexivity.
    + rewrite H0. reflexivity.
    + rewrite <- H0. rewrite Nat.eqb_refl. reflexivity.
    + destruct exc. destruct p. rewrite H0.
      destruct F; try reflexivity.
      do 4 (destruct vl2; try reflexivity). simpl.
      unfold exclass_to_value. destruct e0; destruct e3; simpl; destruct e0; discriminate.
  * intro. destruct e.
    + destruct e.
      - simpl in H. destruct (valclosed_func e) eqn:He; try discriminate.
        inversion H. subst. apply cool_value. apply valclosed_equiv in He. assumption.
      - simpl in H. destruct e; try (inv H; constructor); try reflexivity.
        destruct l eqn:Hl.
        ** inv H. constructor.
        ** destruct p. inv H. constructor.
    + simpl in H. destruct fs; try discriminate.
      destruct f; destruct vs; try discriminate.
      - destruct vs. inv H. constructor. discriminate.
      - destruct vs. inv H. constructor. discriminate.
      - destruct el; discriminate.
      - destruct el.
        ** destruct vs; try discriminate.
           destruct (create_result ident (vl ++ [v])) eqn:H'; try discriminate.
           destruct p. inv H.
           apply eval_cool_params with (l := o). rewrite H'. reflexivity.
        ** destruct vs; try discriminate. inv H. constructor.
      - destruct vs; try discriminate. inv H. constructor.
      - destruct vs; try discriminate. inv H. constructor.
      - destruct vs; try discriminate. inv H. constructor.
      - destruct l. inv H. constructor.
        destruct p. destruct p. destruct (match_pattern_list l0 []) eqn:H'.
        inv H. constructor. assumption.
        inv H. constructor. assumption.
      - destruct l. inv H. constructor.
        destruct p. destruct p. destruct (match_pattern_list l0 (v :: vs)) eqn:H'.
        inv H. constructor. assumption.
        inv H. constructor. assumption.
      - destruct v; try discriminate. destruct l; try discriminate.
        do 4 (destruct s; try discriminate; destruct a; try discriminate;
        destruct b; try discriminate; destruct b0; try discriminate;
        destruct b1; try discriminate; destruct b2; try discriminate;
        destruct b3; try discriminate; destruct b4; try discriminate;
        destruct b5; try discriminate; destruct b6; try discriminate).
        ** destruct s; try discriminate; destruct a; try discriminate;
           destruct b; try discriminate; destruct b0; try discriminate;
           destruct b1; try discriminate; destruct b2; try discriminate;
           destruct b3; try discriminate; destruct b4; try discriminate;
           destruct b5; try discriminate; destruct b6; try discriminate.
           destruct s; try discriminate. destruct vs; try discriminate.
           inv H. constructor.
        ** destruct s; try discriminate. destruct vs; try discriminate.
           inv H. constructor.
      - simpl in H. destruct l.
        ** inv H. constructor. reflexivity.
        ** discriminate.
      - simpl in H. destruct l. discriminate.
        destruct (Datatypes.length vs =? l) eqn:H'.
        inv H. constructor. simpl. f_equal. apply Nat.eqb_eq. assumption.
        discriminate.
      - destruct vs; try discriminate. inv H. constructor.
      - simpl in H. destruct (vl1 =? 0) eqn:H'.
        inv H. constructor. simpl. apply Nat.eqb_eq. assumption.
        discriminate.
      - simpl in H. destruct (vl1 =? S (Datatypes.length vs)) eqn:H'.
        inv H. constructor. simpl. apply Nat.eqb_eq. assumption.
        discriminate.
    + simpl in H. destruct e. destruct p. destruct fs. discriminate.
      destruct f; simpl in *; inv H; try constructor; simpl; try reflexivity.
      do 4 (destruct vl2; try discriminate). inv H1. constructor.
    + simpl in H. destruct fs; try discriminate.
      destruct f; try discriminate. destruct el.
      - destruct ident; try discriminate; simpl in H; inv H.
        ** apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
        ** apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
        ** destruct m; inv H1; 
           try (apply eval_cool_params_0 with (l := None); try discriminate; try reflexivity).
           destruct l.
           ++ destruct f; inv H0;
              try (apply eval_cool_params_0 with (l := None); try discriminate; try reflexivity).
              destruct l.
              -- destruct (eval s s0 vl) eqn:H'; try discriminate. destruct p. inv H1.
                 apply eval_cool_params_0 with (l := o). discriminate.
                 simpl. rewrite H'. reflexivity.
              -- inv H1. apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
           ++ inv H0. apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
        ** destruct (primop_eval f vl) eqn:H'; try discriminate. destruct p. inv H1.
           apply eval_cool_params_0 with (l := o). discriminate. simpl.
           rewrite H'. reflexivity.
        ** destruct v; inv H1;
           try (apply eval_cool_params_0 with (l := None); try discriminate; try reflexivity).
           destruct (params =? Datatypes.length vl) eqn:H'.
           ++ inv H0.
              apply eval_cool_params_0 with (l := None). discriminate.
              simpl. rewrite H'. reflexivity.
           ++ inv H0.
              apply eval_cool_params_0 with (l := None). discriminate.
              simpl. rewrite H'. reflexivity.
      - destruct ident; try discriminate; simpl in H; inv H; constructor; discriminate.
Qed.

(* ------------------------------------------------------------- *)

Definition plsASendSExit :
  PID -> Val -> bool ->
  Process -> option Process :=

  fun ι v is_dead p =>
    if is_dead
    (* p_dead *)
    then
      match p with
      | inr links =>
        match (links !! ι) with
        | Some reason =>
          if bool_decide (reason = v)
           then 
            if valclosed_func v
            then Some (inr (delete ι links))
            else None
           else None
        | _ => None
        end
      | _ => None
      end
    (* p_exit *)
    else
      match p with
      | inl (FParams (ICall erlang exit) [VPid ι'] [] :: fs, RValSeq [v'], mb, links, flag) =>
        if (bool_decide (v' = v) && (ι' =? ι))
          then 
            if valclosed_func v
            then Some (inl (fs, RValSeq [ttrue], mb, links, flag))
            else None
          else None
      | _ => None
      end.

Definition processLocalStepASend : PID -> Signal -> Process ->
  option Process :=

  fun ι msg p =>
    match msg with
    (* p_send *)
    | SMessage v =>
      match p with 
      | inl (FParams (ICall erlang send) [VPid ι'] [] :: fs, RValSeq [v'], mb, links, flag) =>
        if bool_decide (v' = v) && (ι' =? ι)
          then 
            if valclosed_func v 
            then Some (inl (fs, RValSeq [v], mb, links, flag))
            else None
          else None
      | _ => None
      end
    (* p_link *)
    | SLink =>
      match p with
      | inl (FParams (ICall erlang link) [] [] :: fs, RValSeq [VPid ι'], mb, links, flag) =>
        if (ι' =? ι)
          then Some (inl (fs, RValSeq [ok], mb, {[ι]} ∪ links, flag))
          else None
      | _ => None
      end
    (* p_unlink *)
    | SUnlink =>
      match p with
      | inl (FParams (ICall erlang unlink) [] [] :: fs, RValSeq [VPid ι'], mb, links, flag) =>
        if (ι' =? ι)
          then Some (inl (fs, RValSeq [ok], mb, links ∖ {[ι]}, flag))
          else None
      | _ => None
      end
    (* p_dead and p_exit *)
    | SExit v is_dead => plsASendSExit ι v is_dead p
    end.

Print processLocalStepASend.

(* ------------------------------------------------------------- *)

Definition plsAArriveSExit :
  PID -> PID -> Val -> bool ->
  Process -> option Process :=
  
  fun source dest reason b p => 
    match p with
    | inl (fs, e, mb, links, flag) =>
      if flag
      then 
        if b
        then 
          if gset_elem_of_dec source links
          then Some (inl (fs, e, mailboxPush mb (VTuple [EXIT; VPid source; reason]), links, true))
          else 
            if dest =? source
            then None
            else Some p
        else
          if reason =ᵥ kill
          then Some (inr (gset_to_gmap killed links))
          else Some (inl (fs, e, mailboxPush mb (VTuple [EXIT; VPid source; reason]), links, true))
      else 
        if dest =? source
        then 
          if b
          then 
            if reason =ᵥ normal
            then Some (inr (gset_to_gmap normal links))
            else
              if gset_elem_of_dec source links
              then Some (inr (gset_to_gmap reason links))
              else None
          else
            if reason =ᵥ kill
            then Some (inr (gset_to_gmap killed links))
            else Some (inr (gset_to_gmap reason links))
        else
          if b
          then
            if reason =ᵥ normal
            then Some p
            else 
              if gset_elem_of_dec source links
              then Some (inr (gset_to_gmap reason links))
              else Some p
          else
            if reason =ᵥ normal
            then Some p
            else
              if reason =ᵥ kill
              then Some (inr (gset_to_gmap killed links))
              else Some (inr (gset_to_gmap reason links))
    | _ => None
    end.

Print plsAArriveSExit.

Definition processLocalStepAArrive : PID -> PID -> Signal -> Process -> 
  option Process :=

  fun source dest msg p =>
    match msg with
    (* p_arrive *)
    | SMessage v => 
      match p with
      | inl (fs, e, mb, links, flag) => Some (inl (fs, e, mailboxPush mb v, links, flag))
      | _ => None
      end
    (* p_exit_drop, p_exit_terminate and p_exit_convert *)
    | SExit reason b => plsAArriveSExit source dest reason b p
    (* p_link_arrived *)
    | SLink => 
      match p with
      | inl (fs, e, mb, links, flag) => Some (inl (fs, e, mb, {[source]} ∪ links, flag))
      | _ => None
      end
    (* p_unlink_arrived *)
    | SUnlink => 
      match p with
      | inl (fs, e, mb, links, flag) => Some (inl (fs, e, mb, links ∖ {[source]}, flag))
      | _ => None
      end
    end.

Print processLocalStepAArrive.

(* ------------------------------------------------------------- *)

Definition processLocalStepASelf : PID -> Process -> option Process :=
  fun ι p =>
    match p with
    (* p_self *)
    | inl (FParams (ICall erlang self) [] [] :: fs, RBox, mb, links, flag) =>
        Some (inl (fs, RValSeq [VPid ι], mb, links, flag))
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition plsASpawnSpawn :
  PID -> list (nat * nat * Exp) -> nat -> nat -> Exp -> Val ->
  Process -> option Process :=

  fun ι ext id vars e l p =>
    match p with
    | inl (FParams (ICall erlang spawn) [lv] [] :: fs, RValSeq [l'], mb, links, flag) =>
      if (bool_decide (lv = VClos ext id vars e) && bool_decide (l' = l))
        then Some (inl (fs, RValSeq [VPid ι], mb, links, flag))
        else None
    | _ => None
    end.

Definition plsASpawnSpawnLink :
  PID -> list (nat * nat * Exp) -> nat -> nat -> Exp -> Val ->
  Process -> option Process :=

  fun ι ext id vars e l p =>
    match p with
    | inl (FParams (ICall erlang spawn_link) [lv] [] :: fs, RValSeq [l'], mb, links, flag) =>
      if (bool_decide (lv = VClos ext id vars e) && bool_decide (l' = l))
        then Some (inl (fs, RValSeq [VPid ι], mb, {[ι]} ∪ links, flag))
        else None
    | _ => None
    end.

Print plsASpawnSpawnLink.

Definition processLocalStepASpawn :
  PID -> list (nat * nat * Exp) -> nat -> nat -> Exp -> Val -> bool ->
  Process -> option Process :=
  
  fun ι ext id vars e l l_flag p =>
    match len l with
    | Some vars' =>
      if (vars' =? vars)
      then
        match l_flag with
        (* p_spawn *)
        | false => plsASpawnSpawn ι ext id vars e l p
        (* p_spawn_link *)
        | true => plsASpawnSpawnLink ι ext id vars e l p
        end
      else None
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition processLocalStepTau : Process -> option Process :=
  fun p =>
    match p with
    | inl (fs, e, mb, links, flag) =>
      (* p_local *)
      match step_func fs e with
      | Some (fs', e') => Some (inl (fs', e', mb, links, flag))
      | _ =>
        match fs with
        (* p_recv_peek_message_ok *)
        | FParams (IPrimOp "recv_peek_message") [] [] :: fs' => 
          match e with 
          | RBox =>
            match peekMessage mb with
            | Some msg => Some (inl (fs', RValSeq [ttrue;msg], mb, links, flag))
            | _ => None
            end
          | _ => None
          end
        (* p_recv_next *)
        | FParams (IPrimOp "recv_next") [] [] :: fs' =>
          match e with
          | RBox =>
            match recvNext mb with
            | Some mb' => Some (inl (fs', RValSeq [ok], mb', links, flag))
            | _ => None
            end
          | _ => None
          end
        (* p_remove_message *)
        | FParams (IPrimOp "remove_message") [] [] :: fs' =>
          match e with
          | RBox =>
            match removeMessage mb with
            | Some mb' => Some (inl (fs', RValSeq [ok], mb', links, flag))
            | _ => None
            end
          | _ => None
          end
        | FParams (IPrimOp "recv_wait_timeout") [] [] :: fs' =>
          match e with
          | RValSeq [v] =>
            match v with
            (* p_recv_wait_timeout_new_message *)
            | infinity => 
              match mb with
              | (oldmb, msg :: newmb) => 
                  Some (inl (fs', RValSeq [ffalse], (oldmb, msg :: newmb), links, flag))
              | _ => None
              end
            (* p_recv_wait_timeout_0 *)
            | VLit 0%Z => Some (inl (fs', RValSeq [ttrue], mb, links, flag))
            (* p_recv_wait_timeout_invalid *)
            | _ => Some (inl (fs', RExc (timeout_value v), mb, links, flag))
            end
          | _ => None
          end
        (* p_set_flag_exc *)
        | FParams (ICall erlang process_flag) [VLit "trap_exit"%string] [] :: fs' =>
          match e with
          | RValSeq [v] =>
            match bool_from_lit v with
            | None => Some (inl (fs', RExc (badarg v), mb, links, flag))
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition processLocalStepEps : Process -> option Process :=
  fun p =>
    match p with
    (* p_terminate *)
    | inl ([], RValSeq [_], _, links, _) =>
        Some (inr (gset_to_gmap normal links))
    (* p_terminate_exc *)
    | inl ([], RExc exc, _, links, _) =>
        Some (inr (gset_to_gmap exc.1.2 links))
    | inl (FParams ident vl [] :: fs, e, mb, links, flag) =>
      (* p_set_flag *)
      match ident with
      | ICall erlang process_flag =>
        match vl with
        | [VLit (Atom "trap_exit"%string)] =>
          match e with
          | RValSeq [v] =>
            match bool_from_lit v with
            | Some y =>
                Some (inl (fs, RValSeq [lit_from_bool flag], mb, links, y))
            | None => None
            end
          | _ => None
          end
        | _ => None
        end
      (* p_recv_peek_message_no_message *)
      | IPrimOp "recv_peek_message"%string =>
        match vl with
        | [] =>
          match e with
          | RBox => 
            match peekMessage mb with
            | None => Some (inl (fs, RValSeq [ffalse; ErrorVal], mb, links, flag))
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition processLocalStepFunc : Process -> Action -> option Process :=
  fun p a =>
    match a with
    | ASend _ ι msg => processLocalStepASend ι msg p
    | AArrive source dest msg => processLocalStepAArrive source dest msg p
    | ASelf ι => processLocalStepASelf ι p
    | ASpawn ι (VClos ext id vars e) l l_flag =>
        processLocalStepASpawn ι ext id vars e l l_flag p
    | τ => processLocalStepTau p
    | ε => processLocalStepEps p
    | _ => None
    end.

Lemma VLit_val_eq: forall v l, v =ᵥ VLit l = true -> v = VLit l.
Proof.
  intros. destruct v; simpl in H; try congruence.
  apply Lit_eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma VLit_val_neq: forall v l, v =ᵥ VLit l = false -> v <> VLit l.
Proof.
  intros. intro.
  rewrite H0 in H. rewrite Val_eqb_refl in H. discriminate.
Qed.

Theorem processLocalStepEquiv: forall p p' a,
  p -⌈ a ⌉-> p' <-> processLocalStepFunc p a = Some p'.
Proof.
  intros. split; intro.
  * inversion H; simpl.
    + destruct (step_func fs e) eqn:H'.
      - destruct p0. rewrite step_equiv in H0. rewrite H' in H0. inversion H0. reflexivity.
      - rewrite step_equiv in H0. rewrite H' in H0. discriminate.
    + reflexivity.
    + destruct H0.
      - destruct H0. destruct H4. subst. rewrite <- Nat.eqb_neq in H4.
        rewrite H4. destruct b; simpl; reflexivity.
      - destruct H0. destruct H4. subst. destruct flag.
        ** destruct (gset_elem_of_dec source links) eqn:H'.
           ++ contradiction.
           ++ rewrite <- Nat.eqb_neq in H5. rewrite H5. reflexivity.
        ** rewrite <- Nat.eqb_neq in H5. rewrite H5.
           destruct (reason =ᵥ VLit "normal"%string); try reflexivity.
           destruct (gset_elem_of_dec source links) eqn:H'; try reflexivity.
           contradiction.
    + destruct H0.
      - destruct H0. destruct H4. destruct flag; rewrite H4.
        ** rewrite H0. simpl. rewrite H5. reflexivity.
        ** destruct (dest =? source); rewrite H5, H0; simpl; reflexivity.
      - destruct H0; destruct H0; rewrite H0.
        ** destruct H4, H5, H6. destruct (dest =? source); destruct b.
           ++ destruct (reason =ᵥ VLit "normal"%string) eqn:H'.
              -- clear -H4 H'. apply VLit_val_eq in H'. congruence.
              -- destruct (gset_elem_of_dec source links) eqn:H''. rewrite H5. reflexivity.
                 specialize (H6 eq_refl). congruence.
           ++ destruct (reason =ᵥ VLit "kill"%string) eqn:H'; try rewrite H5; try reflexivity.
              specialize (H7 eq_refl).
              clear -H7 H'. apply VLit_val_eq in H'. congruence.
           ++ destruct (reason =ᵥ VLit "normal"%string) eqn:H'.
              -- clear -H4 H'. apply VLit_val_eq in H'. congruence.
              -- specialize (H6 eq_refl).
                 destruct (gset_elem_of_dec source links) eqn:H''; try congruence.
                 rewrite H5. reflexivity.
           ++ destruct (reason =ᵥ VLit "normal"%string) eqn:H'.
              -- clear -H4 H'. apply VLit_val_eq in H'. congruence.
              -- specialize (H7 eq_refl). clear H'. destruct (reason =ᵥ VLit "kill"%string) eqn:H';
                 try rewrite H5; try reflexivity.
                 clear -H7 H'. apply VLit_val_eq in H'. congruence.
        ** destruct H4, H5. symmetry in H5. rewrite <- Nat.eqb_eq in H5. rewrite H5.
           rewrite H4. simpl. subst. destruct b; reflexivity.
    + destruct H0; destruct H0; rewrite H0.
      ** destruct (reason =ᵥ VLit "kill"%string) eqn:H'; try reflexivity.
         clear -H4 H'. apply VLit_val_eq in H'. congruence.
      ** destruct (gset_elem_of_dec source links) eqn:H'. reflexivity. congruence.
    + reflexivity.
    + reflexivity.
    + destruct (bool_decide (v = v) && (ι =? ι)) eqn:H'.
      - destruct (valclosed_func v) eqn:H''; try reflexivity.
        apply valclosed_equiv in H0. rewrite H0 in H''. discriminate.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'. 
        apply bool_decide_eq_false_1 in H'. congruence.
    + destruct (bool_decide (v = v) && (ι =? ι)) eqn:H'.
      - destruct (valclosed_func v) eqn:H''; try reflexivity.
        apply valclosed_equiv in H0. rewrite H0 in H''. discriminate.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'. 
        apply bool_decide_eq_false_1 in H'. congruence.
    + destruct (ι =? ι) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + destruct (ι =? ι) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + destruct (links !! ι) eqn:H'; try discriminate.
      destruct (bool_decide (v = reason)) eqn:H''.
      destruct (valclosed_func reason) eqn:H'''; try reflexivity.
      apply valclosed_equiv in H0. rewrite H0 in H'''. discriminate.
      inversion H1. rewrite H6 in H''. apply bool_decide_eq_false_1 in H''. congruence.
    + reflexivity.
    + unfold processLocalStepASpawn. destruct (len l); try discriminate.
      inversion H0. rewrite Nat.eqb_refl.
      unfold plsASpawnSpawn.
      destruct (bool_decide (VClos ext id n e = VClos ext id n e) && bool_decide (l = l)) eqn:H'.
      reflexivity. apply andb_false_iff in H'. destruct H'.
      apply bool_decide_eq_false_1 in H4. congruence.
      apply bool_decide_eq_false_1 in H4. congruence.
    + unfold processLocalStepASpawn. destruct (len l); try discriminate.
      inversion H0. rewrite Nat.eqb_refl.
      unfold plsASpawnSpawnLink.
      destruct (bool_decide (VClos ext id n e = VClos ext id n e) && bool_decide (l = l)) eqn:H'.
      reflexivity. apply andb_false_iff in H'. destruct H'.
      apply bool_decide_eq_false_1 in H4. congruence.
      apply bool_decide_eq_false_1 in H4. congruence.
    + destruct mb. destruct l0 eqn:H'; simpl. unfold peekMessage in H0. discriminate.
      unfold peekMessage in H0. inversion H0. reflexivity.
    + destruct mb. destruct l0 eqn:H'; simpl. reflexivity.
      unfold peekMessage in H0. discriminate.
    + destruct mb. destruct l0 eqn:H'; simpl. unfold recvNext in H0. discriminate.
      unfold recvNext in H0. inversion H0. reflexivity.
    + destruct mb. destruct l0 eqn:H'. unfold removeMessage in H0. discriminate.
      unfold removeMessage in H0. unfold removeMessage. inversion H0. reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct v eqn:H'; try auto. destruct l eqn:H''.
      - do 8 (destruct s; try reflexivity; destruct a0; 
        destruct b; try reflexivity;
        destruct b0; try reflexivity;
        destruct b1; try reflexivity;
        destruct b2; try reflexivity;
        destruct b3; try reflexivity;
        destruct b4; try reflexivity;
        destruct b5; try reflexivity;
        destruct b6; try reflexivity).
        destruct s; try reflexivity. congruence.
      - destruct x eqn:H'''; try reflexivity. congruence.
    + destruct (bool_from_lit v) eqn:H'; try discriminate. inversion H0. reflexivity.
    + destruct (bool_from_lit v) eqn:H'; try discriminate. inversion H0. reflexivity.
    + reflexivity.
    + reflexivity.
  * unfold processLocalStepFunc in H.
    destruct a.
    + unfold processLocalStepASend in H.
      destruct t eqn:Ht.
      - destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
        destruct f; try discriminate. destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate.
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct v; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate. destruct vs; try discriminate.
        destruct vs; try discriminate. 
        destruct (bool_decide (v = e) && (p =? receiver)) eqn:H'; try discriminate.
        symmetry in H'. apply andb_true_eq in H'. destruct H'.
        symmetry in H1. apply Nat.eqb_eq in H1. rewrite <- H1.
        symmetry in H0. apply bool_decide_eq_true_1 in H0. rewrite H0.
        destruct (valclosed_func e) eqn:H'; try discriminate. inversion H. constructor.
        apply valclosed_equiv. assumption.
      - unfold plsASendSExit in H. destruct b.
        ** destruct p; try discriminate. destruct (d !! receiver) eqn:H'; try discriminate.
           destruct (bool_decide (v = r)) eqn:H''; try discriminate.
           destruct (valclosed_func r) eqn:H'''; try discriminate.
           inversion H. constructor. apply valclosed_equiv. assumption.
           rewrite H'. apply bool_decide_eq_true_1 in H''. rewrite H''. reflexivity.
        ** destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
           destruct f; try discriminate. destruct ident; try discriminate.
           destruct m0; try discriminate. destruct l; try discriminate.
           do 6 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate. destruct f; try discriminate. destruct l;
           try discriminate.
           do 4 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate. destruct vl; try discriminate.
           destruct v; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r0; try discriminate.
           destruct vs; try discriminate. destruct vs; try discriminate.
           destruct (bool_decide (v = r) && (p =? receiver)) eqn:H'; try discriminate.
           symmetry in H'. apply andb_true_eq in H'. destruct H'.
           symmetry in H1. apply Nat.eqb_eq in H1. rewrite <- H1.
           symmetry in H0. apply bool_decide_eq_true_1 in H0. rewrite H0.
           destruct (valclosed_func r) eqn:H'; try discriminate. inversion H.
           constructor. apply valclosed_equiv. assumption.
      - destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
        destruct f; try discriminate. destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 4 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct el; try discriminate.
        destruct r; try discriminate. destruct vs; try discriminate.
        destruct v; try discriminate. destruct vs; try discriminate.
        destruct (p =? receiver) eqn:H'; try discriminate. inversion H.
        apply Nat.eqb_eq in H'. rewrite H'. constructor.
      - destruct p; try discriminate. destruct l, p, p, p.
        destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate. destruct m0; try discriminate.
        destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
        destruct vs; try discriminate. destruct v; try discriminate. destruct vs; try discriminate.
        destruct (p =? receiver) eqn:H'; try discriminate. inversion H.
        apply Nat.eqb_eq in H'. rewrite H'. constructor.
    + unfold processLocalStepAArrive in H. destruct t.
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
      - unfold plsAArriveSExit in H. destruct p; try discriminate.
        destruct l, p, p, p.
        rename p0 into flag. rename sender into source. rename receiver into dest.
        destruct flag eqn:H'.
        ** destruct b eqn:H''.
           ++ destruct (gset_elem_of_dec source g) eqn:H'''.
              -- inversion H. constructor. right. split; try reflexivity.
                 assumption.
              -- destruct (dest =? source) eqn:H''''; try discriminate. inversion H.
                 constructor. right.
                 split. assumption.
                 split. reflexivity. apply Nat.eqb_neq in H''''. assumption.
           ++ destruct (r =ᵥ VLit "kill"%string) eqn:H'''.
              -- inversion H. constructor. left.
                 split. apply VLit_val_eq in H'''. assumption.
                 split; reflexivity.
              -- inversion H. constructor. left.
                 split. reflexivity.
                 apply VLit_val_neq in H'''. assumption.
        ** destruct (dest =? source) eqn:H''.
           ++ destruct b eqn:H'''.
              -- destruct (r =ᵥ VLit "normal"%string) eqn:H''''.
                 *** inversion H. constructor. right. right.
                     split. reflexivity.
                     split. apply VLit_val_eq in H''''. assumption.
                     split. rewrite Nat.eqb_eq in H''. symmetry. assumption.
                     apply VLit_val_eq in H''''. symmetry. assumption.
                 *** destruct (gset_elem_of_dec source g) eqn:H'''''; try discriminate.
                     inversion H. constructor. right. left.
                     split. reflexivity.
                     split. apply VLit_val_neq in H''''. assumption.
                     split. reflexivity.
                     split. intro. assumption.
                     intro. discriminate.
              -- destruct (r =ᵥ VLit "kill"%string) eqn:H''''.
                 *** inversion H. constructor. left.
                     split. apply VLit_val_eq in H''''. assumption.
                     split; reflexivity.
                 *** destruct (r =ᵥ VLit "normal"%string) eqn:H'''''.
                     +++ inversion H. constructor. right. right.
                         split. reflexivity.
                         split. apply VLit_val_eq in H'''''. assumption.
                         split. apply Nat.eqb_eq in H''. symmetry. assumption.
                         reflexivity.
                     +++ inversion H. constructor. right. left.
                         split. reflexivity.
                         split. apply VLit_val_neq in H'''''. assumption.
                         split. reflexivity.
                         split. intro. discriminate.
                         intro. apply VLit_val_neq in H''''. assumption.
           ++ destruct b eqn:H'''.
              -- destruct (r =ᵥ VLit "normal"%string) eqn:H''''.
                 *** inversion H. constructor. left.
                     split. apply VLit_val_eq in H''''. assumption.
                     split. apply Nat.eqb_neq in H''. assumption.
                     reflexivity.
                 *** destruct (gset_elem_of_dec source g) eqn:H'''''.
                     +++ inversion H. constructor. right. left.
                         split. reflexivity.
                         split. apply VLit_val_neq in H''''. assumption.
                         split. reflexivity.
                         split. intro. assumption.
                         intro. discriminate.
                     +++ inversion H. constructor. right.
                         split. assumption.
                         split. reflexivity.
                         apply Nat.eqb_neq in H''. assumption.
              -- destruct (r =ᵥ VLit "normal"%string) eqn:H''''.
                 *** inversion H. constructor. left.
                     split. apply VLit_val_eq in H''''. assumption.
                     split. apply Nat.eqb_neq in H''. assumption.
                     reflexivity.
                 *** destruct (r =ᵥ VLit "kill"%string) eqn:H'''''.
                     +++ inversion H. constructor. left.
                         split. apply VLit_val_eq in H'''''. assumption.
                         split; reflexivity.
                     +++ inversion H. constructor. right. left.
                         split. reflexivity.
                         split. apply VLit_val_neq in H''''. assumption.
                         split. reflexivity.
                         split. intro. discriminate.
                         intro. apply VLit_val_neq in H'''''. assumption.
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
    + unfold processLocalStepASelf in H. destruct p; try discriminate. destruct l, p, p, p.
      destruct f; try discriminate. destruct f; try discriminate.
      destruct ident; try discriminate. destruct m0; try discriminate.
      destruct l; try discriminate.
      do 6 (destruct s; try discriminate;
      destruct a; try discriminate;
      destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
      destruct s; try discriminate.
      destruct f; try discriminate. destruct l; try discriminate.
      do 4 (destruct s; try discriminate;
      destruct a; try discriminate;
      destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
      destruct s; try discriminate.
      destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
      inversion H. constructor.
    + destruct t1; try discriminate. unfold processLocalStepASpawn in H.
      destruct (len t2) eqn:H''''; try discriminate.
      destruct (n =? params) eqn:H'; try discriminate.
      rename link into link_flag. destruct link_flag eqn:H''.
      - unfold plsASpawnSpawnLink in H. destruct p; try discriminate.
        destruct l, p, p, p. destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate. destruct m0; try discriminate.
        destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 10 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate. destruct vs; try discriminate.
        destruct vs; try discriminate.
        destruct (bool_decide (v = VClos ext id params e) && bool_decide (v0 = t2)) eqn:H''';
        try discriminate.
        inversion H. rewrite Nat.eqb_eq in H'. rewrite <- H'.
        apply andb_true_iff in H'''. destruct H'''.
        apply bool_decide_eq_true_1 in H0. rewrite H0.
        apply bool_decide_eq_true_1 in H2. rewrite H2.
        rewrite <- H'. constructor. symmetry. assumption.
      - unfold plsASpawnSpawn in H. destruct p; try discriminate. destruct l, p, p, p.
        destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 5 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate.
        destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (bool_decide (v = VClos ext id params e) && bool_decide (v0 = t2)) eqn:H''';
        try discriminate.
        inversion H. rewrite Nat.eqb_eq in H'. rewrite <- H'.
        apply andb_true_iff in H'''. destruct H'''.
        apply bool_decide_eq_true_1 in H0. rewrite H0.
        apply bool_decide_eq_true_1 in H2. rewrite H2.
        rewrite <- H'. constructor. symmetry. assumption.
    + unfold processLocalStepTau in H. destruct p; try discriminate. destruct l, p, p, p.
      destruct (step_func f r) eqn:H'.
      destruct p. inversion H. constructor. apply step_equiv in H'. assumption. clear H'.
      destruct f; try discriminate. destruct f; try discriminate.
      destruct ident; try discriminate.
      - destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 12 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct v; try discriminate. destruct l; try discriminate.
        do 9 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
        destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (bool_from_lit v) eqn:H''; try discriminate. inversion H.
        apply p_set_flag_exc. symmetry. assumption.
      - do 9 (destruct f; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        ** do 8 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct vs; try discriminate. destruct vs; try discriminate.
           destruct v; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate).
           destruct l eqn:H'.
           ++ clear H1.
              do 8
              (destruct s; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct a; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b0; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b1; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b2; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b3; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b4; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b5; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b6; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10).
              destruct s; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate).
              destruct m. destruct l1; try discriminate.
              inversion H. apply p_recv_wait_timeout_new_message.
           ++ destruct x.
              -- inversion H. apply p_recv_wait_timeout_0.
              -- inversion H. apply p_recv_wait_timeout_invalid; discriminate.
              -- inversion H. apply p_recv_wait_timeout_invalid; discriminate.
        ** destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct (recvNext m) eqn:H''; try discriminate.
           inversion H. constructor. assumption.
        ** do 8 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct (peekMessage m) eqn:H'; try discriminate.
           inversion H. apply p_recv_peek_message_ok. assumption.
        ** do 5 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct (removeMessage m) eqn:H'; try discriminate.
           inversion H. constructor. assumption.
    + unfold processLocalStepEps in H. destruct p; try discriminate. destruct l, p, p, p.
      destruct f.
      - destruct r; try discriminate.
        ** destruct vs; try discriminate. destruct vs; try discriminate.
           inversion H. constructor.
        ** inversion H. constructor.
      - destruct f; try discriminate. destruct el; try discriminate.
        destruct ident; try discriminate.
        ** destruct m0; try discriminate.
           destruct l; try discriminate.
           do 6 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate.
           destruct f; try discriminate. destruct l; try discriminate.
           do 12 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate.
           destruct vl; try discriminate. destruct v; try discriminate.
           destruct l; try discriminate.
           do 9 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate.
           destruct vl; try discriminate. destruct r; try discriminate.
           destruct vs; try discriminate. destruct vs; try discriminate.
           destruct (bool_from_lit v) eqn:H'; try discriminate.
           inversion H. constructor. symmetry. assumption.
        ** do 17 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate.
           destruct vl; try discriminate. destruct r; try discriminate.
           inversion H. destruct (peekMessage m) eqn:H'; try discriminate.
           inversion H. constructor. assumption.
Qed.




















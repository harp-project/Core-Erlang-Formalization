From CoreErlang.FrameStack Require Export Frames SubstSemantics.
From CoreErlang Require Export Auxiliaries Matching.

Import ListNotations.
Import Coq.Lists.List.

Print convert_to_closlist.

Locate "VALCLOSED".
Print ValScoped.
Locate nth.
Print nth.

Check scoped_nil 0.
Check ExpScoped 0 (VVal VNil).
Check VALCLOSED VNil.

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

Fixpoint valscoped_func (n : nat)  (v : Val) : bool :=
  match n, v with
    (* scoped_nil *)
    | _, VNil => true
    
    (* scoped_lit *)
    | _, VLit _ => true
    
    (* scoped_pid *)
    | _, VPid _ => true
    
    (* scoped_var *)
    | n, VVar v => v <? n
    
    (* scoped_funId *)
    | n, VFunId fi => fst fi <? n
    
    (* scoped_vtuple *)
    (* TODO *)
    
    (* scoped_vcons *)
    | n, VCons hd tl => (valscoped_func n hd) && (valscoped_func n tl)
    
    (* scoped_vmap *)
    (* TODO *)
    
    (* scoped_vclos *)
    (* TODO *)
    
    | _, _ => false
    end.

Definition valclosed_func' (v : Val) : bool := valscoped_func 0 v.


Definition step_func' : FrameStack -> Redex -> option (FrameStack * Redex) :=
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

Theorem step_equiv': forall fs fs' e e', 
    ⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩ <-> step_func' fs e = Some (fs', e').
Proof.
  intros. split.
  * intro. inversion H; try auto; unfold step_func'.
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
      admit.
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
Admitted.

Definition step_func : FrameStack -> Redex -> option (FrameStack * Redex) :=
  fun fs r =>
    match fs, r with
    (* cool_value *)
    | xs, ˝v => match valclosed_func v with
                | true => Some (xs, RValSeq [v] )
                | _ => None
                end
    
    (* eval_step_params *)
    | FParams ident vl (e :: el) :: xs, RValSeq [v] =>
          Some (FParams ident (vl ++ [v]) el :: xs , RExp e)
    
    (* eval_step_params_0 *)
    | FParams ident vl (e::el) ::xs, RBox => match ident with
                                             | IMap => None
                                             | _ => Some (FParams ident vl el :: xs, RExp e)
                                             end
    
    (* eval_cool_params_0 *)
    | FParams ident vl [] ::xs, RBox => match ident with
                                        | IMap => None
                                        | _ => match create_result ident vl with
                                               | Some (res, l) => Some (xs, res)
                                               | None => None
                                               end
                                        end
    
    (* eval_cool_params *)
    | FParams ident vl [] :: xs, RValSeq [v] => match create_result ident (vl ++ [v]) with
                                                | Some (res, l) => Some (xs, res)
                                                | None => None
                                                end

    (* eval_heat_values *)
    | xs, EValues el => Some ((FParams IValues [] el)::xs , RBox)
    
    (* eval_heat_tuple *)
    | xs, ETuple el => Some ((FParams ITuple [] el)::xs, RBox )
    
    (* eval_heat_map_0 *)
    | xs, EMap [] => Some (xs, RValSeq [VMap []] )
    
    (* eval_heat_map *)
    | xs, EMap ((e1, e2) :: el) =>
        Some ((FParams IMap [] (e2 :: flatten_list el))::xs, RExp e1 )
        
    (* eval_heat_call_mod *)
    | xs, ECall m f el => Some ( FCallMod f el :: xs, RExp m )
    
    (* eval_heat_call_fun *)
    | FCallMod f el :: xs, RValSeq [v] => Some ( FCallFun v el :: xs, RExp f )
    
    (* eval_heat_call_params *)
    | FCallFun m el :: xs, RValSeq [f] => Some ( (FParams (ICall m f) [] el)::xs, RBox )
    
    (* eval_heat_primop *)
    | xs, EPrimOp f el => Some ( (FParams (IPrimOp f) [] el)::xs, RBox )
    
    (* eval_heat_app2 *)
    | FApp1 el :: xs, RValSeq [v] => Some ( (FParams (IApp v) [] el)::xs, RBox )
    
    (* eval_heat_app *)
    | xs, EApp e l => Some (FApp1 l :: xs, RExp e)
    
    (* eval_cool_cons_1 *)
    | (FCons1 hd )::xs, RValSeq [tl] => Some ( (FCons2 tl)::xs, RExp hd )

    (* eval_cool_cons_2 *)
    | (FCons2 tl)::xs, RValSeq [hd] => Some ( xs, RValSeq [VCons hd tl] )

    (* eval_heat_cons *)
    | xs, ECons hd tl => Some ( (FCons1 hd)::xs, RExp tl )
    
    (* eval_cool_let *)
    | (FLet l e2)::xs, RValSeq vs => match length vs =? l with
                                     | true => Some ( xs, RExp (e2.[ list_subst vs idsubst ]) )
                                     | _ => None
                                     end

    (* eval_heat_let *)
    | xs, ELet l e1 e2 => Some ( (FLet l e2)::xs, RExp e1 )
    
    (* eval_cool_seq *)
    | (FSeq e2)::xs, RValSeq [v] => Some ( xs, RExp e2 )

    (* eval_heat_seq *)
    | xs, ESeq e1 e2 => Some ( (FSeq e2)::xs, RExp e1 )

    (* eval_cool_fun *)
    | xs, EFun vl e => Some (xs, RValSeq [ VClos [] 0 vl e ])

    (* eval_heat_case *)
    | xs, ECase e l => Some ( (FCase1 l)::xs, RExp e )
    
    (* eval_step_case_match and eval_step_case_not_match *)
    | (FCase1 ((lp,e1,e2)::l))::xs, RValSeq vs => 
        match match_pattern_list lp vs with
        | Some vs' => Some ((FCase2 vs e2.[list_subst vs' idsubst] l)::xs, RExp (e1.[list_subst vs' idsubst]) )
        | None => Some ( (FCase1 l)::xs, RValSeq vs )
        end
    
    (* eval_step_case_true *)
    | (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "true") ] => Some ( xs, RExp e' )

    (* eval_step_case_false *)
    | (FCase2 vs e' l)::xs, RValSeq [ VLit (Atom "false") ] => Some ((FCase1 l)::xs, RValSeq vs )

    (* eval_cool_case_empty *)
    | (FCase1 [])::xs, RValSeq vs => Some ( xs, RExc if_clause )
    
    (* eval_heat_letrec *)
    | xs, ELetRec l e => let lc := convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) in
                         Some (xs, RExp e.[list_subst lc idsubst] )
    
    (* eval_cool_try_ok *)
    | (FTry vl1 e2 _ e3)::xs, RValSeq vs => match vl1 =? length vs with
                                            | true => Some ( xs, RExp e2.[ list_subst vs idsubst ] )
                                            | _ => None
                                            end
    
    (* eval_cool_try_err *)
    | (FTry vl1 e2 3 e3)::xs, RExc (class, reason, details) =>
        Some ( xs, RExp e3.[ list_subst [exclass_to_value class; reason; details] idsubst ] )

    (* eval_heat_try *)
    | xs, ETry e1 vl1 e2 vl2 e3 => Some ( (FTry vl1 e2 vl2 e3)::xs, RExp e1 )
    
    (* eval_prop_exc *)
    | F::xs, RExc exc => match isPropagatable F with
                         | true => Some ( xs, RExc exc )
                         | _ => None
                         end
                        
    | _, _ => None
    end.

Theorem step_equiv: forall fs fs' e e', 
    ⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩ <-> step_func fs e = Some (fs', e').
Proof.
  intros. split.
  * intro. induction H; try auto.
    + apply valclosed_equiv in H. unfold step_func. rewrite H.
      destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + simpl. destruct ident; try auto. congruence.
    + simpl. destruct ident; destruct create_result; try congruence; try inversion H0; reflexivity.
    + simpl. destruct create_result; try congruence. inversion H. reflexivity.
    + unfold step_func. destruct xs eqn:H. reflexivity.
      destruct f; try reflexivity.
      destruct el0; reflexivity.
      destruct l0; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      rewrite <- H. clear H vl1 e2 e3 l. induction vl2. reflexivity.
      rewrite <- IHvl2. clear IHvl2.
      Fail reflexivity. (* ???? *)
      remember (Some (FParams IValues [] el :: xs, RBox)) as x. clear Heqx.
      do 4 (destruct vl2; try reflexivity).
      (* destruct vl2. reflexivity. destruct vl2. reflexivity. destruct vl2. reflexivity. destruct vl2; reflexivity.
      admit. *)
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el0; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el0; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f0; try reflexivity.
      destruct el0; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f0; try reflexivity.
      destruct el0; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l0; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + simpl. rewrite H. rewrite Nat.eqb_refl. reflexivity.
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l0; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l0; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + simpl. rewrite H. reflexivity.
    + simpl. rewrite H. reflexivity.
    + unfold step_func. destruct xs. rewrite H. reflexivity.
      destruct f; try rewrite H; try reflexivity.
      destruct el; reflexivity.
      destruct l0; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
    + simpl. rewrite <- H. rewrite Nat.eqb_refl.
      do 4 (destruct vl2; try reflexivity).
    + unfold step_func. destruct xs. reflexivity.
      destruct f; try reflexivity.
      destruct el; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl3; try reflexivity).
    + simpl. rewrite H. clear H. destruct F; try reflexivity.
      destruct el; reflexivity.
      destruct l; try reflexivity.
      destruct p as [[a b] c]. reflexivity.
      do 4 (destruct vl2; try reflexivity).
      destruct exc. destruct p. destruct e; simpl.
      admit. admit. admit.
  * intros. admit.
Admitted.


















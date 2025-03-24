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
    
    (* eval_cool_seq*)
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
    
    (* eval_prop_exc*)
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


















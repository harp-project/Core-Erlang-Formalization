From CoreErlang.Eq.BsFs Require Export B2InductionLemmas.

(* STRUCTURE:
* Insert
  - map_insert_unfold (BigStep)
  - map_insert_length_le (FrameStack)
* MakeLength
  - make_value_map_length (BigStep)
  - make_val_map_length (FrameStack)
* MakeCons
  - make_value_map_cons (BigStep)
  - make_val_map_cons (FrameStack)
*)












Section Insert.



  Import BigStep.

  Lemma map_insert_unfold :
    forall k v kl vl,
      map_insert k v kl vl
    = match kl with
      | [] => match vl with
              | [] => ([k], [v])
              | _ :: _ => ([], [])
              end
      | k' :: ks =>
          match vl with
          | [] => ([], [])
          | v' :: vs =>
              if Value_ltb k k'
              then (k :: k' :: ks, v :: v' :: vs)
              else
               if Value_eqb k k'
               then (k' :: ks, v' :: vs)
               else (k' :: (map_insert k v ks vs).1,
                     v' :: (map_insert k v ks vs).2)
          end
      end.
  Proof.
    (* #1 Destruct Trivial: intro/destruct/trivial *)
    itr.
    des - kl; des - vl :- trv.
  Qed.



  Import SubstSemantics.

  Lemma map_insert_length_le :
    forall k k' v v' vl,
      length (map_insert k v vl) <= length ((k', v') :: vl).
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr.
    ind - vl as [| (key, var) vl IHvl]: sli |> smp.
    (* #2 Destruct Key: destruct/apply + simpl/lia *)
    des > (k <ᵥ key): sli.
    des > (k =ᵥ key): sli.
    bpp - le_n_S.
  Qed.



End Insert.










Section MakeLength.




  Import BigStep.

  Lemma make_value_map_length :
    forall kvl vvl,
        length kvl = length vvl
    ->  length (make_value_map kvl vvl).1
      = length (make_value_map kvl vvl).2.
  Proof.
    (* #1 Destruct Lists: intro/destruct/inversion
        + simpl/congruence + subst/clear *)
    itr - kvl vvl Hlength.
    des - kvl as [| kv kvl];des - vvl as [| vv vvl]
       :- smp - Hlength; con + smp.
    ivc - Hlength as Hlength: H0.
    (* #2 Unfold Map_Insert: refold/rewrite *)
    rfl - make_value_map.
    rwr - map_insert_unfold.
    (* #3 Destruct Elements: destruct + trivial/simpl *)
    des > ((make_value_map kvl vvl).1);
    des > ((make_value_map kvl vvl).2).
    1-3: trv.
    des > (Value_ltb kv v);
    des > (Value_eqb kv v).
    1-3: smp; trv.
    all: admit.
  Admitted.



  Import SubstSemantics.

  Lemma make_val_map_length :
    forall vl,
      length (make_val_map vl) <= length vl.
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr.
    ind - vl as [| (k, v) vl Hvl_cons]: sli |> smp.
    (* #2 Destruct Key: destruct/apply + apply/simpl *)
    des > (make_val_map vl) as [| (k', v') vl']: app - le_n_S |> smp.
    des > (k <ᵥ k'): smp *; app - le_n_S.
    des > (k =ᵥ k'): smp *; app - le_S |> smp.
    app - le_n_S.
    (* #3 Transivity: pose/lia *)
    pse - map_insert_length_le as Hvl_insert: k k' v v' vl'.
    lia.
  Qed.



End MakeLength.









Section MakeCons.



  Import BigStep.

  Theorem make_value_map_cons :
    forall kv kvl vv vvl mkvl mvvl,
        length kvl = length vvl
    ->  make_value_map (kv :: kvl) (vv :: vvl) = (mkvl, mvvl)
    ->  mkvl <> [] /\ mvvl <> [].
  Proof.
    (* #1 Unfold Map_Insert: intro/simpl/rewrite *)
    itr - kv kvl vv vvl mkvl mvvl Hlength Hmake.
    smp - Hmake.
    rwr - map_insert_unfold in Hmake.
    (* #2 Pose Length: pose + clear *)
    psc - make_value_map_length as Hlength_make: kvl vvl Hlength.
    (* #3 Destruct Maps: destruct
        + simpl/symmetry/apply/rewrite/inversion/subst/split/auto *)
    des > ((make_value_map kvl vvl).1).
    {
      smp - Hlength_make.
      sym - Hlength_make.
      app - length_zero_iff_nil as Hempty in Hlength_make.
      rwr - Hempty in *.
      ivs - Hmake.
      spl; ato.
    }
    des > ((make_value_map kvl vvl).2): ivs - Hlength_make.
    (* #4 Destuct Key Eq: destruct + inversion/subst/split/auto *)
    des > (Value_ltb kv v); des > (Value_eqb kv v); ivs - Hmake; spl; ato.
  Qed.



  Import SubstSemantics.

  Theorem make_val_map_cons :
    forall v1 v2 vl,
        (v1, v2) :: vl = make_val_map ((v1, v2) :: vl)
    ->  vl = make_val_map vl.
  Proof.
    (* #1 Destruct Make: intro/inversion/unfold/destruct + inversion *)
    itr - v1 v2 vl Hcons.
    ivc - Hcons as Hcons: H0.
    ufl - Maps.map_insert in Hcons.
    des > (make_val_map vl) as [| (v1', v2') vl'] Hmake: ivr - Hcons.
    (* #2 Destruct Key: destruct + inversion *)
    des > (v1 <ᵥ v1'): ivr - Hcons.
    des > (v1 =ᵥ v1') as Heq; ivc - Hcons.
    * (* #2.1 Insert Key Equals: pose/rewrite/simpl/lia *)
      pse - make_val_map_length as Hlen: vl'.
      cwr - Hmake in Hlen.
      smp - Hlen.
      sli.
    * (* #2.1 Insert Key Bigger: rewrite/congruence*)
      rwr - Val_eqb_refl in Heq.
      con.
  Qed.



End MakeCons.
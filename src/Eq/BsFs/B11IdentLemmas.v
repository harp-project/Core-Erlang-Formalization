From CoreErlang.Eq.BsFs Require Export B10StepTactics.

Import SubstSemantics.

(* STRUCTURE:
* Ident
  - ident_result
  - ident_partial
  - ident_reverse
*)












Section Ident.



  Theorem ident_result :
    forall ident el r vl v' vl' eff Fs,
        create_result ident (vl' ++ v' :: vl) [] = Some (r , eff)
    ->  list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ident vl' el :: Fs, RValSeq [v'] ⟩
          -[ k ]->
          ⟨ Fs, r ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - r vl v' vl' eff Fs Hcreate Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
      (* #3.1 Exact: symmetry/exact *)
      sym.
      exa - Hcreate.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      cwr - Hrewrite in Hcreate.
      spc - Hfs_vl: r vl v (vl' ++ [v']) eff Fs Hcreate Hbiforall.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 FrameStack: eexist/step *)
      eei.
      step - Hstep_v / kv.
      step - Hstep_vl.
  Qed.



  Theorem ident_partial :
    forall ident el e' el' vl v' vl' Fs,
        list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ident vl' (el ++ e' :: el') :: Fs, RValSeq [v'] ⟩
          -[ k ]->
          ⟨ FParams ident (vl' ++ v' :: vl) el' :: Fs, RExp e' ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - e' el' vl v' vl' Fs Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      spc - Hfs_vl: e' el' vl v (vl' ++ [v']) Fs Hbiforall.
      cwl - Hrewrite in Hfs_vl.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 FrameStack: eexist/step *)
      eei.
      step - Hstep_v / kv.
      step - Hstep_vl.
  Qed.



  Theorem ident_reverse :
    forall el e' vl' ident k r,
        ⟨ [FParams ident vl' el], RExp e' ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
    ->  ident = ITuple \/ ident = IMap
    ->  exists v' vl eff,
            create_result ident (vl' ++ v' :: vl) [] = Some (RValSeq r, eff)
        /\  list_biforall
              (fun (e : Exp) (v : Val) => ⟨ [], RExp e ⟩ -->* RValSeq [v])
              (e' :: el)
              (v' :: vl).
  Proof.
    ind - el; itr - e' vl' ident k r Hstep Hident.
    * ivc - Hident.
      - ivc - Hstep as Hstep1 Hstep2: H H0.
        ivc - Hstep1 as Hstep: Hstep2.
        all: adm.
      - adm.
    * ivc - Hident.
      - ivc - Hstep as Hstep1 Hstep2: H H0.
        ivc - Hstep1 as Hstep: Hstep2.
        all: adm.
    (* Not Provable *)
  Admitted.



End Ident.
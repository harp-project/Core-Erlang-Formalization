(* 
NOTE: This is an experimental alternative for creating references by encoding the stack.

This module defines the create_fresh_ref function for creating unique references based
on the existing references inside the FrameStack.

It also defines refs_of_FrameStack, refs_of_Frame, refs_of_Exp, etc. functions for 
collecting references from the frame stack.

The lemma 'refs_are_fresh' proves that a reference created from the frame stack does not 
appear in the frame stack.

A step fs -[create_ref(fs) ]-> fs' puts create_ref(fs) in fs'. Due to this, references
created from fs' will be different from create_ref(fs). Inductively, all references 
created during an execution will be unique.
*)

From CoreErlang Require Export Frames.

From stdpp Require Import gmap sets list.
Require Import Lia.

Import List.
Import ListNotations.

Fixpoint refs_of_Exp (e : Exp) : list Reference := 
    match e with 
    | VVal v => refs_of_Val v
    | EExp nv => refs_of_NonVal nv
    end  

with refs_of_Val (val : Val) : list Reference :=
  match val with 
  | VNil    =>  []
  | VLit l   =>  []
  | VPid pid   =>  []
  | VReference ref =>  [ref]
  | VCons   hd tl => (refs_of_Val hd) ++ (refs_of_Val tl)
  | VTuple  l => List.flat_map refs_of_Val l
  | VMap    l => 
        List.flat_map 
            (fun vv => match vv with | (v,w) => refs_of_Val v ++ refs_of_Val w end) 
            l
  | VVar    n =>  []
  | VFunId  nn => []
  | VClos  ext _id _params e => 
        let extree := 
            List.flat_map (fun nne => match nne with | (_n,_m,e) => refs_of_Exp e end) ext
        in        
        let etree := refs_of_Exp e in
        extree ++ etree
  end

with refs_of_NonVal (nv : NonVal) : list Reference := 
  match nv with 
  | EFun    vl e =>  refs_of_Exp e
  | EValues el => List.flat_map refs_of_Exp el
  | ECons   hd tl => (refs_of_Exp hd) ++ (refs_of_Exp tl)
  | ETuple  l => List.flat_map refs_of_Exp l
  | EMap    l => 
      List.flat_map 
            (fun vv => match vv with | (v,w) => refs_of_Exp v ++ refs_of_Exp w end) 
            l
  | ECall  m f l => 
        refs_of_Exp m ++ refs_of_Exp f ++ List.flat_map refs_of_Exp l
  | EPrimOp _ l  => 
      List.flat_map refs_of_Exp l
  | EApp    exp l =>
      refs_of_Exp exp ++ List.flat_map refs_of_Exp l
  | ECase   e l => 
        let head := refs_of_Exp e in            
        let cls := 
        List.flat_map 
            (fun pge => 
                match pge with 
                (* TODO: erlang:make_ref() cannot appear guard. Do we still need to consider it? *)
                | (_p, _g, e) => refs_of_Exp e
                end) 
            l 
        in
      head ++ cls

  | ELet l e1 e2  =>  
    refs_of_Exp e1 ++ refs_of_Exp e2      
  | ESeq    e1 e2 => 
    refs_of_Exp e1 ++ refs_of_Exp e2    
  | ELetRec l e =>  
        let binds := 
            List.flat_map 
                (fun lr => 
                    match lr with                 
                    | (_l, r) => refs_of_Exp r
                    end) 
                l 
        in
        binds ++ refs_of_Exp e
  | ETry  e1 vl1 e2 vl2 e3 =>      
      (* TODO erlang:make_ref() cannot appear guard. Do we still need to consider it? *) 
      refs_of_Exp e1 ++ refs_of_Exp e2 ++  refs_of_Exp e3
  end.

Definition refs_of_FrameIdent (ident : FrameIdent) : list Reference :=
  match ident with
  | ICall m f => (refs_of_Val m) ++ (refs_of_Val f)
  | IApp v =>  refs_of_Val v
  | _ => []
  end.

Definition refs_of_Frame (fr : Frame) : list Reference := 
  match fr with 
  | FCons1 hd => refs_of_Exp hd
  | FCons2 tl => refs_of_Val tl
  | FParams ident vl el => 
      let idtree := refs_of_FrameIdent ident in
      let vltrees := List.flat_map refs_of_Val vl in 
      let eltrees := List.flat_map refs_of_Exp el in 
      idtree ++ vltrees ++ eltrees
  | FApp1 l =>  List.flat_map refs_of_Exp l
  | FCallMod f l => refs_of_Exp f ++ List.flat_map refs_of_Exp l
  | FCallFun m l => (refs_of_Val m) ++ (List.flat_map refs_of_Exp l)
  | FCase1 l =>        
        List.flat_map 
            (fun pge => 
                match pge with 
                (* TODO: erlang:make_ref() cannot appear guard. Do we still need to consider it? *)
                | (_p, _g, e) => refs_of_Exp e
                end) 
            l 
  | FCase2  lv exp le =>
        let head := List.flat_map refs_of_Val lv in
        let body :=  refs_of_Exp exp in 
        let rest :=  
            List.flat_map 
                (fun pge => 
                    match pge with 
                    (* TODO: erlang:make_ref() cannot appear guard. Do we still need to consider it? *)
                    | (_p, _g, e) => refs_of_Exp e
                    end) 
                le 
        in
        head ++ body ++ rest
  | FLet  _l e => refs_of_Exp e 
  | FSeq  e  => refs_of_Exp e
  | FTry vl1 e2 vl2 e3 =>
    (* TODO erlang:make_ref() cannot appear guard. Do we still need to consider it? *) 
    refs_of_Exp e2 ++ refs_of_Exp e2 ++  refs_of_Exp e3
  end.

Definition refs_of_FrameStack (fs : FrameStack) : list Reference :=
List.flat_map refs_of_Frame fs.
  
Definition create_fresh_ref (fs : FrameStack) : Reference := 
    1 + list_max (refs_of_FrameStack fs).


Lemma refs_are_fresh
    (fs : FrameStack)
    :
    (create_fresh_ref fs) ∉ (refs_of_FrameStack fs).
Proof.    
    (* NOTE The proof does not rely on the definition of refs_of_FrameStack, but 
        it is greatly simplified by (refs_of_FrameStack fs) appearing both 
        in the lemma statement and the definition of create_fresh_ref. *)
    remember (refs_of_FrameStack fs) as refs.
    destruct refs.
    1: apply not_elem_of_nil.
    assert (maxlt : Forall (λ k : nat, k < 1 + list_max (r::refs)) (r::refs)).
    {
        apply list_max_lt.
        1: symmetry; apply nil_cons.
        lia.
    }
    rewrite Heqrefs in maxlt.
    rewrite Heqrefs.
    clear Heqrefs.
    
    unfold create_fresh_ref.
    
    remember (1 + list_max (refs_of_FrameStack fs)) as n.

    intro Contra.    
    specialize Forall_forall with (P:=(λ k : nat, k < n)) (l := refs_of_FrameStack fs).
    intro ff.
    rewrite ff in maxlt.
    specialize maxlt with (x:=n).

    apply elem_of_list_In in Contra.
    apply maxlt in Contra.
    lia.
Qed.

(**
  This file defines substitutions and renamings in the nameless variable
  representation.
*)


From CoreErlang Require Export Scoping Induction.
Import ListNotations.

(** A (parallel) renaming will describe how we want to change the value of the
    indices that represent variables.*)
Definition Renaming : Set := nat -> nat.

(** Renaming shifts:
   This function defines a renaming which returns 0 for 0, and for every other
   name the successor of the original name which was associated with the previous
   name. E.g.
   *)
Definition upren (ρ : Renaming) : Renaming :=
  fun n =>
    match n with
    | 0 => 0
    | S n' => S (ρ n')
    end.

Compute upren (fun x : nat => match x with
                              | 1 => 2
                              | 2 => 3
                              | _ => 10
                              end) 0.
Compute upren (fun x : nat => match x with
                              | 1 => 2
                              | 2 => 3
                              | _ => 10
                              end) 1.
Compute upren (fun x : nat => match x with
                              | 1 => 2
                              | 2 => 3
                              | _ => 10
                              end) 2.
Compute upren (fun x : nat => match x with
                              | 1 => 2
                              | 2 => 3
                              | _ => 10
                              end) 3.

(** `iterate` applies a function `n` times to a base value. *)
Fixpoint iterate {A : Type} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f (iterate f n' a)
  end.

(** The following notation is used to shift renamings `n` times *)
Abbreviation uprenn := (iterate upren).

(** Renaming is applying the renaming function to names, while shifting it
    recursively for binding expressions.
*)
Fixpoint rename (ρ : Renaming) (ex : Exp) : Exp :=
match ex with
 | VVal e => VVal (renameVal ρ e)
 | EExp e => EExp (renameNonVal ρ e)
end
with renameVal (ρ : Renaming) (ex : Val) : Val :=
match ex with
 | VNil               => ex
 | VLit l             => ex
 | VPid p             => ex
 | VCons hd tl        => VCons (renameVal ρ hd) (renameVal ρ tl)
 | VTuple l           => VTuple (map (renameVal ρ) l)
 | VMap l             => VMap (map (prod_map (renameVal ρ) (renameVal ρ)) l)
 | VVar n             => VVar (ρ n)
 | VFunId (n,a)       => VFunId (ρ n, a)
 | VClos ext id vl e  =>
    VClos (map (fun '(i,ls,x) => (i,ls,rename (uprenn (length ext + ls) ρ) x)) ext) id vl (rename (uprenn (length ext + vl) ρ) e)
 | VBitstring b       => VBitstring b
end
with renameNonVal (ρ : Renaming) (ex : NonVal) : NonVal :=
match ex with
 | EFun vl e        => EFun vl (rename (uprenn vl ρ) e)
 | EValues el       => EValues (map (rename ρ) el)
 | ECons   hd tl    => ECons (rename ρ hd) (rename ρ tl)
 | ETuple  l        => ETuple (map (rename ρ ) l)
 | EMap    l        => EMap (map (prod_map (rename ρ) (rename ρ)) l)
 | ECall   m f l    => ECall (rename ρ m) (rename ρ f) (map (rename ρ) l)
 | EPrimOp f l      => EPrimOp f (map (rename ρ) l)
 | EApp    e l      => EApp (rename ρ e) (map (rename ρ) l)
 | ECase   e l      => ECase (rename ρ e)
                             (map (fun '(p,x,y) => (map (renamePat ρ) p,
                                                    rename (uprenn (PatListVars p) ρ) x,
                                                    rename (uprenn (PatListVars p) ρ) y)) l)
 | ELet    l e1 e2  => ELet l (rename ρ e1) (rename (uprenn (l) ρ) e2)
 | ESeq    e1 e2    => ESeq (rename ρ e1) (rename ρ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, rename (uprenn (length l + n) ρ) x)) l) (rename (uprenn (length l) ρ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (rename ρ e1) vl1 (rename (uprenn (vl1) ρ) e2) vl2 (rename (uprenn (vl2) ρ) e3)
 | EBin l => EBin (map (rename ρ) l)
 | ESeg (Build_Segment val size u t s e) => ESeg (Build_Segment (rename ρ val) (rename ρ size) u t s e)
end
with renamePat (ρ : Renaming) (p : Pat) : Pat :=
match p with
 | PVar => p
 | PLit l => p
 | PCons hd tl => PCons (renamePat ρ hd) (renamePat ρ tl)
 | PTuple l => PTuple (map (renamePat ρ) l)
 | PMap l => PMap (map (prod_map (renamePat ρ) (renamePat ρ)) l)
 | PNil => p
 | PBin segments => PBin (map (fun seg =>
                                match seg with
                                | Build_Segment val size u t s e =>
                                  Build_Segment (renamePat ρ val) (renameVal ρ size) u t s e
                                end
                              )
                          segments)
end.

(** We need to have the names for the identity elements explicitly, because
    we couldn't define identity substitution correctly. For example,
    ˝EVar 0.[idsubst] = EVar 0˝ and ˝EFunId (0, a).[idsubst] = EVar 0˝.
    In these cases, the "indentityness" depends on the context (EVar vs EFunId).


    A (parallel) substitution is a function that maps names to values or names.
    *)
Definition Substitution := nat -> Val + nat.

(** The identity substitution maps names to names. This way, we can use the
    context (EVar/EFunId) to not modify these names. *)
Definition idsubst : Substitution := fun x => inr x.

(**
  Name shifting. Every name in values and every name in a substitution
  results will be increased by one.
*)
Definition shift (ξ : Substitution) : Substitution := 
fun s =>
  match ξ s with
  | inl exp => inl (renameVal S exp)
  | inr num => inr (S num)
  end.

(**
  Substitution shifting. Introduce a new identity element for the substitution
  for 0, and shift all names in the original substitution.
*)
Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => shift ξ x'
    end.

(**
  Shifting a substitution `n` times
*)
Abbreviation upn := (iterate up_subst).

(**
  Applying a substitution. Names are replaced by the substitution,
  and in binding expressions the substitution is shifted by the number of bindings.
*)
Fixpoint subst (ξ : Substitution) (base : Exp) : Exp :=
match base with
  | VVal v => VVal (substVal ξ v)
  | EExp e => EExp (substNonVal ξ e)
end
with substVal (ξ : Substitution) (ex : Val) : Val :=
match ex with
 | VNil         => ex
 | VLit l       => ex
 | VPid p       => ex
 | VCons hd tl  => VCons (substVal ξ hd) (substVal ξ tl)
 | VTuple l     => VTuple (map (substVal ξ) l)
 | VMap l       => VMap (map (prod_map (substVal ξ) (substVal ξ)) l)
 (*| VValues el   => VValues (map (fun x => substVal ξ x) el)*)
 | VVar n       => match ξ n with
                     | inl exp => exp
                     | inr num => VVar num
                     end
 | VFunId (n,a) => match ξ n with
                     | inl exp => exp
                     | inr num => VFunId (num, a)
                     end
 | VClos ext id vl e  =>
   VClos (map (fun '(i,ls,x) => (i,ls, subst (upn (length ext + ls) ξ) x)) ext) id vl (subst (upn (length ext + vl) ξ) e)
 | VBitstring b => VBitstring b
end
with substNonVal (ξ : Substitution) (ex : NonVal) : NonVal :=
match ex with
 | EFun vl e        => EFun vl (subst (upn vl ξ) e)
 | EValues el       => EValues (map (subst ξ) el)
 | ECons   hd tl    => ECons (subst ξ hd) (subst ξ tl)
 | ETuple  l        => ETuple (map (subst ξ) l)
 | EMap    l        => EMap (map (prod_map (subst ξ) (subst ξ)) l)
 | ECall   m f l    => ECall (subst ξ m) (subst ξ f) (map (subst ξ) l)
 | EPrimOp f l      => EPrimOp f (map (subst ξ) l)
 | EApp    e l      => EApp (subst ξ e) (map (subst ξ) l)
 | ECase   e l      => ECase (subst ξ e) (map (fun '(p,x,y) => (map (substPat ξ) p,
                                                                subst (upn (PatListVars p) ξ) x,
                                                                subst (upn (PatListVars p) ξ) y)) l)
 | ELet    l e1 e2  => ELet l (subst ξ e1) (subst (upn (l) ξ) e2)
 | ESeq    e1 e2    => ESeq (subst ξ e1) (subst ξ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, subst (upn (length l + n) ξ) x)) l) (subst (upn (length l) ξ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (subst ξ e1) vl1 (subst (upn (vl1) ξ) e2) vl2 (subst (upn (vl2) ξ) e3)
 | EBin l                => EBin (map (subst ξ) l)
 | ESeg (Build_Segment val size u t s e) => ESeg (Build_Segment (subst ξ val) (subst ξ size) u t s e)
end
with substPat (σ : Substitution) (p : Pat) : Pat :=
match p with
 | PVar => p
 | PLit l => p
 | PCons hd tl => PCons (substPat σ hd) (substPat σ tl)
 | PTuple l => PTuple (map (substPat σ) l)
 | PMap l => PMap (map (prod_map (substPat σ) (substPat σ)) l)
 | PNil => p
 | PBin segments => PBin (map (fun seg =>
                                match seg with
                                | Build_Segment val size u t s e =>
                                  Build_Segment (substPat σ val) (substVal σ size) u t s e
                                end
                              )
                          segments)
end.

(**
  To define concrete substitutions, we use the following definition. It binds
  0 to s, and keeps everything else, but with an increased key.
 *)
Definition scons {X : Type} (s : X) (σ : nat -> X) (x : nat) : X :=
  match x with
  | O => s
  | S y => σ y
  end.

(** Notations for substitution application, and concrete substitutions *)
Notation "s .: σ" := (scons (inl s) σ) (at level 55, σ at level 56, right associativity).
Notation "s .:: σ" := (scons s σ) (at level 55, σ at level 56, right associativity).
Notation "s .[ σ ]" := (subst σ s)
  (at level 1, σ at level 200, left associativity,
   format "s .[ σ ]" ).
Notation "s .[ t /]" := (subst (t .: idsubst) s)
  (at level 1, t at level 200, left associativity,
   format "s .[ t /]").
Notation "s .[ t1 , t2 , .. , tn /]" :=
  (subst (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 1, left associativity,
   format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").

(* Val *)
Notation "s .[ σ ]ᵥ" := (substVal σ s)
  (at level 1, σ at level 200, left associativity,
   format "s .[ σ ]ᵥ" ).
Notation "s .[ t /]ᵥ" := (substVal (t .: idsubst) s)
  (at level 1, t at level 200, left associativity,
   format "s .[ t /]ᵥ").
Notation "s .[ t1 , t2 , .. , tn /]ᵥ" :=
  (substVal (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 1, left associativity).
  (* format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").*)

(* NonVal *)
Notation "s .[ σ ]ₑ" := (substNonVal σ s)
  (at level 1, σ at level 200, left associativity,
   format "s .[ σ ]ₑ" ).
Notation "s .[ t /]ₑ" := (substNonVal (t .: idsubst) s)
  (at level 1, t at level 200, left associativity,
   format "s .[ t /]ₑ").
Notation "s .[ t1 , t2 , .. , tn /]ₑ" :=
  (substNonVal (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 1, left associativity).
  (*format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'ₑ").*)

(* Pat *)
Notation "s .[ σ ]ₚ" := (substPat σ s)
  (at level 1, σ at level 200, left associativity,
   format "s .[ σ ]ₚ" ).
Notation "s .[ t /]ₚ" := (substPat (t .: idsubst) s)
  (at level 1, t at level 200, left associativity,
   format "s .[ t /]ₚ").
Notation "s .[ t1 , t2 , .. , tn /]ₚ" :=
  (substPat (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 1, left associativity).
  (*format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'ₚ").*)

(** Definition of a concrete substitution with a list *)
Definition list_subst (l : list Val) (ξ : Substitution) : Substitution :=
  foldr (fun v acc => v .: acc) ξ l.

(** Examples *)

Definition inc (n : Z) := ELet 1 (˝VLit n) (ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 0; ˝VLit 1%Z]).

(** Tests: *)

Goal (inc 1).[VLit 0%Z/] = inc 1. Proof. reflexivity. Qed.
Goal (EApp (˝VVar 0) [˝VVar 0; °ELet 1 (˝VVar 0) (˝VVar 0)]).[VLit 0%Z/]
  = (EApp (˝VLit 0%Z) [˝VLit 0%Z; °ELet 1 (˝VLit 0%Z) (˝VVar 0)]). 
Proof. cbn. reflexivity. Qed.

Compute (VLit (Integer 0) .: VLit (Integer 0) .: idsubst) 3.

(** Composition of substitutions. It's basically function composition,
    defined for a sum-range type. *)
Definition substcomp (ξ η : Substitution) : Substitution :=
  fun x => (* composition (substi ξ) η*)
    match η x with
    | inl exp => inl (substVal ξ exp)
    | inr n   => ξ n
    end.
Notation "σ >> ξ" := (substcomp σ ξ) (at level 56, left associativity).

(** The following tactics folds substitution shifts into one indexed shift *)
Ltac fold_upn :=
match goal with
| |- context G [up_subst (upn ?n ?ξ)] => replace (up_subst (upn n ξ)) with (upn (S n) ξ) by auto
| |- context G [upren (uprenn ?n ?ξ)] => replace (upren (uprenn n ξ)) with (uprenn (S n) ξ) by auto
end.

Ltac fold_upn_hyp :=
match goal with
| [ H : context G [up_subst (upn ?n ?ξ)] |- _ ] => replace (up_subst (upn n ξ)) with (upn (S n) ξ) in H by auto
| [ H : context G [upren (uprenn ?n ?ξ)] |- _ ] => replace (upren (uprenn n ξ)) with (uprenn (S n) ξ) in H by auto
end.

(** Notation for renaming substitutions *)
Definition ren (ρ : Renaming) : Substitution :=
  fun x => inr (ρ x).

(** Properties of renamings and substitutions *)

(**
  Shifting renamings is a homomorpism with respect to making it
  a substitution.
*)
Theorem ren_up ρ :
  ren (upren ρ) = up_subst (ren ρ).
Proof.
  extensionality x. unfold ren, upren, up_subst.
  destruct x; reflexivity.
Qed.

Corollary renn_up : forall n ρ,
  ren (uprenn n ρ) = upn n (ren ρ).
Proof.
  induction n; intros; try reflexivity.
  cbn. rewrite ren_up. rewrite IHn. auto.
Qed.

(**
  The following theorem folds the last shift into the renaming.
*)
Theorem upren_S :
  forall n ρ, uprenn n (upren ρ) = uprenn (S n) ρ.
Proof.
  induction n.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.

(**
  The following theorem folds the last shift into the substitution.
*)
Theorem up_subst_S :
  forall n ρ, upn n (up_subst ρ) = upn (S n) ρ.
Proof.
  induction n.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.

(**
  Applying a renaming is equal to applying a substitution
  created from the renaming.
*)
Theorem renaming_is_subst :
     (forall e ρ, rename ρ e = e.[ren ρ])
  /\ (forall e ρ, renameNonVal ρ e = e.[ren ρ]ₑ)
  /\ (forall e ρ, renameVal ρ e = e.[ren ρ]ᵥ)
  /\ (forall p ρ, renamePat ρ p = p.[ren ρ]ₚ).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall ρ, Forall (fun x : Exp => rename ρ x = x.[ren ρ]) l)
  (QV := fun l => forall ρ, Forall (fun x : Val => renameVal ρ x = x.[ren ρ]ᵥ) l)
  (R  := fun l => forall ρ, Forall (fun x : Exp * Exp =>
   (let '(x0, y) := x in (rename ρ x0, rename ρ y)) =
   (let '(x0, y) := x in (x0.[ren ρ], y.[ren ρ]))) l)
  (RV := fun l => forall ρ, Forall (fun x : Val * Val =>
   (let '(x0, y) := x in (renameVal ρ x0, renameVal ρ y)) =
   (let '(x0, y) := x in (x0.[ren ρ]ᵥ, y.[ren ρ]ᵥ))) l)
  (W  := fun l => forall ρ, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) := x in
     (map (renamePat ρ) p, rename (uprenn (PatListVars p) ρ) x0,
     rename (uprenn (PatListVars p) ρ) y)) =
   (let
    '(p, x0, y) := x in
     (map (substPat (ren ρ)) p, x0.[upn (PatListVars p) (ren ρ)],
     y.[upn (PatListVars p) (ren ρ)]))) l)
  (Z  := fun l => forall ρ, Forall
  (fun x : nat * Exp =>
   (let '(n, x0) := x in (n, rename (uprenn (Datatypes.length l + n) ρ) x0)) =
   (let '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) (ren ρ)]))) l)
  (VV := fun l => forall ρ, Forall
  (fun x : nat * nat * Exp =>
   (let '(i, ls, x0) := x in (i, ls, rename (uprenn (Datatypes.length l + ls) ρ) x0)) =
   (let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length l + ls) (ren ρ)]))) l)
  (PQ := fun l => forall ρ, Forall (fun p => renamePat ρ p = p.[ren ρ]ₚ) l)
  (PR := fun l => forall ρ, Forall (PBoth (fun p => renamePat ρ p = p.[ren ρ]ₚ)) l)
  (PT := fun l => forall ρ, Forall (fun seg => renamePat ρ (val seg) = (val seg).[ren ρ]ₚ /\
                                               renameVal ρ (size seg) = (size seg).[ren ρ]ᵥ) l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Val => x.[ren ρ]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. erewrite map_ext_Forall with (g := prod_map (substVal (ren ρ))
        (substVal (ren ρ))).
    - reflexivity.
    - eapply Forall_impl in H. exact H.
      destruct a; simpl. intros. eassumption.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext + ls) (ren ρ)]))).
    - rewrite H0. rewrite renn_up. reflexivity.
    - apply H.
  * simpl. reflexivity.
  (* NonVal *)
  * simpl. rewrite H. rewrite renn_up. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - reflexivity.
    - apply H.
  * simpl. erewrite map_ext_Forall with (g := prod_map (subst (ren ρ)) (subst (ren ρ))).
    - reflexivity.
    - eapply Forall_impl in H. exact H.
      destruct a; simpl. intros. eassumption.
  * simpl. rewrite H, H0. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - reflexivity.
    - apply H1.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - reflexivity.
    - apply H.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (map (substPat (ren ρ)) p, x.[upn (PatListVars p) (ren ρ)],
      y.[upn (PatListVars p) (ren ρ)]))).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite renn_up. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (ren ρ)]))).
    - rewrite H. rewrite renn_up. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite H1. do 2 rewrite renn_up. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - reflexivity.
    - apply H.
  * simpl. destruct seg. rewrite H. rewrite H0. reflexivity.
  (* Pattern *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Pat => x.[ren ρ]ₚ)).
    - reflexivity.
    - apply H.
  * simpl. erewrite map_ext_Forall with (g := prod_map (substPat (ren ρ))
        (substPat (ren ρ))).
    - reflexivity.
    - eapply Forall_impl in H. exact H.
      destruct a; simpl. intros. destruct H0 as [X Y]. simpl in *. by rewrite X, Y.
  * simpl. erewrite map_ext_Forall.
    - reflexivity.
    - eapply Forall_impl in H. exact H.
      destruct a; simpl; intros. destruct H0 as [X Y]. by rewrite X, Y.

  (* List *)
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite renn_up. reflexivity.
    - pose proof (H0 (upren ρ)). simpl.
      eapply Forall_impl in H1.
      + exact H1.
      + intros. destruct a. destruct p. rewrite upren_S in H2. simpl in H2. rewrite ren_up in H2. rewrite up_subst_S in H2. simpl in H2. apply H2.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H1. rewrite H0. rewrite renn_up.
      f_equal. erewrite map_ext_Forall. 2: exact (H ρ). reflexivity.
    - apply H2.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite renn_up. reflexivity.
    - pose proof (H0 (upren ρ)). simpl.
      eapply Forall_impl in H1.
      + exact H1.
      + intros. destruct a. rewrite upren_S in H2. simpl in H2. rewrite ren_up in H2. rewrite up_subst_S in H2. simpl in H2. apply H2.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - constructor; simpl. by rewrite H. by rewrite H0.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - by rewrite H, H0.
    - apply H1.
Qed.

(**
  Shifing does not change the identity renaming.
*)
Theorem idrenaming_up : upren id = id.
Proof.
  extensionality x. destruct x; auto.
Qed.

Corollary idrenaming_upn n : uprenn n id = id.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idrenaming_up. auto.
Qed.

(**
  Identity renaming does not change expressions/values/non-values.
*)
Theorem idrenaming_is_id : 
     (forall e, rename id e = e)
  /\ (forall e, renameNonVal id e = e)
  /\ (forall e, renameVal id e = e)
  /\ (forall p, renamePat id p = p).
Proof.
  eapply Exp_ind with 
  (Q := fun l => Forall (fun x : Exp => rename id x = id x) l)
  (QV := fun l => Forall (fun ve => renameVal id ve = ve) l)
  (R := fun l => Forall (fun x : Exp * Exp => (let '(x0, y) := x in (rename id x0, rename id y)) = id x) l)
  (RV := fun l => Forall (fun (x : Val * Val) => (let (e1,e2) := x in (renameVal id e1, renameVal id e2)) = x) l)
  (W := fun l => Forall (fun x : list Pat * Exp * Exp => (let '(p, x0, y) := x in (map (renamePat id) p, rename (uprenn (PatListVars p) id) x0, rename (uprenn (PatListVars p) id) y)) = id x) l)
  (Z := fun l => Forall
  (fun x : nat * Exp =>
   (let
    '(n, x0) := x in
     (n, rename (uprenn (Datatypes.length l + n) id) x0)) = 
   id x) l)
  (VV := fun l => Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) := x in
     (i, ls,
     rename (uprenn (Datatypes.length l + ls) Datatypes.id) x0)) =
   Datatypes.id x) l)
  (PQ := Forall (fun x => renamePat id x = x))
  (PR := Forall (PBoth (fun x => renamePat id x = x)))
  (PT := Forall (fun seg => renamePat id (val seg) = val seg /\ renameVal id (size seg) = size seg));
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity. 
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall.
    - rewrite map_id. reflexivity.
    - eapply Forall_impl in H. exact H. by destruct a.
  * simpl. auto.
  * destruct n; simpl. auto.
  * simpl. erewrite map_ext_Forall with (g := Datatypes.id).
    - rewrite map_id. rewrite idrenaming_upn. rewrite H0. reflexivity.
    - apply H.
  * simpl. reflexivity.
  (* NonVal *)
  * simpl. rewrite idrenaming_upn. rewrite H. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - eapply Forall_impl in H. exact H. by destruct a.
  * simpl. rewrite H, H0. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H1.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H. reflexivity.
    - exact H0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H. reflexivity.
    - eapply Forall_impl in H0. exact H0. by destruct a.
  * simpl. rewrite idrenaming_upn. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite idrenaming_upn. rewrite H. reflexivity.
    - exact H0.
  * simpl. do 2 rewrite idrenaming_upn. rewrite H. rewrite H0. rewrite H1. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * destruct seg. simpl in *. by rewrite H, H0.
  (* Pattern *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall.
    - rewrite map_id. reflexivity.
    - eapply Forall_impl in H. exact H. intros a X. destruct a, X; simpl in *.
      by rewrite H0, H1.
  * simpl. erewrite map_ext_Forall.
    - rewrite map_id. reflexivity.
    - eapply Forall_impl in H. exact H. intros a X. destruct a, X; simpl in *.
      by rewrite H0, H1.
  (* List *)
  * apply Forall_nil.
  * apply Forall_cons; auto.
  * constructor.
  * by constructor; auto.
  * constructor.
  * constructor.
    - rewrite H. rewrite H0. auto.
    - exact H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - exact H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite idrenaming_upn. rewrite idrenaming_up. rewrite H. reflexivity.
    - simpl. eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. rewrite idrenaming_upn. rewrite idrenaming_up. auto.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite idrenaming_upn. rewrite H0. rewrite H1.
      erewrite map_ext_Forall, map_id. reflexivity.
      eapply Forall_impl. 2: exact H. by simpl.
    - exact H2.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite idrenaming_upn. rewrite idrenaming_up. rewrite H. reflexivity.
    - simpl. eapply Forall_impl in H0.
      + exact H0.
      + destruct a. rewrite idrenaming_upn. rewrite idrenaming_up. auto.
  * apply Forall_nil.
  * by apply Forall_cons.
  * apply Forall_nil.
  * by apply Forall_cons.
  * apply Forall_nil.
  * by apply Forall_cons.
Qed.

(**
  Shifting does not change the identity substitution.
*)
Theorem idsubst_up : up_subst idsubst = idsubst.
Proof.
  extensionality x. unfold up_subst. destruct x; auto.
Qed.

Corollary idsubst_upn n : upn n idsubst = idsubst.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idsubst_up. auto.
Qed.

(**
  Identity substitution does not change expressions/values/non-values.
*)
Theorem idsubst_is_id : 
     (forall e, e.[idsubst] = e)
  /\ (forall e, e.[idsubst]ₑ = e)
  /\ (forall e, e.[idsubst]ᵥ = e)
  /\ (forall p, p.[idsubst]ₚ = p).
Proof.
  eapply Exp_ind with
  (Q := fun l => Forall (fun x : Exp => x.[idsubst] = id x) l)
  (QV := fun l => Forall (fun x : Val => x.[idsubst]ᵥ = id x) l)
  (R := fun l => Forall (fun x : Exp * Exp => (let '(x0, y) := x in (x0.[idsubst], y.[idsubst])) = id x) l)
  (RV := fun l => Forall (fun x : Val * Val => (let '(x0, y) := x in (x0.[idsubst]ᵥ, y.[idsubst]ᵥ)) = id x) l)
  (W := fun l => Forall (fun x : list Pat * Exp * Exp => (let '(p, x0, y) := x in (map (substPat idsubst) p, x0.[upn (PatListVars p) idsubst], y.[upn (PatListVars p) idsubst])) = id x) l)
  (Z := fun l => Forall
  (fun x : nat * Exp =>
   (let
    '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) idsubst])) =
   id x) l)
  (VV := fun l => Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) := x in
     (i, ls, x0.[upn (Datatypes.length l + ls) idsubst])) =
   Datatypes.id x) l)
  (PQ := Forall (fun p => p.[idsubst]ₚ = p))
  (PR := Forall (PBoth (fun p => p.[idsubst]ₚ = p)))
  (PT := Forall (fun seg => (val seg).[idsubst]ₚ = val seg /\ (size seg).[idsubst]ᵥ = size seg))
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - eapply Forall_impl. 2: exact H. by destruct a.
  * simpl. reflexivity.
  * simpl. destruct n. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := Datatypes.id).
    - rewrite map_id. rewrite idsubst_upn. rewrite H0. reflexivity.
    - apply H.
  * simpl. reflexivity.
  (* NonVal *)
  * simpl. rewrite idsubst_upn. rewrite H. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - eapply Forall_impl. 2: exact H. by destruct a.
  * simpl. rewrite H, H0. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H1.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H. reflexivity.
    - exact H0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite H. reflexivity.
    - exact H0.
  * simpl. rewrite idsubst_upn. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite idsubst_upn. rewrite H. reflexivity.
    - exact H0.
  * simpl. do 2 rewrite idsubst_upn. rewrite H. rewrite H0. rewrite H1. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * destruct seg. simpl in *. rewrite H. rewrite H0. reflexivity.
  (* Pattern *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - eapply Forall_impl. 2: exact H. destruct a. intros [H1 H2].
      simpl in *; by rewrite H1, H2.
  * simpl. erewrite map_ext_Forall with (g := Datatypes.id).
    - by rewrite map_id.
    - eapply Forall_impl. 2: exact H. destruct a. intros [H1 H2].
      simpl in *. by rewrite H1, H2.
  (* List *)
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. auto.
    - exact H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. auto.
    - exact H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. auto.
    - exact H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. auto.
    - exact H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite idsubst_upn. rewrite idsubst_up. rewrite H. reflexivity.
    - simpl. eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. rewrite idsubst_upn. rewrite idsubst_up. auto.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite idsubst_upn. rewrite H0. rewrite H1. auto.
      erewrite map_ext_Forall. 2: exact H. by rewrite map_id.
    - exact H2.
   * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite idsubst_upn. rewrite idsubst_up. rewrite H. reflexivity.
    - simpl. eapply Forall_impl in H0.
      + exact H0.
      + destruct a. rewrite idsubst_upn. rewrite idsubst_up. auto.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
Qed.

(**
  Projections of the previous theorem.
*)
Corollary idsubst_is_id_exp : 
  (forall e, e.[idsubst] = e).
Proof.
  now apply idsubst_is_id.
Qed.

Corollary idsubst_is_id_nval :
  (forall e, e.[idsubst]ₑ = e).
Proof.
  now apply idsubst_is_id.
Qed.

Corollary idsubst_is_id_val :
  (forall e, e.[idsubst]ᵥ = e).
Proof.
  now apply idsubst_is_id.
Qed.

Corollary idsubst_is_id_pat :
  (forall p, p.[idsubst]ₚ = p).
Proof.
  now apply idsubst_is_id.
Qed.


(**
  Shifting a substitution keeps its range after mapping it
  with a renaming.
*)
Lemma up_get_inl ξ x y:
  ξ x = inl y -> up_subst ξ (S x) = inl (renameVal S y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.


Lemma up_get_inr ξ x y:
  ξ x = inr y -> up_subst ξ (S x) = inr (S y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.

(**
  Helper theorem about addition expressed with `iterate`.
*)
Lemma renaming_fold m :
  (fun n => m + n) = iterate S m.
Proof.
  extensionality x. induction m; cbn; auto.
Qed.

(**
  Composing shifted renaming with a shifted substitution is the
  same as composing the original renaming with the original
  substitution, and shifting the result.
*)
Lemma upren_subst_up : forall σ ξ,
  up_subst ξ ∘ upren σ = up_subst (ξ ∘ σ).
Proof.
  intros. extensionality x. unfold upren, up_subst, "∘".
  destruct x; auto.
Qed.

Corollary uprenn_subst_upn n : forall σ ξ,
   upn n ξ ∘ uprenn n σ = upn n (ξ ∘ σ).
Proof.
  induction n; intros; auto.
  cbn. rewrite <- IHn, upren_subst_up. auto.
Qed.

(**
  `PatVars`/`PatListVars` only count pattern variable occurrences, which renaming
  and substitution never introduce, remove, or move.
*)
Lemma PatVars_rename : forall p ρ, PatVars (renamePat ρ p) = PatVars p.
Proof.
  intros p ρ.
  induction p using Pat_ind_weakened with
    (Q := fun l => Forall (fun p => PatVars (renamePat ρ p) = PatVars p) l)
    (R := fun l => Forall (PBoth (fun p => PatVars (renamePat ρ p) = PatVars p)) l)
    (T := fun l => Forall (fun seg => PatVars (renamePat ρ (val seg)) = PatVars (val seg)) l);
  simpl; auto.
  * induction l; simpl; auto. inversion IHp; subst. rewrite H1. f_equal. auto.
  * induction l; simpl; auto. inversion IHp; subst. destruct H1 as [H1a H1b]. destruct a. simpl in *. rewrite H1a, H1b. f_equal. auto.
  * induction l; simpl; auto. inversion IHp; subst. destruct a; simpl in *. rewrite H1. f_equal. auto.
  * constructor. split; [exact IHp1 | exact IHp2]. exact IHp3.
Qed.

Lemma PatVars_subst : forall p ξ, PatVars (substPat ξ p) = PatVars p.
Proof.
  intros p ξ.
  induction p using Pat_ind_weakened with
    (Q := fun l => Forall (fun p => PatVars (substPat ξ p) = PatVars p) l)
    (R := fun l => Forall (PBoth (fun p => PatVars (substPat ξ p) = PatVars p)) l)
    (T := fun l => Forall (fun seg => PatVars (substPat ξ (val seg)) = PatVars (val seg)) l);
  simpl; auto.
  * induction l; simpl; auto. inversion IHp; subst. rewrite H1. f_equal. auto.
  * induction l; simpl; auto. inversion IHp; subst. destruct H1 as [H1a H1b]. destruct a. simpl in *. rewrite H1a, H1b. f_equal. auto.
  * induction l; simpl; auto. inversion IHp; subst. destruct a; simpl in *. rewrite H1. f_equal. auto.
  * constructor. split; [exact IHp1 | exact IHp2]. exact IHp3.
Qed.

Corollary PatListVars_rename : forall l ρ, PatListVars (map (renamePat ρ) l) = PatListVars l.
Proof.
  induction l; intros; simpl; auto.
  unfold PatListVars in *; simpl. rewrite PatVars_rename, IHl. reflexivity.
Qed.

Corollary PatListVars_subst : forall l ξ, PatListVars (map (substPat ξ) l) = PatListVars l.
Proof.
  induction l; intros; simpl; auto.
  unfold PatListVars in *; simpl. rewrite PatVars_subst, IHl. reflexivity.
Qed.

(**
  Application of renamings and substitutions can be expressed as application of their
  composition.
*)
Lemma subst_ren   :
     ( forall e (σ : Renaming) (ξ : Substitution), e.[ren σ].[ξ]   = e.[ξ ∘ σ] )
  /\ ( forall e (σ : Renaming) (ξ : Substitution), e.[ren σ]ₑ.[ξ]ₑ = e.[ξ ∘ σ]ₑ )
  /\ ( forall e (σ : Renaming) (ξ : Substitution), e.[ren σ]ᵥ.[ξ]ᵥ = e.[ξ ∘ σ]ᵥ )
  /\ ( forall p (σ : Renaming) (ξ : Substitution), p.[ren σ]ₚ.[ξ]ₚ = p.[ξ ∘ σ]ₚ ).
Proof.
  (* revert ξ σ. *)
  eapply Exp_ind with
  (Q  := fun l => forall σ ξ, Forall (fun x : Exp => x.[ren σ].[ξ] = x.[ξ ∘ σ]) l)
  (QV := fun l => forall σ ξ, Forall (fun x : Val => x.[ren σ]ᵥ.[ξ]ᵥ = x.[ξ ∘ σ]ᵥ) l)
  (R  := fun l => forall σ ξ, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ren σ], y.[ren σ]) in
     (x0.[ξ], y.[ξ])) =
   (let '(x0, y) := x in (x0.[ξ ∘ σ], y.[ξ ∘ σ]))) l)
  (RV := fun l => forall σ ξ, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ren σ]ᵥ, y.[ren σ]ᵥ) in
     (x0.[ξ]ᵥ, y.[ξ]ᵥ)) =
   (let '(x0, y) := x in (x0.[ξ ∘ σ]ᵥ, y.[ξ ∘ σ]ᵥ))) l)
  (W  := fun l => forall σ ξ, Forall (fun '(p, x0, y) =>
     (map (fun p => p.[ren σ]ₚ.[ξ]ₚ) p, x0.[upn (PatListVars p) (ren σ)].[upn (PatListVars p) ξ],
      y.[upn (PatListVars p) (ren σ)].[upn (PatListVars p) ξ]) =
   (map (fun p => p.[ξ ∘ σ]ₚ) p, x0.[upn (PatListVars p) (ξ ∘ σ)],
     y.[upn (PatListVars p) (ξ ∘ σ)])) l)
  (Z  := fun l => forall σ ξ, Forall
  (fun x : nat * Exp =>
   (let
    '(n, x0) :=
     let
     '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) (ren σ)])
     in
     (n,
     x0.[upn
           (Datatypes.length
              (map
                 (fun '(n0, x1) =>
                  (n0, x1.[upn (Datatypes.length l + n0) (ren σ)]))
                 l) + n) ξ])) =
   (let
    '(n, x0) := x in
     (n, x0.[upn (Datatypes.length l + n) (ξ ∘ σ)]))) l)
  (VV := fun l => forall σ ξ, Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) :=
     let
     '(i, ls, x0) := x in
      (i, ls, x0.[upn (Datatypes.length l + ls) (ren σ)]) in
     (i, ls,
     x0.[upn
           (Datatypes.length
              (map
                 (fun '(i0, ls0, x1) =>
                  (i0, ls0,
                  x1.[upn (Datatypes.length l + ls0) (ren σ)]))
                 l) + ls) ξ])) =
   (let
    '(i, ls, x0) := x in
     (i, ls, x0.[upn (Datatypes.length l + ls) (ξ ∘ σ)]))) l)
  (PQ := fun l => forall σ ξ, Forall (fun x : Pat => x.[ren σ]ₚ.[ξ]ₚ = x.[ξ ∘ σ]ₚ) l)
  (PR := fun l => forall σ ξ, Forall (PBoth (fun x : Pat => x.[ren σ]ₚ.[ξ]ₚ = x.[ξ ∘ σ]ₚ)) l)
  (PT := fun l => forall σ ξ, Forall (fun seg => (val seg).[ren σ]ₚ.[ξ]ₚ = (val seg).[ξ ∘ σ]ₚ /\
                                                 (size seg).[ren σ]ᵥ.[ξ]ᵥ = (size seg).[ξ ∘ σ]ᵥ) l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g:= (fun x : Val => x.[ξ ∘ σ]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - eapply Forall_impl. 2: apply H. destruct a; simpl. intro. inversion H0.
      by rewrite H2, H3.
  * auto.
  * auto. destruct n. auto.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(i, ls, x) =>
      (i, ls, x.[upn (Datatypes.length ext + ls) (ξ ∘ σ)]))).
    - simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H0. rewrite length_map. reflexivity.
    - apply H.
  * simpl. reflexivity.
  (* NonVal *)
  * simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ ∘ σ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ ∘ σ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - eapply Forall_impl. 2: apply H.
      destruct a. intros. inversion H0. simpl. by rewrite H2, H3.
  * simpl. rewrite H, H0. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ ∘ σ])).
    - reflexivity.
    - apply H1.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ ∘ σ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ ∘ σ])).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - rewrite H. reflexivity.
    - eapply Forall_impl. 2: apply H0.
      intros. destruct a, p. inv H1. rewrite map_map, H3.
      rewrite PatListVars_subst. by rewrite H4, H5.
  * simpl. rewrite H. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (ξ ∘ σ)]))).
    - rewrite <- renn_up. rewrite H. rewrite <- uprenn_subst_upn. rewrite length_map. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H0.
    rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H1. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ ∘ σ])).
    - reflexivity.
    - apply H.
  * destruct seg. simpl. rewrite H. rewrite H0. reflexivity.
  (* Pattern *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - eapply Forall_impl. 2: apply H. destruct a; simpl. intro. inversion H0.
      simpl in *.
      by rewrite H1, H2.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - eapply Forall_impl. 2: apply H.
      destruct a; intros [X Y]. simpl in *. by rewrite X, Y.
  (* List *)
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite <- ren_up. rewrite <- upren_subst_up. rewrite H. rewrite length_map.  reflexivity.
    - simpl. specialize (H0 (upren σ) (up_subst ξ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. rewrite length_map. rewrite length_map. intros. rewrite ren_up in H1. rewrite up_subst_S in H1. rewrite up_subst_S in H1. simpl in H1. f_equal. inversion H1. rewrite upren_subst_up in H3. rewrite up_subst_S in H3. simpl in H3. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H0. rewrite H1.
      erewrite map_ext_Forall. 2: apply H. reflexivity.
    - eapply Forall_impl. 2: apply H2. destruct a, p; intros X.
      inversion X. by rewrite H4, H5, H6.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite <- ren_up. rewrite <- upren_subst_up. rewrite H. rewrite length_map.  reflexivity.
    - simpl. specialize (H0 (upren σ) (up_subst ξ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. rewrite length_map. rewrite length_map. intros. rewrite ren_up in H1. rewrite up_subst_S in H1. rewrite up_subst_S in H1. simpl in H1. f_equal. inversion H1. rewrite upren_subst_up in H3. rewrite up_subst_S in H3. simpl in H3. exact H3.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
Qed.

(**
  Folding rename shifts with composition
*)
Lemma upren_comp : forall σ ρ,
  upren σ ∘ upren ρ = upren (σ ∘ ρ).
Proof.
  intros. unfold upren, "∘". extensionality n. destruct n; auto.
Qed.

Corollary uprenn_comp : forall n σ ρ,
  uprenn n σ ∘ uprenn n ρ = uprenn n (σ ∘ ρ).
Proof.
  induction n; intros; auto. simpl. rewrite upren_comp, IHn. auto.
Qed.

(**
  Folding last rename shifts.
*)
Lemma upren_uprenn : forall n σ,
  upren (uprenn n σ) = uprenn n (upren σ).
Proof.
  intros. induction n.
  * simpl. reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.

(**
  Double renaming can be expressed with composition.
*)
Theorem rename_comp :
     (forall e σ ρ, rename σ (rename ρ e) = rename (σ ∘ ρ) e)
  /\ (forall e σ ρ, renameNonVal σ (renameNonVal ρ e) = renameNonVal (σ ∘ ρ) e)
  /\ (forall e σ ρ, renameVal σ (renameVal ρ e) = renameVal (σ ∘ ρ) e)
  /\ (forall p σ ρ, renamePat σ (renamePat ρ p) = renamePat (σ ∘ ρ) p).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall σ ρ, Forall (fun x : Exp => rename σ (rename ρ x) = rename (σ ∘ ρ) x) l)
  (QV := fun l => forall σ ρ, Forall (fun x : Val =>
   renameVal σ (renameVal ρ x) = renameVal (σ ∘ ρ) x) l)
  (R  := fun l => forall σ ρ, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (rename ρ x0, rename ρ y) in
     (rename σ x0, rename σ y)) =
   (let '(x0, y) := x in (rename (σ ∘ ρ) x0, rename (σ ∘ ρ) y))) l)
  (RV := fun l => forall σ ρ, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (renameVal ρ x0, renameVal ρ y)
     in (renameVal σ x0, renameVal σ y)) =
   (let
    '(x0, y) := x in (renameVal (σ ∘ ρ) x0, renameVal (σ ∘ ρ) y))) l)
  (W  := fun l => forall σ ρ, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (map (renamePat ρ) p, rename (uprenn (PatListVars p) ρ) x0,
      rename (uprenn (PatListVars p) ρ) y) in
     (map (renamePat σ) p, rename (uprenn (PatListVars p) σ) x0,
     rename (uprenn (PatListVars p) σ) y)) =
   (let
    '(p, x0, y) := x in
     (map (renamePat (σ ∘ ρ)) p, rename (uprenn (PatListVars p) (σ ∘ ρ)) x0,
     rename (uprenn (PatListVars p) (σ ∘ ρ)) y))) l)
  (Z  := fun l => forall σ ρ, Forall
  (fun x : nat * Exp =>
   (let
    '(n, x0) :=
     let
     '(n, x0) := x in
      (n, rename (uprenn (Datatypes.length l + n) ρ) x0) in
     (n,
     rename
       (uprenn
          (Datatypes.length
             (map
                (fun '(n0, x1) =>
                 (n0,
                 rename (uprenn (Datatypes.length l + n0) ρ) x1)) l) +
           n) σ) x0)) =
   (let
    '(n, x0) := x in
     (n, rename (uprenn (Datatypes.length l + n) (σ ∘ ρ)) x0))) l)
  (VV := fun l => forall σ ρ, Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) :=
     let
     '(i, ls, x0) := x in
      (i, ls, rename (uprenn (Datatypes.length l + ls) ρ) x0) in
     (i, ls, rename (uprenn (Datatypes.length l + ls) σ) x0)) =
   (let
    '(i, ls, x0) := x in
     (i, ls,
     rename (uprenn (Datatypes.length l + ls) (σ ∘ ρ)) x0))) l)
  (PQ := fun l => forall σ ρ, Forall (fun x : Pat => renamePat σ (renamePat ρ x) = renamePat (σ ∘ ρ) x) l)
  (PR := fun l => forall σ ρ, Forall (PBoth (fun x : Pat => renamePat σ (renamePat ρ x) = renamePat (σ ∘ ρ) x)) l)
  (PT := fun l => forall σ ρ, Forall (fun seg => renamePat σ (renamePat ρ (val seg)) = renamePat (σ ∘ ρ) (val seg) /\ renameVal σ (renameVal ρ (size seg)) = renameVal (σ ∘ ρ) (size seg)) l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Val => renameVal (σ ∘ ρ) x)).
    - reflexivity. 
    - apply H.
  * simpl. rewrite map_map.
  erewrite map_ext_Forall with (g := prod_map (renameVal (σ ∘ ρ)) (renameVal (σ ∘ ρ))).
    - reflexivity.
    - eapply Forall_impl in H. exact H. destruct a; simpl; intros; eassumption.
  * simpl. auto.
  * simpl. destruct n. auto.
  * simpl. rewrite map_map. rewrite length_map. erewrite map_ext_Forall with (g := (fun '(i, ls, x) =>
      (i, ls,
      rename (uprenn (Datatypes.length ext + ls) (σ ∘ ρ)) x))).
    - simpl. rewrite H0. rewrite <- uprenn_comp. reflexivity.
    - apply H.
  * simpl. reflexivity.
  (* NonVal *)
  * simpl. rewrite <- uprenn_comp. rewrite H. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (σ ∘ ρ) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (σ ∘ ρ) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map.
  erewrite map_ext_Forall with (g := prod_map (rename (σ ∘ ρ)) (rename (σ ∘ ρ))).
    - reflexivity.
    - eapply Forall_impl in H. exact H. destruct a; simpl; intros; eassumption.
  * simpl. rewrite H, H0. rewrite map_map.
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (σ ∘ ρ) x)).
    - reflexivity.
    - apply H1.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (σ ∘ ρ) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (σ ∘ ρ) x)).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite map_map.
  erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (map (renamePat (σ ∘ ρ)) p, rename (uprenn (PatListVars p) (σ ∘ ρ)) x,
      rename (uprenn (PatListVars p) (σ ∘ ρ)) y))).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite <- uprenn_comp. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
  erewrite map_ext_Forall with (g := (fun '(n, x) =>
      (n, rename (uprenn (Datatypes.length l + n) (σ ∘ ρ)) x))).
    - rewrite <- uprenn_comp. rewrite length_map. rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite H1. do 2 rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite map_map.
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (σ ∘ ρ) x)).
    - reflexivity.
    - apply H.
  * destruct seg. simpl in *. rewrite H. rewrite H0. reflexivity.
  (* Pattern *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := renamePat (σ ∘ ρ)).
    - reflexivity.
    - apply (H σ ρ).
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - specialize (H σ ρ). eapply Forall_impl in H. exact H.
      destruct a; simpl; intros [Ha Hb]; simpl in Ha, Hb. rewrite Ha, Hb. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - specialize (H σ ρ). eapply Forall_impl in H. exact H.
      destruct a; simpl; intros [Ha Hb]; simpl in Ha, Hb. rewrite Ha, Hb. reflexivity.
  (* List *)
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite H. rewrite uprenn_comp. reflexivity.
    - simpl. specialize (H0 (upren σ) (upren ρ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. intros. f_equal. inversion H1.
        do 3 rewrite upren_uprenn. rewrite <- upren_comp. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite (PatListVars_rename l ρ).
      rewrite H0. rewrite H1. rewrite uprenn_comp.
      f_equal. rewrite map_map. erewrite map_ext_Forall with (g := renamePat (σ ∘ ρ)).
      + reflexivity.
      + apply (H σ ρ).
    - apply H2.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite length_map. rewrite H. rewrite uprenn_comp. reflexivity.
    - simpl. specialize (H0 (upren σ) (upren ρ)).
    eapply Forall_impl in H0.
      + exact H0.
      + do 2 rewrite length_map. destruct a. intros. f_equal. inversion H1.
        do 3 rewrite upren_uprenn. rewrite <- upren_comp. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - apply (H σ ρ).
    - apply (H0 σ ρ).
  * apply Forall_nil.
  * apply Forall_cons.
    - split; [apply (H σ ρ) | apply (H0 σ ρ)].
    - apply (H1 σ ρ).
  * apply Forall_nil.
  * apply Forall_cons.
    - split; [apply (H σ ρ) | apply (H0 σ ρ)].
    - apply (H1 σ ρ).
Qed.


(**
  Composing a renaming substitution with a substitution is a homomorphic with
  respect to shifting.
*)
Lemma subst_up_upren :
  forall σ ξ, ren (upren σ) >> up_subst ξ = up_subst (ren σ >> ξ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>", shift.
  destruct x; auto. destruct (ξ x) eqn:P; auto.
  (* pose proof renaming_is_subst. destruct a. destruct H0. *)
  pose proof renaming_is_subst as [_ [_ [H1 _]]].
  rewrite <- H1. rewrite <- H1.
  f_equiv.
  (*apply functional_extensionality.*)
  replace (fun n : nat => match n with
                       | 0 => 0
                       | S n' => S (σ n')
                       end) with (upren σ) by auto.
  pose proof rename_comp as [_ [_ [H2 _]]].
  rewrite H2. rewrite H2. f_equiv.
  extensionality n. unfold "∘". destruct n; reflexivity.
Qed.

Lemma subst_upn_uprenn : forall n σ ξ,
  ren (uprenn n σ) >> upn n ξ = upn n (ren σ >> ξ).
Proof.
  induction n; intros; auto. simpl.
  rewrite subst_up_upren, IHn. auto.
Qed.

(**
  Another lemma saying composing a substitution with a renaming substitution is the same
  as applying them after eachother.
*)
Lemma ren_subst :
     (forall e ξ σ, e.[ξ].[ren σ] = e.[ren σ >> ξ])
  /\ (forall e ξ σ, e.[ξ]ₑ.[ren σ]ₑ = e.[ren σ >> ξ]ₑ)
  /\ (forall e ξ σ, e.[ξ]ᵥ.[ren σ]ᵥ = e.[ren σ >> ξ]ᵥ)
  /\ (forall p ξ σ, p.[ξ]ₚ.[ren σ]ₚ = p.[ren σ >> ξ]ₚ).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall ξ σ, Forall (fun x : Exp => x.[ξ].[ren σ] = x.[ren σ >> ξ]) l)
  (QV := fun l => forall ξ σ, Forall (fun x : Val => x.[ξ]ᵥ.[ren σ]ᵥ = x.[ren σ >> ξ]ᵥ) l)
  (R  := fun l => forall ξ σ, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ], y.[ξ]) in
     (x0.[ren σ], y.[ren σ])) =
   (let '(x0, y) := x in (x0.[ren σ >> ξ], y.[ren σ >> ξ]))) l)
  (RV := fun l => forall ξ σ, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ) in
     (x0.[ren σ]ᵥ, y.[ren σ]ᵥ)) =
   (let '(x0, y) := x in (x0.[ren σ >> ξ]ᵥ, y.[ren σ >> ξ]ᵥ))) l)
   (W  := fun l => forall ξ σ, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (map (substPat ξ) p, x0.[upn (PatListVars p) ξ],
      y.[upn (PatListVars p) ξ]) in
     (map (substPat (ren σ)) p, x0.[upn (PatListVars p) (ren σ)],
     y.[upn (PatListVars p) (ren σ)])) =
   (let
    '(p, x0, y) := x in
     (map (substPat (ren σ >> ξ)) p, x0.[upn (PatListVars p) (ren σ >> ξ)],
     y.[upn (PatListVars p) (ren σ >> ξ)]))) l)
   (Z  := fun l => forall ξ σ, Forall
  (fun x : nat * Exp =>
   (let
    '(n, x0) :=
     let '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) ξ])
     in
     (n,
     x0.[upn
           (Datatypes.length
              (map
                 (fun '(n0, x1) =>
                  (n0, x1.[upn (Datatypes.length l + n0) ξ])) l) + n)
           (ren σ)])) =
   (let
    '(n, x0) := x in
     (n, x0.[upn (Datatypes.length l + n) (ren σ >> ξ)]))) l)
  (VV := fun l => forall ξ σ, Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) :=
     let
     '(i, ls, x0) := x in
      (i, ls, x0.[upn (Datatypes.length l + ls) ξ]) in
     (i, ls, x0.[upn (Datatypes.length l + ls) (ren σ)])) =
   (let
    '(i, ls, x0) := x in
     (i, ls,
     x0.[upn (Datatypes.length l + ls) (ren σ >> ξ)])))
  l)
  (PQ := fun l => forall ξ σ, Forall (fun x : Pat => x.[ξ]ₚ.[ren σ]ₚ = x.[ren σ >> ξ]ₚ) l)
  (PR := fun l => forall ξ σ, Forall (PBoth (fun x : Pat => x.[ξ]ₚ.[ren σ]ₚ = x.[ren σ >> ξ]ₚ)) l)
  (PT := fun l => forall ξ σ, Forall (fun seg => (val seg).[ξ]ₚ.[ren σ]ₚ = (val seg).[ren σ >> ξ]ₚ /\ (size seg).[ξ]ᵥ.[ren σ]ᵥ = (size seg).[ren σ >> ξ]ᵥ) l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Val => x.[ren σ >> ξ]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := prod_map (substVal (ren σ >> ξ)) (substVal (ren σ >> ξ))).
    - reflexivity.
    - eapply Forall_impl in H. exact H. destruct a; simpl; intros; eassumption.
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * simpl. unfold ">>", ren. destruct n. destruct (ξ n) eqn:P; auto.
  * simpl. rewrite map_map. rewrite length_map. erewrite map_ext_Forall with (g := (fun '(i, ls, x) =>
      (i, ls, x.[upn (Datatypes.length ext + ls) (ren σ >> ξ)]))).
    - simpl. f_equal. rewrite <- subst_upn_uprenn. rewrite <- H0. rewrite <- renn_up. reflexivity.
    - apply H.
  * simpl. reflexivity.
  (* NonVal *)
  * simpl. rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite H. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren σ >> ξ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren σ >> ξ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := prod_map (subst (ren σ >> ξ)) (subst (ren σ >> ξ))).
      - reflexivity.
      - eapply Forall_impl in H. exact H. destruct a; simpl; intros; eassumption.
  * simpl. rewrite H, H0. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren σ >> ξ])).
      - reflexivity.
      - apply H1.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren σ >> ξ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren σ >> ξ])).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (map (substPat (ren σ >> ξ)) p, x.[upn (PatListVars p) (ren σ >> ξ)],
      y.[upn (PatListVars p) (ren σ >> ξ)]))).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite H. rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(n, x) =>
      (n, x.[upn (Datatypes.length l + n) (ren σ >> ξ)]))).
      - rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite H. rewrite length_map. reflexivity.
      - apply H0.
  * simpl. rewrite H. do 2 rewrite <- renn_up. do 2 rewrite <- subst_upn_uprenn.
    rewrite H0. rewrite H1. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren σ >> ξ])).
      - reflexivity.
      - apply H.
  * destruct seg. simpl in *. rewrite H. rewrite H0. reflexivity.
  (* Pattern *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := substPat (ren σ >> ξ)).
    - reflexivity.
    - apply (H ξ σ).
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - specialize (H ξ σ). eapply Forall_impl in H. exact H.
      destruct a; simpl; intros [Ha Hb]; simpl in Ha, Hb. rewrite Ha, Hb. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - specialize (H ξ σ). eapply Forall_impl in H. exact H.
      destruct a; simpl; intros [Ha Hb]; simpl in Ha, Hb. rewrite Ha, Hb. reflexivity.
  (* List *)
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite <- subst_upn_uprenn. rewrite <- renn_up.
      rewrite H. reflexivity.
    - simpl. specialize (H0 (up_subst ξ) (upren σ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. intros. f_equal. inversion H1.
        rewrite ren_up in H3 at 1. rewrite up_subst_S in H3. simpl in H3.
        rewrite up_subst_S in H3. simpl in H3. rewrite subst_up_upren in H3.
        rewrite up_subst_S in H3. simpl in H3. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite (PatListVars_subst l ξ).
      rewrite <- renn_up. rewrite H0. rewrite H1. rewrite subst_upn_uprenn.
      f_equal. rewrite map_map. erewrite map_ext_Forall with (g := substPat (ren σ >> ξ)).
      + reflexivity.
      + apply (H ξ σ).
    - apply H2.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite length_map. rewrite <- subst_upn_uprenn. rewrite <- renn_up.
      rewrite H. reflexivity.
    - simpl. specialize (H0 (up_subst ξ) (upren σ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. intros. f_equal. rewrite length_map. inversion H1.
        rewrite ren_up in H3 at 1. rewrite up_subst_S in H3. simpl in H3.
        rewrite up_subst_S in H3. simpl in H3. rewrite subst_up_upren in H3.
        rewrite up_subst_S in H3. simpl in H3.
        rewrite length_map in H3. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - apply (H ξ σ).
    - apply (H0 ξ σ).
  * apply Forall_nil.
  * apply Forall_cons.
    - split; [apply (H ξ σ) | apply (H0 ξ σ)].
    - apply (H1 ξ σ).
  * apply Forall_nil.
  * apply Forall_cons.
    - split; [apply (H ξ σ) | apply (H0 ξ σ)].
    - apply (H1 ξ σ).
Qed.

(**
  Subsitution composition is homomorphic with respect to shifting.
*)
Lemma up_comp ξ η :
  up_subst ξ >> up_subst η = up_subst (ξ >> η).
Proof.
  extensionality x.
  unfold ">>". cbn. unfold up_subst, shift. destruct x; auto.
  destruct (η x) eqn:P; auto.
  pose proof renaming_is_subst as [_ [_ [H1 _]]].
  rewrite H1. rewrite H1.
  pose proof ren_subst as [_ [_ [H2 _]]].
  rewrite H2.
  pose proof subst_ren as [_ [_ [H3 _]]].
  rewrite H3.
  unfold ren. f_equiv. f_equiv. extensionality n.
  unfold "∘", ">>", up_subst, shift. destruct (ξ n) eqn:P0; auto.
  rewrite H1. auto.
Qed.

Corollary upn_comp : forall n ξ η,
  upn n ξ >> upn n η = upn n (ξ >> η).
Proof.
  induction n; intros; auto. simpl. rewrite <- IHn, up_comp. auto.
Qed.

(**
  Applying two substitutions after eachother is the same as applying their composition.
*)
Lemma subst_comp :
     (forall e ξ η, e.[ξ].[η] = e.[η >> ξ])
  /\ (forall e ξ η, e.[ξ]ₑ.[η]ₑ = e.[η >> ξ]ₑ)
  /\ (forall e ξ η, e.[ξ]ᵥ.[η]ᵥ = e.[η >> ξ]ᵥ)
  /\ (forall p ξ η, p.[ξ]ₚ.[η]ₚ = p.[η >> ξ]ₚ).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall ξ η, Forall (fun x : Exp => x.[ξ].[η] = x.[η >> ξ]) l)
  (QV := fun l => forall ξ η, Forall (fun x : Val => x.[ξ]ᵥ.[η]ᵥ = x.[η >> ξ]ᵥ) l)
  (R  := fun l => forall ξ η, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ], y.[ξ]) in (x0.[η], y.[η])) =
   (let '(x0, y) := x in (x0.[η >> ξ], y.[η >> ξ]))) l)
  (RV := fun l => forall ξ η, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ) in
     (x0.[η]ᵥ, y.[η]ᵥ)) =
   (let '(x0, y) := x in (x0.[η >> ξ]ᵥ, y.[η >> ξ]ᵥ))) l)
   (W  := fun l => forall ξ η, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (map (substPat ξ) p, x0.[upn (PatListVars p) ξ],
      y.[upn (PatListVars p) ξ]) in
     (map (substPat η) p, x0.[upn (PatListVars p) η],
     y.[upn (PatListVars p) η])) =
   (let
    '(p, x0, y) := x in
     (map (substPat (η >> ξ)) p, x0.[upn (PatListVars p) (η >> ξ)],
     y.[upn (PatListVars p) (η >> ξ)]))) l)
  (Z  := fun l => forall ξ η, Forall
  (fun x : nat * Exp =>
   (let
    '(n, x0) := let '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) ξ]) in
     (n, x0.[upn (Datatypes.length (map (fun '(n0, x1) => (n0, x1.[upn (Datatypes.length l + n0) ξ])) l) + n) η])) =
   (let '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) (η >> ξ)]))) l)
  (VV := fun l => forall ξ η, Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) := let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length l + ls) ξ]) in
     (i, ls, x0.[upn (Datatypes.length l + ls) η])) =
   (let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length l + ls) (η >> ξ)]))) l)
  (PQ := fun l => forall ξ η, Forall (fun x : Pat => x.[ξ]ₚ.[η]ₚ = x.[η >> ξ]ₚ) l)
  (PR := fun l => forall ξ η, Forall (PBoth (fun x : Pat => x.[ξ]ₚ.[η]ₚ = x.[η >> ξ]ₚ)) l)
  (PT := fun l => forall ξ η, Forall (fun seg => (val seg).[ξ]ₚ.[η]ₚ = (val seg).[η >> ξ]ₚ /\ (size seg).[ξ]ᵥ.[η]ᵥ = (size seg).[η >> ξ]ᵥ) l)
  ;intros.
    (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Val => x.[η >> ξ]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := prod_map (substVal (η >> ξ)) (substVal (η >> ξ))).
    - reflexivity.
    - eapply Forall_impl in H. exact H. destruct a; simpl; intros; eassumption.
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * simpl. unfold ">>", ren. destruct n. destruct (ξ n) eqn:P; auto.
  * simpl. rewrite map_map. rewrite length_map.
    erewrite map_ext_Forall with (g := (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext + ls) (η >> ξ)]))).
    - rewrite H0. f_equal. rewrite upn_comp. reflexivity.
    - apply H.
  * simpl. reflexivity.
  (* NonVal *)
  * simpl. rewrite H. rewrite upn_comp. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[η >> ξ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[η >> ξ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := prod_map (subst (η >> ξ)) (subst (η >> ξ))).
      - reflexivity.
      - eapply Forall_impl in H. exact H. destruct a; simpl; intros; eassumption.
  * simpl. rewrite H, H0. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[η >> ξ])).
      - reflexivity.
      - apply H1.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[η >> ξ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[η >> ξ])).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (map (substPat (η >> ξ)) p, x.[upn (PatListVars p) (η >> ξ)],
      y.[upn (PatListVars p) (η >> ξ)]))).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite upn_comp. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (η >> ξ)]))).
      - rewrite H. rewrite length_map. rewrite upn_comp. reflexivity.
      - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite H1. rewrite upn_comp. rewrite upn_comp. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[η >> ξ])).
      - reflexivity.
      - apply H.
  * destruct seg. simpl in *. rewrite H. rewrite H0. reflexivity.
  (* Pattern *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := substPat (η >> ξ)).
    - reflexivity.
    - apply (H ξ η).
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - specialize (H ξ η). eapply Forall_impl in H. exact H.
      destruct a; simpl; intros [Ha Hb]; simpl in Ha, Hb. rewrite Ha, Hb. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - reflexivity.
    - specialize (H ξ η). eapply Forall_impl in H. exact H.
      destruct a; simpl; intros [Ha Hb]; simpl in Ha, Hb. rewrite Ha, Hb. reflexivity.
  (* List *)
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. reflexivity.
    - apply H0.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite H. rewrite upn_comp. reflexivity.
    - simpl. specialize (H0 (up_subst ξ) (up_subst η)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. intros. f_equal. inversion H1.
        do 2 rewrite up_subst_S in H3. simpl in H3.
        rewrite (upn_comp 1) in H3. simpl in H3. rewrite up_subst_S in H3. simpl in H3. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite (PatListVars_subst l ξ).
      rewrite H0. rewrite H1. rewrite upn_comp.
      f_equal. rewrite map_map. erewrite map_ext_Forall with (g := substPat (η >> ξ)).
      + reflexivity.
      + apply (H ξ η).
    - apply H2.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite length_map. rewrite H. rewrite upn_comp. reflexivity.
    - simpl. specialize (H0 (up_subst ξ) (up_subst η)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. do 2 rewrite length_map. intros. f_equal.  inversion H1.
        do 2 rewrite up_subst_S in H3. simpl in H3.
        rewrite (upn_comp 1) in H3. simpl in H3. rewrite up_subst_S in H3. simpl in H3. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - apply (H ξ η).
    - apply (H0 ξ η).
  * apply Forall_nil.
  * apply Forall_cons.
    - split; [apply (H ξ η) | apply (H0 ξ η)].
    - apply (H1 ξ η).
  * apply Forall_nil.
  * apply Forall_cons.
    - split; [apply (H ξ η) | apply (H0 ξ η)].
    - apply (H1 ξ η).
Qed.

(**
  Projections of the previous theorem.
*)
Corollary subst_comp_exp :
  forall e ξ η, e.[ξ].[η] = e.[η >> ξ].
Proof.
  apply subst_comp.
Qed.

Corollary subst_comp_val :
  forall e ξ η, e.[ξ]ᵥ.[η]ᵥ = e.[η >> ξ]ᵥ.
Proof.
  apply subst_comp.
Qed.

Corollary subst_comp_nval :
  forall e ξ η, e.[ξ]ₑ.[η]ₑ = e.[η >> ξ]ₑ.
Proof.
  apply subst_comp.
Qed.

Corollary subst_comp_pat :
  forall p ξ η, p.[ξ]ₚ.[η]ₚ = p.[η >> ξ]ₚ.
Proof.
  apply subst_comp.
Qed.

(**
  Shiting names by one and applying an extended substition (which maps 0 to some value)
  to an expression is the same as applying only the non-extended substitution to the expression.
*)
Theorem rename_subst_core :
     (forall e v ξ, (rename S e).[v .:: ξ] = e.[ξ])
  /\ (forall e v ξ, (renameNonVal S e).[v .:: ξ]ₑ = e.[ξ]ₑ)
  /\ (forall e v ξ, (renameVal S e).[v .:: ξ]ᵥ = e.[ξ]ᵥ).
Proof.
  pose proof renaming_is_subst as [H0e [H0n [H0v _]]].
  pose proof subst_comp as [H1e [H1n [H1v _]]].
  split. 2: split.
  * intros. rewrite H0e. rewrite H1e. reflexivity.
  * intros. rewrite H0n. rewrite H1n. reflexivity.
  * intros. rewrite H0v. rewrite H1v. reflexivity. 
Qed.

Corollary rename_subst : forall e v,
  (rename S e).[v/] = e.
Proof.
  intros. rewrite (proj1 rename_subst_core e (inl v) idsubst).
  now rewrite idsubst_is_id_exp.
Qed.

(**
  The following lemmas express the equalities between composition and substitution extension.
*)
Lemma scons_substcomp_core v ξ η :
  η >> (v .:: ξ) = match v with 
                   | inl exp => inl (exp.[η]ᵥ)
                   | inr n => η n
                   end .:: (η >> ξ).
Proof.
  extensionality x. unfold scons, substcomp. now destruct x.
Qed.


Lemma scons_substcomp v ξ η :
  η >> (v .: ξ) = v.[η]ᵥ .: (η >> ξ).
Proof.
  apply scons_substcomp_core.
Qed.


Lemma scons_substcomp_list ξ η vals :
  η >> (list_subst vals ξ) = list_subst (map (substVal η) vals) (η >> ξ).
Proof.
  induction vals; simpl. auto.
  rewrite scons_substcomp, IHvals. auto.
Qed.


Lemma substcomp_scons_core v ξ η :
  (v .:: η) >> up_subst ξ = v .:: (η >> ξ).
Proof.
  extensionality x. unfold scons, substcomp, up_subst. destruct x; auto.
  unfold shift. destruct (ξ x) eqn:P; auto.
  pose proof renaming_is_subst as [_ [_ [H _]]].
  pose proof subst_comp as [_ [_ [H0 _]]].
  rewrite H. rewrite H0. f_equal.
Qed.

Lemma substcomp_scons v ξ η :
  (v .: η)  >> up_subst ξ = v .: (η >> ξ).
Proof.
  apply substcomp_scons_core.
Qed.

Corollary substcomp_list l ξ η :
  list_subst l η >> upn (length l) ξ = list_subst l (η >> ξ).
Proof.
  induction l; simpl; auto.
  * now rewrite substcomp_scons, IHl.
Qed.

Corollary substcomp_list_eq l ξ η n:
  n = length l ->
  list_subst l η >> upn n ξ = list_subst l (η >> ξ).
Proof.
  intros. subst. now apply substcomp_list.
Qed.

(**
  The nth value of a concrete substitution comes from the list from which
  it was created, if n is less than the length of that list.
*)
Theorem list_subst_lt : forall n vals ξ, n < length vals ->
  list_subst vals ξ n = inl (nth n vals VNil).
Proof.
  induction n; intros; destruct vals.
  * inversion H.
  * simpl. auto.
  * inversion H.
  * simpl in H. apply Nat.succ_lt_mono in H. eapply IHn in H. simpl. exact H.
Qed.

(**
  Otherwise, it is the "n - length of the list"th value of the base substitution.
*)
Theorem list_subst_ge : forall n vals ξ, n >= length vals ->
  list_subst vals ξ n = ξ (n - length vals).
Proof.
  induction n; intros; destruct vals.
  * simpl. auto.
  * inversion H.
  * cbn. auto.
  * simpl in H. apply le_S_n in H. eapply IHn in H. simpl. exact H.
Qed.

(**
  The previous two theorems combined:
*)
Corollary list_subst_get_possibilities : forall n vals ξ,
  list_subst vals ξ n = inl (nth n vals VNil) /\ n < length vals
\/
  list_subst vals ξ n = ξ (n - length vals) /\ n >= length vals.
Proof.
  intros. pose (Nat.lt_decidable n (length vals)). destruct d.
  * left. split. now apply list_subst_lt. auto.
  * right. split. apply list_subst_ge. lia. lia.
Qed.

(**
  Identity substitution is left and right identity w.r.t. composition.
*)
Lemma substcomp_id_l :
  forall ξ, idsubst >> ξ = ξ.
Proof.
  pose proof idsubst_is_id as [H0e [H0n [H0v _]]].
  unfold ">>". intros. extensionality x.
  break_match_goal; auto. rewrite H0v. auto.
Qed.

Lemma substcomp_id_r :
  forall ξ, ξ >> idsubst = ξ.
Proof.
  unfold ">>", idsubst. intros. extensionality x. auto.
Qed.

(**
  More corollaries about substitution extension and shifting.
*)
Corollary subst_list_extend : forall n ξ vals, length vals = n ->
  (list_subst vals idsubst) >> (upn n ξ) = list_subst vals ξ.
Proof.
  intros. rewrite substcomp_list_eq; auto.
  now rewrite substcomp_id_l.
Qed.

Theorem subst_extend : forall ξ v,
  (v .: idsubst) >> (up_subst ξ) = v .: ξ.
Proof.
  intros. now rewrite substcomp_scons_core, substcomp_id_l.
Qed.

Lemma subst_ren_scons : forall (ξ : Substitution) e,
  ξ 0 = inl e ->
  (e .: ξ ∘ (fun n : nat => n + 1)) = ξ.
Proof.
  intros. extensionality x. unfold "∘", scons. destruct x; auto.
  rewrite Nat.add_comm. reflexivity.
Qed.

(**
  Renaming by one is swappable with shifted substitution.
*)
Lemma ren_up_subst :
  forall ξ,
    up_subst ξ >> ren S = ren S >> ξ.
Proof.
  pose proof renaming_is_subst as [_ [_ [H0v _]]].
  intros. extensionality x; cbn.
  unfold shift. unfold ">>".
  break_match_goal; cbn.
  now rewrite <- H0v.
  reflexivity.
Qed.

(**
  Renaming everything at least by one eliminates the first element
  of an extended substitution.
*)
Lemma ren_scons :
  forall ξ f, forall x, (x .: ξ) >> ren (S ∘ f) = ξ >> ren f.
Proof.
  intros.
  extensionality k. cbn. unfold ">>", "∘".  simpl . auto.
Qed.

(**
  The previous lemma generalised to lists of substitutions.
*)
Lemma rename_upn_list_subst :
  forall m ξ vals, length vals = m ->
    (list_subst vals idsubst >> upn m ξ ) >> ren (fun n => m + n) = ξ.
Proof.
  intros.
  rewrite (subst_list_extend m ξ vals H).
  generalize dependent vals. induction m; intros; cbn.
  - replace (ren (fun n => n)) with idsubst by auto. apply length_zero_iff_nil in H.
    subst. cbn. now rewrite substcomp_id_r.
  - assert (length vals = S m) by auto.
    apply eq_sym, element_exist in H as [x0 [xs H1]]. subst. inversion H0.
    replace (list_subst (x0 :: xs) ξ) with (x0 .: list_subst xs ξ) by auto.
    specialize (IHm xs H1).
    erewrite H1.
    replace (fun n : nat => S (m + n)) with (S ∘ fun n => m + n) by reflexivity.
    now rewrite ren_scons.
Qed.

(**
  The following tactics fold substitution extension back to list substitution.
*)
Ltac fold_list_subst :=
match goal with
| |- context G [?x .: list_subst ?xs ?ξ] => replace (x .: list_subst xs ξ) with (list_subst (x :: xs) ξ) by auto
end.

Ltac fold_list_subst_hyp :=
match goal with
| [H: context G [?x .: list_subst ?xs ?ξ] |- _] => replace (x .: list_subst xs ξ) with (list_subst (x :: xs) ξ) in H by auto
end.

Lemma substcomp_assoc :
  forall ξ σ η, (ξ >> σ) >> η = ξ >> (σ >> η).
Proof.
  pose proof subst_comp as [_ [_ [H0v _]]].
  intros. extensionality x. unfold ">>".
  destruct (η x) eqn:D1; auto.
  rewrite H0v. reflexivity.
Qed.

(** This Definition describes that a ξ Substitution is subscoped with Γ Γ' numbers if, for all input number of ξ Substitution that is smaller than Γ, if the substitution returns an Exp it will be an Exp that is scoped in Γ', or if it returns a nuber it will be smaller than Γ'.
Basically, the substitution maps Γ to Γ' scoped values*)
Definition subscoped (Γ Γ' : nat) (ξ : Substitution) : Prop :=
  forall x, x < Γ -> (match ξ x with
                      | inl exp => VAL Γ' ⊢ exp
                      | inr num => num < Γ'  (** in case of identity subst *)
                      end).

Notation "'SUBSCOPE' Γ ⊢ ξ ∷ Γ'" := (subscoped Γ Γ' ξ)
         (at level 69, ξ at level 99, no associativity).

(** This Definition describes that a ξ Renaming is renscoped with Γ Γ' numbers if, for all input number of ξ Renaming that is smaller than Γ, the renaming returns a nuber that is smaller than Γ'.
This is a similar concept as the previouus one, for renamings. *)
Definition renscoped (Γ : nat) (Γ' : nat) (ξ : Renaming) : Prop :=
  forall x, x < Γ -> (ξ x) < Γ'.

Notation "'RENSCOPE' Γ ⊢ ξ ∷ Γ'" := (renscoped Γ Γ' ξ)
         (at level 69, ξ at level 99, no associativity).

(**
  Substitution definition for exceptions.
*)
Definition excsubst (ξ : Substitution) (e : Exception) : Exception :=
  match e with
  | (c, r, v) => (c, r.[ξ]ᵥ, v.[ξ]ᵥ)
  end.

Notation "s .[ σ ]ₑₓ" := (excsubst σ s)
  (at level 1, σ at level 200, left associativity,
    format "s .[ σ ]ₑₓ" ).

(**
  Substitution definition for redexes.
*)
Definition redsubst (ξ : Substitution) (r : Redex) : Redex :=
  match r with
  | RExp e => RExp e.[ξ]
  | RValSeq vl => RValSeq (map (substVal ξ) vl)
  | RExc e => RExc e.[ξ]ₑₓ
  | RBox => RBox
  end.

Notation "s .[ σ ]ᵣ" := (redsubst σ s)
  (at level 1, σ at level 200, left associativity,
    format "s .[ σ ]ᵣ" ).

(**
  Substitution composition is commutative, if one of the substitutions is a list
  substitution. However, the general substitution should be applied first on the
  list.
*)
Lemma subst_comm :
  forall l ξ,
    ξ >> list_subst l idsubst = list_subst (map (substVal ξ) l) idsubst >> upn (length l) ξ .
Proof.
  induction l; intros; simpl.
  * now rewrite substcomp_id_l.
  * rewrite substcomp_scons. rewrite <- IHl.
    now rewrite scons_substcomp.
Qed.

(**
  This function creates a list of variables from n up to m + n, i.e.,
  `[VVar n; VVar (S n); ... ; VVar (m + n)]`

  We rely on this definition in the proof that proving CIU equivalence is
  sufficient for reasoning about the equivalence of final results (values/exceptions).
  See `CIU.v: Theorem CIU_Val_compat_closed_reverse`
*)
Fixpoint varsFrom n m : list Val :=
  match m with
  | O => []
  | S m' => VVar n :: varsFrom (S n) m'
  end.

(**
  Alternative phrasing for the previous function based on `take` and `drop`.
*)
Lemma map_varsFrom : forall m n l,
  length l >= n + m ->
  map (fun x => x.[list_subst l idsubst]ᵥ) (varsFrom n m) =
  firstn m (skipn n l).
Proof.
  induction m; intros; simpl; auto.
  rewrite list_subst_lt. 2: lia. simpl.
  rewrite (IHm (S n) l ltac:(lia)).
  destruct l. simpl in H. lia.
  rewrite (skipn_S n _ VNil); auto. simpl in *; lia.
Qed.

(**
  The length of the variable list created with `varsFrom` is its second argument.
*)
Lemma varsFrom_length :
  forall m n, length (varsFrom n m) = m.
Proof.
  induction m; intros; simpl; auto.
Qed.


(**
  The following substitution maps all variables to the given value.
*)
Definition default_subst v : Substitution := fun _ => inl v.

(**
  The following three lemmas describe how a value can be obtained from a shifted
  substitution.
*)
Lemma upn_inl_eq_1 :
  forall n x v ξ, upn n ξ x = inl v -> ξ (x - n) = inl (renameVal (fun m => m - n) v).
Proof.
  induction n; intros; cbn in *. rewrite Nat.sub_0_r.
  replace (fun m => _) with (id : nat -> nat). 2: extensionality y; unfold id; lia.
  now rewrite (proj1 (proj2 (proj2 idrenaming_is_id))).
  destruct x; inv H. simpl. unfold Manipulation.shift in H1. break_match_hyp; inv H1.
  apply IHn in Heqs. rewrite Heqs. f_equal.
  rewrite (proj1 (proj2 (proj2 rename_comp))). f_equal.
Qed.

Lemma upn_inl_eq_2 :
  forall n x v ξ, ξ x = inl v -> upn n ξ (x + n) = inl (renameVal (fun m => m + n) v).
Proof.
  induction n; intros; cbn in *.
  rewrite Nat.add_0_r. replace (fun m => _) with (id : nat -> nat). 2: extensionality y; unfold id; lia. now rewrite (proj1 (proj2 (proj2 idrenaming_is_id))).
  apply IHn in H.
  rewrite <- plus_n_Sm. simpl. unfold Manipulation.shift. rewrite H. f_equal.
  rewrite (proj1 (proj2 (proj2 rename_comp))). f_equal.
  extensionality y. unfold "∘". lia.
Qed.

Lemma upn_Var : forall (Γ : nat) (ξ : Substitution) (v : nat),
    v < Γ -> upn Γ ξ v = inr v.
Proof.
  intros Γ ξ.
  induction Γ;
    intros.
  + inversion H.
  + simpl. destruct v.
    * simpl. auto.
    * simpl. unfold shift. rewrite IHΓ. 2: lia. auto.
Qed.

(**
  Lemmas about concrete substitutions. The relation between composition and
  extension.
*)
Corollary scons_subst :
  forall x ξ, x.[ξ]ᵥ .: ξ = ξ >> (x .: idsubst).
Proof. 
  intros.
  now rewrite scons_substcomp.
Qed.

Lemma list_subst_app_1 :
  forall l1 l2 ξ, list_subst (l1 ++ l2) ξ =
                  list_subst l1 (list_subst l2 ξ).
Proof.
  induction l1; intros; simpl.
  * auto.
  * now rewrite IHl1.
Qed.

Lemma list_subst_app_2 :
  forall l1 l2,
    list_subst (l1 ++ l2) idsubst = 
    list_subst l1 idsubst >> upn (length l1) (list_subst l2 idsubst).
Proof.
  induction l1; cbn; intros.
  * now rewrite substcomp_id_l.
  * unfold list_subst in *. rewrite IHl1; auto.
    now rewrite substcomp_scons_core.
Qed.

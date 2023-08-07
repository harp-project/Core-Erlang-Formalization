From CoreErlang Require Export Scoping Induction.
Import ListNotations.
(** 
  TODO: enhance renamings and substitutions. Currently, variables
  and function identifiers are handled together, however, two separate
  substitutions would work better, because it could distinguish 
  function identifiers with the same name, but different arities.
  Or, an alternative approach could be the elimination of function
  identifiers, since in the nameless representation every variable
  is different, thus function identifier with the same name, but
  different arities can be represented as disctinct dB indices.
*)

(** A Renaming will describe how we want to change the value of the indexes that represent variables.*)
Definition Renaming : Type := nat -> nat.

(** This changes a Renaming so it will give a value bigger number for every value other than 0 adn will return 0 for 0.*)
Definition upren (ρ : Renaming) : Renaming :=
  fun n =>
    match n with
    | 0 => 0
    | S n' => S (ρ n')
    end.

Fixpoint iterate {A : Type} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f (iterate f n' a)
  end.

Notation uprenn := (iterate upren).

Fixpoint rename (ρ : Renaming) (ex : Exp) : Exp :=
match ex with
 | VVal e => VVal (renameVal ρ e)
 | EExp e => EExp (renameNonVal ρ e)
end
with renameVal (ρ : Renaming) (ex : Val) : Val :=
match ex with
 | VNil               => ex
 | VLit l             => ex
 | VCons hd tl        => VCons (renameVal ρ hd) (renameVal ρ tl)
 | VTuple l           => VTuple (map (fun x => renameVal ρ x) l)
 | VMap l             => VMap (map (fun '(x,y) => (renameVal ρ x, renameVal ρ y)) l)
 | VVar n             => VVar (ρ n)
 | VFunId (n,a)       => VFunId (ρ n, a)
 | VClos ext id vl e  =>
    VClos (map (fun '(i,ls,x) => (i,ls,rename (uprenn (length ext + ls) ρ) x)) ext) id vl (rename (uprenn (length ext + vl) ρ) e)
end
with renameNonVal (ρ : Renaming) (ex : NonVal) : NonVal :=
match ex with
 | EFun vl e        => EFun vl (rename (uprenn vl ρ) e)
 | EValues el       => EValues (map (fun x => rename ρ x) el)
 | ECons   hd tl    => ECons (rename ρ hd) (rename ρ tl)
 | ETuple  l        => ETuple (map (fun x => rename ρ x) l)
 | EMap    l        => EMap (map (fun '(x,y) => (rename ρ x, rename ρ y)) l)
 | ECall   m f l    => ECall (rename ρ m) (rename ρ f) (map (fun x => rename ρ x) l)
 | EPrimOp f l      => EPrimOp f (map (fun x => rename ρ x) l)
 | EApp    e l      => EApp (rename ρ e) (map (fun x => rename ρ x) l)
 | ECase   e l      => ECase (rename ρ e)
                             (map (fun '(p,x,y) => (p, rename (uprenn(PatListScope p) ρ) x, rename (uprenn(PatListScope p) ρ) y)) l)
 | ELet    l e1 e2  => ELet l (rename ρ e1) (rename (uprenn (l) ρ) e2)
 | ESeq    e1 e2    => ESeq (rename ρ e1) (rename ρ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, rename (uprenn (length l + n) ρ) x)) l) (rename (uprenn (length l) ρ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (rename ρ e1) vl1 (rename (uprenn (vl1) ρ) e2) vl2 (rename (uprenn (vl2) ρ) e3)
 | EReceive l       => EReceive (map (fun '(p,x,y) => (p, rename (uprenn(PatListScope p) ρ) x, rename (uprenn(PatListScope p) ρ) y)) l)
end.

(** We need to have the names for the
    identity elements explicitly, because 
    of the shiftings (up, upn). Otherwise,
    `EVar 0.[idsubst] = EVar 0` and
    `EFunId (0, a).[idsubst] = EVar 0`
    could be implemented only as identity, which is clearly not one.
    *)
Definition Substitution := nat -> Val + nat.

Definition idsubst : Substitution := fun x => inr x.

Definition shift (ξ : Substitution) : Substitution := 
fun s =>
  match ξ s with
  | inl exp => inl (renameVal S exp)
  | inr num => inr (S num)
  end.

Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => shift ξ x'
    end.

Notation upn := (iterate up_subst).


Fixpoint subst (ξ : Substitution) (base : Exp) : Exp :=
match base with
  | VVal v => VVal (substVal ξ v)
  | EExp e => EExp (substNonVal ξ e)
end
with substVal (ξ : Substitution) (ex : Val) : Val :=
match ex with
 | VNil         => ex
 | VLit l       => ex
 | VCons hd tl  => VCons (substVal ξ hd) (substVal ξ tl)
 | VTuple l     => VTuple (map (fun x => substVal ξ x) l)
 | VMap l       => VMap (map (fun '(x,y) => (substVal ξ x, substVal ξ y)) l)
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
end
with substNonVal (ξ : Substitution) (ex : NonVal) : NonVal :=
match ex with
 | EFun vl e        => EFun vl (subst (upn vl ξ) e)
 | EValues el       => EValues (map (fun x => subst ξ x) el)
 | ECons   hd tl    => ECons (subst ξ hd) (subst ξ tl)
 | ETuple  l        => ETuple (map (fun x => subst ξ x) l)
 | EMap    l        => EMap (map (fun '(x,y) => (subst ξ x, subst ξ y)) l)
 | ECall   m f l    => ECall (subst ξ m) (subst ξ f) (map (fun x => subst ξ x) l)
 | EPrimOp f l      => EPrimOp f (map (fun x => subst ξ x) l)
 | EApp    e l      => EApp (subst ξ e) (map (fun x => subst ξ x) l)
 | ECase   e l      => ECase (subst ξ e) (map (fun '(p,x,y) => (p, subst (upn(PatListScope p) ξ) x, subst (upn(PatListScope p) ξ) y)) l)
 | ELet    l e1 e2  => ELet l (subst ξ e1) (subst (upn (l) ξ) e2)
 | ESeq    e1 e2    => ESeq (subst ξ e1) (subst ξ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, subst (upn (length l + n) ξ) x)) l) (subst (upn (length l) ξ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (subst ξ e1) vl1 (subst (upn (vl1) ξ) e2) vl2 (subst (upn (vl2) ξ) e3)
 | EReceive l       => EReceive (map (fun '(p,x,y) => (p, subst (upn(PatListScope p) ξ) x, subst (upn(PatListScope p) ξ) y)) l)
end.

Definition scons {X : Type} (s : X) (σ : nat -> X) (x : nat) : X :=
  match x with 
  | S y => σ y
  | _ => s
  end.
Notation "s .: σ" := (scons (inl s) σ) (at level 55, σ at level 56, right associativity).
Notation "s .:: σ" := (scons s σ) (at level 55, σ at level 56, right associativity).
Notation "s .[ σ ]" := (subst σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]" ).
Notation "s .[ t /]" := (subst (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]").
Notation "s .[ t1 , t2 , .. , tn /]" :=
  (subst (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").
   
(* Val *)
Notation "s .[ σ ]ᵥ" := (substVal σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]ᵥ" ).
Notation "s .[ t /]ᵥ" := (substVal (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]ᵥ").
Notation "s .[ t1 , t2 , .. , tn /]ᵥ" :=
  (substVal (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 2, left associativity).
  (* format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").*)

(* NonVal *)
Notation "s .[ σ ]ₑ" := (substNonVal σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]ₑ" ).
Notation "s .[ t /]ₑ" := (substNonVal (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]ₑ").
Notation "s .[ t1 , t2 , .. , tn /]ₑ" :=
  (substNonVal (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 2, left associativity).
  (*format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'ₑ").*)

(* custom composition notation: *)
Notation "f >>> g" := (compose g f)
  (at level 56, left associativity).

Definition list_subst (l : list Val) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.

(** Examples *)

Definition inc (n : Z) := ELet 1 (`VLit n) (ECall (`VLit "erlang"%string) (`VLit "+"%string) [`VVar 0; `VLit 1%Z]).

(** Tests: *)

Goal (inc 1).[VLit 0%Z/] = inc 1. Proof. reflexivity. Qed.
Goal (EApp (`VVar 0) [`VVar 0; °ELet 1 (`VVar 0) (`VVar 0)]).[VLit 0%Z/]
  = (EApp (`VLit 0%Z) [`VLit 0%Z; °ELet 1 (`VLit 0%Z) (`VVar 0)]). 
Proof. cbn. reflexivity. Qed.

Compute (VLit (Integer 0) .: VLit (Integer 0) .: idsubst) 3.

Definition substcomp (ξ η : Substitution) : Substitution :=
  fun x => (* composition (substi ξ) η*)
    match ξ x with
    | inl exp => inl (substVal η exp)
    | inr n   => η n
    end.

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

Definition ren (ρ : Renaming) : Substitution :=
  fun x => inr (ρ x).

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

Theorem upren_S :
  forall n ρ, uprenn n (upren ρ) = uprenn (S n) ρ.
Proof.
  induction n.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.

Theorem up_subst_S :
  forall n ρ, upn n (up_subst ρ) = upn (S n) ρ.
Proof.
  induction n.
  - intros. simpl. reflexivity.
  - intros. simpl. rewrite IHn. reflexivity.
Qed.

Theorem renaming_is_subst2 : 
     (forall e ρ, rename ρ e = e.[ren ρ])
  /\ (forall e ρ, renameNonVal ρ e = e.[ren ρ]ₑ)
  /\ (forall e ρ, renameVal ρ e = e.[ren ρ]ᵥ).
Proof.
  eapply Exp_ind with
    (QV := fun l => forall ρ, Forall (fun ve => renameVal ρ ve = ve.[ren ρ]ᵥ) l)
    (Q := fun l => forall ρ, Forall (fun e => rename ρ e = e.[ren ρ]) l)
    (R := fun l => forall ρ, Forall (fun (x : Exp * Exp) =>
      (let (e1, e2) := x in (rename ρ e1, rename ρ e2)) = (let (e1, e2) := x in (e1.[ren ρ], e2.[ren ρ]))) l)
    (RV := fun l => forall ρ, Forall (fun (x : Val * Val) =>
      (let (e1, e2) := x in (renameVal ρ e1, renameVal ρ e2)) = (let (e1, e2) := x in (e1.[ren ρ]ᵥ, e2.[ren ρ]ᵥ))) l)
    (W := fun l => forall ρ, Forall (fun (x : list Pat * Exp * Exp) =>
      (let '(pl, e1, e2) := x in (pl, rename (uprenn (PatListScope pl) ρ) e1,
                                      rename (uprenn (PatListScope pl) ρ) e2)) =
      (let '(pl, e1, e2) := x in (pl, e1.[upn (PatListScope pl) (ren ρ)],
                                      e2.[upn (PatListScope pl) (ren ρ)]))) l)
    (Z := fun l => forall ρ, Forall (fun x : nat * Exp =>
   (let '(n, x0) := x in (n, rename (uprenn (Datatypes.length l + n) ρ) x0)) =
   (fun '(n, x0) => (n, x0.[upn (Datatypes.length l + n) (ren ρ)])) x) l)
   (VV := fun l => forall ρ, Forall
  (fun x : nat * nat * Exp =>
   (let '(i, ls, x0) := x in (i, ls, rename (uprenn (Datatypes.length l + ls) ρ) x0)) =
   (let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length l + ls) (ren ρ)]))) l)
  ; intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * reflexivity.
  * reflexivity.
  * simpl. rewrite H, H0. reflexivity.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  (* * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto. *)
  * reflexivity.
  * reflexivity.
  * simpl. rewrite H0. rewrite renn_up.
    erewrite map_ext_Forall with (g := (fun '(i, l, x) => (i, l, x.[upn (Datatypes.length ext + l) (ren ρ)]))).
    - reflexivity.
    - apply H.
  (* NonVal *)
  * simpl. rewrite H. rewrite renn_up. reflexivity.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. rewrite H, H0. reflexivity.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall, H, H0. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. rewrite H. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. rewrite H. erewrite map_ext_Forall. reflexivity. simpl. apply H0.
  * simpl. rewrite H, H0. rewrite renn_up. reflexivity.
  * simpl. rewrite H, H0. reflexivity.
  * simpl. rewrite H. rewrite renn_up. erewrite map_ext_Forall. reflexivity. apply H0. 
    (* revert ρ. exact H0. *)
  * simpl. rewrite H, H0, H1. do 2 rewrite renn_up. reflexivity.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. apply H.
  (* Lists *)
  * apply Forall_nil.
  * apply Forall_cons; auto.
  * constructor.
  * constructor; auto.
  * constructor.
  * constructor; auto. rewrite H, H0. reflexivity.
  * constructor.
  * constructor; auto. rewrite H, H0. reflexivity.
  * constructor.
  (** constructor; auto. rewrite H. rewrite renn_up. reflexivity. rewrite ren_up.  exact H0.*)
  * constructor.
    - rewrite H. rewrite renn_up. reflexivity.
    - pose proof (H0 (upren ρ)). simpl.
      eapply Forall_impl in H1.
      + exact H1.
      + intros. destruct a. destruct p. rewrite upren_S in H2. simpl in H2. rewrite ren_up in H2. rewrite up_subst_S in H2. simpl in H2. apply H2.
  * constructor.
  * constructor; auto. rewrite H, H0. rewrite renn_up. reflexivity.
  * constructor.
  * constructor.
    - rewrite H. rewrite renn_up. reflexivity.
    - pose proof (H0 (upren ρ)). simpl.
      eapply Forall_impl in H1.
      + exact H1.
      + intros. destruct a. rewrite upren_S in H2. simpl in H2. rewrite ren_up in H2. rewrite up_subst_S in H2. simpl in H2. apply H2.
Qed.

(*
Theorem up_subst_upn_ren :
  forall n ρ e, e.[up_subst (upn n (ren ρ))] = e.[upn n (ren ρ)].
Proof.
  induction n.
  * intros. simpl. simpl.
Qed.
*)

Theorem renaming_is_subst : 
     (forall e ρ, rename ρ e = e.[ren ρ])
  /\ (forall e ρ, renameNonVal ρ e = e.[ren ρ]ₑ)
  /\ (forall e ρ, renameVal ρ e = e.[ren ρ]ᵥ).
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
     (p, rename (uprenn (PatListScope p) ρ) x0,
     rename (uprenn (PatListScope p) ρ) y)) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (PatListScope p) (ren ρ)],
     y.[upn (PatListScope p) (ren ρ)]))) l)
  (Z  := fun l => forall ρ, Forall
  (fun x : nat * Exp =>
   (let '(n, x0) := x in (n, rename (uprenn (Datatypes.length l + n) ρ) x0)) =
   (let '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) (ren ρ)]))) l)
  (VV := fun l => forall ρ, Forall
  (fun x : nat * nat * Exp =>
   (let '(i, ls, x0) := x in (i, ls, rename (uprenn (Datatypes.length l + ls) ρ) x0)) =
   (let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length l + ls) (ren ρ)]))) l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Val => x.[ren ρ]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ren ρ]ᵥ, y.[ren ρ]ᵥ))).
    - reflexivity.
    - apply H.
  (* * simpl. erewrite map_ext_Forall with (g := (fun x : Val => x.[ren ρ]ᵥ)).
    - reflexivity.
    - apply H. *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext + ls) (ren ρ)]))).
    - rewrite H0. rewrite renn_up. reflexivity.
    - apply H.
  (* NonVal *)
  * simpl. rewrite H. rewrite renn_up. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Exp => x.[ren ρ])).
    - reflexivity.
    - apply H.
  * simpl. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ren ρ], y.[ren ρ]))).
    - reflexivity.
    - apply H.
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
      (p, x.[upn (PatListScope p) (ren ρ)],
      y.[upn (PatListScope p) (ren ρ)]))).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite renn_up. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (ren ρ)]))).
    - rewrite H. rewrite renn_up. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite H1. do 2 rewrite renn_up. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (PatListScope p) (ren ρ)],
      y.[upn (PatListScope p) (ren ρ)]))).
    - reflexivity.
    - apply H.
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
    - rewrite H. rewrite H0. rewrite renn_up. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite renn_up. reflexivity.
    - pose proof (H0 (upren ρ)). simpl.
      eapply Forall_impl in H1.
      + exact H1.
      + intros. destruct a. rewrite upren_S in H2. simpl in H2. rewrite ren_up in H2. rewrite up_subst_S in H2. simpl in H2. apply H2.
Qed.

Theorem idrenaming_up : upren id = id.
Proof.
  extensionality x. destruct x; auto.
Qed.

Corollary idrenaming_upn n : uprenn n id = id.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idrenaming_up. auto.
Qed.

Theorem idrenaming_is_id : 
     (forall e, rename id e = e)
  /\ (forall e, renameNonVal id e = e)
  /\ (forall e, renameVal id e = e).
Proof.
  eapply Exp_ind with 
  (Q := fun l => Forall (fun x : Exp => rename id x = id x) l)
  (QV := fun l => Forall (fun ve => renameVal id ve = ve) l)
  (R := fun l => Forall (fun x : Exp * Exp => (let '(x0, y) := x in (rename id x0, rename id y)) = id x) l)
  (RV := fun l => Forall (fun (x : Val * Val) => (let (e1,e2) := x in (renameVal id e1, renameVal id e2)) = x) l)
  (W := fun l => Forall (fun x : list Pat * Exp * Exp => (let '(p, x0, y) := x in (p, rename (uprenn (PatListScope p) id) x0, rename (uprenn (PatListScope p) id) y)) = id x) l)
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
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity. 
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall.
    - rewrite map_id. reflexivity.
    - exact H.
  (* * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H. *)
  * simpl. auto.
  * destruct n; simpl. auto.
  * simpl. erewrite map_ext_Forall with (g := Datatypes.id).
    - rewrite map_id. rewrite idrenaming_upn. rewrite H0. reflexivity.
    - apply H.
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
    - exact H.
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
  * simpl. rewrite idrenaming_upn. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. rewrite idrenaming_upn. rewrite H. reflexivity.
    - exact H0.
  * simpl. do 2 rewrite idrenaming_upn. rewrite H. rewrite H0. rewrite H1. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  (* List *)
  * apply Forall_nil.
  * apply Forall_cons; auto.
  * constructor.
  * constructor; auto.
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
    - rewrite idrenaming_upn. rewrite H. rewrite H0. reflexivity.
    - exact H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite idrenaming_upn. rewrite idrenaming_up. rewrite H. reflexivity.
    - simpl. eapply Forall_impl in H0.
      + exact H0.
      + destruct a. rewrite idrenaming_upn. rewrite idrenaming_up. auto.
Qed.

Theorem idsubst_up : up_subst idsubst = idsubst.
Proof.
  extensionality x. unfold up_subst. destruct x; auto.
Qed.

Corollary idsubst_upn n : upn n idsubst = idsubst.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idsubst_up. auto.
Qed.


Theorem idsubst_is_id : 
     (forall e, e.[idsubst] = e)
  /\ (forall e, e.[idsubst]ₑ = e)
  /\ (forall e, e.[idsubst]ᵥ = e).
Proof.
  eapply Exp_ind with
  (Q := fun l => Forall (fun x : Exp => x.[idsubst] = id x) l)
  (QV := fun l => Forall (fun x : Val => x.[idsubst]ᵥ = id x) l)
  (R := fun l => Forall (fun x : Exp * Exp => (let '(x0, y) := x in (x0.[idsubst], y.[idsubst])) = id x) l)
  (RV := fun l => Forall (fun x : Val * Val => (let '(x0, y) := x in (x0.[idsubst]ᵥ, y.[idsubst]ᵥ)) = id x) l)
  (W := fun l => Forall (fun x : list Pat * Exp * Exp => (let '(p, x0, y) := x in (p, x0.[upn (PatListScope p) idsubst], y.[upn (PatListScope p) idsubst])) = id x) l)
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
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - exact H.
  * simpl. reflexivity.
  * simpl. destruct n. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := Datatypes.id).
    - rewrite map_id. rewrite idsubst_upn. rewrite H0. reflexivity.
    - apply H.
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
    - exact H.
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
    - rewrite idsubst_upn. rewrite H. rewrite H0. auto.
    - exact H1.
   * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite idsubst_upn. rewrite idsubst_up. rewrite H. reflexivity.
    - simpl. eapply Forall_impl in H0.
      + exact H0.
      + destruct a. rewrite idsubst_upn. rewrite idsubst_up. auto.
Qed.

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

Lemma renaming_fold m :
  (fun n => m + n) = iterate S m.
Proof.
  extensionality x. induction m; cbn; auto.
Qed.

Lemma upren_subst_up : forall σ ξ,
  upren σ >>> up_subst ξ = up_subst (σ >>> ξ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>>".
  destruct x; auto.
Qed.

Corollary uprenn_subst_upn n : forall σ ξ,
  uprenn n σ >>> upn n ξ = upn n (σ >>> ξ).
Proof.
  induction n; intros; auto.
  cbn. rewrite <- IHn, upren_subst_up. auto.
Qed.

Lemma subst_ren   :
     ( forall e (σ : Renaming) (ξ : Substitution), e.[ren σ].[ξ]   = e.[σ >>> ξ] )
  /\ ( forall e (σ : Renaming) (ξ : Substitution), e.[ren σ]ₑ.[ξ]ₑ = e.[σ >>> ξ]ₑ )
  /\ ( forall e (σ : Renaming) (ξ : Substitution), e.[ren σ]ᵥ.[ξ]ᵥ = e.[σ >>> ξ]ᵥ ).
Proof.
  (* revert ξ σ. *)
  eapply Exp_ind with
  (Q  := fun l => forall σ ξ, Forall (fun x : Exp => x.[ren σ].[ξ] = x.[σ >>> ξ]) l)
  (QV := fun l => forall σ ξ, Forall (fun x : Val => x.[ren σ]ᵥ.[ξ]ᵥ = x.[σ >>> ξ]ᵥ) l)
  (R  := fun l => forall σ ξ, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ren σ], y.[ren σ]) in
     (x0.[ξ], y.[ξ])) =
   (let '(x0, y) := x in (x0.[σ >>> ξ], y.[σ >>> ξ]))) l)
  (RV := fun l => forall σ ξ, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ren σ]ᵥ, y.[ren σ]ᵥ) in
     (x0.[ξ]ᵥ, y.[ξ]ᵥ)) =
   (let '(x0, y) := x in (x0.[σ >>> ξ]ᵥ, y.[σ >>> ξ]ᵥ))) l)
   (W  := fun l => forall σ ξ, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, x0.[upn (PatListScope p) (ren σ)],
      y.[upn (PatListScope p) (ren σ)]) in
     (p, x0.[upn (PatListScope p) ξ],
     y.[upn (PatListScope p) ξ])) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (PatListScope p) (σ >>> ξ)],
     y.[upn (PatListScope p) (σ >>> ξ)]))) l)
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
     (n, x0.[upn (Datatypes.length l + n) (σ >>> ξ)]))) l)
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
     (i, ls, x0.[upn (Datatypes.length l + ls) (σ >>> ξ)]))) l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g:= (fun x : Val => x.[σ >>> ξ]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[σ >>> ξ]ᵥ, y.[σ >>> ξ]ᵥ))).
    - reflexivity.
    - apply H.
  (* * simpl. rewrite map_map. erewrite map_ext_Forall with (g:= (fun x : Val => x.[σ >>> ξ]ᵥ)).
    - reflexivity.
    - apply H. *)
  * auto.
  * auto. destruct n. auto.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(i, ls, x) =>
      (i, ls, x.[upn (Datatypes.length ext + ls) (σ >>> ξ)]))).
    - simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H0. rewrite map_length. reflexivity.
    - apply H.
  (* NonVal *)
  * simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[σ >>> ξ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[σ >>> ξ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[σ >>> ξ], y.[σ >>> ξ]))).
    - reflexivity.
    - apply H.
  * simpl. rewrite H, H0. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[σ >>> ξ])).
    - reflexivity.
    - apply H1.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[σ >>> ξ])).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Exp => x.[σ >>> ξ])).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (PatListScope p) (σ >>> ξ)],
      y.[upn (PatListScope p) (σ >>> ξ)]))).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (σ >>> ξ)]))).
    - rewrite <- renn_up. rewrite H. rewrite <- uprenn_subst_upn. rewrite map_length. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H0.
    rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H1. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (PatListScope p) (σ >>> ξ)],
      y.[upn (PatListScope p) (σ >>> ξ)]))).
    - reflexivity.
    - apply H.
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
    - simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite <- ren_up. rewrite <- upren_subst_up. rewrite H. rewrite map_length.  reflexivity.
    - simpl. specialize (H0 (upren σ) (up_subst ξ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. rewrite map_length. rewrite map_length. intros. rewrite ren_up in H1. rewrite up_subst_S in H1. rewrite up_subst_S in H1. simpl in H1. f_equal. inversion H1. rewrite upren_subst_up in H3. rewrite up_subst_S in H3. simpl in H3. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite <- ren_up. rewrite <- upren_subst_up. rewrite H. rewrite map_length.  reflexivity.
    - simpl. specialize (H0 (upren σ) (up_subst ξ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. rewrite map_length. rewrite map_length. intros. rewrite ren_up in H1. rewrite up_subst_S in H1. rewrite up_subst_S in H1. simpl in H1. f_equal. inversion H1. rewrite upren_subst_up in H3. rewrite up_subst_S in H3. simpl in H3. exact H3.
Qed.

Notation "σ >> ξ" := (substcomp σ ξ) (at level 56, left associativity).

Theorem upren_comp : forall σ ρ,
  upren σ >>> upren ρ = upren (σ >>> ρ).
Proof.
  intros. unfold upren, ">>>". extensionality n. destruct n; auto.
Qed.

Corollary uprenn_comp : forall n σ ρ,
  uprenn n σ >>> uprenn n ρ = uprenn n (σ >>> ρ).
Proof.
  induction n; intros; auto. simpl. rewrite upren_comp, IHn. auto.
Qed.

Theorem upren_uprenn : forall n σ,
  upren (uprenn n σ) = uprenn n (upren σ).
Proof.
  intros. induction n.
  * simpl. reflexivity.
  * simpl. rewrite IHn. reflexivity.
Qed.

Theorem rename_up : 
     (forall e n σ ρ, rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e)
  /\ (forall e n σ ρ, renameNonVal (uprenn n σ) (renameNonVal (uprenn n ρ) e) = renameNonVal (uprenn n (ρ >>> σ)) e)
  /\ (forall e n σ ρ, renameVal (uprenn n σ) (renameVal (uprenn n ρ) e) = renameVal (uprenn n (ρ >>> σ)) e).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall n σ ρ, Forall (fun x : Exp =>
   rename (uprenn n σ) (rename (uprenn n ρ) x) =
   rename (uprenn n (ρ >>> σ)) x) l)
  (QV := fun l => forall n σ ρ, Forall (fun x : Val =>
   renameVal (uprenn n σ) (renameVal (uprenn n ρ) x) = renameVal (uprenn n (ρ >>> σ)) x) l)
  (R  := fun l => forall n σ ρ, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) :=
     let
     '(x0, y) := x in (rename (uprenn n ρ) x0, rename (uprenn n ρ) y) in
     (rename (uprenn n σ) x0, rename (uprenn n σ) y)) =
   (let
    '(x0, y) := x in
     (rename (uprenn n (ρ >>> σ)) x0, rename (uprenn n (ρ >>> σ)) y))) l)
  (RV := fun l => forall n σ ρ, Forall (fun x : Val * Val =>
   (let
    '(x0, y) :=
     let
     '(x0, y) := x in
      (renameVal (uprenn n ρ) x0, renameVal (uprenn n ρ) y) in
     (renameVal (uprenn n σ) x0, renameVal (uprenn n σ) y)) =
   (let
    '(x0, y) := x in
     (renameVal (uprenn n (ρ >>> σ)) x0,
     renameVal (uprenn n (ρ >>> σ)) y))) l)
  (W  := fun l => forall n σ ρ, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, rename (uprenn (PatListScope p) (uprenn n ρ)) x0,
      rename (uprenn (PatListScope p) (uprenn n ρ)) y) in
     (p, rename (uprenn (PatListScope p) (uprenn n σ)) x0,
     rename (uprenn (PatListScope p) (uprenn n σ)) y)) =
   (let
    '(p, x0, y) := x in
     (p, rename (uprenn (PatListScope p) (uprenn n (ρ >>> σ))) x0,
     rename (uprenn (PatListScope p) (uprenn n (ρ >>> σ))) y))) l)
  (Z  := fun l => forall n σ ρ, Forall
  (fun x : nat * Exp =>
   (let
    '(n0, x0) :=
     let
     '(n0, x0) := x in
      (n0,
      rename (uprenn (Datatypes.length l + n0) (uprenn n ρ)) x0) in
     (n0,
     rename
       (uprenn
          (Datatypes.length
             (map
                (fun '(n1, x1) =>
                 (n1,
                 rename
                   (uprenn (Datatypes.length l + n1) (uprenn n ρ))
                   x1)) l) + n0) (uprenn n σ)) x0)) =
   (let
    '(n0, x0) := x in
     (n0,
     rename (uprenn (Datatypes.length l + n0) (uprenn n (ρ >>> σ)))
       x0))) l)
  (VV := fun l => forall n σ ρ,Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) :=
     let
     '(i, ls, x0) := x in
      (i, ls,
      rename (uprenn (Datatypes.length l + ls) (uprenn n ρ)) x0)
     in
     (i, ls,
     rename (uprenn (Datatypes.length l + ls) (uprenn n σ)) x0)) =
   (let
    '(i, ls, x0) := x in
     (i, ls,
     rename
       (uprenn (Datatypes.length l + ls) (uprenn n (ρ >>> σ))) x0)))
  l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite <- uprenn_comp. rewrite H. rewrite <- uprenn_comp. rewrite H0. 
  rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Val => renameVal (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(x, y) =>
      (renameVal (uprenn n (ρ >>> σ)) x,
      renameVal (uprenn n (ρ >>> σ)) y))).
    - reflexivity.
    - apply H.
  (* * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Val => renameVal (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply H. *)
  * simpl. rewrite <- uprenn_comp. auto.
  * simpl. rewrite <- uprenn_comp. destruct n. auto.
  * simpl. rewrite map_map. rewrite map_length.
    erewrite map_ext_Forall with (g := (fun '(i, ls, x) => (i, ls, rename (uprenn (Datatypes.length ext + ls) (uprenn n (ρ >>> σ))) x))).
    - rewrite H0. rewrite uprenn_comp. reflexivity.
    - apply H.
  (* NonVal *)
  * simpl. repeat fold_upn. rewrite <- uprenn_comp. rewrite <- uprenn_comp.  rewrite H. rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(x, y) =>
      (rename (uprenn n (ρ >>> σ)) x, rename (uprenn n (ρ >>> σ)) y))).
    - reflexivity.
    - apply H.
  * simpl. rewrite H, H0. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply H1.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (uprenn n (ρ >>> σ)) x)).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, rename (uprenn (PatListScope p) (uprenn n (ρ >>> σ))) x,
      rename (uprenn (PatListScope p) (uprenn n (ρ >>> σ))) y))).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(n0, x) =>
      (n0,
      rename (uprenn (Datatypes.length l + n0) (uprenn n (ρ >>> σ)))
        x))).
    - rewrite map_length. rewrite H. rewrite <- uprenn_comp. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite H1. rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, rename (uprenn (PatListScope p) (uprenn n (ρ >>> σ))) x,
      rename (uprenn (PatListScope p) (uprenn n (ρ >>> σ))) y))).
    - reflexivity.
    - apply H.
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
    - simpl. f_equal. do 6 rewrite upren_uprenn. rewrite H.
      rewrite uprenn_comp. rewrite upren_comp. reflexivity.
    - simpl. specialize (H0 (n0) (upren σ) (upren ρ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. destruct p. intros. f_equal. inversion H1.
        do 6 rewrite upren_uprenn. rewrite <- upren_comp. exact H3.
  * apply Forall_nil.
  * apply Forall_cons.
    - rewrite H. rewrite H0. do 3 rewrite <- uprenn_comp. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - simpl. rewrite map_length. f_equal. do 6 rewrite upren_uprenn. rewrite H.
      rewrite uprenn_comp. rewrite upren_comp. reflexivity.
    - simpl. specialize (H0 (n0) (upren σ) (upren ρ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. do 2 rewrite map_length. intros. f_equal. inversion H1.
        do 6 rewrite upren_uprenn. rewrite <- upren_comp. exact H3.
Qed.

Theorem rename_comp :
     (forall e σ ρ, rename σ (rename ρ e) = rename (ρ >>> σ) e)
  /\ (forall e σ ρ, renameNonVal σ (renameNonVal ρ e) = renameNonVal (ρ >>> σ) e)
  /\ (forall e σ ρ, renameVal σ (renameVal ρ e) = renameVal (ρ >>> σ) e).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall σ ρ, Forall (fun x : Exp => rename σ (rename ρ x) = rename (ρ >>> σ) x) l)
  (QV := fun l => forall σ ρ, Forall (fun x : Val =>
   renameVal σ (renameVal ρ x) = renameVal (ρ >>> σ) x) l)
  (R  := fun l => forall σ ρ, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (rename ρ x0, rename ρ y) in
     (rename σ x0, rename σ y)) =
   (let '(x0, y) := x in (rename (ρ >>> σ) x0, rename (ρ >>> σ) y))) l)
  (RV := fun l => forall σ ρ, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (renameVal ρ x0, renameVal ρ y)
     in (renameVal σ x0, renameVal σ y)) =
   (let
    '(x0, y) := x in (renameVal (ρ >>> σ) x0, renameVal (ρ >>> σ) y))) l)
  (W  := fun l => forall σ ρ, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, rename (uprenn (PatListScope p) ρ) x0,
      rename (uprenn (PatListScope p) ρ) y) in
     (p, rename (uprenn (PatListScope p) σ) x0,
     rename (uprenn (PatListScope p) σ) y)) =
   (let
    '(p, x0, y) := x in
     (p, rename (uprenn (PatListScope p) (ρ >>> σ)) x0,
     rename (uprenn (PatListScope p) (ρ >>> σ)) y))) l)
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
     (n, rename (uprenn (Datatypes.length l + n) (ρ >>> σ)) x0))) l)
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
     rename (uprenn (Datatypes.length l + ls) (ρ >>> σ)) x0))) l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Val => renameVal (ρ >>> σ) x)).
    - reflexivity. 
    - apply H.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(x, y) => (renameVal (ρ >>> σ) x, renameVal (ρ >>> σ) y))).
    - reflexivity.
    - apply H.
  (* * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Val => renameVal (ρ >>> σ) x)).
    - reflexivity.
    - apply H. *)
  * simpl. auto.
  * simpl. destruct n. auto.
  * simpl. rewrite map_map. rewrite map_length. erewrite map_ext_Forall with (g := (fun '(i, ls, x) =>
      (i, ls,
      rename (uprenn (Datatypes.length ext + ls) (ρ >>> σ)) x))).
    - simpl. rewrite H0. rewrite <- uprenn_comp. reflexivity.
    - apply H.
  (* NonVal *)
  * simpl. rewrite <- uprenn_comp. rewrite H. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(x, y) => (rename (ρ >>> σ) x, rename (ρ >>> σ) y))).
    - reflexivity.
    - apply H.
  * simpl. rewrite H, H0. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply H1.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun x : Exp => rename (ρ >>> σ) x)).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, rename (uprenn (PatListScope p) (ρ >>> σ)) x,
      rename (uprenn (PatListScope p) (ρ >>> σ)) y))).
    - rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite <- uprenn_comp. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map. 
  erewrite map_ext_Forall with (g := (fun '(n, x) =>
      (n, rename (uprenn (Datatypes.length l + n) (ρ >>> σ)) x))).
    - rewrite <- uprenn_comp. rewrite map_length. rewrite H. reflexivity.
    - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite H1. do 2 rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite map_map. 
    erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, rename (uprenn (PatListScope p) (ρ >>> σ)) x,
      rename (uprenn (PatListScope p) (ρ >>> σ)) y))).
    - reflexivity.
    - apply H.
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
    - rewrite H. rewrite H0. rewrite <- uprenn_comp. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite map_length. rewrite H. rewrite uprenn_comp. reflexivity.
    - simpl. specialize (H0 (upren σ) (upren ρ)).
    eapply Forall_impl in H0.
      + exact H0.
      + do 2 rewrite map_length. destruct a. intros. f_equal. inversion H1.
        do 3 rewrite upren_uprenn. rewrite <- upren_comp. exact H3.
Qed.


Lemma subst_up_upren :
  forall σ ξ, up_subst ξ >> ren (upren σ) = up_subst (ξ >> ren σ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>", shift.
  destruct x; auto. destruct (ξ x) eqn:P; auto.
  (* pose proof renaming_is_subst. destruct a. destruct H0. *)
  pose proof renaming_is_subst as [_ [_ H1]].
  rewrite <- H1. rewrite <- H1.
  f_equiv.
  (*apply functional_extensionality.*)
  replace (fun n : nat => match n with
                       | 0 => 0
                       | S n' => S (σ n')
                       end) with (upren σ) by auto.
  pose proof rename_comp as [_ [_ H2]].
  rewrite H2. rewrite H2. f_equiv.
Qed.

Lemma subst_upn_uprenn : forall n σ ξ,
  upn n ξ >> ren (uprenn n σ) = upn n (ξ >> ren σ).
Proof.
  induction n; intros; auto. simpl.
  rewrite subst_up_upren, IHn. auto.
Qed.

Lemma ren_subst :
     (forall e ξ σ, e.[ξ].[ren σ] = e.[ξ >> ren σ])
  /\ (forall e ξ σ, e.[ξ]ₑ.[ren σ]ₑ = e.[ξ >> ren σ]ₑ)
  /\ (forall e ξ σ, e.[ξ]ᵥ.[ren σ]ᵥ = e.[ξ >> ren σ]ᵥ).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall ξ σ, Forall (fun x : Exp => x.[ξ].[ren σ] = x.[ξ >> ren σ]) l)
  (QV := fun l => forall ξ σ, Forall (fun x : Val => x.[ξ]ᵥ.[ren σ]ᵥ = x.[ξ >> ren σ]ᵥ) l)
  (R  := fun l => forall ξ σ, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ], y.[ξ]) in
     (x0.[ren σ], y.[ren σ])) =
   (let '(x0, y) := x in (x0.[ξ >> ren σ], y.[ξ >> ren σ]))) l)
  (RV := fun l => forall ξ σ, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ) in
     (x0.[ren σ]ᵥ, y.[ren σ]ᵥ)) =
   (let '(x0, y) := x in (x0.[ξ >> ren σ]ᵥ, y.[ξ >> ren σ]ᵥ))) l)
   (W  := fun l => forall ξ σ, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, x0.[upn (PatListScope p) ξ],
      y.[upn (PatListScope p) ξ]) in
     (p, x0.[upn (PatListScope p) (ren σ)],
     y.[upn (PatListScope p) (ren σ)])) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (PatListScope p) (ξ >> ren σ)],
     y.[upn (PatListScope p) (ξ >> ren σ)]))) l)
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
     (n, x0.[upn (Datatypes.length l + n) (ξ >> ren σ)]))) l)
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
     x0.[upn (Datatypes.length l + ls) (ξ >> ren σ)])))
  l)
  ;
  intros.
  (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Val => x.[ξ >> ren σ]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> ren σ]ᵥ, y.[ξ >> ren σ]ᵥ))).
    - reflexivity.
    - apply H.
  (* * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Val => x.[ξ >> ren σ]ᵥ)).
    - reflexivity.
    - apply H. *)
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * simpl. unfold ">>", ren. destruct n. destruct (ξ n) eqn:P; auto.
  * simpl. rewrite map_map. rewrite map_length. erewrite map_ext_Forall with (g := (fun '(i, ls, x) =>
      (i, ls, x.[upn (Datatypes.length ext + ls) (ξ >> ren σ)]))).
    - simpl. f_equal. rewrite <- subst_upn_uprenn. rewrite <- H0. rewrite <- renn_up. reflexivity.
    - apply H.
  (* NonVal *)
  * simpl. rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite H. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> ren σ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> ren σ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> ren σ], y.[ξ >> ren σ]))).
      - reflexivity.
      - apply H.
  * simpl. rewrite H, H0. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> ren σ])).
      - reflexivity.
      - apply H1.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> ren σ])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> ren σ])).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (PatListScope p) (ξ >> ren σ)],
      y.[upn (PatListScope p) (ξ >> ren σ)]))).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite H. rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite H0. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(n, x) =>
      (n, x.[upn (Datatypes.length l + n) (ξ >> ren σ)]))).
      - rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite H. rewrite map_length. reflexivity.
      - apply H0.
  * simpl. rewrite H. do 2 rewrite <- renn_up. do 2 rewrite <- subst_upn_uprenn.
    rewrite H0. rewrite H1. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (PatListScope p) (ξ >> ren σ)],
      y.[upn (PatListScope p) (ξ >> ren σ)]))).
      - reflexivity.
      - apply H.
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
    - rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite H. rewrite H0. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite map_length. rewrite <- subst_upn_uprenn. rewrite <- renn_up.
      rewrite H. reflexivity.
    - simpl. specialize (H0 (up_subst ξ) (upren σ)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. intros. f_equal. rewrite map_length. inversion H1.
        rewrite ren_up in H3 at 1. rewrite up_subst_S in H3. simpl in H3.
        rewrite up_subst_S in H3. simpl in H3. rewrite subst_up_upren in H3.
        rewrite up_subst_S in H3. simpl in H3.
        rewrite map_length in H3. exact H3.
Qed.

Lemma up_comp ξ η :
  up_subst ξ >> up_subst η = up_subst (ξ >> η).
Proof.
  extensionality x.
  unfold ">>". cbn. unfold up_subst, shift. destruct x; auto.
  destruct (ξ x) eqn:P; auto.
  pose proof renaming_is_subst as [_ [_ H1]].
  rewrite H1. rewrite H1.
  pose proof ren_subst as [_ [_ H2]].
  rewrite H2.
  pose proof subst_ren as [_ [_ H3]].
  rewrite H3.
  unfold ren. f_equiv. f_equiv. extensionality n.
  unfold ">>>", ">>", up_subst, shift. destruct (η n) eqn:P0; auto.
  rewrite H1. auto.
Qed.

Corollary upn_comp : forall n ξ η,
  upn n ξ >> upn n η = upn n (ξ >> η).
Proof.
  induction n; intros; auto. simpl. rewrite <- IHn, up_comp. auto.
Qed.

Lemma subst_comp :
     (forall e ξ η, e.[ξ].[η] = e.[ξ >> η])
  /\ (forall e ξ η, e.[ξ]ₑ.[η]ₑ = e.[ξ >> η]ₑ)
  /\ (forall e ξ η, e.[ξ]ᵥ.[η]ᵥ = e.[ξ >> η]ᵥ).
Proof.
  eapply Exp_ind with
  (Q  := fun l => forall ξ η, Forall (fun x : Exp => x.[ξ].[η] = x.[ξ >> η]) l)
  (QV := fun l => forall ξ η, Forall (fun x : Val => x.[ξ]ᵥ.[η]ᵥ = x.[ξ >> η]ᵥ) l)
  (R  := fun l => forall ξ η, Forall (fun x : Exp * Exp =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ], y.[ξ]) in (x0.[η], y.[η])) =
   (let '(x0, y) := x in (x0.[ξ >> η], y.[ξ >> η]))) l)
  (RV := fun l => forall ξ η, Forall (fun x : Val * Val =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ) in
     (x0.[η]ᵥ, y.[η]ᵥ)) =
   (let '(x0, y) := x in (x0.[ξ >> η]ᵥ, y.[ξ >> η]ᵥ))) l)
   (W  := fun l => forall ξ η, Forall (fun x : list Pat * Exp * Exp =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, x0.[upn (PatListScope p) ξ],
      y.[upn (PatListScope p) ξ]) in
     (p, x0.[upn (PatListScope p) η],
     y.[upn (PatListScope p) η])) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (PatListScope p) (ξ >> η)],
     y.[upn (PatListScope p) (ξ >> η)]))) l)
  (Z  := fun l => forall ξ η, Forall
  (fun x : nat * Exp =>
   (let
    '(n, x0) := let '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) ξ]) in
     (n, x0.[upn (Datatypes.length (map (fun '(n0, x1) => (n0, x1.[upn (Datatypes.length l + n0) ξ])) l) + n) η])) =
   (let '(n, x0) := x in (n, x0.[upn (Datatypes.length l + n) (ξ >> η)]))) l)
  (VV := fun l => forall ξ η, Forall
  (fun x : nat * nat * Exp =>
   (let
    '(i, ls, x0) := let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length l + ls) ξ]) in
     (i, ls, x0.[upn (Datatypes.length l + ls) η])) =
   (let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length l + ls) (ξ >> η)]))) l)
  ;intros.
    (* Exp *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* Val *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Val => x.[ξ >> η]ᵥ)).
    - reflexivity.
    - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> η]ᵥ, y.[ξ >> η]ᵥ))).
    - reflexivity.
    - apply H.
  (* * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Val => x.[ξ >> η]ᵥ)).
    - reflexivity.
    - apply H. *)
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * simpl. unfold ">>", ren. destruct n. destruct (ξ n) eqn:P; auto.
  * simpl. rewrite map_map. rewrite map_length.
    erewrite map_ext_Forall with (g := (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext + ls) (ξ >> η)]))).
    - rewrite H0. f_equal. rewrite upn_comp. reflexivity.
    - apply H.
  (* NonVal *)
  * simpl. rewrite H. rewrite upn_comp. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> η])).
      - reflexivity.
      - apply H.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> η])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> η], y.[ξ >> η]))).
      - reflexivity.
      - apply H.
  * simpl. rewrite H, H0. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> η])).
      - reflexivity.
      - apply H1.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> η])).
      - reflexivity.
      - apply H.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Exp => x.[ξ >> η])).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (PatListScope p) (ξ >> η)],
      y.[upn (PatListScope p) (ξ >> η)]))).
      - rewrite H. reflexivity.
      - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite upn_comp. reflexivity.
  * simpl. rewrite H. rewrite H0. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[upn (Datatypes.length l + n) (ξ >> η)]))).
      - rewrite H. rewrite map_length. rewrite upn_comp. reflexivity.
      - apply H0.
  * simpl. rewrite H. rewrite H0. rewrite H1. rewrite upn_comp. rewrite upn_comp. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (PatListScope p) (ξ >> η)],
      y.[upn (PatListScope p) (ξ >> η)]))).
      - reflexivity.
      - apply H.
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
    - rewrite H. rewrite H0. rewrite upn_comp. reflexivity.
    - apply H1.
  * apply Forall_nil.
  * apply Forall_cons.
    - f_equal. rewrite map_length. rewrite H. rewrite upn_comp. reflexivity.
    - simpl. specialize (H0 (up_subst ξ) (up_subst η)).
    eapply Forall_impl in H0.
      + exact H0.
      + destruct a. do 2 rewrite map_length. intros. f_equal.  inversion H1.
        do 2 rewrite up_subst_S in H3. simpl in H3.
        rewrite (upn_comp 1) in H3. simpl in H3. rewrite up_subst_S in H3. simpl in H3. exact H3.
Qed.

Corollary subst_comp_exp :
  forall e ξ η, e.[ξ].[η] = e.[ξ >> η].
Proof.
  apply subst_comp.
Qed.

Corollary subst_comp_val :
  forall e ξ η, e.[ξ]ᵥ.[η]ᵥ = e.[ξ >> η]ᵥ.
Proof.
  apply subst_comp.
Qed.

Corollary subst_comp_nval :
  forall e ξ η, e.[ξ]ₑ.[η]ₑ = e.[ξ >> η]ₑ.
Proof.
  apply subst_comp.
Qed.

Theorem rename_subst_core :
     (forall e v ξ, (rename S e).[v .:: ξ] = e.[ξ])
  /\ (forall e v ξ, (renameNonVal S e).[v .:: ξ]ₑ = e.[ξ]ₑ)
  /\ (forall e v ξ, (renameVal S e).[v .:: ξ]ᵥ = e.[ξ]ᵥ).
Proof.
  pose proof renaming_is_subst as [H0e [H0n H0v]].
  pose proof subst_comp as [H1e [H1n H1v]].
  split. 2: split.
  * intros. rewrite H0e. rewrite H1e. reflexivity.
  * intros. rewrite H0n. rewrite H1n. reflexivity.
  * intros. rewrite H0v. rewrite H1v. reflexivity. 
Qed.

Theorem rename_subst : forall e v,
  (rename S e).[v/] = e.
Proof.
  intros. rewrite (proj1 rename_subst_core e (inl v) idsubst).
  now rewrite idsubst_is_id_exp.
Qed.


Lemma scons_substcomp_core v ξ η :
  (v .:: ξ) >> η = match v with 
                   | inl exp => inl (exp.[η]ᵥ)
                   | inr n => η n
                   end .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp. now destruct x.
Qed.


Lemma scons_substcomp v ξ η :
  (v .: ξ) >> η = v.[η]ᵥ .: (ξ >> η).
Proof.
  apply scons_substcomp_core.
Qed.


Lemma scons_substcomp_list ξ η vals :
  (list_subst vals ξ) >> η = list_subst (map (substVal η) vals) (ξ >> η).
Proof.
  induction vals; simpl. auto.
  rewrite scons_substcomp, IHvals. auto.
Qed.


Lemma substcomp_scons_core v ξ η :
  up_subst ξ >> v .:: η = v .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp, up_subst. destruct x; auto.
  unfold shift. destruct (ξ x) eqn:P; auto.
  pose proof renaming_is_subst as [_ [_ H]].
  pose proof subst_comp as [_ [_ H0]].
  rewrite H. rewrite H0. f_equiv.
Qed.

Lemma substcomp_scons v ξ η :
  up_subst ξ >> v .: η = v .: (ξ >> η).
Proof.
  apply substcomp_scons_core.
Qed.

Corollary substcomp_list l ξ η :
  upn (length l) ξ >> list_subst l η = list_subst l (ξ >> η).
Proof.
  induction l; simpl; auto.
  * now rewrite substcomp_scons, IHl.
Qed.

Corollary substcomp_list_eq l ξ η n:
  n = length l ->
  upn n ξ >> list_subst l η = list_subst l (ξ >> η).
Proof.
  intros. subst. now apply substcomp_list.
Qed.

Theorem subst_extend_core : forall ξ η v,
  (up_subst ξ) >> (v .:: η) = v .:: (ξ >> η).
Proof.
  intros. unfold substcomp. extensionality x. destruct x; auto.
  cbn. break_match_goal.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs.
    pose proof rename_subst_core as [_ [_ Hv]]. now rewrite Hv.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. cbn. reflexivity.
Qed.

Corollary subst_list_extend : forall n ξ vals, length vals = n ->
  (upn n ξ) >> (list_subst vals idsubst) = list_subst vals ξ.
Proof.
  induction n; intros.
  * apply length_zero_iff_nil in H. subst. cbn. unfold substcomp. extensionality x.
    break_match_goal.
    - pose proof idsubst_is_id as [_ [_ H]]. rewrite H. reflexivity.
    - auto.
  * simpl. apply eq_sym in H as H'. apply element_exist in H'. destruct H', H0. subst.
    simpl. rewrite substcomp_scons. rewrite IHn; auto.
Qed.

Theorem list_subst_lt : forall n vals ξ, n < length vals ->
  list_subst vals ξ n = inl (nth n vals VNil).
Proof.
  induction n; intros; destruct vals.
  * inversion H.
  * simpl. auto.
  * inversion H.
  * simpl in H. apply Nat.succ_lt_mono in H. eapply IHn in H. simpl. exact H.
Qed.

Theorem list_subst_ge : forall n vals ξ, n >= length vals ->
  list_subst vals ξ n = ξ (n - length vals).
Proof.
  induction n; intros; destruct vals.
  * simpl. auto.
  * inversion H.
  * cbn. auto.
  * simpl in H. apply le_S_n in H. eapply IHn in H. simpl. exact H.
Qed.

Corollary list_subst_get_possibilities : forall n vals ξ,
  list_subst vals ξ n = inl (nth n vals VNil) /\ n < length vals
\/
  list_subst vals ξ n = ξ (n - length vals) /\ n >= length vals.
Proof.
  intros. pose (Nat.lt_decidable n (length vals)). destruct d.
  * left. split. now apply list_subst_lt. auto.
  * right. split. apply list_subst_ge. lia. lia.
Qed.

Lemma substcomp_id_r :
  forall ξ, ξ >> idsubst = ξ.
Proof.
  pose proof idsubst_is_id as [H0e [H0n H0v]].
  unfold ">>". intros. extensionality x.
  break_match_goal; auto. rewrite H0v. auto.
Qed.

Lemma substcomp_id_l :
  forall ξ, idsubst >> ξ = ξ.
Proof.
  unfold ">>", idsubst. intros. extensionality x. auto.
Qed.

Theorem subst_extend : forall ξ v,
  (up_subst ξ) >> (v .: idsubst) = v .: ξ.
Proof.
  intros. now rewrite subst_extend_core, substcomp_id_r.
Qed.

Lemma subst_ren_scons : forall (ξ : Substitution) e,
  ξ 0 = inl e ->
  (e .: (fun n : nat => n + 1) >>> ξ) = ξ.
Proof.
  intros. extensionality x. unfold ">>>", scons. destruct x; auto.
  rewrite Nat.add_comm. reflexivity.
Qed.


Lemma ren_up_subst :
  forall ξ,
    ren S >> up_subst ξ = ξ >> ren S.
Proof.
  pose proof renaming_is_subst as [_ [_ H0v]].
  intros. extensionality x; cbn.
  unfold shift. unfold ">>".
  break_match_goal; cbn.
  now rewrite <- H0v.
  reflexivity.
Qed.

Lemma ren_scons :
  forall ξ f, forall x, ren (fun n => S (f n)) >> x .: ξ = ren (fun n => f n) >> ξ.
Proof.
  intros.
  extensionality k. cbn. auto.
Qed.

Lemma rename_upn_list_subst :
  forall m ξ vals, length vals = m ->
    ren (fun n => m + n) >> (upn m ξ >> list_subst vals idsubst) = ξ.
Proof.
  intros.
  rewrite (subst_list_extend m ξ vals H).
  generalize dependent vals. induction m; intros; cbn.
  - replace (ren (fun n => n)) with idsubst by auto. apply length_zero_iff_nil in H.
    subst. cbn. now rewrite substcomp_id_l.
  - assert (length vals = S m) by auto.
    apply eq_sym, element_exist in H as [x0 [xs H1]]. subst. inversion H0.
    replace (list_subst (x0 :: xs) ξ) with (x0 .: list_subst xs ξ) by auto.
    specialize (IHm xs H1).
    erewrite H1, ren_scons; eauto.
Qed.

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
  pose proof subst_comp as [_ [_ H0v]].
  intros. extensionality x. unfold ">>".
  destruct (ξ x) eqn:D1; auto.
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

Definition excsubst (ξ : Substitution) (e : Exception) : Exception :=
  match e with
  | (c, r, v) => (c, r.[ξ]ᵥ, v.[ξ]ᵥ)
  end.

Notation "s .[ σ ]ₑₓ" := (excsubst σ s)
  (at level 2, σ at level 200, left associativity,
    format "s .[ σ ]ₑₓ" ).

Definition redsubst (ξ : Substitution) (r : Redex) : Redex :=
  match r with
  | RExp e => RExp e.[ξ]
  | RValSeq vl => RValSeq (map (substVal ξ) vl)
  | RExc e => RExc e.[ξ]ₑₓ
  | RBox => RBox
  end.

Notation "s .[ σ ]ᵣ" := (redsubst σ s)
  (at level 2, σ at level 200, left associativity,
    format "s .[ σ ]ᵣ" ).


Lemma subst_comm :
  forall l ξ,
    list_subst l idsubst >> ξ = upn (length l) ξ >> list_subst (map (substVal ξ) l) idsubst.
Proof.
  induction l; intros; simpl.
  * now rewrite substcomp_id_r.
  * rewrite substcomp_scons. rewrite <- IHl.
    now rewrite scons_substcomp.
Qed.

Fixpoint varsFrom n m : list Val :=
  match m with
  | O => []
  | S m' => VVar n :: varsFrom (S n) m'
  end.

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

Lemma varsFrom_length :
  forall m n, length (varsFrom n m) = m.
Proof.
  induction m; intros; simpl; auto.
Qed.

Definition default_subst v : Substitution := fun _ => inl v.

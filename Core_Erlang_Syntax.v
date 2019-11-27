From Coq Require ZArith.BinInt.
From Coq Require Reals.
From Coq Require Init.Nat.
From Coq Require Strings.String.

Module Core_Erlang_Syntax.

Import ZArith.BinInt.
Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Definition Var : Type := string.

Inductive Literal : Type :=
| Atom (s: string) (* TODO: How could we define these? Atom vs string, mindkettő string belső reprezentációval? Atomok száma véges... Később id lehetne a string helyett *)
| Integer (x : Z)
(* | Float (q : R) *)
| EmptyList
| EmptyTuple
| EmptyMap.

(* Patterns are not expressions, because there are expressions that are not patterns and patters that are not expressions (these are not implemented yet) *)
Inductive Pattern : Type :=
| PVar     (v : Var)
| PLiteral (l : Literal)
| PList  (hd tl : Pattern)
| PTuple (t : Tuple)
with Tuple : Type :=
| TNil 
| TCons (hd : Pattern) (tl : Tuple).

Notation "[[ ]]" := TNil (format "[[ ]]").
Notation "[[ x ]]" := (TCons x TNil).
Notation "[[ x ; y ; .. ; z ]]" := (TCons x (TCons y .. (TCons z TNil) ..)).

Definition FunctionSignature : Type := string * nat.

Inductive Expression : Type :=
| ELiteral (l : Literal)
| EVar     (v : Var)
| EFunction (f : Fun)
| EList  (hd tl : Expression)
| ETuple (l : list Expression) (* maybe vector is more appropriate, or * (product) *)
(* | ETuple            (n: nat) (l : t Expression n)  (* vectorial implementation for tuples *) *)
| ECall  (f: FunctionSignature)     (l : list Expression) (* For built-in functions and primitive operations *)
| EApply (f: Var)     (l : list Expression)
| EApplyTopLevel (f : FunctionSignature) (l : list Expression)
(*| ECase  (e: Expression)            (l : list Clause)*)
| ELet   (s : list Var)             (el : list Expression) (e : Expression)
| ELetrec (fnames : list FunctionSignature) (fs : list Fun) (e : Expression)
| EMap   (kl vl : list Expression)   (* maybe map would be better *)
(* | ETry   (e ex : Expression) (v1 v2 : Var) *)
(* with Clause : Type :=
 | CConstructor (p: Pattern)   (guard e : Expression)*)
 with Fun : Type := (* Restriction because of the Letrec -> here only functions can be defined *)
 | FunDecl (vl : list Var) (e : Expression).

Section All.
  Variable T : Type.
  Variable P : T -> Prop.

  Fixpoint All (ls : list T) : Prop :=
    match ls with
      | [ ] => True
      | h::t => P h /\ All t
    end.
End All.


Section induct.

  Variable P : Expression -> Prop.


  Hypothesis literal_case : forall l, P (ELiteral l).
  Hypothesis var_case : forall v : Var, P (EVar v).
  Hypothesis function_case : forall f: Fun, P (EFunction f).
  Hypothesis list_case : forall hd tl : Expression, P hd /\ P tl -> P (EList hd tl).
  (*Hypothesis tuple_case : forall exps : list Expression, All Expression P exps -> P (ETuple exps).*)
  Hypothesis tuple_case : forall exps : list Expression, All Expression P exps -> P (ETuple exps).
  Hypothesis call_case : forall f exps, All Expression P exps -> P (ECall f exps).
  Hypothesis apply_case : forall f exps, All Expression P exps -> P (EApply f exps).
  Hypothesis top_apply_case : forall f exps, All Expression P exps -> P (EApplyTopLevel f exps).
  Hypothesis let_case : forall sl el e, All Expression P el /\ P e -> P (ELet sl el e).
  Hypothesis letrec_case : forall fnames fs e, P e -> P (ELetrec fnames fs e).
  Hypothesis map_case : forall kl vl, All Expression P kl /\ All Expression P vl -> P (EMap kl vl).
  
  Fixpoint expr_induct (e : Expression) : P e :=
    match e with
     | ELiteral l => literal_case l
     | EVar v => var_case v
     | EFunction f => function_case f
     | EList hd tl => list_case hd tl (conj (expr_induct hd) (expr_induct tl))
     | ETuple l => tuple_case l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | ECall f l => call_case f l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | EApply f l => apply_case f l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | EApplyTopLevel f l => top_apply_case f l ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) l)
     | ELet s el e => let_case s el e (conj ((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) el) (expr_induct e))
     | ELetrec fnames fs e => letrec_case fnames fs e (expr_induct e)
     | EMap kl vl => map_case kl vl (conj (((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) kl)) (((fix list_ind (ls : list Expression) : All Expression P ls :=
        match ls with
        | [] => I
        | x::xs => conj (expr_induct x) (list_ind xs)
        end) vl)))
    end.

End induct.


Inductive ErlFunction : Type := TopLevelFun (n : FunctionSignature) (f : Fun).

Inductive ErlModule : Type := ErlMod (a : string) (fl : list ErlFunction).

(* What should we call a value *)
Reserved Notation "t 'val'" (at level 1).
Inductive ValueJudgement : Expression -> Prop :=
| VJ_Literal e : (ELiteral e) val
| VJ_Function f : (EFunction f) val
| VJ_List hd tl: hd val -> tl val -> (EList hd tl) val
| VJ_Tuple (exprs : list Expression) : (forall exp : Expression, In exp exprs -> exp val) -> (ETuple exprs) val
| VJ_Map kl vl : (forall exp : Expression, In exp vl -> exp val) -> (EMap kl vl) val
where "t 'val'" := (ValueJudgement t).

(*Section value_induct.

  Variable P : Expression -> Prop.

  Hypothesis VJ_lit_case : 

End value_induct.*)

Definition Value : Type := { e : Expression | e val }.
Notation "e p: t" := (exist _ e t) (at level 45).

(* To describe faults *)

Definition ErrorValue : Value := exist _ (ELiteral (Atom "error"%string)) (VJ_Literal _).
Definition ErrorExp : Expression := (ELiteral (Atom "error"%string)).
Definition ErrorPat : Pattern := PLiteral (Atom "error"%string).

End Core_Erlang_Syntax.
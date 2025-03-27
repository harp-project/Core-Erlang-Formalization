(**
 * In this file we aim to implement reachability logic PSD system as defined
 * in https://arxiv.org/pdf/1909.01744
 * The ultimate goal is to come up with an implementation that would allow us
 * to reason about label trace in iterative / loop constructs.
 *)

From CoreErlang.FrameStack Require Export SubstSemanticsLabeledLemmas.
From stdpp Require Import list.
Import ListNotations.

Definition trans fs r l fs' r' l' : Prop :=
  exists se, ⟨ fs, r ⟩ -⌊ se ⌋-> ⟨ fs', r' ⟩ /\
  match se with
  | Some eff => l' = eff :: l
  | None     => l' = l
  end.

Definition final fs r l := forall fs' r' l', ~ (trans fs r l fs' r' l').

Definition SymState := FrameStack * Redex * list SideEffect -> Prop.
Definition symTrans (q: SymState) :=
  fun s: FrameStack * Redex * list SideEffect =>
  match s with
  | (fs', r', l') => exists fs r l, q (fs, r, l) /\ trans fs r l fs' r' l'
  end.

Inductive RLF :=
| rlf (p q: SymState): RLF.

Notation "l =><> r" := (rlf l r) (at level 100).


Parameter l1 l2: SymState.

(* Proof system draft. Draft because I suspect some rules may have to go *)
Inductive PSD: (* will give me PTSD ahahahahahahaha *)
  list (bool * RLF) -> (bool * RLF) -> Type
:=
| Trv : forall H r b,   PSD  H (b, r=><> r)
| Hyp : forall H1 H2 f, PSD (H1 ++ [(false,f)] ++ H2) (true, f)
| Str :  forall H l l' r b,
    (forall fs e ls, l (fs, e, ls) -> l' (fs, e, ls)) ->
    PSD H (b, l'=><> r) ->
    PSD H (b, l =><> r)
| Spl : forall H l1 l2 r b,
    PSD H (b, l1 =><> r) ->
    PSD H (b, l2 =><> r) ->
    PSD H (b, ((fun s => l1 s \/ l2 s) =><> r))
| Tra : forall H l m r b,
    PSD H (b, l =><> m) ->
    PSD H (b, m =><> r) ->
    PSD H (b, (l =><> r))
| Stp : forall H l r b,
    (forall fs e ls, l (fs, e, ls) -> ~ (is_result e)) ->
    PSD H (true, (symTrans l =><> r)) ->
    PSD H (b, l =><> r)
| Cof : forall H f b,
    PSD ((false,f)::H) (false,f) ->
    PSD H (b,f)
| Cut : forall H b f f',
    PSD H (false,f') ->
    PSD ((false,f') :: H) (b,f) ->
    PSD H (b,f)
| Clr : forall H1 H2 h f,
    PSD (H1 ++ H2) f ->
    PSD (H1 ++ [h] ++ H2) f.

(* ⟨(= []), (= ECall m f el)⟩ =[ ls ]=> ⟨(= []), (= RValSeq vs)⟩ *)
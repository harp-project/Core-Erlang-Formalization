(**
 * In this file we aim to implement reachability logic proof system as defined
 * in https://fsl.cs.illinois.edu/publications/rosu-stefanescu-ciobaca-moore-2013-lics.pdf
 * The ultimate goal is to come up with an implementation that would allow us
 * to reason about label trace in iterative / loop constructs.
 *)

From CoreErlang.FrameStack Require Export SubstSemanticsLabeledLemmas.
From stdpp Require Import list.
Import ListNotations.

Definition flush_hyps (C: list Prop) (g: Prop) : Prop :=
  foldr (fun h acc => h -> acc) g C.

Lemma reach_trans (C: list Prop) :
  forall (fs fs' fs'': FrameStack) (e e' e'': Redex) (l l': list SideEffect),
  (* all of Props in C are result of reach_circu *) 
  ⟨ fs, e ⟩ -[ l ]->* ⟨ fs', e' ⟩ (* reaches C fs e l fs' e' *) ->
  flush_hyps C (⟨ fs', e' ⟩ -[ l' ]->* ⟨ fs'', e'' ⟩) ->
  ⟨ fs, e ⟩ -[ l ++ l' ]->* ⟨ fs'', e'' ⟩.
Proof.
  intros. generalize dependent C.
  induction C; simpl; intro.
  - apply (transitive_any_eval H H0).
  - Abort.

(* Definition reaches (C: list Prop) :
  FrameStack -> Redex -> list SideEffect -> FrameStack -> Redex -> Prop
:=
  fun fs r l fs' r' =>
    reach_refl C fs r l fs' r' \/

Lemma reach_trans (C: list Prop) :=
  forall fs r l fs' r' l' fs'' r'':
  reaches *)

Inductive PSD :
  FrameStack -> Redex -> list SideEffect -> FrameStack -> Redex -> Prop :=
(* Proof system rules *)

(*
  Axiom.
*)
| psd_axiom fs r l l' fs' r':
  step fs r l fs' r' ->
  l' = match l with | None => [] | Some se => [se] end ->
  (* or a rule from circularity set *)
  PSD fs r l' fs' r'

(* Reflexivity *)
| psd_reflx fs r:
  PSD fs r [] fs r

(* Transitivity *)
| psd_trans fs r l fs' r' l' fs'' r'':
  PSD fs r l fs' r' ->
  PSD fs' r' l' fs'' r'' -> (* need to somehow incl circ set *)
  PSD fs r (l ++ l') fs'' r''

(* Consequence *)
(* | psd_consq: *)
  (* don't know how to encode fs r -> fs' r' *)

(* | psd_casea *)
  (* same here. i guess i need fs -> r -> Prop for patterns, but do I really need it? *).

(* abstr and circ *)

(**
 * Below is the original content of proof_system.v. I will try to adapt it to our 
 * semantics (in other words, remove the generalisation)
 *)

Section domain.
Variable cfg : Set.

(* Because we are showing soundness, it's a stronger result if we don't put any
   restrictions on the syntax or domains of matching logic patterns,
   so we instead allow an arbitrary satisfaction relation.
 *)
Definition formula env : Type := env -> cfg -> Prop. (* pattern *)
Definition stateless env : Type := env -> Prop.      (* boolean claims *)

(* Rather than explicitly tagging rules as one-path or all-path,
   observe that none of the rules mix quantifiers, so we'll just
   state the proof system without saying whether it's one-path or
   all-path, and prove that soundness for both interpretations.
 *)
Definition system := forall env,
  formula env -> formula env -> Prop.

Definition my_system :=
  FrameStack -> Redex -> list SideEffect -> FrameStack -> Redex -> Prop.

Definition in_opt_system (S : option system) env (phi phi' : formula env) : Prop :=
  match S with
    | None => False
    | Some sys => sys env phi phi'
  end.

Definition cons_system env (phi phi' : formula env) (S : system) : system :=
  fun env0 X X0 =>
    S env0 X X0 \/
    {H : env = env0 | phi = eq_rect_r _ X H /\ phi' = eq_rect_r _ X0 H}.

Definition cons_opt_system env (phi phi' : formula env) (S : option system) : option system :=
  Some (cons_system env phi phi' (in_opt_system S)).

Definition system_empty (S : option system) : Prop :=
  match S with
    | Some _ => False
    | None => True
  end.

Definition union_system (C : option system) (S : system) : system :=
  match C with
    | None => S
    | Some S1 =>
      fun env0 X X0 => S1 env0 X X0 \/ S env0 X X0
  end.

Section FixTransition.
Variable (S : cfg -> cfg -> Prop).

Search fst.

(* The proof system defined for soundness.
   Because we are only interested in soundness here, including additional
   rules is a stronger result (such as allowing logical framing at any
   point rather than just combined with axiom, including substitution
   as an explicit rule, or including step even during the
   one-path soundness proof)
 *)
Inductive IS (C : option system) (A : system) : forall env,
  formula env -> formula env -> Prop :=
  (* This step is written in terms of a transtion relation, rather
     than a system given as a set of rules.
     Equavalence to the version in the paper is shown
     later in this file. *)
  | is_step : forall env (phi phi' : formula env),
                (forall e c, phi e c ->
                             (exists c2, S c c2) /\
                             (forall c2, S c c2 -> phi' e c2)) ->
                 IS C A env phi phi' (* won't be needed since fss is determenistic *)
  (* if we can make a step / transition *)
  | is_axiom : forall env phi phi',
                 A env phi phi' -> IS C A env phi phi'
  (* if there is a step fs, e -[l]->* fs' e' *)
  | is_refl : forall env phi, system_empty C -> IS C A env phi phi
  | is_trans : forall env phi phi' phi'',
       IS C A env phi phi' ->
       IS None (union_system C A) env phi' phi'' ->
       IS C A env phi phi''
  | is_conseq : forall env
       (phi1 phi1' phi2 phi2' : formula env),
       (forall e g, phi1 e g -> phi1' e g) ->
       (forall e g, phi2 e g -> phi2' e g) ->
       IS C A env phi1' phi2 ->
       IS C A env phi1 phi2'
  | is_case : forall env phi phi1 phi',
       IS C A env phi  phi' ->
       IS C A env phi1 phi' ->
       IS C A env (fun e g => phi e g \/ phi1 e g) phi'
(* Abstraction with frehsness made manifest by giving phi a biggern env. *)
  | is_abstr : forall env denx
       (phi : formula (env * denx)) (phi' : formula env),
       IS C A (env * denx) phi (fun rho_and_x g => phi' (fst rho_and_x) g) ->
       IS C A env (fun rho g => exists x, phi (rho , x) g) phi'
(* Abstraction done by replacing the value in the environment,
   with the operation (repx) of replacing that value in the environment left abstract,
   and freeness of phi' taken as an assumption. *)
  | is_abstr' : forall env denx repx
       (phi phi' : formula env),
       (forall rho (x : denx) gamma, phi' rho gamma <-> phi' (repx x rho) gamma) ->
       IS C A env phi phi' ->
       IS C A env (fun rho g => exists x, phi (repx x rho) g) phi'
  | is_circ : forall env phi phi',
       IS (cons_opt_system env phi phi' C) A env phi phi' ->
       IS C A env phi phi'
  | is_subst : forall env env' f phi phi',
       IS C A env' phi phi' ->
       IS C A env (fun e g => phi (f e) g) (fun e g => phi' (f e) g)
  | is_lf : forall env phi phi' psi,
       IS C A env phi phi' ->
       IS C A env (fun e g => phi e g  /\ psi e)
                  (fun e g => phi' e g /\ psi e).

(* Now some lemmas checking adequacy of definitions that
   won't be needed outside this file
 *)

(* For soundness, the weakly-well-defined condition is used mostly
   just to be sure that the transition system induced by a set of
   rules actually makes it's own rules semantically valid.
   Check that here. *)
(* A transition relation where each rule in the system
   induces an immediate step *)
Definition relation_of_system (S : system) : cfg -> cfg -> Prop :=
  fun gamma gamma' =>
    exists env, exists (rho : env), exists phi, exists phi',
       (S env phi phi') /\ phi rho gamma /\ phi' rho gamma'.
(* A system consisting of rules all of whose instances
   hold in exactly one step along some path *)
Definition system_of_relation (R : cfg -> cfg -> Prop) : system :=
  fun env phi phi' =>
    forall (rho : env) gamma gamma',
      phi rho gamma -> phi' rho gamma' -> R gamma gamma'.
(* A weakly well-defined rule *)
Definition weakly_well_defined (env : Set) phi phi' : Prop :=
  forall (gamma : cfg) (rho : env), phi rho gamma -> exists (gamma' : cfg), phi' rho gamma'.
(* Show that the if a rule is weakly-well-defined, then included in the
   system of the transition relation of any system including that rule *)
Lemma weakly_well_defined_rule_valid :
  forall (S : system) (env : Set) (phi phi' : formula env),
    S env phi phi' -> weakly_well_defined env phi phi' ->
    (system_of_relation (relation_of_system S) env phi phi').
unfold system_of_relation, relation_of_system; eauto 40.
Qed.

Section StepGood.
Variable (Ssys : system).
Hypothesis (Ssys_welldef :
              forall env phi phi' e c1,
                (Ssys env phi phi' /\ phi e c1) ->
                exists c2, phi' e c2).
Hypothesis (Ssys_good :
              forall c1 c2, S c1 c2 <->
                            exists env phi phi' e,
              (Ssys env phi phi' /\ phi e c1 /\ phi' e c2)).

(* Check that the step rule is faithful compared to the
   paper proof as long as S is generated from
   a set of sell-defined reachability rules *)

Lemma s_prog :
  forall c,
    (exists c2, S c c2)
      <-> (exists env phi phi' e,
            Ssys env phi phi' /\ phi e c).
split. firstorder eauto.
intros.
destruct H as (env & phi & phi' & e & H).
specialize (@Ssys_welldef env phi phi' e c H).
destruct Ssys_welldef.
exists x.
apply Ssys_good.
firstorder eauto.
Qed.

Lemma s_succs :
  forall env1 (e : env1) c (phi_g : formula env1),
    ((forall c2, S c c2 -> phi_g e c2)
      <->
     (forall env phi phi',
       Ssys env phi phi' ->
       forall e2, phi e2 c ->
                  forall c2, phi' e2 c2 -> phi_g e c2)).
Proof.
intros.
split.
intros.
apply H.
apply Ssys_good.
firstorder eauto.

intros.
apply Ssys_good in H0.
destruct H0 as (env & phi & phi' & e2 & Hssys & Hphi & Hphi').
apply (H env phi phi' Hssys e2 Hphi c2 Hphi').
Qed.
End StepGood.
End FixTransition.

End domain.
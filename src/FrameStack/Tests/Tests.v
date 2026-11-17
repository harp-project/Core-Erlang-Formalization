(**
  This file contains evaluation examples for the frame stack semantics, proved
  by explicit stepping.
*)
From CoreErlang.FrameStack Require Export SubstSemantics.

Import ListNotations.

Open Scope string_scope.

(** `take n steps` makes `n` reduction steps, solving the premises of the
    applied rules (scoping, simple equalities) automatically. *)
Tactic Notation "take" integer(n) "steps" :=
  do n (cbn; eapply step_trans; [ (constructor + econstructor); try scope_solver; cbn; try reflexivity; try congruence|]).

(** Mutually recursive functions of a `letrec`, calling each other. *)
Example multiple_top_level_funs2 :
  ⟨ [], ELetRec [(0, °EApp (˝VFunId (2, 0)) []);
                    (0, ˝VLit (Integer 42));
                    (0, °EApp (˝VFunId (1, 0)) [])]
     (EApp (˝VFunId (0, 0)) []) ⟩
-->*
  RValSeq [VLit (Integer 42)].
Proof.
  eexists. split. shelve.
  take 14 steps. apply step_refl.
  Unshelve. constructor.
Qed.

(** A tricky combination of `letrec`, function parameters and application,
    testing the de Bruijn indexing of function identifiers and variables. *)
Example weird_apply : ⟨[], ELetRec [(1,
   °ECase (˝VVar 1)
          [([PLit (Integer 0)], ˝VLit (Atom "true"), ˝VLit (Integer 5));
           ([PLit (Integer 1)], ˝VLit (Atom "true"), °EApp (˝VFunId (0, 1)) [˝VLit (Integer 0)]);
           ([PVar], ˝VLit (Atom "true"), °EApp (˝VFunId (1, 1)) [˝VLit (Integer 1)])]
   )]
   (ELet 1 (EFun 1
       (ELetRec [(1, ˝VLit (Integer 0))]
          (EApp (˝VVar 2) [˝VLit (Integer 2)])
       ))
    (EApp (˝VVar 0) [˝VFunId (1, 1)])
   )⟩
-->*
  RValSeq [VLit (Integer 5)].
Proof.
  eexists. split. constructor. repeat constructor.
  take 19 steps.
  eapply step_trans. apply eval_step_case_not_match. reflexivity.
  eapply step_trans. apply eval_step_case_not_match. reflexivity.
  take 22 steps.
  take 5 steps.
  apply step_refl.
Qed.

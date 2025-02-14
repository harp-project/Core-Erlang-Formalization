(**
  This file contains numerous semantic properties about the frame stack semantics
  (labelled version) of Core Erlang.
 *)
From CoreErlang.FrameStack Require Export SubstSemanticsLabeled.
Import ListNotations.

Theorem transitive_eval :
  forall {n e e' l fs fs'}, ⟨ fs, e ⟩ -[ n, l ]-> ⟨ fs', e' ⟩ ->
  forall {n' e'' l' fs''},  ⟨ fs', e' ⟩ -[ n', l' ]-> ⟨ fs'', e'' ⟩
->
  ⟨ fs, e ⟩ -[ n + n', l ++ l' ]-> ⟨ fs'', e'' ⟩.
Proof.
  intros n Fs Fs' l e e' IH.
  induction IH; intros; auto using app_nil_l.
  simpl. econstructor. exact H. apply IHIH. exact H1.
  destruct s; rewrite H0; auto.
Qed.

Theorem step_determenism {e e' l fs fs'} :
  ⟨ fs, e ⟩ -⌊ l ⌋-> ⟨ fs', e' ⟩ ->
  (forall l' fs'' e'', ⟨ fs, e ⟩ -⌊ l' ⌋-> ⟨ fs'', e'' ⟩
  -> l = l' /\ fs'' = fs' /\ e'' = e').
Proof.
  intro H. inv H; intros; inv H; auto.
  - rewrite <- H1 in H9. now inv H9.
  - rewrite <- H0 in H8. now inv H8.
  - rewrite H0 in H10. now inv H10.
  - rewrite H0 in H10; congruence.
  - rewrite H0 in H10; congruence.
  - simpl in *. congruence.
  - simpl in *. congruence.
Qed.

Theorem value_nostep v :
  is_result v ->
  forall fs' v' l, ⟨[], v⟩ -⌊l⌋-> ⟨fs' , v'⟩ -> False.
Proof.
  intros H fs' v' l' HD. inversion H; subst; inversion HD.
Qed.



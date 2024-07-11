Require Import Coq.Lists.List.
Import ListNotations. 
Require Import stdpp.list.

Lemma map_length_eq :
  forall A B (f : A -> B) l1 l2,
    map f l1 = l2 ->
      length l2 = length l1.
Proof.
  intros.
  Check map_length.
  rewrite <- H.
  apply map_length.
Qed.


Lemma map_notemptylist_is_notempty :
  forall A B (f : A -> B) a l,
    map f (a :: l) = [] -> False.
Proof.
  intros.
  assert ( length (map f (a ::l)) = length (a :: l)).
  {
    apply map_length.
  }
  rewrite H in H0.
  cbn in H0.
  congruence.
Qed.

Lemma mapM_length_eq :
  forall A B (f : A -> option B) (l1 : list A) (l2 : list B),
    mapM f l1 = Some l2 ->
      length l2 = length l1.
Proof.
  intros.
  remember (mapM f l1) as opt_l2.
  destruct opt_l2.
  * admit.
  * congruence.
Admitted.



Fixpoint sequence {A : Type} (l : list (option A)) : option (list A) :=
 match l with
 | [] => Some []
 | hd :: tl => match hd with
             | Some x => match sequence tl with
                         | Some xs => Some (x :: xs)
                         | None => None
                         end
             | None => None
             end
 end.
 
 
 Definition map_opt {A B : Type} 
                    (f : A -> option B)
                    (l : list A)
                    : option (list B) :=
  
  sequence (map f l).


Definition has_some {A : Type} (a : option A) : Prop :=
  match a with
  | None => False
  | Some _ => True
  end.

Lemma sequence_some : 
  forall {A : Type} (l : list (option A)) (l' : list A),
    sequence l = Some l' ->
      Forall (λ x : option A, has_some x) l.
Proof.
  intros.
  induction l.
  * constructor.
  * simpl in H.
    case_match. 2:
    {
      congruence.
    }
    case_match. 2:
    {
      congruence.
    }
    admit.
Admitted.

Lemma sequence_some1 : 
  forall {A : Type} (l : list (option A)),
    has_some (sequence l) ->
      Forall (λ x : option A, has_some x) l.
Proof.
  intros.
  induction l.
  * constructor.
  * simpl in H.
    case_match. 2:
    {
      inversion H.
    }
    case_match. 2:
    {
      inversion H.
    }
    constructor.
    - assumption.
    - apply IHl.
      auto.
Qed.

 Lemma map_opt_length_eq :
  forall A B (f : A -> option B) (l1 : list A) (l2 : list B),
    map_opt f l1 = Some l2 ->
      length l2 = length l1.
Proof.
  intros.
  unfold map_opt in H.
  unfold sequence in H.
  
  induction l1.
  * cbn in H.
    inversion H.
    reflexivity.
  * 
Admitted.



Theorem map_ite :
  forall {A B : Type} (f : A -> B) (a : A) (l : list A),
    map f (a :: l) = f a :: (map f l).
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem mapM_ite : 
  forall {A B : Type} (f : A -> option B) (a : A) (l : list A),
    mapM f (a :: l) = match f a with
                      | None => None
                      | Some b => match mapM f l with
                                  | None => None
                                  | Some lb => Some (b :: lb)
                                  end
                      end.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Search mapM.

Theorem mapM_ite1 : 
  forall {A B : Type} (f : A -> option B) (a : A) (l : list A) (b : B) (l' : list B),
    mapM f (a :: l) = Some (b :: l') ->
    f a = Some b /\ mapM f l = Some l'.
Proof.
  intros.
  rewrite mapM_ite in H.
  remember (f a) as fa.
  remember (mapM f l) as fl.
  case_match. 2:
  {
    congruence.
  }
  case_match. 2:
  {
    congruence.
  }
  inversion H.
  split.
  * reflexivity.
  * reflexivity.
Qed.

Theorem map_lambda :
  forall A B (f : A -> B) (l : list A),
    map f l = map (λ x, f x) l.
Proof.
  intros.
  reflexivity.
Qed.

(**
exp_to_val_fs (bs_to_fs_exp f (val_to_exp (subst_env (measure_val x)) x))
     ≫= (λ y : Val,
           mapM exp_to_val_fs
             (map (λ x : Expression, bs_to_fs_exp f x)
                (map (val_to_exp (subst_env (measure_val (VTuple l)))) l))
           ≫= (λ k : list Val, mret (y :: k))) = Some l0
*)

Lemma something1 :
  forall A (y1 : option A) (k1 : option (list A)) (l0 : list A),
    y1
      ≫= (λ y, k1
        ≫= (λ k, mret (y :: k))) = Some l0.
Proof.
  intros A y1 k1 l0.
  destruct y1 as [y |]; simpl.
  - destruct k1 as [k |]; simpl.
    + intros H; inversion H; reflexivity.
    + intros H; inversion H.
  - intros H; inversion H.
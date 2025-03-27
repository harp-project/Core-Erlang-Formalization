Require Import Classical.
Require Import Program.
Require Import List.
Require Import Lia.
Import ListNotations.
Require Import Inverse_Image.

From CoreErlang.FrameStack Require Export SubstSemanticsLabeled.

Module Type SigMod.

Definition State : Type := FrameStack * Redex * list SideEffect.
Definition trans : State -> State -> Prop :=
fun s s' =>
match s, s' with
| (fs, r, l), (fs', r', l') =>
  exists se, ⟨ fs, r ⟩ -⌊ se ⌋-> ⟨ fs', r' ⟩ /\
  match se with
  | Some eff => l' = eff :: l
  | None     => l' = l
  end
end.

End SigMod.


Section LexProd .

Variable A B : Type.
Variable leA : A -> A -> Prop.
Variable leB : B -> B -> Prop.

Inductive LexProd : (A*B) -> (A*B) -> Prop :=
    | leftLexProd :
      forall (x x':A) (y y':B),
        leA x x' -> LexProd (x, y) (x', y')
    | rightLexProd :
      forall (x:A) (y y':B),
        leB y y' -> LexProd (x, y) (x, y').

Variable wf_leA : well_founded leA.
Variable wf_leB : well_founded leB.


Definition P(a:A) : Prop :=  forall b, Acc LexProd (a,b).
 
Lemma wfPrincA  : forall a,  (forall a',  leA a' a -> P a') -> P a.
Proof. 
intros a0 H.
set (Q :=  fun b => Acc LexProd (a0, b)).
assert (forall b ,  (forall b',  leB b' b -> Q b') -> Q b).
  +  intros b0 Hb0.
     unfold Q.
     constructor ; intro y ; destruct y as (c,d) ; intro Hlex.
     inversion Hlex ; subst.
     - apply H ; assumption.
     - apply Hb0 ; assumption.
  +  generalize (well_founded_induction_type wf_leB (fun b => Q b)) ; intros H1.
     unfold P.
     unfold Q in *.
     apply H1 ; auto.
Qed.
 
Theorem wf_LexProd : well_founded LexProd.
Proof.
unfold well_founded ; intro a.
destruct a.   
generalize b ; clear b.
replace (forall b : B, Acc LexProd (a, b)) with (P a) ; auto.
apply (well_founded_induction_type wf_leA P) ; intros.
apply wfPrincA ; auto.
Qed.
End LexProd.


Section LexProd3.

Variable B C D: Type.
Variable ltB : B -> B -> Prop.
Variable ltC : C -> C -> Prop.
Variable ltD : D -> D -> Prop.

Variable wf_ltB : well_founded ltB.
Variable wf_ltC : well_founded ltC.
Variable wf_ltD : well_founded ltD.


Definition LexProd3 :   B * C * D-> B * C * D-> Prop := LexProd (B*C) D  (LexProd B C ltB ltC) ltD.

Lemma wf_LexProd3 : well_founded LexProd3.
Proof.
apply wf_LexProd ; auto.
apply wf_LexProd ; auto.
Qed.

End LexProd3.

Section Subrel.

Variable A : Type.

Definition subRel  ( S R : A -> A -> Prop) : Prop := 
forall x y, S x y -> R x y.


Theorem subrel_wf : forall R S, well_founded R -> subRel S R -> well_founded S.
Proof.
constructor.
generalize (well_founded_induction H (fun a => forall y, S y a -> Acc S y)) ; intros.
eapply H1 ; clear H1; eauto ; intros.
unfold subRel in H0.
specialize (H0 _ _ H3).
specialize(H1 _ H0).
constructor ; auto.
Qed.

End Subrel.

Ltac inj_pair2 :=
repeat match goal with
  | H : existT ?P ?p _ = existT ?P ?p _ |- _ => apply inj_pair2 in H
  end.

Module LogicMod(ST: SigMod) .
 Import ST. 

Definition SymState := State -> Prop.
Definition top : SymState := fun _ => True.
Definition bot : SymState := fun _ => False.
Definition cnj(p q :SymState) := fun s => p s /\ q s.
Definition dsj(p q :SymState) := fun s => p s \/ q s.
Definition neg (p:SymState) := fun s => ~ p s.
Definition imp(p q :SymState) := forall s, p s -> q s.

Lemma imp_trans : forall p q r,  imp p q -> imp q r -> imp p r.
Proof.  
unfold imp ;intros.
apply H0, H ; auto.
Qed.

Lemma imp_refl : forall p, imp p p. 
Proof.
unfold imp ; intros ; auto.  
Qed.

Definition symTrans(q:SymState) := fun s => exists s', q s' /\ trans s' s.

Lemma symTrans_mono : forall p q,  imp p q -> imp (symTrans p) (symTrans q).
Proof.
unfold imp, symTrans ; intros.
destruct H0 as [s' [Hp Htr]].
exists s'; split ; auto.
Qed.

Definition final : SymState := fun s => forall s', ~trans s s'.

Inductive seq  : Type :=
| one : forall s:State , seq
| add : State -> seq  -> seq.                                          

Definition head(sq : seq) : State :=
  match sq with
    | one s => s
    | add s _ => s
   end.

Fixpoint nth(n:nat)(sq:seq) : option State :=
  match n,sq with
  |0,  one s => Some s
  |0,  add s _  => Some s                    
  |S n', add _ tau' => nth n' tau'
  |_,_ => None
 end.           

Fixpoint suffix(n:nat)(sq:seq) : option seq :=
  match n,sq with
  |S n', add _ tau' => suffix n' tau'   
  |0, _ => Some sq
  |_,_ => None
 end.           

Lemma nth_suffix_nth  :
  forall n m s tau tau', suffix n tau = Some tau' -> nth m tau' = Some s ->
  nth (n + m) tau = Some s.                                             
Proof.
 induction n ; intros.
* cbn in *. injection H ; intros ; subst ; assumption.
* destruct tau ; cbn in * ; try discriminate.
   eapply IHn ; eauto.  
Qed.

   Lemma nth_Some_suffix : forall n sq s',  nth n sq = Some s' ->  exists sq', suffix n sq = Some sq'.
Proof.
induction n  ; intros.
* destruct sq ; cbn in *.
  + injection H ; intros ; subst.  
    now exists (one s').  
  + injection H ; intros ; subst.  
      now exists (add s' sq).  
 * destruct sq ; cbn in *  ; try discriminate.
    eapply IHn ; eauto.
Qed.

Lemma head_nth_suffix : forall n sq  sq' s,
    suffix n sq = Some sq' ->
    nth n sq = Some s ->
    s = head sq'.
Proof.
induction n ; intros.
 * destruct sq ; cbn in *.
    +injection H0 ; injection H ; intros  ; subst ; reflexivity.
    +injection H0 ; injection H ; intros  ; subst ; reflexivity.
*  destruct sq ; cbn in * ; try discriminate.
   eapply IHn; eauto.
Qed.

Definition length(tau:seq) : nat.
induction tau.
* exact 0.
* exact (S IHtau).   
Defined.

Lemma length_add : forall s tau,  length(add s tau) = S (length tau).
Proof.
  intros.
 reflexivity.
Qed.

Lemma length_suffix : forall n sq sq' ,
  suffix n sq = Some sq' -> n + length sq'   = length sq.
Proof.
induction n; intros.
* injection H ; intros; subst ; reflexivity.
*  destruct sq ; try discriminate.
   rewrite length_add.
   rewrite <- (IHn _ _ H).
   lia.   
Qed.

 Inductive isPath: seq -> Prop :=
|path_one : forall s,  final s -> isPath (one s)
|path_add : forall s sq,  trans s (head sq) -> isPath sq -> isPath (add s sq).
 
Lemma isPath_suffix : forall n sq  sq' ,  isPath sq -> suffix n sq = Some sq' -> isPath sq'.
Proof.
 induction n ; intros.
* destruct sq; cbn in *.
   + injection H0 ; intros ; subst.
      inversion H0 ; subst ; auto.
   + injection H0 ; intros ; subst ; auto.
 *   destruct sq; cbn in *.
     + discriminate.
     + inversion H ; subst.
       apply IHn with sq ; auto.
Qed.

Inductive reach : seq -> SymState -> Prop :=
|reach_now_one : forall s (r:SymState),  r s-> reach (one s) r
|reach_now_add : forall s tau (r:SymState),   r s-> reach (add s tau) r
|reach_later : forall s tau (r:SymState),  reach tau r -> reach (add s tau) r.

Inductive Rlf:Type  :=
| rlf: forall p q: SymState, Rlf.

Notation "l  =><> r"  := (rlf  l r) (at level 100).                              

Definition lhs (f : Rlf) := match f with (l  =><> _)  => l end.
Definition rhs (f : Rlf) := match f with (_  =><> r)  => r end.

Definition sat tau f : Prop := isPath tau  /\  (lhs f) (head tau) /\ reach tau (rhs f).

Lemma sat_trv : forall tau (r:SymState),  isPath tau ->   r (head tau) -> sat tau (r =><> r).
Proof.
  intros tau r HisPath.
  repeat split  ; auto ; cbn.
  destruct tau;  constructor ; auto.
Qed.
  
Lemma sat_str : forall (l:SymState) l' r tau, l (head tau) -> sat tau (l' =><> r) -> sat tau (l =><> r).
Proof.
intros  l l' r tau  Hhead Hsat.
destruct Hsat as (HisPast & Hinit & Hreach) ; cbn in *.
repeat split; auto ; cbn.
Qed.

Lemma sat_dsj_1  : forall l1 l2 r tau,  sat tau (l1 =><> r) -> sat tau ((dsj l1 l2) =><>  r).
Proof.
  intros l1 l2 r tau Hsat.
  destruct Hsat as (HisPast & Hinit & Hreach) ; cbn in *.
  repeat split; auto ; cbn.
  left ; auto.  
Qed.

Lemma sat_dsj_2 : forall l1 l2 r tau,  sat tau (l2 =><> r) -> sat tau ((dsj l1 l2) =><>  r).
Proof.
  intros l1 l2 r tau Hsat.
  destruct Hsat as (HisPast & Hinit & Hreach) ; cbn in *.
  repeat split; auto ; cbn.
  right ; auto.  
Qed. 

Lemma sat_dsj : forall l1 l2 r tau,
(sat tau (l1 =><> r) \/  sat tau (l2 =><> r))-> sat tau ((dsj l1 l2) =><>  r).

Proof. 
intros l1 l2 r tau [Hsat | Hsat].
* apply sat_dsj_1; auto.
* apply sat_dsj_2; auto.  
Qed.

Lemma sat_exn : forall tau  l r,  sat tau (l =><> r) -> l (head tau) /\ exists n s,  nth n tau = Some s /\ r s.
Proof.
intros tau.  
induction tau ; intros  l r Hsat.
* destruct Hsat as (HisPath & Hinit & Hreach) ; cbn in *.
  inversion Hreach ;  subst ; split; auto.
  now exists 0, s.
*  destruct Hsat as (HisPath & Hinit & Hreach) ; cbn in *.
   inversion Hreach ; subst ; split ; auto.
   +    now exists 0, s.
   + inversion HisPath ; subst.
     assert (Hsat : sat tau (symTrans  l =><> r)).
     {  repeat split ; auto  ; cbn.   now exists s.  }  
     destruct (IHtau _ _ Hsat) as (Hsym &  k' & s' & Hnths & Hr).
     now exists (S k'),  s'.     
Qed.

Lemma exn_sat : forall tau, isPath tau   ->  forall (l r:SymState) n s, l(head tau) -> nth n tau = Some s -> r s ->  sat tau (l =><> r) .
Proof.
intros tau  HisPath.
induction tau ; intros  l r n sn Hsome Hnth Hr.
* destruct n ; cbn in *; try discriminate.
   injection Hnth ; intros ; subst.
   repeat split; auto ; cbn.
   constructor  ; auto.
* destruct  n ; cbn in *.
   +injection Hnth ; intros ; subst.
    repeat split; auto ; cbn.
    constructor 2 ; auto.
   + inversion HisPath ; subst.
     assert (Hsym : (symTrans l) (head tau)).
     {
       now exists s.  
     }
     specialize (IHtau H2  _ _ _ _ Hsym Hnth Hr).
     repeat split ; auto ; cbn.
     destruct (classic (r s)).
     - constructor 2 ; auto.
     - constructor 3.       
       destruct IHtau as (HisPath' & (s' & Hs' & Htrans')  &  Hreach') ; auto.
Qed.

Lemma sat_tra : forall l r m n tau tau',
    isPath tau -> 
    sat tau (l =><> m) ->
    suffix n tau = Some tau' -> sat tau' (m =><> r)
    -> sat tau (l =><> r).
Proof.
  intros l r  m  n tau tau' HisPath  Hsat1 Hsome Hsat2.
  apply sat_exn in Hsat1 ; auto.
  apply sat_exn in Hsat2 ; auto.
   destruct Hsat1 as (Hl & k1 & sk1 & Hnth1 & Hm).
    destruct Hsat2 as (H'm & k2 & sk2 & Hnth2 & Hr).        
    eapply exn_sat with (n + k2) sk2 ; auto.
    apply nth_suffix_nth with tau' ; auto.
Qed.

Lemma sat_stp : forall tau (l:SymState) r s,
    l s -> isPath (add s tau) -> sat tau (symTrans l =><> r) -> sat( add s tau) (l =><> r).
Proof.
  intros tau l r s Hl HisPath Hsat.
  repeat split ; cbn ; auto.
   destruct Hsat as (HisPath' &  (s' & Hs' & Htrans')  & Hreach') ; cbn in *.
   constructor 3 ; auto.
 Qed.

Definition valid(f:Rlf) : Prop :=
  forall tau,   isPath tau  -> (lhs f) (head tau) -> reach tau (rhs f).

Lemma valid_sat : forall f,  valid f -> forall tau,  isPath tau -> (lhs f) (head tau) -> sat tau f.
Proof.
intros (l,r) Hval tau HisPath  Hstart ; cbn in *.
specialize (Hval _ HisPath  Hstart) ; cbn in *.
repeat split ; auto.
Qed.

Lemma sat_valid : forall f,  ( forall tau,  isPath tau -> (lhs f) (head tau) -> sat tau f) -> valid f.
Proof.
intros (l,r) Htau ; cbn in *.
unfold valid ; intros ; cbn in *.
specialize (Htau _ H H0).
 destruct Htau as (HisPath & Hinit & Hreach) ; auto.
Qed.

Inductive proof :  list (bool*Rlf ) -> (bool*Rlf ) -> Type :=
| Trv :  forall H r b ,  proof  H (b, r=><> r)
| Hyp: forall H1 H2 f, proof (H1 ++ [(false,f)] ++ H2) (true,f)
| Str :  forall H l l' r b,
    imp  l l' ->
    proof H (b, l'=><> r) ->
    proof H (b, l =><> r)
| Spl : forall H l1 l2 r b,
    proof H (b, l1 =><> r) ->
    proof H (b, l2 =><> r) ->
    proof H (b, ((dsj l1 l2) =><> r))
| Tra : forall H l m r b,
    proof H (b, l =><> m) ->
    proof H (b, m =><> r) ->
    proof H (b, (l =><> r))
| Stp : forall H l r b,
    imp (cnj l final) bot ->
    proof H (true, (symTrans l =><> r)) ->
    proof H (b, l =><> r)  
| Cof : forall H f b,
    proof ((false,f)::H) (false,f) ->
    proof H (b,f)
| Cut : forall H b f f',
    proof H (false,f') ->
    proof ((false,f') :: H) (b,f) ->
    proof H (b,f)          
|Clr : forall H1 H2 h f,
    proof (H1++ H2) f ->
    proof (H1 ++ [h] ++ H2) f.

Fixpoint size H f  (p:proof H f) :=
  match p with
  | Trv _ _ _  => 1
  | Hyp _ _ _ => 1
  | Str _ _  _ _ _   _ Hpr => S (size _ _  Hpr)
  | Spl _ _ _ _ _ Hpr1 Hpr2 => S ((size _ _ Hpr1) +  (size _ _ Hpr2))
  | Tra _ _ _ _ _ Hpr1 Hpr2 => S ((size _ _ Hpr1) +  (size _ _ Hpr2))
  | Stp _ _ _ _ _ Hpr =>  S (size _ _  Hpr)                        
  | Cof _ _ _ Hpr => S (size _ _ Hpr)
  | Cut _ _ _ _ Hpr1 Hpr2 =>   S ((size _ _ Hpr1) +  (size _ _ Hpr2))                
  | Clr _ _ _ _ Hpr => S (size _  _ Hpr)                      
  end.

Inductive subproof:  forall H'  f' p' H f p,  Type :=
|subproof_str: forall H l l' r b Himp  Hpr,
     subproof H (b,l' =><> r) Hpr H (b,l =><> r) (Str H l l' r b   Himp Hpr)
| subproof_spl_l: forall H l1 l2 r b  Hpr1 Hpr2,
    subproof H (b, l1 =><> r) Hpr1 H (b, (dsj l1 l2) =><> r) (Spl H l1 l2 r b Hpr1 Hpr2)
| subproof_spl_r: forall H l1 l2 r b  Hpr1 Hpr2,
    subproof H (b, l2 =><> r) Hpr2 H (b, (dsj l1 l2) =><> r) (Spl H l1 l2 r b Hpr1 Hpr2)
| subproof_tra_l: forall H l m r b  Hpr1 Hpr2,
    subproof H (b, l =><> m) Hpr1 H (b, l =><> r) (Tra H l m r b Hpr1 Hpr2)
| subproof_tra_r: forall H l m r b  Hpr1 Hpr2,
    subproof H (b, m =><> r) Hpr2 H (b, l =><> r) (Tra H l m  r b Hpr1 Hpr2)             
|subproof_stp : forall H l r b  Himp Hpr,
    subproof H  (true, symTrans l =><> r) Hpr H (b,  l =><> r) (Stp H l r b  Himp Hpr)
|subproof_cof : forall H f b Hpr,   subproof ((false,f)::H) (false,f)  Hpr H (b,f) (Cof H f b Hpr)
|subproof_cut1 : forall H b f f' Hpr1 Hpr2,  subproof  H  (false,f') Hpr1 H (b,f) (Cut H b f f' Hpr1 Hpr2)
|subproof_cut2 : forall H b f f' Hpr1 Hpr2,  subproof  ((false,f')::H)   (b,f) Hpr2 H (b,f) (Cut H b f f' Hpr1 Hpr2)                                                            
|subproof_clr : forall H1 H2 h f Hpr,
    subproof (H1++ H2) f Hpr  (H1 ++ [h] ++ H2) f (Clr H1 H2 h f Hpr).

                                             
Lemma  subproof_size :  forall H'  f' p' H f p,
                     subproof H' f' p' H  f p -> size H' f' p' < size H f p .
Proof.
intros H' f' p' H f p Hsub.  
induction Hsub ; cbn ; try lia.
Qed.

Inductive subproof_star :  forall H'  f' p' H f p,  Type :=
|subproof_star_refl : forall H f p,  subproof_star H f p H f p
|subproof_star_step : forall   H f p H'  f' p' H'' f'' p''   ,
    subproof H' f' p' H'' f'' p'' -> subproof_star H'' f'' p'' H f p -> subproof_star H' f' p' H  f p.

Lemma  subproof_star_size :  forall H'  f' p' H f p,
                     subproof_star H' f' p' H  f p -> size H' f' p' <=  size H f p .
Proof.
intros H' f' p' H f p Hsub.  
induction Hsub ; cbn ; try lia.
* apply subproof_size  in s; auto;  lia.
Qed.

Inductive subproof_plus :  forall H'  f' p' H f p,  Prop :=
|subproof_plus_one : forall H' f' p' H f p,  subproof H' f' p' H f p -> subproof_plus H' f' p' H f p
|subproof_plus_step : forall   H f p H'  f' p' H'' f'' p''   ,
    subproof H' f' p' H'' f'' p'' -> subproof_plus H'' f'' p'' H f p -> subproof_plus H' f' p' H  f p.

Lemma  subproof_plus_size :  forall H'  f' p' H f p,
                     subproof_plus H' f' p' H  f p -> size H' f' p' < size H f p .
Proof.
intros H' f' p' H f p Hsub.  
induction Hsub ; cbn ; try lia.
* apply subproof_size  ; auto.
* apply subproof_size in X ;  lia.
Qed.

Fixpoint InT {A:Type} (a:A) (l:list A)  {struct l} : Type :=
  match l with
  | [] => False
  | a' :: m => InT a m + {a = a'}
  end.

Lemma InT_app{A:Type} : forall l1 l2 a,  InT(A:=A) a  (l1 ++ [a] ++ l2).
Proof.
  induction l1 ; intros.
  * right ; reflexivity.
  * left. apply IHl1.
Qed.

Lemma app_InT{A:Type} : forall l1 l2 a,  InT(A:=A) a  (l1 ++ l2) -> InT a l1 +  InT a l2.
Proof.
  induction l1 ; intros.
  * right ; auto.
  * inversion X ; subst; auto.
    destruct (IHl1 _ _ X0).
    + left ; constructor; auto.
    +  right ; auto.
    +  left ;constructor 2; auto.
Qed.

Lemma app_InT_l{A:Type} : forall l1 l2 a,  InT a l1 -> InT(A:=A) a  (l1 ++ l2).
Proof.
  induction l1 ; intros.
  * inversion X.
  * inversion X ; subst; auto.
   + 
     rewrite <- app_comm_cons.
     constructor.
     apply IHl1; auto.
   +  rewrite <- app_comm_cons.
        constructor 2 ; reflexivity.
Qed.


Lemma app_InT_r{A:Type} : forall l1 l2 a,  InT a l2 -> InT(A:=A) a  (l1 ++ l2).
Proof.
  induction l1 ; intros ; auto.
  rewrite <- app_comm_cons.
  constructor.
apply IHl1 ; auto.
Qed.

Lemma Int_In{A:Type} : forall  l a,  InT a l -> In (A:=A) a l. 
Proof.
  induction l ; intros.
 * inversion X.
 * inversion X ; subst.
  + right; apply IHl; assumption.
  + left  ; reflexivity.
Qed.
    
Definition hypos_were_goals_or_init_or_valid : forall H' f' p' H f p,
    subproof_star H' f' p' H f p ->
    forall h',  InT h' H' -> {H'' & {p'' & subproof_star H'' h' p'' H f p}} + InT h' H + valid (snd h').
  intros H' f' p' H f p Hsub h' Hin.
  dependent induction Hsub ; subst.
 * left; right ; assumption. 
 *  remember p'' as Hpr.
   dependent induction  p''; cbn in *.
  +  subst ; inversion s.
  + subst ; inversion s.
  +  subst;     dependent induction s ; subst ; cbn in * ; apply IHHsub ; assumption.
  +  subst;     dependent induction s ; subst ; cbn in *; apply IHHsub ; assumption.
  +  subst;     dependent induction s ; subst ; cbn in *; apply IHHsub ; assumption.
  +  subst;     dependent induction s ; subst ; cbn in *; apply IHHsub ; assumption.
  +   clear IHp''.   inversion  s ; subst;  cbn in *;  inj_pair2 ; subst.
      - apply IHHsub ; assumption.
      -  apply IHHsub ; assumption.
      -  apply IHHsub ; assumption.     
      -  apply IHHsub ; assumption.
      -  apply IHHsub ; assumption.
      -  apply IHHsub ; assumption.
      - clear Hpr2 H11 Hpr3 H12 H5 H6.
        destruct Hin.
        ** apply IHHsub ; assumption.
        **   left; left ; subst.
             exists   ((false, f0) :: H0), p'.
             econstructor 2 ; eauto.
      - discriminate.
      - discriminate.  
      - discriminate.
   + clear IHp''1 IHp''2.
          subst;  inversion  s ; subst;  cbn in *;  inj_pair2 ; subst.    
      -  
         apply IHHsub ; assumption.
      - clear Hpr10  Hpr6 H14 Hpr8 H13 Hpr4 H12 Hpr7 H11 Hpr5 H6 H5 Hpr3.
        destruct Hin.
        ** apply IHHsub ; assumption.
        ** clear IHHsub.
             subst.
             left; left.
             exists   H0, p''1.
             econstructor 2 ; eauto.
             constructor.
   + subst;     dependent induction s ; subst ; cbn in *; apply IHHsub.
    rewrite <- x0.            
     apply app_InT in Hin.
           destruct Hin.
           - apply app_InT_l ; auto.
          -     apply app_InT_r.
                  constructor ; auto.          
Defined.

Definition goals H f p : Type := {H' & {f' & {p' & subproof_star H' f' p' H f p}}}.

Definition measure H f p (g:goals H f p) :nat.
Proof.
destruct g as (H' & f' & (p', Hsub)).
exact (size H' f' p').
Defined.

Definition getForm H f p (g:goals H f p) : Rlf.
  destruct g  as (_ & (_ & g) & _).
exact g.
Defined.

Definition dom H f p : Type := {tau & { g: _  &  isPath tau  & lhs(getForm H f p g) (head tau) }}. 

Definition getPath H f p (d:dom H f p) : seq.
Proof.
destruct d as (tau & _).
exact tau.
Defined.

Definition getGoal H f p (d:dom H f p) : goals H f p.
  destruct d as (_ & (g,_,_)).
exact g.
Defined.

Definition ord H f p : dom H f p -> dom H f p -> Prop.
  intros d1 d2.
  destruct d1 as (tau1 & (g1,Hfin1,Hsat1)).
  destruct d2 as (tau2 & (g2,Hfin2,Hsat2)).
  Search "lt_eq_lt_dec".
  destruct   (Compare_dec.lt_eq_lt_dec (length  tau1 ) (length tau2)) as [[Hlt | Heq ]| Hgt].
 *  exact True.
*   
  destruct g1 as  (H1 & (b1,f1) & p1 & Hsub1).
  destruct g2 as (H2 & (b2,f2) & p2 & Hsub2) ; cbn in *.
  destruct b1, b2.
   + exact (subproof_plus  H1 (true,f1) p1 H2 (true,f2) p2).
    + exact False. 
    +  exact True.
    +  exact (subproof_plus  H1 (false,f1) p1 H2 (false,f2) p2).
* exact False.
Defined.

Definition ordG H f p : goals H f p -> goals H f p -> Prop.
Proof.
  intros g1 g2.
destruct g1  as (H1 & f1 & (p1,Hsub1)).
destruct g2  as (H2 & f2 & (p2, Hsub2)).
exact (subproof_plus H1 f1 p1 H2 f2 p2).
Defined.

Lemma ordG_measure : forall H f p g1 g2,  ordG H f p g1 g2 -> measure H f p g1 < measure H f p g2.
Proof.
  intros.
unfold ordG in *.
  destruct g1  as (H1 & f1 & (p1,Hsub1)).
destruct g2  as (H2 & f2 & (p2, Hsub2)) ; cbn.
apply subproof_plus_size in H0 ; auto.
Qed. 

Lemma ordG_wf : forall H f p, well_founded (ordG H f p). 
Proof.
  intros.
  Search "well_founded_ltof".
  specialize (Wf_nat.well_founded_ltof (goals H f p) (fun g => measure H f p g)) ; intro Hwf.
  apply  (subrel_wf _  _  _ Hwf ); auto.
  intros g1 g2 HordG.
apply ordG_measure ; auto.
Qed.

Definition ordB : bool -> bool-> Prop :=
  fun b1 b2 =>  match b1, b2 with
                  | false, true => True
                  | _,_ => False                 
   end.             

Lemma ordB_wf : well_founded ordB.
Proof.
  constructor ; intros b ; destruct b ; intros.
  * inversion H; subst.
  * destruct a.
  -  constructor  ; intros.
     destruct y ;  inversion H0.
  - inversion H.
Qed.

Definition ordPBG H f p := LexProd3 nat bool (goals H f p) lt ordB (ordG H f p).

Lemma ordPBG_wf : forall H f p, well_founded(ordPBG H f p).
Proof.
  intros.
  apply wf_LexProd3.
  Search "lt_wf".
  * apply Wf_nat.lt_wf.
  * apply  ordB_wf .
  * apply ordG_wf.
Qed.

Definition mkGoal H f p :
forall Hg g pg (Hsub : subproof_star Hg g pg H f p),  goals H f p.
Proof.
  intros.
  unfold goals.
  exists Hg, g, pg.
  assumption.
Defined.

Definition destructG : forall H f p,  dom H f p -> nat * bool * (goals H f p). 
Proof.
  intros H f p d.
  destruct    d as (tau & (g,_,_)).
  destruct g  as (H' & (b',f') & (Hp,Hsub)).
 exact (length tau,b',  (mkGoal _ _ _   _ _ _ Hsub )).
Defined.

Lemma subrel_ord_ordPBG : forall H f p d1 d2,   ord H f p d1 d2 ->
  ordPBG H f p (destructG H f p d1) (destructG H f p d2).
Proof.
  intros H f p d1 d2 Hord.
  destruct d1 as (tau1 & (g1,Hfin1,Hsat1)).
  destruct d2 as (tau2 & (g2,Hfin2,Hsat2)).
  destruct g1  as (H1 & (b1,f1) & (Hp1,Hsub1)).
  destruct g2  as (H2 & (b2,f2) & (Hp2,Hsub2)).
  cbn in *.
unfold ord, ordPBG, destructG in  * ; cbn in *.
destruct ( Compare_dec.lt_eq_lt_dec (length tau1) (length tau2)) as [[Hlt | Heq ] | Hge] ; try lia.
  * do 2 constructor; auto.
  *  destruct b1, b2.
  +  rewrite Heq ; auto.
     constructor 2 ; intuition.
   +  inversion Hord.    
   + constructor.
      rewrite Heq .  constructor 2; auto.
   + rewrite Heq. constructor 2  ; auto.
Qed.             

Lemma ord_wf : forall H f p, well_founded (ord H f p).
Proof.
  intros H f p.
  specialize (wf_inverse_image _ _ _  (destructG H f p) (ordPBG_wf H f p)) ; intro Hwf.
  apply  (subrel_wf _  _  _ Hwf ); auto. 
unfold subRel ; intros.
apply subrel_ord_ordPBG ; auto.
Qed.

Definition mkDom H f p tau g  (HisPath : isPath tau)(Hinit :  lhs(getForm H f p g) (head tau) ) : dom H f p.
Proof.
  exists tau, g; try split  ; assumption.
Defined.

Lemma soundness_aux : forall H f p,
(forall h,  In h H  -> valid (snd h)) ->
    forall d, sat (getPath _ _ _ d) (getForm _ _ _  (getGoal H f  p d)).
Proof.
  intros H f p  Hinit.
apply (well_founded_ind (ord_wf H f p)).
intros d Hind.
destruct d as (tau & (g,HisPath, Hstart)) ; cbn in *.
destruct g as (H' & (b',f') & p' & Hsub') ; cbn in *.
remember p' as Hpr'.
dependent induction p' ; cbn in *.
* apply sat_trv  ; auto.
*specialize (InT_app H1 H2 (false,f')) ; intro Hin.
   subst.
   destruct   (hypos_were_goals_or_init_or_valid _ _ _ _ _ _ Hsub' _ Hin)
     as [[Hcase |  Hcase] | Hcase].
     + destruct Hcase as (H'' & p'' & Hsub).
       set (grich := mkGoal _ _ _  _ _ _ Hsub).
       set (d := mkDom _ _ _  _ grich  HisPath Hstart).
     specialize  (Hind d) ; cbn in Hind.
     destruct  (Compare_dec.lt_eq_lt_dec (length tau) (length tau)) as [[Hlt | Heq] | Hgt]  ; try lia.
     apply Hind ; auto.
  + specialize (Int_In _ _ Hcase) ; intro Hin'.
     specialize  (Hinit _ Hin'); cbn in *.
     apply valid_sat ; auto.
  +  apply valid_sat ; auto.
 * cbn in *;   clear IHp' ; subst.
   assert (Hsub : subproof_star H0 (b', l' =><> r) p'  H f p).
   {   econstructor 2 ; eauto ;   constructor. }
   assert (Hstart'   : l' (head tau)).
   { apply i ; auto. }
     set (grich := mkGoal _ _ _  _ _ _ Hsub) ; cbn in *.
   set (d := mkDom _ _ _  _ grich  HisPath Hstart') ; cbn in *.
   apply sat_str with l' ; auto.
   specialize (Hind d)  ; cbn in *.
    destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (length tau )) as [[Hlt | Heq] | Hgt]  ; try lia.
  destruct b' ; apply Hind; auto ; constructor ; constructor.
* cbn in *;   clear IHp'1 IHp'2 ; subst.
   
   assert (Hsub1 : subproof_star H0 (b', l1 =><> r) p'1  H f p).
   {     econstructor 2 ; eauto ;   constructor.  }
    assert (Hsub2 : subproof_star H0 (b', l2 =><> r) p'2  H f p).
   {  constructor 2 with H0  (b', (dsj l1 l2) =><> r) (Spl H0 l1 l2 r b' p'1 p'2) ; auto ; constructor.  } 
  set (grich1 := mkGoal _ _ _  _ _ _ Hsub1).
   set (grich2 := mkGoal _ _ _  _ _ _ Hsub2).
     apply sat_dsj.
   destruct Hstart as [Hstart | Hstart].
     +  left.
        set (d := mkDom _ _ _  _ grich1  HisPath Hstart) ; cbn in *.
         specialize (Hind d)  ; cbn in *.
    destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (length tau )) as [[Hlt | Heq] | Hgt]  ; try lia.
    destruct b' ; apply Hind; auto ; constructor ; constructor.
    +  right.
        set (d := mkDom _ _ _  _ grich2  HisPath Hstart) ; cbn in *.
         specialize (Hind d)  ; cbn in *.
    destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (length tau )) as [[Hlt | Heq] | Hgt]  ; try lia.
    destruct b' ; apply Hind; auto ; constructor ; constructor.
  * cbn in *;   clear IHp'1 IHp'2 ; subst.
     assert (Hlm : sat tau (l =><> m)).         
     {    assert (Hsub1 : subproof_star H0 (b', l =><> m) p'1  H f p).
       { econstructor 2 ; eauto ;   constructor. }
       set (grich1 := mkGoal _ _ _  _ _ _ Hsub1).
       set (d := mkDom _ _ _  _ grich1  HisPath Hstart) ; cbn in *.
        specialize (Hind d)  ; cbn in *.
        destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (length tau )) as [[Hlt | Heq] | Hgt]  ; try lia.
        destruct b' ; apply Hind; auto ; constructor ; constructor.
     }
     generalize Hlm.
     apply sat_exn in Hlm.
     destruct Hlm as (_ & n & s & Hnth & Hm).
     intro Hlm.
     generalize Hnth.
     apply nth_Some_suffix in Hnth ; auto.
     intro Hnth'.
     destruct Hnth as (tau' & HisPath').
     generalize HisPath'.
     apply isPath_suffix in HisPath'  ; auto.
     intro Hsuf'.
      specialize (head_nth_suffix  _ _ _ _  Hsuf' Hnth') ; intro Heq ; subst.
     assert (Hmr : sat  tau' (m =><> r)).
     {   assert (Hsub2 : subproof_star H0 (b', m =><> r) p'2  H f p).
           {   constructor 2 with H0  (b', l =><> r) (Tra H0 l m r b' p'1 p'2) ; auto ; constructor.
      }
       destruct n.
       -  injection Hsuf' ; intros; subst ; clear Hsuf'.
         set (grich2 := mkGoal _ _ _  _ _ _ Hsub2).
         set (d := mkDom _ _ _  _ grich2  HisPath Hm).
         specialize (Hind d)  ; cbn in Hind.
        destruct  (Compare_dec.lt_eq_lt_dec (length tau' ) (length tau' )) as [[Hlt | Heq] | Hgt]  ; try lia.
        destruct b' ; apply Hind; auto ; constructor ; constructor.              
       -
         set (grich2 := mkGoal _ _ _  _ _ _ Hsub2).
         set (d := mkDom _ _ _  _ grich2  HisPath' Hm).
         specialize (Hind d)  ; cbn in Hind.
         apply length_suffix in Hsuf'.
         assert (Hlt :length tau' < length tau) ; try lia.
         cbn in Hind.
         destruct  (Compare_dec.lt_eq_lt_dec (length tau') (length tau))  as [[Hlt' | Heq] | Hgt]  ;
           try lia.
          apply Hind; auto.
      }
     eapply sat_tra ; eauto.
 * cbn in *  ; clear IHp' ; subst.
    destruct tau.   
    +  inversion HisPath ; subst; cbn in *.
       exfalso ; apply (i s); split ; auto.
    + cbn in *.
      apply sat_stp ; auto.
      assert (Hsub2 : subproof_star H0 (true, symTrans l  =><> r) p' H f p).
           {  econstructor 2 ; eauto ; constructor. }
           set (grich:= mkGoal _ _ _  _ _ _ Hsub2).
           inversion HisPath  ; subst.
           assert (Hsym :  (symTrans l) (head tau) ).
           { now exists s.  }  
         set (d := mkDom _ _ _  _ grich  H4 Hsym); cbn in *.
           specialize (Hind d); cbn in Hind.
           replace ( (seq_rec (fun _ : seq => nat) (fun _ : State => 0)
           (fun (_ : State) (_ : seq) (IHtau : nat) => S IHtau) tau)) with (length tau) in Hind; try reflexivity.
         destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (S (length tau))) as [[Hlt' | Heq] | Hgt]  ; auto ; try lia.
  * cbn in *  ; clear IHp' ; subst.
      assert (Hsub : subproof_star ((false, f') :: H0)   (false, f')  p'  H f p).
       {     econstructor 2 ; eauto ;   constructor.  }
       set (grich := mkGoal _ _ _  _ _ _ Hsub).
       set (d := mkDom _ _ _  _ grich  HisPath Hstart) ; cbn in *.
        specialize (Hind d)  ; cbn in *.
        destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (length tau )) as [[Hlt | Heq] | Hgt]  ; try lia.
        destruct b' ; apply Hind; auto ; constructor ; constructor.
* cbn in *;   clear IHp'1 IHp'2 ; subst.
   assert (Hsub1 : subproof_star ((false, f'0) :: H0) (b', f') p'2  H f p).
   {     econstructor 2 ; eauto ;   constructor.  }
  set (grich1 := mkGoal _ _ _  _ _ _ Hsub1).
   set (d := mkDom _ _ _  _ grich1  HisPath Hstart) ; cbn in *.
    specialize (Hind d)  ; cbn in *.
    destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (length tau )) as [[Hlt | Heq] | Hgt]  ; try lia.
    destruct b' ; apply Hind; auto ; constructor ; constructor.
  * cbn in *  ; clear IHp' ; subst.
      assert (Hsub : subproof_star (H1 ++ H2)   (b', f')  p'  H f p).
       {     econstructor 2 ; eauto ;   constructor.  }
       set (grich := mkGoal _ _ _  _ _ _ Hsub).
       set (d := mkDom _ _ _  _ grich  HisPath Hstart) ; cbn in *.
        specialize (Hind d)  ; cbn in *.
        destruct  (Compare_dec.lt_eq_lt_dec (length tau ) (length tau )) as [[Hlt | Heq] | Hgt]  ; try lia.
        destruct b' ; apply Hind; auto ; constructor ; constructor.
Qed.
                  
Lemma  soundness_gen : forall H f,  (forall h,  In h H  -> valid (snd h)) ->
proof H f  -> valid (snd f).
Proof.
  intros H f Hhyp Hproof.
 specialize (soundness_aux _ _ Hproof Hhyp) ; intros.
 assert (Hsub : subproof_star H f Hproof H f Hproof) ; try   constructor.
 destruct f as (i,f) ;
 intros tau HisPath Hstarts; cbn in *.
 set (grich:= mkGoal _ _ _  _ _ _ Hsub).
 set (d := mkDom _ _ _  _ (mkGoal _ _ _  _ _ _ Hsub)  HisPath Hstarts).
 specialize (H0 d) ; cbn in *.
destruct H0 ; intuition.
Qed.

Definition proved f := proof [] (false,f).

Theorem soundness : forall f,  proved f -> valid f.
Proof.
intros f Hpr.  
apply (soundness_gen [] (false,f)) ; auto.
intros H Habs ; inversion Habs.
Qed.



Section CompleteStrategy.
  Variable l  r  q : SymState.
  Hypothesis Hinit : imp  l (dsj q r).
  Hypothesis Hnonblock : imp (cnj q final) bot.
  Hypothesis HquasiInv : imp (symTrans q) (dsj q r).

Lemma strategy : proved(l =><> r).
Proof.
apply Str with (dsj q r) ; auto.
  apply Cof. (* like doing a cofix *)
  apply Spl ; cbn. 
  * apply Stp  ; auto.
    apply Str with (dsj q r) ; auto.
    apply (Hyp [] []).
  * apply Trv.
Qed.

End CompleteStrategy.


        
(* we now prove that a "q" like above always exists for valid rlfs *)
Definition coReach(r:SymState) : SymState :=
  fun s => ~ r s /\ forall tau, s = head tau-> isPath tau -> reach tau r.

Lemma init : forall f, valid f -> imp (lhs f) (dsj (coReach (rhs f)) (rhs f)).
Proof.
  unfold valid, coReach, imp, dsj; intros.
  destruct f as (l,r) ; cbn in *.
  destruct (classic (r s)) ; auto.
  left ; split; auto ; intros ; subst.
   apply H; auto.    
Qed.

Lemma nonBlock : forall r,  imp (cnj (coReach r) final) bot.
Proof.
  unfold imp, cnj, coReach, bot ; intros.
  do 2 destruct H.
  assert (isPath (one s)).
  * constructor ; auto.
  *  specialize (H1 (one s) (refl_equal _) H2).
     inversion H1; subst ; intuition.
Qed.

Lemma quasiInv : forall r, imp (symTrans (coReach r)) (dsj  (coReach r) r).
Proof.
  unfold imp, symTrans, coReach, dsj; intros.
  destruct H as [s' [[Hnr Hreach] Htrans]].
  destruct (classic (r s)) ; auto.
  left  ; split ; auto ; intros ; subst.
  assert (reach (add s' tau) r).
  * apply Hreach ; try reflexivity.
    constructor ; auto.
  *  inversion H0 ; subst ; intuition.
Qed.

Theorem completeness : forall f,  valid f -> proved f.
  intros.
  destruct f as (l,r).
  apply strategy with (coReach r).
  * apply (init (l =><> r))  ; auto.
  *  apply nonBlock.
  *  apply quasiInv.
 Qed.    



Section MutualCompStrategy.
  Variables f1 f2 : Rlf.
  Variable H :   list (bool*Rlf).
  Hypothesis H1 : proof( (false, f1)::H) (false, f2).
  Hypothesis H2 : proof( (false, f2) :: H) (false, f1). 

 Lemma MutCompStrat : proof H (false,f1).
apply Cof.
 apply Cut with f2 ; auto.
 apply  (Clr [(false,f2)] H) ; auto.
 Qed.
 
End MutualCompStrategy.

End LogicMod.
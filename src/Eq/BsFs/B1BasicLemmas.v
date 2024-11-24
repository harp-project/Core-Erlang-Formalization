From CoreErlang.Eq.Tactics Require Export T1ParamZero.
From CoreErlang.Eq.Tactics Require Export T2ParamSingle.
From CoreErlang.Eq.Tactics Require Export T3ParamMultiple.
From CoreErlang.Eq.Tactics Require Export T4Name.
From CoreErlang.Eq.Tactics Require Export T5Transform.
From CoreErlang.Eq.Tactics Require Export T6Destruct.
From CoreErlang Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.

Import BigStep.

(* STRUCTURE:
* List
  - length_lt_split
  - cons_app
* Injection
  - cons_inj
  - vcons_inj
  - vtuple_inj
  - vmap_inj
*)












Section List.



  Lemma cons_app :
    forall T (x : T) (l : list T),
      x :: l = [x] ++ l.
  Proof.
    trv.
  Qed.



  Lemma length_lt_split :
    forall A B (al : list A) (bl : list B),
        length al < length bl
    ->  exists bl1 bl2 : list B,
            bl = bl1 ++ bl2
        /\  length bl1 = length al.
  Proof.
    (* #1 Exists: intro/exists/split *)
    itr - A B al bl Hl.
    exi - (firstn (length al) bl)
          (skipn (length al) bl).
    spl.
    * (* #2.1 Equality: rewrite *)
      by rewrite take_drop.
    * (* #2.2 Length: rewrite/reflexivity/lia *)
      rwr - firstn_length_le.
      - rfl.
      - lia.
  Qed.



End List.









Section Injection.



  Lemma cons_inj :
    forall
      (T : Type)
      (x y : T)
      (xs ys : list T),
        x :: xs = y :: ys
    ->  x = y /\ xs = ys.
  Proof.
    (* #1 Inversion: intro/inversion/auto + clear *)
    itr.
    ivc - H.
    ato.
  Qed.



  Lemma vcons_inj :
    forall
      (T : Type)
      (f : T -> Val)
      (x1 x2 : T)
      (y : Val),
        Syntax.VCons (f x1) (f x2) = y
    ->  exists z1 z2,
            (f x1) = z1
        /\  (f x2) = z2
        /\  y = Syntax.VCons z1 z2.
  Proof.
    (* #1 Exists: intro/exists/auto *)
    itr.
    exi - (f x1) (f x2).
    ato.
  Qed.



  Lemma vtuple_inj :
    forall
      (T : Type)
      (f : T -> Val)
      (x : T)
      (xl : list T)
      (y : Val),
        Syntax.VTuple ((f x) :: (map f xl)) = y
    ->  exists z zl,
            (f x) = z
        /\  (map f xl) = zl
        /\  y = Syntax.VTuple (z :: zl).
  Proof.
    (* #1 Exists: intro/exists/auto *)
    itr.
    exi - (f x) (map f xl).
    ato.
  Qed.



  Lemma vmap_inj :
    forall
      (T : Type)
      (f : T -> Val)
      (x1 x2 : T)
      (xll : list (T * T))
      (y : Val),
        Syntax.VMap (((f x1), (f x2)) :: (map (prod_map f f) xll)) = y
    ->  exists z1 z2 zll,
            (f x1) = z1
        /\  (f x2) = z2
        /\  (map (prod_map f f) xll) = zll
        /\  y = Syntax.VMap ((z1, z2) :: zll).
  Proof.
    (* #1 Exists: intro/exists/auto *)
    itr.
    exi - (f x1) (f x2) (map (prod_map f f) xll).
    ato.
  Qed.



End Injection.
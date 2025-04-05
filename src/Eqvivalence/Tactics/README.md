# Tactics

## Zero Parameters

`src/Eqvivalence/Tactics/T1ParamZero.v`

- rfl → reflexivity
- asm → assumption
- dis → discriminate
- con → congruence
- spl → split
- lft → left
- rgt → right
- sbt → subst
- trv → trivial
- ato → auto
- tau → tauto
- itu → intuition
- fro → firstorder
- feq → f_equal
- ceq → case_eq
- adm → admit
- sli → simpl; lia
- cli → cbn; nia
- sni → simpl; cia
- cni → cbn; nia

## Single Parameters

`src/Eqvivalence/Tactics/T2ParamSingle.v`

- inj → injection;
  - - constr {as ident}
- exa → exact
  - - constr
- eea → eexact
  - - constr
- app → apply
  - - constr {as ident} {in hyp}
  - + constr as ident in hyp
  - - contr in hyp as ident
  - + contr in hyp as ident
  - - constr : tactic {|> tactic}
  - - constr :- tactic {|> tactic}
  - > constr {as ident} {in hyp}
  - < constr as ident in hyp
  - < contr in hyp as ident
  - > constr : tactic {|> tactic}
  - > constr :- tactic {|> tactic}
- epp → eapply
  - - constr {as ident} {in hyp}
  - + constr as ident in hyp
  - - contr in hyp as ident
  - + contr in hyp as ident
  - - constr : tactic {|> tactic}
  - - constr :- tactic {|> tactic}
  - > constr {as ident} {in hyp}
  - < constr as ident in hyp
  - < contr in hyp as ident
  - > constr : tactic {|> tactic}
  - > constr :- tactic {|> tactic}
- ass → assert
  - > constr {as ident} {by tactic}
  - > constr {as ident} {: tactic}
  - - as ident > constr {by tactic}
  - - as ident > constr {: tactic}
  - - as ident by tactic > constr
  - - as ident : tactic > constr
  - - by tactic > constr
  - - : tactic > constr
- des → destruct
  - - ident {as {simple_intropattern} {ident}} {: tactic {|> tactic}}
  - - ident {as {simple_intropattern} {ident}} {:- tactic {|> tactic}}
  - - ident {as {simple_intropattern} {ident}} {:> tactic}
  - > constr {as {simple_intropattern} {ident}} {: tactic {|> tactic}}
  - > constr {as {simple_intropattern} {ident}} {:-tactic {|> tactic}}
  - > constr {as {simple_intropattern} {ident}} {:> tactic}
- ind → induction
  - - ident {as simple_intropattern} {: tactic {|> tactic}}
  - - ident {as simple_intropattern} {:- tactic {|> tactic}}
  - - ident {as simple_intropattern} {:> tactic}
  - ~ constr - ident {: tactic {|> tactic}}
  - ~ constr - ident {:- tactic {|> tactic}}
  - ~ constr - ident {:> tactic}
  - > constr {as simple_intropattern} {: tactic {|> tactic}}
  - > constr {as simple_intropattern} {:-tactic {|> tactic}}
  - > constr {as simple_intropattern} {:> tactic}
- cns → constructor
  - 
  - : tactic {|> tactic}
  - :- tactic {|> tactic}
  - :> tactic
- ens → econstructor
  - 
  - : tactic {|> tactic}
  - :- tactic {|> tactic}
  - :> tactic
- trn → transitivity
  - 
  - : tactic {|> tactic}
  - :- tactic {|> tactic}
  - :> tactic
- ern → etransitivity
  - 
  - : tactic {|> tactic}
  - :- tactic {|> tactic}
  - :> tactic
- cma → case\_match
  - 
  - |1: tactic {|> tactic}
  - |2: tactic {|> tactic}
  - : tactic {|> tactic}
  - :- tactic {|> tactic}
  - :> tactic

## Multiple Parameters

`src/Eqvivalence/Tactics/T3ParamMultiple.v`

- itr → intros
  - 
  - - [ident]:1-20
- exi → exists
  - 
  - - [constr]:1-20
- eei → eexists
- rev → revert
  - - [ident]:1-20
- gen → generalize dependent
  - - [ident]:1-20
- clear\_refl
- clr → clear
  - - [ident]:1-10
  - + [ident]:1-10
- sym → symmetry
  - 
  - *
  - - [ident]:1-10
  - + [ident]:1-10
- smp → simple
  - 
  - *
  - - [ident]:1-10
  - + [ident]:1-10
  - ~ constr
  - ~ constr - ident
- sbn → cbn
  - 
  - *
  - - [ident]:1-10
  - + [ident]:1-10
- fld → fold
  - - [constr]:1-8
  - - [constr]:1-8 in *
  - - [constr]:1-8 in [hyp]:1-5
  - + [constr]:1-8 in [hyp]:1-5
- ufl → unfold
  - - [constr]:1-8
  - - [constr]:1-8 in *
  - - [constr]:1-8 in [hyp]:1-5
  - + [constr]:1-8 in [hyp]:1-5
- rfl → refold: (unfold; fold)
  - - [constr]:1-8
  - - [constr]:1-8 in *
  - - [constr]:1-8 in [hyp]:1-5
  - + [constr]:1-8 in [hyp]:1-5
- tfl → tryfold: (try unfold; fold)
  - - [constr]:1-8
  - - [constr]:1-8 in *
  - - [constr]:1-8 in [hyp]:1-5
  - + [constr]:1-8 in [hyp]:1-5

## Name

`src/Eqvivalence/Tactics/T4Name.v`

- ren → rename
  - - N:[ident]:1-10 : N:[ident]:1-10
- rep → replace
  - - N:[constr]:1-10 : N:[constr]:1-10
- rep → replace
  - - N:[ident]:1-10 : N:[constr]:1-10
  - - N:[ident]:1-10 : N:[constr]:1-10 as N:[ident]:1-10
  - - N:[ident]:1-10 as N:[ident]:1-10 : N:[constr]:1-10
- ivr → inversion
  - - [hyp]:1-10
  - - hyp as simple_intropattern
  - - hyp as N:[ident]:1-10 : N:[ident]:1-10
- ivs → inversion; subst
  - - [hyp]:1-10
  - - hyp as simple_intropattern
  - - hyp as N:[ident]:1-10 : N:[ident]:1-10
- ivc → inversion; subst; clear
  - - [hyp]:1-10
  - - hyp as simple_intropattern
  - - hyp as N:[ident]:1-10 : N:[ident]:1-10

## Transform

`src/Eqvivalence/Tactics/T5Transform.v`

- spe → specialize
  - - hyp {as ident}: [constr]:1-20
  - + hyp as ident: [constr]:1-20
- spe\_rfl → specialize (eq_refl)
  - - [hyp]:1-5
- pse → pose proof
  - - constr {as ident}: [constr]:1-20
- rwr → rewrite ->
  - - [constr]:1-10
  - - [constr]:1-10 in *
  - - [constr]:1-10 in [hyp]:1-5
  - + [constr]:1-10 in [hyp]:1-5
- rwl → rewrite <-
  - - [constr]:1-10
  - - [constr]:1-10 in *
  - - [constr]:1-10 in [hyp]:1-5
  - + [constr]:1-10 in [hyp]:1-5

## Clear

`src/Eqvivalence/Tactics/T6Clear.v`

- ivr → inversion; clear
  - - hyp as simple_intropattern / M:[ident]:0-10
  - - hyp as N:[ident]:1-10 : N:[ident]:1-10 / M:[ident]:0-10
- ivs → inversion; subst; clear
  - - hyp as simple_intropattern / M:[ident]:0-10
  - - hyp as N:[ident]:1-10 : N:[ident]:1-10 / M:[ident]:0-10
- ivc → inversion; subst; clear; clear
  - - hyp as simple_intropattern / M:[ident]:0-10
  - - hyp as N:[ident]:1-10 : N:[ident]:1-10 / M:[ident]:0-10
- spc → specialize; clear
  - - hyp {as ident}: [constr]:1-20
  - + hyp as ident: [constr]:1-20
  - - hyp: [constr]:1-5 / [ident]:1-5
- psc → pose proof; clear
  - - constr {as ident}: [constr]:1-20
  - - hyp: [constr]:1-5 / [ident]:1-5
- cwr → rewrite -> ; clear
  - - [constr]:1-10
  - - [constr]:1-10 in *
  - - [constr]:1-10 in [hyp]:1-5
  - + [constr]:1-10 in [hyp]:1-5
  - - [constr]:1-5 in * / [ident]:1-10
- cwl → rewrite <- ; clear
  - - [constr]:1-10
  - - [constr]:1-10 in *
  - - [constr]:1-10 in [hyp]:1-5
  - + [constr]:1-10 in [hyp]:1-5
  - - [constr]:1-5 in * / [ident]:1-10

## Solve

`src/Eqvivalence/Tactics/T7Solve.v`

- bpp → by apply; trivial
  - - constr {in hyp}
  - > constr {in hyp}
- app → by apply; auto
  - - constr {in hyp}
  - > constr {in hyp}
- bym→ by symmetry; trivial
- aym→ by symmetry; auto
- bpm→ by simpl; trivial
- aom→ by simpl; auto
- bbn→ by cbn; trivial
- abn→ by cbn; auto
- bvs → by inversion; subst; trivial
  - - [hyp]:1-10
- avs → by inversion; subst; auto
  - - [hyp]:1-10
- bpe → by specialize; trivial
  - - hyp: [constr]:1-20
- ape → by specialize; auto
  - - constr: [constr]:1-20
- bse → by pose proof; trivial
  - - constr: [constr]:1-20
- ase → by pose proof; auto
  - - constr: [constr]:1-20
- bwr → by rewrite -> ; trivial
  - - [constr]:1-10
- awr → by rewrite -> ; auto
  - - [constr]:1-10
- bwl → by rewrite <- ; trivial
  - - [constr]:1-10
- awl → by rewrite <- ; auto
  - - [constr]:1-10

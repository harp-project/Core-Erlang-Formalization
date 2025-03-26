From CoreErlang.Eqvivalence Require Export EX4Basics.

Import BigStep.
Import EX3Notations.
Require Import String Ascii.

Print ascii.

Open Scope string_scope.

Inductive digit : Set :=
  | D0
  | D1
  | D2
  | D3
  | D4
  | D5
  | D6
  | D7
  | D8
  | D9.

Definition increase_digit (d : digit) : digit :=
  match d with
  | D0 => D1
  | D1 => D2
  | D2 => D3
  | D3 => D4
  | D4 => D5
  | D5 => D6
  | D6 => D7
  | D7 => D8
  | D8 => D9
  | D9 => D0
  end.

Definition increase_digit_
    (d : digit)
    : (digit * bool)
    :=
  match d with
  | D0 => (D1, false)
  | D1 => (D2, false)
  | D2 => (D3, false)
  | D3 => (D4, false)
  | D4 => (D5, false)
  | D5 => (D6, false)
  | D6 => (D7, false)
  | D7 => (D8, false)
  | D8 => (D9, false)
  | D9 => (D0, true)
  end.

Fixpoint increase_digits
    (ds : list digit)
    : list digit
    :=
  match ds with
  | [] => []
  | d :: ds' =>
    match increase_digit_ d with
    | (d', false) => d' :: ds'
    | (d', true) => 
      match ds' with
      | [] => d' :: [D1]
      | _ :: _ => d' :: increase_digits ds'
      end
    end
  end.

Fixpoint nat_to_digits
    (n : nat)
    : list digit
    :=
  match n with
  | 0 => [D0]
  | S n' => increase_digits (nat_to_digits n')
  end.

Compute nat_to_digits 139.

Definition digit_to_string
    (d : digit)
    : string
    :=
  match d with
  | D0 => "0"
  | D1 => "1"
  | D2 => "2"
  | D3 => "3"
  | D4 => "4"
  | D5 => "5"
  | D6 => "6"
  | D7 => "7"
  | D8 => "8"
  | D9 => "9"
  end.

Compute increase_digits [D9; D9; D9; D9].

Fixpoint digits_to_string
    (ds : list digit)
    : string
    :=
  match ds with
  | [] => ""
  | d :: ds' => digits_to_string ds' ++ digit_to_string d
  end.

Compute digits_to_string [D9; D9; D9; D1].

Definition nat_to_sting
    (n : nat)
    : string
    :=
  digits_to_string (nat_to_digits n).


Compute nat_to_sting 1466.

Definition nat_to_name
    (n : nat)
    : string
    :=
  "X" ++ nat_to_sting n.


Fixpoint n_names_
    (n i : nat)
    : list string
    :=
  match n with
  | 0 => [nat_to_name i]
  | S n' => nat_to_name i :: n_names_ n' (S i)
  end.


Definition n_names
    (n : nat)
    : list string
    :=
  n_names_ n 0.


Compute n_names_ 5 1.


Definition give_vars
    (n xs : nat)
    : list Var
    :=
  match xs with
  | 0 => []
  | S n' => n_names_ n' n
  end.
  (* n_names_ n' n. *)

Definition give_name
    (n i : nat)
    : string
    :=
  nat_to_name (i + n).


(* Definition all_names_
    (n n' : nat)
    :=
   *)

Compute give_vars 1 3.

Fixpoint count_vars_pat
    (p : Pat)
    : nat
    :=
  match p with

  | Syntax.PNil => 0

  | Syntax.PVar => 1

  | Syntax.PLit l => 0

  | Syntax.PCons p₁ p₂ => count_vars_pat p₁ + count_vars_pat p₂

  | Syntax.PTuple ps => list_sum (map count_vars_pat ps)

  | Syntax.PMap pps =>
    list_sum (map (fun '(x, y) => (count_vars_pat x) + (count_vars_pat y)) pps)

  end.

Definition count_vars_pats
    (ps : list Pat)
    : nat
    :=
  list_sum (map count_vars_pat ps).

Fixpoint count_vars_exp
    (e : Exp)
    : nat
    :=
  match e with
  | VVal v => count_vars_vval v
  | EExp nv => count_vars_eexp nv
  end
with count_vars_vval
    (v : Val)
    : nat
    :=
  match v with

  | Syntax.VNil => 0

  | Syntax.VLit l => 0

  | Syntax.VCons v₁ v₂ =>
    count_vars_vval v₁ +
    count_vars_vval v₂

  | Syntax.VTuple vs =>
    list_sum (map count_vars_vval vs)

  | Syntax.VMap vvs =>
    list_sum
      (map (fun '(x, y) => count_vars_vval x + count_vars_vval y) vvs)

  | Syntax.VVar i => 1

  | Syntax.VFunId (i, a) => 1

  | Syntax.VPid _ => 0

  | Syntax.VClos os id xs e =>
    list_sum (map (fun '(_, xs', e') => count_vars_exp e') os)
    + count_vars_exp e

  end

with count_vars_eexp
    (nv : NonVal)
    : nat
    :=
  match nv with

  | Syntax.ECons e₁ e₂ =>
    count_vars_exp e₁ +
    count_vars_exp e₂

  | Syntax.ETuple es =>
    list_sum (map count_vars_exp es)

  | Syntax.EMap ees =>
    list_sum
      (map (fun '(x, y) => count_vars_exp x + count_vars_exp y) ees)

  | Syntax.ESeq e₁ e₂ =>
    count_vars_exp e₁ +
    count_vars_exp e₂

  | Syntax.EValues es =>
    list_sum (map count_vars_exp es)

  | Syntax.EPrimOp s es =>
    list_sum (map count_vars_exp es)

  | Syntax.EApp ᶠe es =>
    count_vars_exp ᶠe +
    list_sum (map count_vars_exp es)

  | Syntax.ECall ᵐe ᶠe es =>
    count_vars_exp ᵐe +
    count_vars_exp ᶠe +
    list_sum (map count_vars_exp es)

  | Syntax.ECase ᵖe us =>
    count_vars_exp ᵖe +
      list_sum
        (map
          (fun '(ps, ᵍe, ᵇe) =>
            (count_vars_pats ps +
            count_vars_exp ᵍe +
            count_vars_exp ᵇe))
          us)

  | Syntax.EFun xs ᵇe =>
    count_vars_exp ᵇe

  | Syntax.ELet xs e₁ e₂ =>
    count_vars_exp e₁ +
    count_vars_exp e₂
  | _ =>
    0

  end.
















Fixpoint count_binds_exp
    (e : Exp)
    : nat
    :=
  match e with
  | VVal v => count_binds_vval v
  | EExp nv => count_binds_eexp nv
  end
with count_binds_vval
    (v : Val)
    : nat
    :=
  match v with

  | Syntax.VNil => 0

  | Syntax.VLit l => 0

  | Syntax.VCons v₁ v₂ => 0

  | Syntax.VTuple vs => 0

  | Syntax.VMap vvs => 0

  | Syntax.VVar i => 0

  | Syntax.VFunId (i, a) => 0

  | Syntax.VPid _ => 0

  | Syntax.VClos os id xs e =>
    list_sum (map (fun '(_, xs', e') => xs' + (count_binds_exp e')) os)
    + xs
    + count_binds_exp e

  end

with count_binds_eexp
    (nv : NonVal)
    : nat
    :=
  match nv with

  | Syntax.ECons e₁ e₂ =>
    count_binds_exp e₁ +
    count_binds_exp e₂

  | Syntax.ETuple es =>
    list_sum (map count_binds_exp es)

  | Syntax.EMap ees =>
    list_sum
      (map (fun '(x, y) => count_binds_exp x + count_binds_exp y) ees)

  | Syntax.ESeq e₁ e₂ =>
    count_binds_exp e₁ +
    count_binds_exp e₂

  | Syntax.EValues es =>
    list_sum (map count_binds_exp es)

  | Syntax.EPrimOp s es =>
    list_sum (map count_binds_exp es)

  | Syntax.EApp ᶠe es =>
    count_binds_exp ᶠe +
    list_sum (map count_binds_exp es)

  | Syntax.ECall ᵐe ᶠe es =>
    count_binds_exp ᵐe +
    count_binds_exp ᶠe +
    list_sum (map count_binds_exp es)

  | Syntax.ECase ᵖe us =>
    count_binds_exp ᵖe +
      list_sum
        (map
          (fun '(ps, ᵍe, ᵇe) =>
            (count_vars_pats ps +
            count_binds_exp ᵍe +
            count_binds_exp ᵇe))
          us)

  | Syntax.EFun xs ᵇe =>
    xs +
    count_binds_exp ᵇe

  | Syntax.ELet xs e₁ e₂ =>
    xs +
    count_binds_exp e₁ +
    count_binds_exp e₂
  | _ =>
    0

  end.





Definition convert_lit
    (l : Lit)
    : Literal
    :=
  match l with
  | Syntax.Atom s => Atom s
  | Syntax.Integer x => Integer x
  end.


Fixpoint give_pat_list
    (f : nat -> Pat -> Pattern)
    (n : nat)
    (ps : list Pat)
    : list Pattern
    :=
  match ps with
  | [] => []
  | p :: ps' =>
    f n p :: give_pat_list f (n + count_vars_pat p) ps'
  end.


Fixpoint give_pat_map
    (f : nat -> Pat -> Pattern)
    (n : nat)
    (pps : list (Pat * Pat))
    : list (Pattern * Pattern)
    :=
  match pps with
  | [] => []
  | (p₁, p₂) :: pps' =>
    (f n p₁, f (n + count_vars_pat p₁) p₂)
    :: give_pat_map f (n + count_vars_pat p₁ + count_vars_pat p₂) pps'
  end.


Fixpoint give_pat
    (n : nat)
    (p : Pat)
    : Pattern
    :=
    match p with

    | Syntax.PNil =>
      PNil

    | Syntax.PVar =>
      PVar (nat_to_name n)

    | Syntax.PLit l =>
      PLit
        (convert_lit l)

    | Syntax.PCons p₁ p₂ =>
      PCons
        (give_pat n p₁)
        (give_pat (n + count_vars_pat p₁) p₂)

    | Syntax.PTuple ps =>
      PTuple
        (give_pat_list give_pat n ps)

    | Syntax.PMap pps =>
      PMap
        (give_pat_map give_pat n pps)

    end.


Fixpoint give_pats
    (n : nat)
    (ps : list Pat)
    : list Pattern
    :=
  match ps with
  | [] => []
  | p :: ps' => give_pat n p :: give_pats (n + count_vars_pat p) ps'
  end.




(*  Import SubstSemantics.

Compute give_pat 0 (PTuple [PCons PVar PVar; PCons PVar PVar]).
Compute give_pats 0 [PTuple [PCons PVar PVar; PCons PVar PVar]; PTuple [PCons PVar PVar; PCons PVar PVar]]. *)


Fixpoint give_val
    (v : Val)
    : Value
    :=
    match v with

    | Syntax.VNil =>
      VNil

    | Syntax.VLit l =>
      VLit
        (convert_lit l)

    | Syntax.VCons v₁ v₂ =>
      VCons
        (give_val v₁)
        (give_val v₂)

    | Syntax.VTuple vs =>
      VTuple
        (map give_val vs)

    | Syntax.VMap vvs =>
      VMap
        (map (fun '(x, y) => (give_val x, give_val y)) vvs)

    | _ =>
      VNil

    end.


Fixpoint give_exp
    (n : nat)
    (e : Exp)
    : Expression
    :=
  match e with
  | VVal v => give_vval n v
  | EExp nv => give_eexp n nv
  end

with give_vval
    (n : nat)
    (v : Val)
    : Expression
    :=
  match v with

  | Syntax.VNil =>
    ENil

  | Syntax.VLit l =>
    ELit
      (convert_lit l)

  | Syntax.VCons v₁ v₂ =>
    ECons
      (give_vval n v₁)
      (give_vval n v₂)

  | Syntax.VTuple vs =>
    ETuple
      (map (give_vval n) vs)

  | Syntax.VMap vvs =>
    EMap
      (map (fun '(x, y) => (give_vval n x, give_vval n y)) vvs)

  | Syntax.VVar i =>
    EVar
      (give_name n i)

  | Syntax.VFunId (i, a) =>
    EFunId
      (give_name n i, a)

  | Syntax.VPid _ => ENil

  | Syntax.VClos os id n' e =>
    EFun
      (give_vars n n')
      (give_exp (n' + n) e)

  end

with give_eexp
    (n : nat)
    (nv : NonVal)
    : Expression
    :=
  match nv with

  | Syntax.ECons e₁ e₂ =>
    ECons
      (give_exp n e₁)
      (give_exp n e₂)

  | Syntax.ETuple es =>
    ETuple
      (map (give_exp n) es)

  | Syntax.EMap ees =>
    EMap
      (map (fun '(x, y) => (give_exp n x, give_exp n y)) ees)

  | Syntax.ESeq e₁ e₂ =>
    ESeq
      (give_exp n e₁)
      (give_exp n e₂)

  | Syntax.EValues es =>
    EValues
      (map (give_exp n) es)

  | Syntax.EPrimOp s es =>
    EPrimOp
      s
      (map (give_exp n) es)

  | Syntax.EApp ᶠe es =>
    EApp
      (give_exp n ᶠe)
      (map (give_exp n) es)

  | Syntax.ECall ᵐe ᶠe es =>
    ECall
      (give_exp n ᵐe)
      (give_exp n ᶠe)
      (map (give_exp n) es)

  | Syntax.ECase ᵖe us =>
    ECase
      (give_exp n ᵖe)
      (map
        (fun '(ps, ᵍe, ᵇe) =>
          (give_pats n ps,
          give_exp (count_vars_pats ps + n) ᵍe,
          give_exp (count_vars_pats ps + n) ᵇe))
        us)

  | Syntax.EFun xs ᵇe =>
    EFun
      (give_vars (count_binds_exp ᵇe + n) xs)
      (give_exp n ᵇe)

  | Syntax.ELet xs e₁ e₂ =>
    ELet
      (give_vars (count_binds_exp e₂ + n) xs)
      (give_exp (count_binds_exp e₂ + xs + n) e₁)
      (give_exp n e₂)

  | _ =>
    ENil

  end.


Import SubstSemantics.
Compute give_exp 1
  (˝VTuple [VVar 0; VVar 1; VVar 2]).
Compute give_exp 0
  (°EFun 2
    (˝VTuple [VVar 0; VVar 1; VVar 2])).
Compute give_exp 0
  (°EFun 2
    (°EFun 2
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (˝VTuple [VVar 0; VVar 1; VVar 2])).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (°ELet 2
      (˝VNil)
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (°ELet 2
      (˝VTuple [VVar 0; VVar 1; VVar 2])
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VTuple [VVar 0; VVar 1; VVar 2])
    (°ELet 2
      (˝VTuple [VVar 0; VVar 1; VVar 2])
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).


Fixpoint give_vval
    (n : nat)
    (v : Val)
    : Expression
    :=
  match v with

  | Syntax.VNil =>
    ENil

  | Syntax.VLit l =>
    ELit
      (convert_lit l)

  | Syntax.VCons v₁ v₂ =>
    ECons
      (give_vval n v₁)
      (give_vval n v₂)

  | Syntax.VTuple vs =>
    ETuple
      (map (give_vval n) vs)

  | Syntax.VMap vvs =>
    EMap
      (map (fun '(x, y) => (give_vval n x, give_vval n y)) vvs)

  | Syntax.VVar i =>
    EVar (nat_to_name i)

  | Syntax.VFunId (i, a) =>
    EFunId (nat_to_name i, a)

  | Syntax.VPid _ => ENil

  | Syntax.VClos os id n' e =>
    EFun (give_vars n n') ENil

  end.


Fixpoint give_exp
    (n : nat)
    (e : Exp)
    : Expression
    :=
    match e with
    | ˝ v => ˝

      match v with
      | Syntax.VNil =>
        VNil

      | Syntax.VLit l =>
        VLit
          (convert_lit l)

      | Syntax.VCons v₁ v₂ =>
        VCons
          (give_exp n (˝v₁))
          (give_exp n (˝v₂))

      | Syntax.VTuple vs =>
        VTuple
          (map (give_exp n) vs)

      | Syntax.VMap vvs =>
        EMap
          (map (fun '(x, y) => (give_exp n x, give_exp n y))) vvs)

      | _ =>
        ENil

      end

    | EExp nv => ENil
    end.

      match nv with
      | Syntax.VNil =>
        ENil

      | Syntax.VLit l =>
        VLit
          (convert_lit l)

      | Syntax.VCons v₁ v₂ =>
        VCons
          (give_val v₁)
          (give_val v₂)

      | Syntax.VTuple vs =>
        VTuple
          (map give_val vs)

      | Syntax.VMap vvs =>
        VMap
          (map (fun '(x, y) => (give_val x, give_val y)) vvs)

      | _ =>
        VNil

      end

    end.



(* Fixpoint increase_digits_
  (ds : list (digit * bool))
  : list list (digit * bool)
  := *)

Fixpoint increase_digits (ds : list digit) : list digit :=
  match ds with
  | [] => []
  | d :: ds' =>
    match d with
    | D0 => D1 :: ds'
    | D1 => D2 :: ds'
    | D2 => D3 :: ds'
    | D3 => D4 :: ds'
    | D4 => D5 :: ds'
    | D5 => D6 :: ds'
    | D6 => D7 :: ds'
    | D7 => D8 :: ds'
    | D8 => D9 :: ds'
    | D9 => D0 :: (increase_digit ds')
    end
  end.

Fixpoint increase_digit (ds : list digit) : list digit :=
  match ds with
  | [] => []
  | d :: ds' =>
    match d with
    | D0 => D1 :: ds'
    | D1 => D2 :: ds'
    | D2 => D3 :: ds'
    | D3 => D4 :: ds'
    | D4 => D5 :: ds'
    | D5 => D6 :: ds'
    | D6 => D7 :: ds'
    | D7 => D8 :: ds'
    | D8 => D9 :: ds'
    | D9 => D0 :: (increase_digit ds')
    end
  end.

Compute increase_digit [D9].

Fixpoint nat_to_digit_ (n : nat) (ds :list digit) : list digit :=
  match n with
  | 0 => ds
  | S n' => nat_to_digit_ n' (increase_digit ds)
  end.

Definition nat_to_digit (n : nat) : list digit :=
  nat_to_digit_ n [D0].


Compute nat_to_digit 10.

Open Scope string_scope.

(* Helper function to convert a digit (0-9) to its corresponding ASCII character *)
Definition digit_to_ascii (n : nat) : ascii :=
  match n with
  | 0 => "0"
  | 1 => "1"
  | 2 => "2"
  | 3 => "3"
  | 4 => "4"
  | 5 => "5"
  | 6 => "6"
  | 7 => "7"
  | 8 => "8"
  | 9 => "9"
  | _ => "0" (* Default case, should not happen for single digits *)
  end.

(* Function to convert a natural number to a list of digits *)
(* Fixpoint nat_to_digits (n : nat) : list nat :=
  match n with
  | 0 => [0]
  | _ => let d := Nat.modulo n 10 in
         let m := Nat.div n 10 in
         if Nat.eqb m 0 then [d] else d :: nat_to_digits m
  end. *)


Fixpoint increase_digits (l : list nat) : list nat :=
  match l with
  | [] => []
  | n :: l' =>
    match n 

Fixpoint nat_to_digits (n : nat) : list nat :=
  match n with
  | S (S (S (S (S (S (S (S (S (S n')))))))))

(* Function to convert a list of digits to a string *)
Fixpoint digits_to_string (digits : list nat) : string :=
  match digits with
  | [] => ""
  | d :: ds => String (digit_to_ascii d) (digits_to_string ds)
  end.

(* Main function to convert a natural number to a string *)
Definition nat_to_string (n : nat) : string :=
  digits_to_string (rev (nat_to_digits n)).

(* Example usage *)
Compute nat_to_string 12345. (* Should output "12345" *)
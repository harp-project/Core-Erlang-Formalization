# Eqvivalence Proof of Big-step and Frame Stack Semantics

## Tactics

Shorten version of old tactics, they only consists of 3 letters. Some has extra function to their original counter parts. Tactics with multiple parameters don't use comma fore separation.

- `src/Eqvivalence/Tactics/T1ParamZero.v`: tactics with zero parameters;
- `src/Eqvivalence/Tactics/T2ParamSingle.v`: tactics with one parameters;
- `src/Eqvivalence/Tactics/T3ParamMultiple.v`: tactics with multiple parameters;
- `src/Eqvivalence/Tactics/T4Name.v`: tactics which include renaming;
- `src/Eqvivalence/Tactics/T5Transform.v`: tactics which transforms terms by rewrite, specify or pose;
- `src/Eqvivalence/Tactics/T6Clear.v`: tactics which include clear;
- `src/Eqvivalence/Tactics/T7Solve.v`: tactics which include solve.

## Basics

Defining the basics needs of both sides of the implications.

- `src/Eqvivalence/E1Induction.v`: induction for value and expression in both syntax;
- `src/Eqvivalence/E2WellFormedMap.v`: a map is well formed if all values are sorted;
- `src/Eqvivalence/E3Notations.v`: getter functions and notations, most of then is not used;
- `src/Eqvivalence/E3Basics.v`: basics lemmas and theorems, most of them is about list.

## Big-step implies Frame Stack Semantics

Necessary definitions, lemmas, theorems and tactics to prove big-step implies frame stack.

- `src/Eqvivalence/BsFs/B1EraseNames.v`: erase names from syntax, convert the big-step syntax to frame stack and substitute the environment;
- `src/Eqvivalence/BsFs/B2MeasureReduction.v`: reduce and eliminate the fuel of the value name eraser;
- `src/Eqvivalence/BsFs/B3Tactics.v`: scope and step tactics for frame stack evaluation;
- `src/Eqvivalence/BsFs/B4Helpers.v`: helper lemmas and theorems for the main theorem;
- `src/Eqvivalence/BsFs/B5Eqvivalence.v`: the main theorem;
- `src/Eqvivalence/BsFs/BXRemoveKeys.v`: unique case where remove keys can be removed from the term, not yet included.

## Frame Stack implies Big-Step Semantics 

Necessary definitions, lemmas, theorems and tactics to prove frame stack implies big-step.
Under construction, the content of the files very disorganized.

- `src/Eqvivalence/FsBs/F1GiveNames.v`: give names to syntax, convert the frame stack syntax to big-step;
- `src/Eqvivalence/FsBs/F2Steps.v`: frame stack steps theorems;
- `src/Eqvivalence/BsFs/F3Helpers.v`: helper lemmas and theorems for the main theorem;
- `src/Eqvivalence/BsFs/F4Eqvivalence.v`: the main theorem.



# Basics Files Detailed 

## Induction

`src/Eqvivalence/E1Induction.v`

- Big-Step:
  - `ind_bs_val`: induction on big-step value;
  - `ind_bs_exp`: induction on big-step expression;
- Frame Stack:
  - `ind_fs_val`: induction on frame stack value;
  - `ind_fs_exp`: induction on frame stack expression.

## Well Formed Map

`src/Eqvivalence/E2WellFormedMap.v`

- Big-Step:
  - `wfm_bs_val`: big-step value has well formed maps;
- Frame Stack:
  - `wfm_fs_val`: frame stack value has well formed maps.

## Getters and Notations

`src/Eqvivalence/E3Notations.v`

- Getters functions:
  - `get_keys`: **Get keys of map**:
    - Gets the first element of each pair from a pair list;
    - *get.keys*;
  - `get_vals`: **Get values of map**:
    - Gets the second element of each pair from a pair list;
    - *get.vals*;
  - `get_fids/get_fids_noid`: **Get function identifier of closure item/Get function identifiers of extension**:
    - Gets the function identifier of each closure item of the extension;
    - *get.fid/get.fids*.

## Basics

`src/Eqvivalence/E3Basics.v`

- Either:
  - `left_eq`: (inl a1 = inl a2) ↔ (a1 = a2);
  - `right_eq`: (inr ab1 = inr b2) ↔ (b1 = ab);
  - `left_neq`: (inl a1 ≠ inl a2) ↔ (a1 ≠ a2);
  - `right_neq`: (inr ab1 ≠ inr b2) ↔ (b1 ≠ ab);
- List:
  - `cons_app`: (x :: l = \[x\] ++ l);
  - `map_nil`: (map f \[\] = \[\]);
  - `map_single`: (map f \[a\] = \[f a\]);
  - `flatten_cons`: ((flatten\_list ((x, y) :: ll) = x :: y :: flatten\_list ll));
  - `flatten_cons_app1`: (flatten\_list ((x, y) :: ll) = \[x\] ++ y :: flatten\_list ll);
  - `nth_after_app`: (nth (length al1) (al1 ++ a :: al2) d = a);
  - `list_fst_eq`: (l1 = l2) → (map fst l1 = map fst l2);
  - `list_snd_eq`: (l1 = l2) → (map snd l1 = map snd l2);
  - `list_app_fst`: (l = l1 ++ l2) → (map fst l = map fst l1 ++ map fst l2);
  - `list_app_snd`: (l = l1 ++ l2) → (map snd l = map snd l1 ++ map snd l2);
  - `list_app_inl`: (l = l1 ++ l2) → (map inl l = map inl l1 ++ map inl l2);
  - `list_app_inr`: (l = l1 ++ l2) → (map inr l = map inr l1 ++ map inr l2);
- Length:
  - `length_eq`: (l1 = l2) → (length l1 = length l2);
  - `length_cons_eq`: (length (a :: al) = length (b :: bl)) → (length al = length bl);
  - `length_empty_fst`: (length al = length \[\]) → (al = \[\]);
  - `length_empty_snd`: (length \[\] = length al) → (al = \[\]);
  - `length_match2`: (length al = length cl) → (length bl = length cl) →  (length al = length bl);
  - `length_lt_split`: (length al < length bl) → (∃ bl1 bl2 : (bl = bl1 ++ bl2) ∧ (length al = length bl1));
  - `length_lt_split_middle`: (length al < length bl) → (∃ bl1 b bl2 : (bl = bl1 ++ \[b\] ++ bl2) ∧ (length al = length bl1));
  - `length_lt_split_middle_app`: (l1 ++ l2 = l1' ++ \[a\] ++ l2') → (∃ l : (l1 = l1' ++ \[a\] ++ l) ∧ (l2' = l ++ l2)) ∨ (∃ l : (l1' = l1 ++ l) ∧ (l2 = l ++ \[a\] ++ l2'));
  - `length_map_inl`: (length l = length (map inl l));
  - `length_map_inr`: (length l = length (map inr l));
  - `length_map_fst`: (length l = length (map fst l));
  - `length_map_snd`: (length l = length (map snd l));
  - `length_map_from_eq`: (bl = map f al) → (length al = length bl);
  - `length_map_from_eq_fst`: (bl = map f al) → ((length al = n) ↔ (length bl = n));
  - `length_map_from_eq_snd`: (bl = map f al) → ((n = length al) ↔ (n = length bl));
  - `length_app_single_end`: (length al = length bl) → (length (al ++ \[a\]) = length (bl ++ \[b\]));
  - `length_flatten_both_eq`: (length all = length bll) ↔ (length (flatten\_list all) = length (flatten\_list bll));
  - `length_flatten_both_lt`: (length all < length bll) ↔ (length (flatten\_list all) < length (flatten\_list bll));
  - `length_app_end_any`: (length l + length \[b\] = length l + length \[c\]);
  - `length_app_le`: (length (l ++ l') < n) → (length l < n);
  - `length_add_end_le`: (length l < length l + length \[a\]);
  - `length_add_end_eq`: (length (l ++ \[a\]) = S n) → (length l' = n) → (length l = length l');
  - `length_succ_add_end`: (S (length al) = S (length bl)) → (length (al ++ \[a\]) = length (bl ++ \[b\]));
  - `length_diff_plus1`: (length l = n + 1) → (length l' = n) →  (∃ l'' a : (l = l'' ++ \[a\]) ∧  (length l'' = length l');
  - `length_eq_map`: (map f1 l1 = map f2 l2) → (length l1 = length l2);
- List2:
  - `list_app_fst_split`: (map fst l = l1 ++ l2) → (∃ l1' l2' : (l = l1' ++ l2') ∧ (map fst l1' = l1) ∧ (map fst l2' = l2));
  - `list_app_snd_split`: (map snd l = l1 ++ l2) → (∃ l1' l2' : (l = l1' ++ l2') ∧ (map snd l1' = l1) ∧ (map snd l2' = l2));
  - `list_app_inl_split`: (map inl l = l1 ++ l2) → (∃ l1' l2' : (l = l1' ++ l2') ∧ (map inl l1' = l1) ∧ (map inl l2' = l2));
  - `list_app_inr_split`: (map inr l = l1 ++ l2) → (∃ l1' l2' : (l = l1' ++ l2') ∧ (map inr l1' = l1) ∧ (map inr l2' = l2));
  - `list_app_fst_split_other`: (map fst l = l1 ++ l2) → (∃ l1' l2' : (map snd l = map snd l1' ++ map snd l2') ∧ (length l1' = length l1) ∧ (length l2' = length l2));
  - `list_app_snd_split_other`: (map snd l = l1 ++ l2) → (∃ l1' l2' : (map fst l = map fst l1' ++ map fst l2') ∧ (length l1' = length l1) ∧ (length l2' = length l2));
  - `list_app_fst_split_middle`: (map fst l = l1 ++ \[a\] ++ l2) → (∃ (l1' l2' b : (l = l1' ++ \[(a, b)\] ++ l2') ∧ (map fst l1' = l1) ∧ (map fst l2' = l2));
  - `list_app_fst_split_middle_other`: (map snd l = l1 ++ \[a\] ++ l2) → (∃ (l1' l2' b : (map snd l = map snd l1' ++ \[b\] ++ map snd l2') ∧  (length l1' = length l1) ∧ (length l2' = length l2));
  - `list_app_fst_split_middle_both`: (map snd l = l1 ++ \[a\] ++ l2) → (∃ (l1' l2' b : (l = l1' ++ \[(a, b)\] ++ l2') ∧ (map snd l = map snd l1' ++ \[b\] ++ map snd l2') ∧ (map fst l1' = l1) ∧ (map fst l2' = l2) ∧  (length l1' = length l1) ∧ (length l2' = length l2));
- Zips:
  - `zip_fst`: (length al = length bl) → (map fst (zip al bl) = al);
  - `zip_snd`: (length al = length bl) → (map snd (zip al bl) = bl);
  - `zip_empty`: (length al = length bl) → (zip al bl = \[\]) → ((al = \[\]) ∧ (bl = \[\]));
  - `zip_equal`: (length al = length bl) → (l = zip al bl) → ((al = map fst l) ∧ (bl = map snd l));
  - `zip_self`: (l = zip (map fst l) (map snd l));
  - `zip_combine_eq`: (combine l1 l2 = zip l1 l2);
- Mods:
  - `kmod2list_is_either_empty_or_single`: (length l = k % 2) → ((l = \[\]) ∨ (∃ v : l = \[v\]));
  - `kmod2length_combined`: (length ll = k / 2) → (length l = k % 2) → (length (flatten\_list ll ++ l) = k);
- Extension:
  - `ext_to_env_fst`: (map fst (map (λ '(n, fid, (vars, e)), (inr fid, VClos Γ defext n vars e)) ext) = map (inr ∘ snd ∘ fst) ext);
- Exception:
  - `exc_to_vals`: **Exception to value sequence**:
    - Makes value sequence from an exception;
    - *exc.to.vals*;
  - `exc_to_vals_eq`: (\[exclass\_to\_value x.1.1; x.1.2; x.2\] = exc\_to\_vals x).



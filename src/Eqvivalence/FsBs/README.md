# Frame Stack implies Big-step Semantics

## Give Names

`src/Eqvivalence/FsBs/F1GiveNames.v`

- Digits:
 - `digit`: digit type;
 - `increase_digit`: increase digit by one;
 - `increase_digits`: increase digits by one;
 - `nat_to_digits`: convert natural number to list of digits;
- To String:
 - `digit_to_string`: convert digit to string;
 - `digits_to_string`: convert list of digits to string;
 - `nat_to_sting`: convert natural number to string;
 - `nat_to_name`: convert natural number to variable or function identifier names (appends 'X');
 - `digit_to_string_var`: convert digits to string in a unique way for variables;
 - `digits_to_string_var`: convert digits to variable name;
 - `nat_to_var`: convert natural number to variable name;
 - `digit_to_string_fid`: convert digits to string in a unique way for function identifier name;
 - `digits_to_string_fid`: convert digits to function identifier name;
 - `nat_to_fid`: convert natural number to function identifier name;
- Count:
 - `count_vars_pat`: count the number of variables in pattern;
 - `count_vars_pats`: count the number of variables in a list of pattern;
 - `count_binds_exp`: count the number of binds in an expression;
- Give Name Helpers:
 - `convert_lit`: convert literal from frame stack to big-step;
 - `convert_class`: convert exception class from frame stack to big-step;;
 - `give_name`: give name to index;
 - `give_name_var`: give unique variable name to index;
 - `give_name_fid`: give unique function identifier name to index;
 - `give_var`: give name to variable;
 - `give_fid`: give name to function identifier;
 - `give_vars`: give list of variables from the length;
 - `give_pat_list`: give names to a list of pattern;
 - `give_pat_map`: give names to a map of pattern;
 - Not finished
- Give Name Main:
 - `give_pat`: give names to pattern;
 - `give_pats`: give names to patterns;
 - `give_exp`: give names to expression;
 - `give_val`: give names to value;
 - `give_valseq`: give names to value sequence;
 - `give_exc`: give names to exception;
 - `give_redex`: give name to redex;
 - `give_result`: give name to result;
 - `to_redex`: make redex from result;
 - `give_names`: give names to expression.

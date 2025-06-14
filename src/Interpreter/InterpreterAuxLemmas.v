From CoreErlang.Interpreter Require Export InterpreterAux.

Lemma convert_primop_to_code_equiv: forall s, convert_primop_to_code s = convert_primop_to_code_NEW s.
Proof.
  intros. unfold convert_primop_to_code_NEW.
  destruct (s =? "match_fail")%string eqn:H1.
  rewrite String.eqb_eq in H1. rewrite H1. reflexivity.
  destruct (s =? "raise")%string eqn:H2.
  rewrite String.eqb_eq in H2. rewrite H2. reflexivity.
  destruct (s =? "recv_next")%string eqn:H3.
  rewrite String.eqb_eq in H3. rewrite H3. reflexivity.
  destruct (s =? "recv_peek_message")%string eqn:H4.
  rewrite String.eqb_eq in H4. rewrite H4. reflexivity.
  destruct (s =? "remove_message")%string eqn:H5.
  rewrite String.eqb_eq in H5. rewrite H5. reflexivity.
  destruct (s =? "recv_wait_timeout")%string eqn:H6.
  rewrite String.eqb_eq in H6. rewrite H6. reflexivity.

  rewrite String.eqb_neq in *.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
  all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
    destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
    destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
  all:destruct s; try reflexivity; try congruence.
Qed.

Lemma eval_primop_error_equiv: forall (fname : string) (params : list Val), 
  eval_primop_error fname params = eval_primop_error_NEW fname params.
Proof.
  intros.
  unfold eval_primop_error_NEW. rewrite <- convert_primop_to_code_equiv. reflexivity.
Qed.

Lemma primop_eval_equiv: forall (fname : string) (params : list Val),
  primop_eval fname params = primop_eval_NEW fname params.
Proof.
  intros.
  unfold primop_eval_NEW.
  rewrite <- convert_primop_to_code_equiv.
  rewrite <- eval_primop_error_equiv.
  reflexivity.
Qed.

Lemma convert_string_to_code_equiv: forall (s1 s2 : string),
  convert_string_to_code (s1, s2) = convert_string_to_code_NEW (s1, s2).
Proof.
  intros. unfold convert_string_to_code_NEW.
  destruct (s1 =? "erlang")%string eqn:H1.
  * rewrite String.eqb_eq in H1. rewrite H1.
    destruct (s2 =? "+")%string eqn:H2.
    rewrite String.eqb_eq in H2. rewrite H2. reflexivity.
    destruct (s2 =? "-")%string eqn:H3.
    rewrite String.eqb_eq in H3. rewrite H3. reflexivity.
    destruct (s2 =? "*")%string eqn:H4.
    rewrite String.eqb_eq in H4. rewrite H4 . reflexivity.
    destruct (s2 =? "/")%string eqn:H5.
    rewrite String.eqb_eq in H5. rewrite H5. reflexivity.
    destruct (s2 =? "bsl")%string eqn:H6.
    rewrite String.eqb_eq in H6. rewrite H6. reflexivity.
    destruct (s2 =? "bsr")%string eqn:H7.
    rewrite String.eqb_eq in H7. rewrite H7. reflexivity.
    destruct (s2 =? "rem")%string eqn:H8.
    rewrite String.eqb_eq in H8. rewrite H8. reflexivity.
    destruct (s2 =? "div")%string eqn:H9.
    rewrite String.eqb_eq in H9. rewrite H9. reflexivity.
    destruct (s2 =? "abs")%string eqn:H10.
    rewrite String.eqb_eq in H10. rewrite H10. reflexivity.
    destruct (s2 =? "and")%string eqn:H11.
    rewrite String.eqb_eq in H11. rewrite H11. reflexivity.
    destruct (s2 =? "or")%string eqn:H12.
    rewrite String.eqb_eq in H12. rewrite H12. reflexivity.
    destruct (s2 =? "not")%string eqn:H13.
    rewrite String.eqb_eq in H13. rewrite H13. reflexivity.
    destruct (s2 =? "==")%string eqn:H14.
    rewrite String.eqb_eq in H14. rewrite H14. reflexivity.
    destruct (s2 =? "=:=")%string eqn:H15.
    rewrite String.eqb_eq in H15. rewrite H15. reflexivity.
    destruct (s2 =? "/=")%string eqn:H16.
    rewrite String.eqb_eq in H16. rewrite H16. reflexivity.
    destruct (s2 =? "=/=")%string eqn:H17.
    rewrite String.eqb_eq in H17. rewrite H17. reflexivity.
    destruct (s2 =? "++")%string eqn:H18.
    rewrite String.eqb_eq in H18. rewrite H18. reflexivity.
    destruct (s2 =? "--")%string eqn:H19.
    rewrite String.eqb_eq in H19. rewrite H19. reflexivity.
    destruct (s2 =? "tuple_to_list")%string eqn:H20.
    rewrite String.eqb_eq in H20. rewrite H20. reflexivity.
    destruct (s2 =? "list_to_tuple")%string eqn:H21.
    rewrite String.eqb_eq in H21. rewrite H21. reflexivity.
    destruct (s2 =? "<")%string eqn:H22.
    rewrite String.eqb_eq in H22. rewrite H22. reflexivity.
    destruct (s2 =? ">")%string eqn:H23.
    rewrite String.eqb_eq in H23. rewrite H23. reflexivity.
    destruct (s2 =? "=<")%string eqn:H24.
    rewrite String.eqb_eq in H24. rewrite H24. reflexivity.
    destruct (s2 =? "list_to_atom")%string eqn:H25.
    rewrite String.eqb_eq in H25. rewrite H25. reflexivity.
    destruct (s2 =? "length")%string eqn:H26.
    rewrite String.eqb_eq in H26. rewrite H26. reflexivity.
    destruct (s2 =? "tuple_size")%string eqn:H27.
    rewrite String.eqb_eq in H27. rewrite H27. reflexivity.
    destruct (s2 =? ">=")%string eqn:H28.
    rewrite String.eqb_eq in H28. rewrite H28. reflexivity.
    destruct (s2 =? "hd")%string eqn:H29.
    rewrite String.eqb_eq in H29. rewrite H29. reflexivity.
    destruct (s2 =? "tl")%string eqn:H30.
    rewrite String.eqb_eq in H30. rewrite H30. reflexivity.
    destruct (s2 =? "element")%string eqn:H31.
    rewrite String.eqb_eq in H31. rewrite H31. reflexivity.
    destruct (s2 =? "setelement")%string eqn:H32.
    rewrite String.eqb_eq in H32. rewrite H32. reflexivity.
    destruct (s2 =? "is_number")%string eqn:H33.
    rewrite String.eqb_eq in H33. rewrite H33. reflexivity.
    destruct (s2 =? "is_integer")%string eqn:H34.
    rewrite String.eqb_eq in H34. rewrite H34. reflexivity.
    destruct (s2 =? "is_atom")%string eqn:H35.
    rewrite String.eqb_eq in H35. rewrite H35. reflexivity.
    destruct (s2 =? "is_boolean")%string eqn:H36.
    rewrite String.eqb_eq in H36. rewrite H36. reflexivity.
    destruct (s2 =? "fun_info")%string eqn:H37.
    rewrite String.eqb_eq in H37. rewrite H37. reflexivity.
    destruct (s2 =? "error")%string eqn:H38.
    rewrite String.eqb_eq in H38. rewrite H38. reflexivity.
    destruct (s2 =? "exit")%string eqn:H39.
    rewrite String.eqb_eq in H39. rewrite H39. reflexivity.
    destruct (s2 =? "throw")%string eqn:H40.
    rewrite String.eqb_eq in H40. rewrite H40. reflexivity.
    destruct (s2 =? "!")%string eqn:H41.
    rewrite String.eqb_eq in H41. rewrite H41. reflexivity.
    destruct (s2 =? "spawn")%string eqn:H42.
    rewrite String.eqb_eq in H42. rewrite H42. reflexivity.
    destruct (s2 =? "process_flag")%string eqn:H43.
    rewrite String.eqb_eq in H43. rewrite H43. reflexivity.
    destruct (s2 =? "spawn_link")%string eqn:H44.
    rewrite String.eqb_eq in H44. rewrite H44. reflexivity.
    destruct (s2 =? "self")%string eqn:H45.
    rewrite String.eqb_eq in H45. rewrite H45. reflexivity.
    destruct (s2 =? "link")%string eqn:H46.
    rewrite String.eqb_eq in H46. rewrite H46. reflexivity.
    destruct (s2 =? "unlink")%string eqn:H47.
    rewrite String.eqb_eq in H47. rewrite H47. reflexivity.
    
    rewrite String.eqb_neq in *.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
    all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
      destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
      destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
    all:destruct s2; try reflexivity; try congruence.
  
  * destruct (s1 =? "io")%string eqn:H2.
    rewrite String.eqb_eq in H2. rewrite H2.
    + destruct (s2 =? "fwrite")%string eqn:H3.
      rewrite String.eqb_eq in H3. rewrite H3. reflexivity.
      destruct (s2 =? "fread")%string eqn:H4.
      rewrite String.eqb_eq in H4. rewrite H4. reflexivity.
      rewrite String.eqb_neq in *.
      all:destruct s2; try reflexivity; try congruence.
      all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
        destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
        destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
      all:destruct s2; try reflexivity; try congruence.
      all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
        destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
        destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
      all:destruct s2; try reflexivity; try congruence.
      all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
        destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
        destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
      all:destruct s2; try reflexivity; try congruence.
      all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
        destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
        destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
      all:destruct s2; try reflexivity; try congruence.
      all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
        destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
        destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
      all:destruct s2; try reflexivity; try congruence.
      all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
        destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
        destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
      all:destruct s2; try reflexivity; try congruence.
    + destruct (s1 =? "lists")%string eqn:H3.
      rewrite String.eqb_eq in H3. rewrite H3.
      - destruct (s2 =? "split")%string eqn:H4.
        rewrite String.eqb_eq in H4. rewrite H4. reflexivity.
        rewrite String.eqb_neq in *.
        all:destruct s2; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s2; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s2; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s2; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s2; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s2; try reflexivity; try congruence.
      - rewrite String.eqb_neq in *.
        all:destruct s1; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s1; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s1; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s1; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s1; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s1; try reflexivity; try congruence.
        all:destruct a; try reflexivity; destruct b; try reflexivity; destruct b0; try reflexivity;
          destruct b1; try reflexivity; destruct b2; try reflexivity; destruct b3; try reflexivity;
          destruct b4; try reflexivity; destruct b5; try reflexivity; destruct b6; try reflexivity.
        all:destruct s1; try reflexivity; try congruence.
Qed.

Lemma eval_arith_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_arith mname fname params = eval_arith_NEW mname fname params.
Proof.
  intros. unfold eval_arith_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_io_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_io mname fname params = eval_io_NEW mname fname params.
Proof.
  intros. unfold eval_io_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_logical_equiv: forall (mname fname : string) (params : list Val),
  eval_logical mname fname params = eval_logical_NEW mname fname params.
Proof.
  intros. unfold eval_logical_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_equality_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_equality mname fname params = eval_equality_NEW mname fname params.
Proof.
  intros. unfold eval_equality_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_transform_list_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_transform_list mname fname params = eval_transform_list_NEW mname fname params.
Proof.
  intros. unfold eval_transform_list_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_list_tuple_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_list_tuple mname fname params = eval_list_tuple_NEW mname fname params.
Proof.
  intros. unfold eval_list_tuple_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_list_atom_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_list_atom mname fname params = eval_list_atom_NEW mname fname params.
Proof.
  intros. unfold eval_list_atom_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_cmp_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_cmp mname fname params = eval_cmp_NEW mname fname params.
Proof.
  intros. unfold eval_cmp_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_hd_tl_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_hd_tl mname fname params = eval_hd_tl_NEW mname fname params.
Proof.
  intros. unfold eval_hd_tl_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_elem_tuple_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_elem_tuple mname fname params = eval_elem_tuple_NEW mname fname params.
Proof.
  intros. unfold eval_elem_tuple_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_check_equiv: forall (mname fname : string) (params : list Val),
  eval_check mname fname params = eval_check_NEW mname fname params.
Proof.
  intros. unfold eval_check_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_error_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_error mname fname params = eval_error_NEW mname fname params.
Proof.
  intros. unfold eval_error_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_concurrent_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_concurrent mname fname params = eval_concurrent_NEW mname fname params.
Proof.
  intros. unfold eval_concurrent_NEW.
  rewrite <- convert_string_to_code_equiv. reflexivity.
Qed.

Lemma eval_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval mname fname params = eval_NEW mname fname params.
Proof.
  intros. unfold eval_NEW.
  rewrite <- convert_string_to_code_equiv.
  rewrite <- eval_io_equiv.
  rewrite <- eval_logical_equiv.
  rewrite <- eval_equality_equiv.
  rewrite <- eval_transform_list_equiv.
  rewrite <- eval_list_tuple_equiv.
  rewrite <- eval_list_atom_equiv.
  rewrite <- eval_cmp_equiv.
  rewrite <- eval_hd_tl_equiv.
  rewrite <- eval_elem_tuple_equiv.
  rewrite <- eval_check_equiv.
  rewrite <- eval_error_equiv.
  rewrite <- eval_concurrent_equiv.
  rewrite <- eval_arith_equiv.
  reflexivity.
Qed.

Lemma create_result_equiv: forall (ident : FrameIdent) (vl : list Val),
  create_result ident vl = create_result_NEW ident vl.
Proof.
  intros. unfold create_result_NEW.
  destruct ident; try reflexivity.
  * destruct m; try reflexivity. destruct l; try reflexivity. destruct f; try reflexivity.
    destruct l; try reflexivity. rewrite <- eval_equiv. reflexivity.
  * rewrite <- primop_eval_equiv. reflexivity.
Qed.






















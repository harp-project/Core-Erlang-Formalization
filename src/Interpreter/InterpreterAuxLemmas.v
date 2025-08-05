From CoreErlang.Concurrent  Require Export NodeSemanticsLemmas. 
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
    destruct (s2 =? "list_to_atom")%string eqn:H21'.
    rewrite String.eqb_eq in H21'. rewrite H21'. reflexivity.
    destruct (s2 =? "integer_to_list")%string eqn:H21''.
    rewrite String.eqb_eq in H21''. rewrite H21''. reflexivity.
    destruct (s2 =? "<")%string eqn:H22.
    rewrite String.eqb_eq in H22. rewrite H22. reflexivity.
    destruct (s2 =? ">")%string eqn:H23.
    rewrite String.eqb_eq in H23. rewrite H23. reflexivity.
    destruct (s2 =? "=<")%string eqn:H24.
    rewrite String.eqb_eq in H24. rewrite H24. reflexivity.
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

Lemma eval_convert_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval_convert mname fname params = eval_convert_NEW mname fname params.
Proof.
  intros. unfold eval_convert_NEW.
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
  rewrite <- eval_convert_equiv.
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

Lemma usedPIDsExp_equiv: forall (e : Exp), usedPIDsExp e = usedPIDsExpNew e.
Proof.
  intros. unfold usedPIDsExpNew.
  induction e using Exp_ind2 with
  (PV := fun v => usedPIDsVal v = usedPIDsValNew v)
  (PE := fun e => usedPIDsExp e = usedPIDsExpNew e)
  (Q  := Forall (fun e => usedPIDsExp e = usedPIDsExpNew e))
  (QV := Forall (fun v => usedPIDsVal v = usedPIDsValNew v))
  (R  := Forall (PBoth (fun e => usedPIDsExp e = usedPIDsExpNew e)))
  (RV := Forall (PBoth (fun v => usedPIDsVal v = usedPIDsValNew v)))
  (VV := Forall (fun e => usedPIDsExp e.2 = usedPIDsExpNew e.2))
  (W  := Forall (fun '(e1, e2, e3) => usedPIDsExp e2 = usedPIDsExpNew e2
                                      /\ usedPIDsExp e3 = usedPIDsExpNew e3))
  (Z  := Forall (fun e => usedPIDsExp e.2 = usedPIDsExpNew e.2)); auto.
  * simpl. unfold pids_union. rewrite IHe. rewrite IHe0. reflexivity.
  * simpl. unfold flat_union. unfold flat_unionNew. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * simpl. unfold flat_union. unfold flat_unionNew. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. inv H1. rewrite H. rewrite H0.
      apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExpNew in IHe0. simpl.
    unfold pids_union. unfold flat_union. unfold flat_unionNew. unfold pids_empty.
    rewrite IHe0.
    induction ext.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1.
      apply IHext in H2. unfold pids_union.
      assert (usedPIDsExpNew e ∪ (usedPIDsExpNew a.2
       ∪ foldr (λ (x : nat * nat * Exp) (acc : gset PID), usedPIDsExp x.2 ∪ acc) ∅ ext) =
       usedPIDsExpNew a.2 ∪ (usedPIDsExpNew e
       ∪ foldr (λ (x : nat * nat * Exp) (acc : gset PID), usedPIDsExp x.2 ∪ acc) ∅ ext) ) as Hhelp1.
       { set_solver. }
      rewrite Hhelp1. rewrite H2. set_solver.
  * simpl. unfold flat_union. unfold flat_unionNew. unfold pids_union. unfold pids_empty.
    induction el.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHel in H2. rewrite H2. reflexivity.
  * fold usedPIDsExpNew in IHe1, IHe2. simpl. rewrite IHe1. rewrite IHe2. unfold pids_union. reflexivity.
  * simpl. unfold flat_union. unfold flat_unionNew. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * simpl. unfold flat_union. unfold flat_unionNew. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. inv H1. rewrite H, H0. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExpNew in IHe1, IHe2. simpl. unfold pids_union. rewrite IHe1, IHe2.
    assert (usedPIDsExpNew e1 ∪ (usedPIDsExpNew e2 ∪ flat_unionNew usedPIDsExpNew l) =
            usedPIDsExpNew e1 ∪ usedPIDsExpNew e2 ∪ flat_unionNew usedPIDsExpNew l) as Hhelp.
    { set_solver. }
    rewrite Hhelp. clear Hhelp.
    unfold flat_union. unfold flat_unionNew. unfold pids_empty. unfold pids_union.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe3. rewrite H1. apply IHl in H2.
      assert (usedPIDsExpNew e1 ∪ usedPIDsExpNew e2
              ∪ (usedPIDsExpNew a ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l) =
              usedPIDsExpNew a ∪ (usedPIDsExpNew e1
              ∪ usedPIDsExpNew e2 ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l)) 
              as Hhelp.
      { set_solver. } rewrite Hhelp.
      rewrite H2. set_solver.
  * simpl. unfold flat_union. unfold flat_unionNew. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExpNew in IHe. simpl. unfold flat_union, flat_unionNew, pids_union, pids_empty.
    rewrite IHe. f_equal.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe0. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExpNew in IHe. simpl. unfold flat_union, flat_unionNew, pids_union, pids_empty.
    rewrite IHe. f_equal.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe0. destruct a, p. simpl. destruct H1. rewrite H, H0. f_equal.
      apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExpNew in IHe1, IHe2. simpl. rewrite IHe1, IHe2. reflexivity.
  * fold usedPIDsExpNew in IHe1, IHe2. simpl. rewrite IHe1, IHe2. reflexivity.
  * fold usedPIDsExpNew in IHe. simpl. unfold flat_union, flat_unionNew, pids_union, pids_empty.
    rewrite IHe. f_equal.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe0. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExpNew in IHe1, IHe2, IHe3. simpl. unfold pids_union. rewrite IHe1, IHe2, IHe3. set_solver.
Qed.

Lemma usedPIDsRed_equiv : forall (r : Redex), usedPIDsRed r = usedPIDsRedNew r.
Proof.
  intros. destruct r.
  * cbn. apply usedPIDsExp_equiv.
  * cbn. unfold flat_union, flat_unionNew, pids_union, pids_empty.
    induction vs.
    + simpl. reflexivity.
    + simpl. rewrite IHvs.
      assert (usedPIDsVal a = usedPIDsValNew a) by (apply (usedPIDsExp_equiv (VVal a))).
      rewrite H. reflexivity.
  * cbn. unfold pids_union.
    assert (usedPIDsVal e.1.2 = usedPIDsValNew e.1.2) by (apply (usedPIDsExp_equiv (VVal e.1.2))).
    assert (usedPIDsVal e.2   = usedPIDsValNew e.2  ) by (apply (usedPIDsExp_equiv (VVal e.2  ))).
    rewrite H, H0. reflexivity.
  * reflexivity.
Qed.

Lemma usedPIDsFrameId_equiv : forall (i : FrameIdent), usedPIDsFrameId i = usedPIDsFrameIdNew i.
Proof.
  intros. destruct i; auto.
  * simpl. unfold pids_union.
    assert (usedPIDsVal m = usedPIDsValNew m) by (apply (usedPIDsExp_equiv (VVal m))).
    assert (usedPIDsVal f = usedPIDsValNew f) by (apply (usedPIDsExp_equiv (VVal f))).
    rewrite H, H0. reflexivity.
  * simpl.
    exact (usedPIDsExp_equiv (VVal v)).
Qed.

Lemma usedPIDsFrame_equiv : forall (f : Frame), usedPIDsFrame f = usedPIDsFrameNew f.
Proof.
  intros. destruct f; simpl.
  * exact (usedPIDsExp_equiv hd).
  * exact (usedPIDsExp_equiv (VVal tl)).
  * unfold flat_union, flat_unionNew, pids_union, pids_empty.
    rewrite (usedPIDsFrameId_equiv ident).
    assert (usedPIDsFrameIdNew ident ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
            ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el =
            usedPIDsFrameIdNew ident ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
            ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el)).
    { set_solver. }
    rewrite H. f_equal. clear H.
    induction vl.
    + simpl. f_equal.
      induction el.
      - simpl. reflexivity.
      - simpl.
        rewrite (usedPIDsExp_equiv a), IHel. reflexivity.
    + simpl.
      assert (usedPIDsVal a = usedPIDsValNew a) by (apply (usedPIDsExp_equiv (VVal a))).
      rewrite H.
      assert (usedPIDsValNew a ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
              ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el =
              usedPIDsValNew a ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
              ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el)).
      { set_solver. } rewrite H0. rewrite IHvl. set_solver.
  * unfold flat_union, flat_unionNew, pids_union, pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. rewrite (usedPIDsExp_equiv a), IHl. reflexivity.
  * unfold flat_union, flat_unionNew, pids_union, pids_empty. induction l.
    + simpl. rewrite (usedPIDsExp_equiv f). reflexivity.
    + simpl.
      assert (usedPIDsExp f ∪ 
              (usedPIDsExp a ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l) =
              usedPIDsExp a ∪ 
              (usedPIDsExp f ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l)) by set_solver.
      rewrite H. rewrite IHl, (usedPIDsExp_equiv a). set_solver.
  * unfold flat_union, flat_unionNew, pids_union, pids_empty.
    assert (usedPIDsVal m = usedPIDsValNew m) by (apply (usedPIDsExp_equiv (VVal m))).
    rewrite H. f_equal.
    induction l.
    + reflexivity.
    + simpl. rewrite (usedPIDsExp_equiv a), IHl. reflexivity.
  * unfold flat_union, flat_unionNew, pids_union, pids_empty.
    induction l.
    + reflexivity.
    + simpl. rewrite (usedPIDsExp_equiv a.1.2), (usedPIDsExp_equiv a.2), IHl. reflexivity.
  * unfold flat_union, flat_unionNew, pids_union, pids_empty.
    rewrite (usedPIDsExp_equiv ex).
    assert (usedPIDsExpNew ex ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ lv
            ∪ foldr (λ (x : list Pat * Exp * Exp) (acc : gset PID), 
              usedPIDsExp x.1.2 ∪ usedPIDsExp x.2 ∪ acc) ∅ le =
            usedPIDsExpNew ex ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ lv
            ∪ foldr (λ (x : list Pat * Exp * Exp) (acc : gset PID), 
              usedPIDsExp x.1.2 ∪ usedPIDsExp x.2 ∪ acc) ∅ le)) by set_solver.
    rewrite H. f_equal. clear H. f_equal.
    + induction lv.
      - reflexivity.
      - simpl. rewrite IHlv.
        assert (usedPIDsVal a = usedPIDsValNew a) by (apply (usedPIDsExp_equiv (VVal a))).
        rewrite H. reflexivity.
    + induction le.
      - reflexivity.
      - simpl. rewrite (usedPIDsExp_equiv a.1.2), (usedPIDsExp_equiv a.2), IHle. reflexivity.
  * exact (usedPIDsExp_equiv e).
  * exact (usedPIDsExp_equiv e).
  * unfold pids_union. rewrite (usedPIDsExp_equiv e2), (usedPIDsExp_equiv e3). reflexivity.
Qed.

Lemma usedPIDsStack_equiv : forall (fs : FrameStack), usedPIDsStack fs = usedPIDsStackNew fs.
Proof.
  intros. induction fs.
  + reflexivity.
  + simpl. rewrite (usedPIDsFrame_equiv a), IHfs. reflexivity.
Qed.

Instance LeibnizEquiv_gset_pid : LeibnizEquiv (gset (gset PID)) := _.

Lemma usedPIDsProc_equiv : forall (p : Process), usedPIDsProc p = usedPIDsProcNew p.
Proof.
  intros. destruct p; simpl.
  * destruct l, p, p, p. unfold flat_union, flat_unionNew, pids_union, pids_empty.
    assert (usedPIDsStack f ∪ usedPIDsRed r ∪ g
            ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.1
            ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.2 =
            usedPIDsStack f ∪ (usedPIDsRed r ∪ (g
            ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.1
            ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.2)))) by set_solver.
    rewrite H. clear H.
    rewrite (usedPIDsStack_equiv f), (usedPIDsRed_equiv r). do 4 f_equal.
    + destruct m. simpl. induction l.
      - reflexivity.
      - simpl. assert (usedPIDsVal a = usedPIDsValNew a) by (apply (usedPIDsExp_equiv (VVal a))).
        rewrite H, IHl. reflexivity.
    + destruct m. simpl. induction l0.
      - reflexivity.
      - simpl. assert (usedPIDsVal a = usedPIDsValNew a) by (apply (usedPIDsExp_equiv (VVal a))).
        rewrite H, IHl0. reflexivity.
  * unfold pids_map_set_union, pids_insert. f_equal.
    induction d using map_first_key_ind.
    + unfold map_to_set. setoid_rewrite map_to_list_empty. simpl. reflexivity.
    + unfold map_to_set.
      assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
      { apply map_to_list_insert_first_key; assumption. }
      setoid_rewrite H1. clear H1. simpl. f_equal.
      - assert (usedPIDsVal x = usedPIDsValNew x) by (apply (usedPIDsExp_equiv (VVal x))).
        rewrite H1. f_equal. set_solver.
      - exact IHd.
Qed.

Lemma allPIDsPool_equiv: forall (p : ProcessPool), allPIDsPool p = allPIDsPoolNew p.
Proof.
  intros. unfold allPIDsPool. unfold allPIDsPoolNew.
  unfold flat_union, flat_unionNew, pids_union, pids_empty, pool_toList, pids_insert.
  induction p using map_first_key_ind.
  * setoid_rewrite map_to_list_empty. simpl. reflexivity.
  * assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
    { apply map_to_list_insert_first_key; assumption. }
    setoid_rewrite H1. clear H1. simpl.
    assert ({[i]} ∪ usedPIDsProc x = usedPIDsProcNew x ∪ {[i]}).
    { assert (usedPIDsProc x = usedPIDsProcNew x) by (apply (usedPIDsProc_equiv x)). 
      rewrite H1. set_solver. }
    rewrite H1. f_equal. exact IHp.
Qed.

Lemma usedPIDsSignal_equiv: forall (s : Signal), usedPIDsSignal s = usedPIDsSignalNew s.
Proof.
  intros.
  destruct s; auto; simpl.
  * exact (usedPIDsExp_equiv (VVal e)).
  * exact (usedPIDsExp_equiv (VVal r)).
Qed.

Lemma allPIDsEther_equiv : forall (eth : Ether), allPIDsEther eth = allPIDsEtherNew eth.
Proof.
  intros. unfold allPIDsEther, allPIDsEtherNew.
  unfold flat_union, flat_unionNew, pids_insert, pids_union, pids_empty, pids_singleton, ether_toList.
  induction eth using map_first_key_ind.
  * setoid_rewrite map_to_list_empty. simpl. reflexivity.
  * assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
    { apply map_to_list_insert_first_key; assumption. }
    setoid_rewrite H1. clear H1. simpl. f_equal.
    + destruct i. f_equal.
      - set_solver.
      - clear. induction x.
        ** simpl. reflexivity.
        ** simpl. rewrite (usedPIDsSignal_equiv a), IHx. reflexivity.
    + exact IHeth.
Qed.

Lemma usedInPool_equiv: forall (pid : PID) (p : ProcessPool), usedInPool pid p = usedInPoolNew pid p.
Proof.
  intros. unfold usedInPool, usedInPoolNew, pids_member.
  rewrite allPIDsPool_equiv.
  destruct (gset_elem_of_dec _ _); reflexivity.
Qed.

Lemma usedInEther_equiv: forall (pid : PID) (eth : Ether), usedInEther pid eth = usedInEtherNew pid eth.
Proof.
  intros. unfold usedInEther, usedInEtherNew, pids_member.
  rewrite allPIDsEther_equiv.
  destruct (gset_elem_of_dec _ _); reflexivity.
Qed.

Lemma etherAdd_equiv: forall (source dest : PID) (m : Signal) (n : Ether),
  etherAdd source dest m n = etherAddNew source dest m n.
Proof.
  intros. unfold etherAddNew, etherAdd, ether_lookup, ether_insert. reflexivity.
Qed.

Lemma etherPop_equiv: forall (source dest : PID) (n : Ether),
  etherPop source dest n = etherPopNew source dest n.
Proof.
  intros. unfold etherPop, etherPopNew, ether_lookup, ether_insert. reflexivity.
Qed.

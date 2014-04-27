(** * ImpCEvalFun: Evaluation Function for Imp *)

(* $Date: 2013-07-01 18:48:47 -0400 (Mon, 01 Jul 2013) $ *)

(* #################################### *)
(** ** Evaluation Function *)

Require Import Imp.

(** Here's a first try at an evaluation function for commands,
    omitting [WHILE]. *)

Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with 
    | SKIP => 
        st
    | l ::= a1 => 
        update st l (aeval st a1)
    | c1 ;; c2 => 
        let st' := ceval_step1 st c1 in
        ceval_step1 st' c2
    | IFB b THEN c1 ELSE c2 FI => 
        if (beval st b) 
          then ceval_step1 st c1 
          else ceval_step1 st c2
    | WHILE b1 DO c1 END => 
        st  (* bogus *)
  end.

(** In a traditional functional programming language like ML or
    Haskell we could write the WHILE case as follows:
<<
    | WHILE b1 DO c1 END => 
        if (beval st b1) 
          then ceval_step1 st (c1;; WHILE b1 DO c1 END)
          else st 
>>
    Coq doesn't accept such a definition ([Error: Cannot guess
    decreasing argument of fix]) because the function we want to
    define is not guaranteed to terminate. Indeed, the changed
    [ceval_step1] function applied to the [loop] program from [Imp.v] would
    never terminate. Since Coq is not just a functional programming
    language, but also a consistent logic, any potentially
    non-terminating function needs to be rejected. Here is an
    invalid(!) Coq program showing what would go wrong if Coq allowed
    non-terminating recursive functions:
<<
     Fixpoint loop_false (n : nat) : False := loop_false n.
>>
    That is, propositions like [False] would become
    provable (e.g. [loop_false 0] would be a proof of [False]), which
    would be a disaster for Coq's logical consistency.

    Thus, because it doesn't terminate on all inputs, the full version
    of [ceval_step1] cannot be written in Coq -- at least not
    without one additional trick... *)


(** Second try, using an extra numeric argument as a "step index" to
    ensure that evaluation always terminates. *)

Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with 
  | O => empty_state
  | S i' =>
    match c with 
      | SKIP => 
          st
      | l ::= a1 => 
          update st l (aeval st a1)
      | c1 ;; c2 => 
          let st' := ceval_step2 st c1 i' in
          ceval_step2 st' c2 i' 
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step2 st c1 i' 
            else ceval_step2 st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1) 
          then let st' := ceval_step2 st c1 i' in
               ceval_step2 st' c i'
          else st
    end
  end.

(** _Note_: It is tempting to think that the index [i] here is
    counting the "number of steps of evaluation."  But if you look
    closely you'll see that this is not the case: for example, in the
    rule for sequencing, the same [i] is passed to both recursive
    calls.  Understanding the exact way that [i] is treated will be
    important in the proof of [ceval__ceval_step], which is given as
    an exercise below. *)

(** Third try, returning an [option state] instead of just a [state]
    so that we can distinguish between normal and abnormal
    termination. *)

Fixpoint ceval_step3 (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ;; c2 => 
          match (ceval_step3 st c1 i') with
          | Some st' => ceval_step3 st' c2 i'
          | None => None
          end
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step3 st c1 i' 
            else ceval_step3 st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then match (ceval_step3 st c1 i') with
               | Some st' => ceval_step3 st' c i'
               | None => None
               end
          else Some st
    end
  end.

(** We can improve the readability of this definition by introducing a
    bit of auxiliary notation to hide the "plumbing" involved in
    repeatedly matching against optional states. *)

Notation "'LETOPT' x <== e1 'IN' e2" 
   := (match e1 with
         | Some x => e2
         | None => None
       end)
   (right associativity, at level 60).

Fixpoint ceval_step (st : state) (c : com) (i : nat) 
                    : option state :=
  match i with 
  | O => None
  | S i' =>
    match c with 
      | SKIP => 
          Some st
      | l ::= a1 => 
          Some (update st l (aeval st a1))
      | c1 ;; c2 => 
          LETOPT st' <== ceval_step st c1 i' IN
          ceval_step st' c2 i'
      | IFB b THEN c1 ELSE c2 FI => 
          if (beval st b) 
            then ceval_step st c1 i' 
            else ceval_step st c2 i'
      | WHILE b1 DO c1 END => 
          if (beval st b1)           
          then LETOPT st' <== ceval_step st c1 i' IN
               ceval_step st' c i'
          else Some st
    end
  end.

Definition test_ceval (st:state) (c:com) := 
  match ceval_step st c 500 with
  | None    => None
  | Some st => Some (st X, st Y, st Z)
  end.  

(* Eval compute in 
     (test_ceval empty_state 
         (X ::= ANum 2;;
          IFB BLe (AId X) (ANum 1)
            THEN Y ::= ANum 3 
            ELSE Z ::= ANum 4
          FI)).
   ====>
      Some (2, 0, 4)   *)

(** **** Exercise: 2 stars (pup_to_n) *)
(** Write an Imp program that sums the numbers from [1] to
   [X] (inclusive: [1 + 2 + ... + X]) in the variable [Y].  Make sure
   your solution satisfies the test that follows. *)

Definition pup_to_n : com := 
  Y ::= (ANum 0);;
  WHILE (BNot (BLe (AId X) (ANum 0))) DO
    Y ::= APlus (AId Y) (AId X) ;;
    X ::= AMinus (AId X) (ANum 1)
  END.

Example pup_to_n_1 : 
  test_ceval (update empty_state X 5) pup_to_n
  = Some (0, 15, 0).
Proof. reflexivity. Qed.
(** [] *)

(** **** Exercise: 2 stars, optional (peven) *)
(** Write a [While] program that sets [Z] to [0] if [X] is even and
    sets [Z] to [1] otherwise.  Use [ceval_test] to test your
    program. *)
Definition peven : com :=
  Z ::= (ANum 0);;
  WHILE (BNot (BLe (AId X) (ANum 0))) DO
    X ::= AMinus (AId X) (ANum 1) ;;
    IFB (BEq (AId Z) (ANum 0)) THEN
      Z ::= (ANum 1)
    ELSE
      Z ::= (ANum 0)
    FI
  END.
Example peven_1 : 
  test_ceval (update empty_state X 5) peven
  = Some (0, 0, 1).
Proof. reflexivity. Qed.
Example peven_2 : 
  test_ceval (update empty_state X 8) peven
  = Some (0, 0, 0).
Proof. reflexivity. Qed.
(** [] *)

(* ################################################################ *)
(** ** Equivalence of Relational and Step-Indexed Evaluation *)

(** As with arithmetic and boolean expressions, we'd hope that
    the two alternative definitions of evaluation actually boil down
    to the same thing.  This section shows that this is the case.
    Make sure you understand the statements of the theorems and can
    follow the structure of the proofs. *)

Theorem ceval_step__ceval: forall c st st',
      (exists i, ceval_step st c i = Some st') ->
      c / st || st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [| i' ].

  Case "i = 0 -- contradictory".
    intros c st st' H. inversion H.

  Case "i = S i'".
    intros c st st' H.
    com_cases (destruct c) SCase; 
           simpl in H; inversion H; subst; clear H. 
      SCase "SKIP". apply E_Skip.
      SCase "::=". apply E_Ass. reflexivity.

      SCase ";;".
        destruct (ceval_step st c1 i') eqn:Heqr1. 
        SSCase "Evaluation of r1 terminates normally".
          apply E_Seq with s. 
            apply IHi'. rewrite Heqr1. reflexivity.
            apply IHi'. simpl in H1. assumption.
        SSCase "Otherwise -- contradiction".
          inversion H1.

      SCase "IFB". 
        destruct (beval st b) eqn:Heqr.
        SSCase "r = true".
          apply E_IfTrue. rewrite Heqr. reflexivity.
          apply IHi'. assumption.
        SSCase "r = false".
          apply E_IfFalse. rewrite Heqr. reflexivity.
          apply IHi'. assumption.

      SCase "WHILE". destruct (beval st b) eqn :Heqr.
        SSCase "r = true". 
         destruct (ceval_step st c i') eqn:Heqr1.
          SSSCase "r1 = Some s".
            apply E_WhileLoop with s. rewrite Heqr. reflexivity.
            apply IHi'. rewrite Heqr1. reflexivity. 
            apply IHi'. simpl in H1. assumption.
          SSSCase "r1 = None".
            inversion H1.
        SSCase "r = false".
          inversion H1. 
          apply E_WhileEnd. 
          rewrite <- Heqr. subst. reflexivity.  Qed.

(** **** Exercise: 4 stars (ceval_step__ceval_inf) *)
(** Write an informal proof of [ceval_step__ceval], following the
    usual template.  (The template for case analysis on an inductively
    defined value should look the same as for induction, except that
    there is no induction hypothesis.)  Make your proof communicate
    the main ideas to a human reader; do not simply transcribe the
    steps of the formal proof. *)

(* I am glad I am not submitting the following for marking. 

  We want to prove that, if the computation evaluates from state st 
    to state st' in some number of steps, then the computation reduces
    state st to st'.

   Call the number of steps i. We want to prove that, for all i,
       given that ceval_step st c i = Some st' implies c / st || st'

   We proceed by induction on i.

   In the case where i = 0, we have an assumption that
   ceval_step st c 0 = Some st', which is inconsistent, so this
   case never happens.

   In the case where i = S i', we have an assumption that st is evaluable
   to st' in (S i') steps, and by induction that for all computations,
   if it evaluates from state st to state st' in i' steps then it
   reduces from state st to st'.

   We consider all the possible computations c.
   
   SKIP and ::= are trivial, because they can't loop.

   If c = c1 ;; c2, we consider the possible results of evaluating c1. 
   When it terminates normally, we use the induction hypothesis in both
   cases and are done. The case where it doesn't terminate normally is
   inconsistent and doesn't need to be considered.

   If c = IFB a THEN c1 ELSE c2 FI, then a can evaluate to either
   true or false. When it evaluates to true, the command becomes c1 and
   the induction hypothesis applies. When it evaluates to false, the
   command becomes c2 and again the induction hypothesis applies.

   If c = WHILE b DO c1 END, b can evaluate to either true or false.
   
   First consider the case where b is true. We know that evaluating c1
   can either succeed, producing a state s, or fail. When it fails,
   our assumption that some state exists no longer holds, so we don't
   need to consider the case further. When it succeeds, we look at what
   needs to be true for the while loop to reduce the way we want it to.
   We need the test to evaluate to true, which we have as an assumption.
   We need executing c1 to evaluate to s, which is true by the induction
   hypothesis and the case that we're considering. And finally we need
   the loop to reduce s to st', which follows from the induction hypothesis
   and our assumption that some state exists.

   Next consider the case where b is false. The ceval_step term in our
   assumption is equal to Some st, so we know st and st' are equal. Therefore
   we need to prove that the while loop reduces a state st to the same state
   st, that is, that the while loop is a no-op in terms of reduction when
   the test is false. This follows directly from the test.




[]
*)

Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 -> 
  ceval_step st c i1 = Some st' -> 
  ceval_step st c i2 = Some st'.
Proof. 
induction i1 as [|i1']; intros i2 st st' c Hle Hceval.
  Case "i1 = 0".
    simpl in Hceval. inversion Hceval.
  Case "i1 = S i1'".
    destruct i2 as [|i2']. inversion Hle. 
    assert (Hle': i1' <= i2') by omega.
    com_cases (destruct c) SCase.
    SCase "SKIP".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase "::=".
      simpl in Hceval. inversion Hceval.
      reflexivity.
    SCase ";;".
      simpl in Hceval. simpl. 
      destruct (ceval_step st c1 i1') eqn:Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption.
        rewrite Heqst1'o. simpl. simpl in Hceval.
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "st1'o = None".
        inversion Hceval.

    SCase "IFB".
      simpl in Hceval. simpl.
      destruct (beval st b); apply (IHi1' i2') in Hceval; assumption.
    
    SCase "WHILE".
      simpl in Hceval. simpl.
      destruct (beval st b); try assumption. 
      destruct (ceval_step st c i1') eqn: Heqst1'o.
      SSCase "st1'o = Some".
        apply (IHi1' i2') in Heqst1'o; try assumption. 
        rewrite -> Heqst1'o. simpl. simpl in Hceval. 
        apply (IHi1' i2') in Hceval; try assumption.
      SSCase "i1'o = None".
        simpl in Hceval. inversion Hceval.  Qed.

(** **** Exercise: 3 stars (ceval__ceval_step) *)
(** Finish the following proof.  You'll need [ceval_step_more] in a
    few places, as well as some basic facts about [<=] and [plus]. *)

Theorem ceval__ceval_step: forall c st st',
      c / st || st' ->
      exists i, ceval_step st c i = Some st'.
Proof. 
  intros c st st' Hce.
  ceval_cases (induction Hce) Case.
  Case "E_Skip".
    exists 1. simpl. reflexivity.
  Case "E_Ass".
    exists 1. simpl. rewrite H. reflexivity.
  Case "E_Seq".
    inversion IHHce1.
    inversion IHHce2.
    exists (S (x + x0)).
    simpl.
    apply ceval_step_more with (i2:=x+x0) in H.
    apply ceval_step_more with (i2:=x+x0) in H0.
    rewrite H. rewrite H0. reflexivity.
    apply le_plus_r. apply le_plus_l.
  Case "E_IfTrue".
    inversion IHHce. exists (S x).
    simpl. rewrite H. apply H0.
  Case "E_IfFalse".
    inversion IHHce. exists (S x).
    simpl. rewrite H. apply H0.
  Case "E_WhileEnd".
    exists 1. simpl. rewrite H. reflexivity.
  Case "E_WhileLoop".
    inversion IHHce1.
    inversion IHHce2.
    exists (S (x + x0)).
    simpl. rewrite H.
    apply ceval_step_more with (i2:=x+x0) in H0.
    apply ceval_step_more with (i2:=x+x0) in H1.
    rewrite H0. rewrite H1. reflexivity.
      apply le_plus_r. apply le_plus_l.
Qed.
(** [] *)

Theorem ceval_and_ceval_step_coincide: forall c st st',
      c / st || st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
  intros c st st'.
  split. apply ceval__ceval_step. apply ceval_step__ceval.
Qed.

(* ####################################################### *)
(** ** Determinism of Evaluation (Simpler Proof) *)

(** Here's a slicker proof showing that the evaluation relation is
    deterministic, using the fact that the relational and step-indexed
    definition of evaluation are the same. *)

Theorem ceval_deterministic' : forall c st st1 st2,
     c / st || st1  ->
     c / st || st2 ->
     st1 = st2.
Proof. 
  intros c st st1 st2 He1 He2.
  apply ceval__ceval_step in He1.
  apply ceval__ceval_step in He2.
  inversion He1 as [i1 E1]. 
  inversion He2 as [i2 E2].
  apply ceval_step_more with (i2 := i1 + i2) in E1.
  apply ceval_step_more with (i2 := i1 + i2) in E2.
  rewrite E1 in E2. inversion E2. reflexivity. 
  omega. omega.  Qed.

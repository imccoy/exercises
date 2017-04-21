(** * Logic: Logic in Coq *)

Require Export Tactics.
Require Export Induction.


(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions ([forall
    x, P]).  In this chapter, we will see how Coq can be used to carry
    out other familiar forms of logical reasoning.

    Before diving into details, let's talk a bit about the status of
    mathematical statements in Coq.  Recall that Coq is a _typed_
    language, which means that every sensible expression in its world
    has an associated type.  Logical claims are no exception: any
    statement we might try to prove in Coq has a type, namely [Prop],
    the type of _propositions_.  We can see this with the [Check]
    command: *)

Check 3 = 3.
(* ===> Prop *)

Check forall n m : nat, n + m = m + n.
(* ===> Prop *)

(** Note that _all_ syntactically well-formed propositions have type
    [Prop] in Coq, regardless of whether they are true or not.

    Simply _being_ a proposition is one thing; being _provable_ is
    something else! *)

Check forall n : nat, n = 2.
(* ===> Prop *)

Check 3 = 4.
(* ===> Prop *)

(** Indeed, propositions don't just have types: they are _first-class
    objects_ that can be manipulated in the same ways as the other
    entities in Coq's world.  So far, we've seen one primary place
    that propositions can appear: in [Theorem] (and [Lemma] and
    [Example]) declarations. *)

Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof. reflexivity.  Qed.

(** But propositions can be used in many other ways.  For example, we
    can give a name to a proposition using a [Definition], just as we
    have given names to expressions of other sorts. *)

Definition plus_fact : Prop := 2 + 2 = 4.
Check plus_fact.
(* ===> plus_fact : Prop *)

(** We can later use this name in any situation where a proposition is
    expected -- for example, as the claim in a [Theorem] declaration. *)

Theorem plus_fact_is_true :
  plus_fact.
Proof. reflexivity.  Qed.

(** We can also write _parameterized_ propositions -- that is,
    functions that take arguments of some type and return a
    proposition. *)

(** For instance, the following function takes a number
    and returns a proposition asserting that this number is equal to
    three: *)

Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three.
(* ===> nat -> Prop *)

(** In Coq, functions that return propositions are said to define
    _properties_ of their arguments.

    For instance, here's a (polymorphic) property defining the
    familiar notion of an _injective function_. *)

Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.

(** **** Exercise: 1 star, optional (proj2) *)
Theorem proj2 : forall P Q : Prop, 
  P /\ Q -> Q.
Proof.
  intros P Q H.
  inversion H as [HP HQ].
  apply HQ.
Qed.
(** [] *)

Theorem and_commut : forall P Q : Prop, 
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q H.
  inversion H as [HP HQ]. 
  split.  
    -  (* left *) apply HQ. 
    -  (* right *) apply HP.  Qed.
  

(** **** Exercise: 2 stars (and_assoc) *)
(** In the following proof, notice how the _nested pattern_ in the
    [inversion] breaks the hypothesis [H : P /\ (Q /\ R)] down into
    [HP: P], [HQ : Q], and [HR : R].  Finish the proof from there: *)

Theorem and_assoc : forall P Q R : Prop, 
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  inversion H as [HP [HQ HR]].
  split.
    -  (* left *) split.
      +  (* left *) apply HP.
      +  (* right *) apply HQ.
    -  (* right *) apply HR.
Qed.
(** [] *)

Lemma succ_inj : injective S.
Proof.
  intros n m H. inversion H. reflexivity.
Qed.

Definition even (n:nat) : Prop := 
  evenb n = true.

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  intros n.
  induction n as [|n'].
    -  (* n = 0 *) split.
      +  (* ev 0 *) intros H. apply ev_0.
      +  (* ev (S 0) *) intros H. inversion H.
    -  (* n = S n' *) split.
      +  (* ev (S n') *)
        intros H. 
        inversion IHn'. apply H1. apply H.
      +  (* ev (S (S n')) *)
        intros H.
        inversion IHn'. apply ev_SS. apply H0.
        inversion H. unfold even. apply H3.
Qed.

(** [] *)
(** The equality operator [=] is also a function that returns a
    [Prop].
    The expression [n = m] is syntactic sugar for [eq n m], defined
    using Coq's [Notation] mechanism. Because [eq] can be used with
    elements of any type, it is also polymorphic: *)

Check @eq.
(* ===> forall A : Type, A -> A -> Prop *)

(** (Notice that we wrote [@eq] instead of [eq]: The type
    argument [A] to [eq] is declared as implicit, so we need to turn
    off implicit arguments to see the full type of [eq].) *)

(* ################################################################# *)
(** * Logical Connectives *)

(* ================================================================= *)
(** ** Conjunction *)

(** The _conjunction_ (or _logical and_) of propositions [A] and [B]
    is written [A /\ B], representing the claim that both [A] and [B]
    are true. *)

Example and_example : 3 + 4 = 7 /\ 2 * 2 = 4.

(** To prove a conjunction, use the [split] tactic.  It will generate
    two subgoals, one for each part of the statement: *)

Proof.
  (* WORKED IN CLASS *)
  split.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** For any propositions [A] and [B], if we assume that [A] is true
    and we assume that [B] is true, we can conclude that [A /\ B] is
    also true. *)

Theorem iff_refl : forall P : Prop, 
  P <-> P.
Proof. 
  intros P. split.
    intros HP. apply HP.
    intros HP. apply HP.
Qed.    

Theorem iff_trans : forall P Q R : Prop, 
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQ HQR.
  inversion HPQ as [HiPQ HiQP].
  inversion HQR as [HiQR HiRQ].
  split.
    -  (* P -> R *) intros HP. apply HiQR. apply HiPQ. apply HP.
    -  (* R -> P *) intros HR. apply HiQP. apply HiRQ. apply HR.
Qed.

(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)
Lemma and_intro : forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B HA HB. split.
  - apply HA.
  - apply HB.
Qed.

(** Since applying a theorem with hypotheses to some goal has the
    effect of generating as many subgoals as there are hypotheses for
    that theorem, we can apply [and_intro] to achieve the same effect
    as [split]. *)

Example and_example' : 3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - (* 3 + 4 = 7 *) reflexivity.
  - (* 2 + 2 = 4 *) reflexivity.
Qed.

(** **** Exercise: 2 stars (and_exercise)  *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  split.
  - induction m.
    rewrite <- plus_n_O in H. assumption.
    rewrite <- plus_n_Sm in H. inversion H.
  -  destruct n. simpl in H. assumption. simpl in H. inversion H.
Qed.

(** [] *)

(** So much for proving conjunctive statements.  To go in the other
    direction -- i.e., to _use_ a conjunctive hypothesis to help prove
    something else -- we employ the [destruct] tactic.

    If the proof context contains a hypothesis [H] of the form
    [A /\ B], writing [destruct H as [HA HB]] will remove [H] from the
    context and add two new hypotheses: [HA], stating that [A] is
    true, and [HB], stating that [B] is true.  *)

Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  (* WORKED IN CLASS *)
  intros n m H.
  destruct H as [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** As usual, we can also destruct [H] right when we introduce it,
    instead of introducing and then destructing it: *)

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [Hn Hm].
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** You may wonder why we bothered packing the two hypotheses [n = 0]
    and [m = 0] into a single conjunction, since we could have also
    stated the theorem with two separate premises: *)

Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m Hn Hm.
  rewrite Hn. rewrite Hm.
  reflexivity.
Qed.

(** For this theorem, both formulations are fine.  But it's important
    to understand how to work with conjunctive hypotheses because
    conjunctions often arise from intermediate steps in proofs,
    especially in bigger developments.  Here's a simple example: *)

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  assert (H' : n = 0 /\ m = 0).
  { apply and_exercise. apply H. }
  destruct H' as [Hn Hm].
  rewrite Hn. reflexivity.
Qed.

(** Another common situation with conjunctions is that we know
    [A /\ B] but in some context we need just [A] (or just [B]).
    The following lemmas are useful in such cases: *)

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q [HP HQ].
  apply HP.  Qed.

(** **** Exercise: 1 star, optional (proj2)  *)
Lemma proj2' : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q [HP HQ].      
  apply HQ. Qed.
(** [] *)

(** Finally, we sometimes need to rearrange the order of conjunctions
    and/or the grouping of multi-way conjunctions.  The following
    commutativity and associativity theorems are handy in such
    cases. *)

Theorem and_commut' : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HQ].
  split.
    - (* left *) apply HQ.
    - (* right *) apply HP.  Qed.
  
(** By the way, the infix notation [/\] is actually just syntactic
    sugar for [and A B].  That is, [and] is a Coq operator that takes
    two propositions as arguments and yields a proposition. *)

Check and.
(* ===> and : Prop -> Prop -> Prop *)

(* ================================================================= *)
(** ** Disjunction *)

(** Another important connective is the _disjunction_, or _logical or_
    of two propositions: [A \/ B] is true when either [A] or [B]
    is.  (Alternatively, we can write [or A B], where [or : Prop ->
    Prop -> Prop].)

    To use a disjunctive hypothesis in a proof, we proceed by case
    analysis, which, as for [nat] or other data types, can be done
    with [destruct] or [intros].  Here is an example: *)

Lemma or_example :
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m H.
  destruct H.
  - rewrite H. reflexivity.
  - rewrite H. rewrite mult_0_r. reflexivity.
  
Qed.

(** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
    - intros H. destruct H. split. left. assumption. left. assumption.
      destruct H. split. right. assumption. right. assumption.
    - intros [HPQ HPR]. 
      destruct HPQ. 
        + left. assumption.
        + destruct HPR. left. assumption. right. split; assumption.

Qed.
(** [] *)

(** Conversely, to show that a disjunction holds, we need to show that
    one of its sides does. This is done via two tactics, [left] and
    [right].  As their names imply, the first one requires
    proving the left side of the disjunction, while the second
    requires proving its right side.  Here is a trivial use... *)

Lemma or_intro : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.

(** ... and a slightly more interesting example requiring both [left]
    and [right]: *)

Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros [|n].
  - left. reflexivity.
  - right. reflexivity.
Qed.

(** **** Exercise: 1 star (mult_eq_0)  *)
Lemma mult_eq_0 :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros b c H.
  induction b. left. reflexivity. simpl in H.
  assert (Hplus_n_0_0: forall m n, m + n * m = 0 -> m = 0).
    intros m n Hmult. induction m. reflexivity. simpl in Hmult. inversion Hmult.
  apply Hplus_n_0_0 in H. right. assumption.
Qed.

(** **** Exercise: 2 stars, optional (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  intros b c H.
  destruct b.
    -  (* b = true *) destruct c.
      +  (* c = true *) inversion H.
      +  (* c = false *) right. reflexivity.
    -  (* b = false *) left. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 1 star (or_commut)  *)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q HPQ.
  destruct HPQ. right. assumption. left. assumption.
Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros b c Horb.
  destruct b.
    -  (* b = true *) inversion Horb.
    -  (* b = false *) destruct c.
      +  (* c = true *) inversion Horb.
      +  (* c = false *) split. reflexivity. reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** Falsehood and Negation *)

(** So far, we have mostly been concerned with proving that certain
    things are _true_ -- addition is commutative, appending lists is
    associative, etc.  Of course, we may also be interested in
    _negative_ results, showing that certain propositions are _not_
    true. In Coq, such negative statements are expressed with the
    negation operator [~].

    To see how negation works, recall the discussion of the _principle
    of explosion_ from the [Tactics] chapter; it asserts that, if we
    assume a contradiction, then any other proposition can be derived.
    Following this intuition, we could define [~ P] ("not [P]") as
    [forall Q, P -> Q].  Coq actually makes a slightly different
    choice, defining [~ P] as [P -> False], where [False] is a
    _particular_ contradictory proposition defined in the standard
    library. *)

Module MyNot.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

End MyNot.

(** Since [False] is a contradictory proposition, the principle of
    explosion also applies to it. If we get [False] into the proof
    context, we can [destruct] it to complete any goal: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  destruct contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from falsehood
    follows whatever you like"; this is another common name for the
    principle of explosion. *)

(** **** Exercise: 2 stars, optional (not_implies_our_not)  *)
(** Show that Coq's definition of negation implies the intuitive one
    mentioned above: *)


Fact not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HnotP Q HP. unfold not in HnotP. apply HnotP in HP. inversion HP.
Qed.
(** [] *)

(** This is how we use [not] to state that [0] and [1] are different
    elements of [nat]: *)

Theorem zero_not_one : ~(0 = 1).
Proof.
  intros contra. inversion contra.
Qed.

(** Such inequality statements are frequent enough to warrant a
    special notation, [x <> y]: *)

Check (0 <> 1).
(* ===> Prop *)

Theorem zero_not_one' : 0 <> 1.
Proof.
  intros H. inversion H.
Qed.

(** It takes a little practice to get used to working with negation in
    Coq.  Even though you can see perfectly well why a statement
    involving negation is true, it can be a little tricky at first to
    get things into the right configuration so that Coq can understand
    it!  Here are proofs of a few familiar facts to get you warmed
    up. *)

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H. destruct H. Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HP HNA]. unfold not in HNA.
  apply HNA in HP. destruct HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced, recommendedM (double_neg_inf)  *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P]. *)

   (*
   _Proof_: (one way)
     We know that P holds. Therefore, not-P doesn't. Since not-P doesn't hold,
     it follows that not-not-P does hold.

   _Proof_: (another way)
     We want to prove that (not (not P)) holds. This is equivalent to proving
     that (not P) implies False.
       
     We know P holds, so (not P) is False. Since (not P) is False, proving
     that (not P) implies False is trivial and we're done.
*)
(** [] *)

(** **** Exercise: 2 stars, recommended (contrapositive)  *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HnQ.
  unfold not in HnQ.
  unfold not. intros HP.
  apply HPQ in HP. apply HnQ in HP. apply HP.
Qed.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false)  *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intros P. unfold not. apply contradiction_implies_anything.
Qed.
(** [] *)

(** **** Exercise: 1 star, advancedM (informal_not_PNP)  *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(*
P either holds or does not hold, but not both. For P /\ ~P to hold, P
would need to both hold and not hold. Therefore it is not the case
that P /\ ~P, and we can say it is true that ~(P /\ ~P).

These informal proofs are the hardest bit of this book.
*)

(** [] *)

(** Similarly, since inequality involves a negation, it requires a
    little practice to be able to work with it fluently.  Here is one
    useful trick.  If you are trying to prove a goal that is
    nonsensical (e.g., the goal state is [false = true]), apply
    [ex_falso_quodlibet] to change the goal to [False].  This makes it
    easier to use assumptions of the form [~P] that may be available
    in the context -- in particular, assumptions of the form
    [x<>y]. *)

Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = true *)
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H. reflexivity.
  - (* b = false *)
    reflexivity.
Qed.

(** Since reasoning with [ex_falso_quodlibet] is quite common, Coq
    provides a built-in tactic, [exfalso], for applying it. *)

Theorem ev_S_S_ev : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H.
  inversion H. assumption. Qed.

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. (* not n! *)
  -  (* ev 1 *) intros H. inversion H.
  -  (* ev (S (S (S n))) *)
    intros HevSSS. apply ev_S_S_ev in HevSSS.
    apply IHev. assumption.
Qed.
(** [] *)

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  intros [] H.
  - (* b = false *)
    unfold not in H.
    exfalso.                (* <=== *)
    apply H. reflexivity.
  - (* b = true *) reflexivity.
Qed.

(* ================================================================= *)
(** ** Truth *)

(** Besides [False], Coq's standard library also defines [True], a
    proposition that is trivially true. To prove it, we use the
    predefined constant [I : True]: *)

Lemma True_is_true : True.
Proof. apply I. Qed.

Definition peirce := forall P Q: Prop, 
  ((P->Q)->P)->P.
Definition classic := forall P:Prop, 
  ~~P -> P.
Definition excluded_middle := forall P:Prop, 
  P \/ ~P.
Definition de_morgan_not_and_not := forall P Q:Prop, 
  ~(~P /\ ~Q) -> P\/Q.
Definition implies_to_or := forall P Q:Prop, 
  (P->Q) -> (~P\/Q). 

Theorem excluded_middle_classic : excluded_middle -> classic.
Proof. unfold excluded_middle. unfold classic.
  intros Hclassic P.
  assert (Hor := Hclassic P).
  inversion Hor.
  intros HP. apply H.
  unfold not. unfold not in H.
  intros HP. apply HP in H. inversion H.
Qed.

Theorem de_morgan_not_and_not_excluded_middle : de_morgan_not_and_not -> excluded_middle.
Proof. unfold de_morgan_not_and_not. unfold excluded_middle.
  intros Hdm Q.
  assert (HdmQQ := Hdm Q (~Q)).
  apply HdmQQ.
  apply not_both_true_and_false.
Qed.

Theorem classic_de_morgan_not_and_not : classic -> de_morgan_not_and_not.
Proof. unfold classic. unfold de_morgan_not_and_not.
  intros Hclassic P Q.
  assert (HcP := Hclassic (P \/ Q)).
  intros H.
  apply HcP.
  unfold not. unfold not in H.
  intros HPorQ.
  apply H.
  split.
  intros HP. apply HPorQ. left. apply HP.
  intros HQ. apply HPorQ. right. apply HQ.
Qed.

Theorem excluded_middle_implies_to_or : excluded_middle -> implies_to_or.
Proof. unfold excluded_middle. unfold implies_to_or.
  intros Hito P Q.
  assert (HitoP := Hito P).
    inversion HitoP.
      intros HPQ. apply HPQ in H. right. apply H.
      intros HPQ. left. apply H.
Qed.

Theorem implies_to_or_excluded_middle : implies_to_or -> excluded_middle.
Proof. unfold implies_to_or. unfold excluded_middle.
  intros Hexm.
  intros P.
  apply or_commut. apply Hexm.
  intros HP. apply HP.
Qed.

Theorem imp_trans : forall P Q R : Prop,
  (P -> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R HPQ HQR HP.
  apply HQR. apply HPQ. apply HP.
Qed.

Theorem excluded_middle_peirce : excluded_middle -> peirce.
Proof. unfold excluded_middle. unfold peirce.
  intros Hem P Q.
  assert (HemP := Hem P). unfold not in HemP.
  inversion HemP.
    intros HPQP. apply H.
    intros HPQP.
      assert (HPQF := imp_trans (P -> Q) P False).
      assert (HPQP' := HPQP).
      apply HPQF in HPQP'. inversion HPQP'. apply H.
      intros HP. apply H in HP. inversion HP.
Qed.

Theorem peirce_classic : peirce -> classic.
Proof. unfold peirce. unfold classic.
  intros Hp P. unfold not.
  intros HPFF.
  apply Hp with (Q := False).
  intros H.
  apply HPFF in H.
  inversion H.
Qed.

(* connect them all up, now, just to see if we can. *)
Theorem classic__peirce: classic <-> peirce.
Proof. split.
  intros Hclassic. apply excluded_middle_peirce.  apply de_morgan_not_and_not_excluded_middle. apply classic_de_morgan_not_and_not. apply Hclassic.
  intros Hpeirce. apply peirce_classic. apply Hpeirce.
Qed.
Theorem excluded_middle__classic: excluded_middle <-> classic.
Proof. split.
  intros Hexm. apply excluded_middle_classic. apply Hexm.
  intros Hclassic. apply de_morgan_not_and_not_excluded_middle. apply classic_de_morgan_not_and_not. apply Hclassic.
Qed.
Theorem de_morgan_not_and_not__excluded_middle: de_morgan_not_and_not <-> excluded_middle.
Proof. split.
  intros Hdm. apply de_morgan_not_and_not_excluded_middle. apply Hdm.
  intros Hexm. apply classic_de_morgan_not_and_not. apply excluded_middle_classic. apply Hexm.
Qed.
Theorem implies_to_or__de_morgan_not_and_not: implies_to_or <-> de_morgan_not_and_not.
Proof. split.
  intros Hito. apply classic_de_morgan_not_and_not. apply excluded_middle_classic. apply implies_to_or_excluded_middle. apply Hito.
  intros Hdm. apply excluded_middle_implies_to_or. apply de_morgan_not_and_not_excluded_middle. apply Hdm.
Qed.
Theorem peirce__implies_to_or: peirce <-> implies_to_or.
Proof. split.
  intros Hpeirce. apply excluded_middle_implies_to_or. apply de_morgan_not_and_not_excluded_middle. apply classic_de_morgan_not_and_not. apply peirce_classic. apply Hpeirce.
  intros Hito. apply excluded_middle_peirce. apply implies_to_or_excluded_middle. apply Hito.
Qed.


(** [] *)
(** Unlike [False], which is used extensively, [True] is used quite
    rarely, since it is trivial (and therefore uninteresting) to prove
    as a goal, and it carries no useful information as a hypothesis.
    But it can be quite useful when defining complex [Prop]s using
    conditionals or as a parameter to higher-order [Prop]s.  We will
    see examples of such uses of [True] later on.
*)

(* ================================================================= *)
(** ** Logical Equivalence *)

(** The handy "if and only if" connective, which asserts that two
    propositions have the same truth value, is just the conjunction of
    two implications. *)

Module MyIff.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                      (at level 95, no associativity)
                      : type_scope.

End MyIff.

Theorem iff_sym : forall P Q : Prop,
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q [HAB HBA].
  split.
  - (* -> *) apply HBA.
  - (* <- *) apply HAB.  Qed.

Theorem Sn_ne_Sm__n_ne_m: forall n m: nat,
  S n <> S m -> n <> m.
Proof.
  intros n.
  induction n.
    intros m H. destruct m.
      unfold not in H. unfold not. intros H0. apply H. reflexivity.
      unfold not in H. unfold not. intros H0Sm. inversion H0Sm.
    intros m H. destruct m.
      -  (* 0 *)
        unfold not in H.
        unfold not. intros HSn0.
        inversion HSn0.
      -  (* S *)
        unfold not in H.
        unfold not. intros HSnSm.
        inversion HSnSm. apply H. rewrite H1. reflexivity.
Qed.

(** **** Exercise: 2 stars (false_beq_nat) *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. 
  intros n.
  induction n as [|n'].
    -  (* n = 0 *) intros m H. destruct m as [|m'].
      +  (* m = 0 *)
        simpl. apply ex_falso_quodlibet.
        unfold not in H. apply H. reflexivity.
      +  (* m = S m' *)
        simpl. reflexivity.
    -  (* n = 1 *) intros m H. destruct m as [|m'].
      +  (* m = 0 *)
        simpl. reflexivity.
      +  (* m = S m' *)
        apply Sn_ne_Sm__n_ne_m in H.
        simpl. apply IHn'. apply H.
Qed.
(** [] *)


(** **** Exercise: 2 stars, optional (beq_nat_false) *)
Theorem beq_nat_n_n : forall n,
  beq_nat n n = true.
Proof.
  intros n.
  induction n.
    simpl. reflexivity.
    simpl. rewrite IHn. reflexivity.
Qed.

Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  (* WORKED IN CLASS *)
  intros b. split.
  - (* -> *) apply not_true_is_false.
  - (* <- *)
    intros H. rewrite H. intros H'. inversion H'.
Qed.

(** **** Exercise: 1 star, optional (iff_properties)  *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

Theorem iff_refl' : forall P : Prop,
  P <-> P.
Proof.
  intros P. split.
  - intros H. assumption.
  - intros H. assumption.
Qed.

Theorem iff_trans' : forall P Q R : Prop,
  (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R HPQP HQRQ. destruct HPQP as [HPQ HQP]. destruct HQRQ as [HQR HRQ]. split.
  - intros HP. apply HQR. apply HPQ. assumption.
  - intros HR. apply HQP. apply HRQ. assumption.
Qed.

Theorem beq_nat_false : forall n m,
  beq_nat n m = false -> n <> m.
Proof.
  intros n m H.
  unfold not.
  intros Hnm.
  rewrite Hnm in H. rewrite beq_nat_n_n in H. inversion H.
Qed.
(** [] *)

Theorem O_le_n: forall n,
  0 <= n.
Proof.
  intros n. induction n.
    apply le_n.
    apply le_S. apply IHn.
Qed.

Theorem Sn_le_Sm__n_le_m: forall n m: nat,
  S n <= S m -> n <= m.
Proof.
  intros n m H. generalize dependent n. induction m as [|m'].
    intros n H. destruct n as [|n'].
      apply le_n.
      inversion H. inversion H1.
    intros n H. inversion H.
      apply le_n.
      apply le_S.
      apply IHm' in H1. apply H1.
Qed.
      
Theorem leb_true : forall n m,
  leb n m = true -> n <= m.
Proof. intros n m Hnm.
  generalize dependent n.
  induction m.
  - intros n Hn. destruct n. left. simpl in Hn. inversion Hn.
  - intros n Hn. destruct n. apply le_0_n. apply le_n_S. apply IHm. simpl in Hn. assumption.
Qed.

Theorem lte_leb_true : forall n m,
  n <= m -> leb n m = true.
Proof. intros n m Hnm.
  generalize dependent m.
  induction n. 
  - intros m Hm. reflexivity.
  - intros m Hm. destruct m.
    + inversion Hm.
    + simpl. apply IHn. apply le_S_n. assumption.
Qed.

(** **** Exercise: 2 stars, optional (ble_nat_false) *)
Theorem leb_false : forall n m,
  leb n m = false -> ~(n <= m).
Proof. intros n m Hnm.
  intros H.
  apply lte_leb_true in H. rewrite H in Hnm. inversion Hnm.
Qed.

(** Some of Coq's tactics treat [iff] statements specially, avoiding
    the need for some low-level proof-state manipulation.  In
    particular, [rewrite] and [reflexivity] can be used with [iff]
    statements, not just equalities.  To enable this behavior, we need
    to import a special Coq library that allows rewriting with other
    formulas besides equality: *)

Require Import Coq.Setoids.Setoid.

(** Here is a simple example demonstrating how these tactics work with
    [iff].  First, let's prove a couple of basic iff equivalences... *)

Lemma mult_0 : forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_eq_0.
  - apply or_example.
Qed.

Lemma or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R. split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.

(** We can now use these facts with [rewrite] and [reflexivity] to
    give smooth proofs of statements involving equivalences.  Here is
    a ternary version of the previous [mult_0] result: *)

Lemma mult_0_3 :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mult_0. rewrite mult_0. rewrite or_assoc.
  reflexivity.
Qed.

(** The [apply] tactic can also be used with [<->]. When given an
    equivalence as its argument, [apply] tries to guess which side of
    the equivalence to use. *)

Lemma apply_iff_example :
  forall n m : nat, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H. apply mult_0. apply H.
Qed.

(* ================================================================= *)
(** ** Existential Quantification *)

(** Another important logical connective is _existential
    quantification_.  To say that there is some [x] of type [T] such
    that some property [P] holds of [x], we write [exists x : T,
    P]. As with [forall], the type annotation [: T] can be omitted if
    Coq is able to infer from the context what the type of [x] should
    be. *)

(** To prove a statement of the form [exists x, P], we must show that
    [P] holds for some specific choice of value for [x], known as the
    _witness_ of the existential.  This is done in two steps: First,
    we explicitly tell Coq which witness [t] we have in mind by
    invoking the tactic [exists t].  Then we prove that [P] holds after
    all occurrences of [x] are replaced by [t]. *)

Lemma four_is_even : exists n : nat, 4 = n + n.
Proof.
  exists 2. reflexivity.
Qed.

(** Conversely, if we have an existential hypothesis [exists x, P] in
    the context, we can destruct it to obtain a witness [x] and a
    hypothesis stating that [P] holds of [x]. *)

Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  (* WORKED IN CLASS *)
  intros n [m Hm]. (* note implicit [destruct] here *)
  exists (2 + m).
  apply Hm.  Qed.

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* There is a natural number whose successor is beautiful. *)

(** **** Exercise: 1 star (dist_not_exists)  *)
(** Prove that "[P] holds for all [x]" implies "there is no [x] for
    which [P] does not hold." *)

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof. 
  intros X P Hforall.
  unfold not.
  intros Hexists.
  inversion Hexists as [HX HPHX].
  apply HPHX in Hforall.
  apply Hforall.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (not_exists_dist) *)
(** (The other direction of this theorem requires the classical "law
    of the excluded middle".) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros Hexm X P Hexists x.
  unfold excluded_middle in Hexm.
  unfold not in Hexists.
  assert (Px := (Hexm (P x))).
  inversion Px as [HPx|HNPx]. apply HPx.
  unfold not in HNPx. 
  assert (He: exists x, (P x -> False)).
  exists x.
  apply HNPx.
  apply Hexists in He.
  inversion He.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or)  *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  -  (* exists (P \/ Q) -> (exists P) \/ (exists Q) *)
    intro Hexists. inversion Hexists as [x HPQ]. inversion HPQ.
    left. exists x. apply H.
    right. exists x. apply H.
  -  (* (exists P) \/ (exists Q) -> exists (P \/ Q) *)
    intro Hexists. inversion Hexists.
    inversion H as [Hx HP]. exists Hx. left. apply HP.
    inversion H as [Hx HQ]. exists Hx. right. apply HQ.
Qed.
(** [] *)

(* ################################################################# *)
(** * Programming with Propositions *)

(** The logical connectives that we have seen provide a rich
    vocabulary for defining complex propositions from simpler ones.
    To illustrate, let's look at how to express the claim that an
    element [x] occurs in a list [l].  Notice that this property has a
    simple recursive structure: *)

(** - If [l] is the empty list, then [x] cannot occur on it, so the
      property "[x] appears in [l]" is simply false.

    - Otherwise, [l] has the form [x' :: l'].  In this case, [x]
      occurs in [l] if either it is equal to [x'] or it occurs in
      [l'].

    We can translate this directly into a straightforward recursive
    function from taking an element and a list and returning a
    proposition: *)

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [ ] => False
  | x' :: l' => x' = x \/ In x l'
  end.

(** When [In] is applied to a concrete list, it expands into a
    concrete sequence of nested disjunctions. *)

Example In_example_1 : In 4 [1; 2; 3; 4; 5].
Proof.
  (* WORKED IN CLASS *)
  simpl. right. right. right. left. reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  (* WORKED IN CLASS *)
  simpl.
  intros n [H | [H | []]].
  - exists 1. rewrite <- H. reflexivity.
  - exists 2. rewrite <- H. reflexivity.
Qed.
(** (Notice the use of the empty pattern to discharge the last case
    _en passant_.) *)

(** We can also prove more generic, higher-level lemmas about [In].

    Note, in the next, how [In] starts out applied to a variable and
    only gets expanded when we do case analysis on this variable: *)

Lemma In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
    In x l ->
    In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - (* l = nil, contradiction *)
    simpl. intros [].
  - (* l = x' :: l' *)
    simpl. intros [H | H].
    + rewrite H. left. reflexivity.
    + right. apply IHl'. apply H.
Qed.

(** This way of defining propositions recursively, though convenient
    in some cases, also has some drawbacks.  In particular, it is
    subject to Coq's usual restrictions regarding the definition of
    recursive functions, e.g., the requirement that they be "obviously
    terminating."  In the next chapter, we will see how to define
    propositions _inductively_, a different technique with its own set
    of strengths and limitations. *)

Lemma in_map_cons :
    forall (A : Type) (l : list A) (x y : A),
    In y l -> In y (x::l).
Proof.
  intros A l.
  induction l.
  - intros x y H. inversion H.
  - intros x' y H. inversion H.
    + simpl. right. left. assumption.
    + simpl. right. right. assumption.
Qed.


Lemma and_or_distr :
  forall A B C, (A /\ (B \/ C)) <-> (A /\ B) \/ (A /\ C).
Proof.
  intros A B C. split.
  - intros H. inversion H. inversion H1. 
    + left; split; assumption. 
    + right; split; assumption.
  -  intros H. split.
    + inversion H. inversion H0. assumption. inversion H0. assumption.
    + inversion H. inversion H0. left. assumption. inversion H0. right. assumption.
Qed.


Lemma exists_or_distr : forall (X : Type) (A B : X -> Prop),
  (exists x, (A x \/ B x)) -> (exists x, A x) \/ (exists x, B x).
Proof.
  intros X A B H.
  inversion H. inversion H0.
  left. exists x. assumption.
  right. exists x. assumption.
Qed.

(** **** Exercise: 2 stars (In_map_iff)  *)
Lemma In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
    In y (map f l) <->
    exists x, f x = y /\ In x l.
Proof.
  intros A B f l.
  split.
  - intros H. generalize dependent y. induction l.
      + intros y H. inversion H.
      + intros y H. inversion H.
        * exists x. split. assumption. simpl. left. reflexivity.
        * assert (Hxl := IHl y H0). inversion Hxl. exists x0. inversion H1. split.
          assumption.
          apply in_map_cons. assumption.
  - intros H. generalize dependent y. induction l.
      + intros y H. inversion H. inversion H0. inversion H2.
      + intros y H. simpl in H.
        assert (HB: (exists x0 : A, f x0 = y /\ x = x0) \/ (exists x0 : A, f x0 = y /\ In x0 l)).
          apply exists_or_distr. inversion H. exists x0. apply and_or_distr. assumption.
          inversion HB. simpl. inversion H0. inversion H1. subst. left. reflexivity.
          simpl. right. apply IHl. assumption.
Qed.
(** [] *)

Lemma in_cons_conj : forall (A:Type) (l l':list A) (a b:A),
  In a l \/ In a (b::l') <-> In a (b::l) \/ In a l'.
Proof.
  intros A l l' a b.
  split; intros H.
  - inversion H. simpl. left. right. assumption.
    inversion H0. simpl. left. left. assumption. right. assumption.
  - inversion H. inversion H0. simpl. right. left. assumption.
    left. assumption. simpl. right. right. assumption.
Qed.

(** **** Exercise: 2 stars (in_app_iff)  *)
Lemma in_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  - (* -> *)
    intros H. generalize dependent l'. generalize dependent a.
    induction l.
      +  intros a l' H. simpl in H. right. assumption.
      + intros a l' H. simpl. 
        simpl in H. inversion H.
          left. left. assumption.
          rewrite <- or_assoc. right. apply IHl. assumption.
 - (* <- *)
    intros H. generalize dependent l'. generalize dependent a.
    induction l.
    + intros a l' H. inversion H. inversion H0. simpl. assumption.
    + intros a l' H. assert (In a l \/ In a (x :: l')). inversion H. apply in_cons_conj in H. assumption. apply in_cons_conj. assumption. simpl. simpl in H. apply or_assoc in H. inversion H.
      * left. assumption.
      *  right. apply IHl. assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars (All)  *)
(** Recall that functions returning propositions can be seen as
    _properties_ of their arguments. For instance, if [P] has type
    [nat -> Prop], then [P n] states that property [P] holds of [n].

    Drawing inspiration from [In], write a recursive function [All]
    stating that some property [P] holds of all elements of a list
    [l]. To make sure your definition is correct, prove the [All_In]
    lemma below.  (Of course, your definition should _not_ just
    restate the left-hand side of [All_In].) *)

Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
   | (x :: xs) => P x /\ (All P xs)
   | [] => True
  end.

Lemma All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split.
  - intros H.
    induction l.
      simpl. apply I.
      simpl. split.
        apply H. simpl. left. reflexivity.
        apply IHl. intros x0 Hx0. apply H. simpl. right. assumption.
  
  
  - induction l; intros H x' Hin. inversion Hin.
       simpl in H. inversion H.
       simpl in Hin.
       inversion Hin. subst. assumption.
       apply IHl. assumption. assumption.
Qed.
(** [] *)

(** **** Exercise: 3 stars (combine_odd_even)  *)
(** Complete the definition of the [combine_odd_even] function below.
    It takes as arguments two properties of numbers, [Podd] and
    [Peven], and it should return a property [P] such that [P n] is
    equivalent to [Podd n] when [n] is odd and equivalent to [Peven n]
    otherwise. *)

Definition combine_odd_even (Podd Peven : nat -> Prop) : nat -> Prop :=
  fun (n: nat) => if oddb n then Podd n else Peven n.


(** To test your definition, prove the following facts: *)

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (oddb n = true -> Podd n) ->
    (oddb n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n Hodd Heven.
  unfold combine_odd_even.
  destruct (oddb n).
    apply Hodd. reflexivity.
    apply Heven. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = true ->
    Podd n.
Proof.
  intros Podd Peven n Hcomb Hodd.
  unfold combine_odd_even in Hcomb. rewrite Hodd in Hcomb. assumption.
Qed.

Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    oddb n = false ->
    Peven n.
Proof.
  intros Podd Peven n Hcomb Hoddb.
  unfold combine_odd_even in Hcomb. rewrite Hoddb in Hcomb. assumption.
Qed.
(** [] *)

(* ################################################################# *)
(** * Applying Theorems to Arguments *)

(** One feature of Coq that distinguishes it from many other proof
    assistants is that it treats _proofs_ as first-class objects.

    There is a great deal to be said about this, but it is not
    necessary to understand it in detail in order to use Coq.  This
    section gives just a taste, while a deeper exploration can be
    found in the optional chapters [ProofObjects] and
    [IndPrinciples]. *)

(** We have seen that we can use the [Check] command to ask Coq to
    print the type of an expression.  We can also use [Check] to ask
    what theorem a particular identifier refers to. *)

Check plus_comm.
(* ===> forall n m : nat, n + m = m + n *)

(** Coq prints the _statement_ of the [plus_comm] theorem in the same
    way that it prints the _type_ of any term that we ask it to
    [Check].  Why?

    The reason is that the identifier [plus_comm] actually refers to a
    _proof object_ -- a data structure that represents a logical
    derivation establishing of the truth of the statement [forall n m
    : nat, n + m = m + n].  The type of this object _is_ the statement
    of the theorem that it is a proof of. *)

(** Intuitively, this makes sense because the statement of a theorem
    tells us what we can use that theorem for, just as the type of a
    computational object tells us what we can do with that object --
    e.g., if we have a term of type [nat -> nat -> nat], we can give
    it two [nat]s as arguments and get a [nat] back.  Similarly, if we
    have an object of type [n = m -> n + n = m + m] and we provide it
    an "argument" of type [n = m], we can derive [n + n = m + m]. *)

(** Operationally, this analogy goes even further: by applying a
    theorem, as if it were a function, to hypotheses with matching
    types, we can specialize its result without having to resort to
    intermediate assertions.  For example, suppose we wanted to prove
    the following result: *)

Lemma plus_comm3 :
  forall n m p, n + (m + p) = (p + m) + n.

(** It appears at first sight that we ought to be able to prove this
    by rewriting with [plus_comm] twice to make the two sides match.
    The problem, however, is that the second [rewrite] will undo the
    effect of the first. *)

Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite plus_comm.
  (* We are back where we started... *)
Abort.

(** One simple way of fixing this problem, using only tools that we
    already know, is to use [assert] to derive a specialized version
    of [plus_comm] that can be used to rewrite exactly where we
    want. *)

Lemma plus_comm3_take2 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  assert (H : m + p = p + m).
  { rewrite plus_comm. reflexivity. }
  rewrite H.
  reflexivity.
Qed.

(** A more elegant alternative is to apply [plus_comm] directly to the
    arguments we want to instantiate it with, in much the same way as
    we apply a polymorphic function to a type argument. *)

Lemma plus_comm3_take3 :
  forall n m p, n + (m + p) = (p + m) + n.
Proof.
  intros n m p.
  rewrite plus_comm.
  rewrite (plus_comm m).
  reflexivity.
Qed.

(** You can "use theorems as functions" in this way with almost all
    tactics that take a theorem name as an argument.  Note also that
    theorem application uses the same inference mechanisms as function
    application; thus, it is possible, for example, to supply
    wildcards as arguments to be inferred, or to declare some
    hypotheses to a theorem as implicit by default.  These features
    are illustrated in the proof below. *)

Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
           as [m [Hm _]].
  rewrite mult_0_r in Hm. rewrite <- Hm. reflexivity.
Qed.

(** We will see many more examples of the idioms from this section in
    later chapters. *)

(* ################################################################# *)
(** * Coq vs. Set Theory *)

(** Coq's logical core, the _Calculus of Inductive Constructions_,
    differs in some important ways from other formal systems that are
    used by mathematicians for writing down precise and rigorous
    proofs.  For example, in the most popular foundation for
    mainstream paper-and-pencil mathematics, Zermelo-Fraenkel Set
    Theory (ZFC), a mathematical object can potentially be a member of
    many different sets; a term in Coq's logic, on the other hand, is
    a member of at most one type.  This difference often leads to
    slightly different ways of capturing informal mathematical
    concepts, but these are, by and large, quite natural and easy to
    work with.  For example, instead of saying that a natural number
    [n] belongs to the set of even numbers, we would say in Coq that
    [ev n] holds, where [ev : nat -> Prop] is a property describing
    even numbers.

    However, there are some cases where translating standard
    mathematical reasoning into Coq can be either cumbersome or
    sometimes even impossible, unless we enrich the core logic with
    additional axioms.  We conclude this chapter with a brief
    discussion of some of the most significant differences between the
    two worlds. *)

(* ================================================================= *)
(** ** Functional Extensionality *)

(** The equality assertions that we have seen so far mostly have
    concerned elements of inductive types ([nat], [bool], etc.).  But
    since Coq's equality operator is polymorphic, these are not the
    only possibilities -- in particular, we can write propositions
    claiming that two _functions_ are equal to each other: *)

Example function_equality_ex1 : plus 3 = plus (pred 4).
Proof. reflexivity. Qed.

(** In common mathematical practice, two functions [f] and [g] are
    considered equal if they produce the same outputs:

    (forall x, f x = g x) -> f = g

    This is known as the principle of _functional extensionality_.

    Informally speaking, an "extensional property" is one that
    pertains to an object's observable behavior.  Thus, functional
    extensionality simply means that a function's identity is
    completely determined by what we can observe from it -- i.e., in
    Coq terms, the results we obtain after applying it.

    Functional extensionality is not part of Coq's basic axioms.  This
    means that some "reasonable" propositions are not provable. *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.

(** However, we can add functional extensionality to Coq's core logic
    using the [Axiom] command. *)

Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.

(** Using [Axiom] has the same effect as stating a theorem and
    skipping its proof using [Admitted], but it alerts the reader that
    this isn't just something we're going to come back and fill in
    later!

    We can now invoke functional extensionality in proofs: *)

Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply plus_comm.
Qed.

(** Naturally, we must be careful when adding new axioms into Coq's
    logic, as they may render it _inconsistent_ -- that is, they may
    make it possible to prove every proposition, including [False]!

    Unfortunately, there is no simple way of telling whether an axiom
    is safe to add: hard work is generally required to establish the
    consistency of any particular combination of axioms.

    However, it is known that adding functional extensionality, in
    particular, _is_ consistent.

    To check whether a particular proof relies on any additional
    axioms, use the [Print Assumptions] command.  *)

Print Assumptions function_equality_ex2.
(* ===>
     Axioms:
     functional_extensionality :
         forall (X Y : Type) (f g : X -> Y),
                (forall x : X, f x = g x) -> f = g *)

(** **** Exercise: 4 stars (tr_rev)  *)
(** One problem with the definition of the list-reversing function
    [rev] that we have is that it performs a call to [app] on each
    step; running [app] takes time asymptotically linear in the size
    of the list, which means that [rev] has quadratic running time.
    We can improve this with the following definition: *)

Fixpoint rev_append' {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append' l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append' l [].

(** This version is said to be _tail-recursive_, because the recursive
    call to the function is the last operation that needs to be
    performed (i.e., we don't have to execute [++] after the recursive
    call); a decent compiler will generate very efficient code in this
    case.  Prove that the two definitions are indeed equivalent. *)

Lemma rev_append_app : forall (X:Type) (l:list X) (t:list X), rev_append' l t = (rev_append' l []) ++ t.
Proof. intros X l. induction l.
  intros x. reflexivity.
  intros x'.
  simpl. 
  replace (rev_append' l [x]) with (rev_append' l [] ++ [x]). rewrite IHl. rewrite <- app_assoc. reflexivity.
  rewrite <- IHl. reflexivity.
Qed.

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.



Lemma tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof. intros X. apply functional_extensionality. intros l.
  unfold tr_rev.
  induction l. reflexivity.
  simpl.
  rewrite <- IHl. rewrite rev_append_app. reflexivity.
Qed.


Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil : all X P []
  | all_cons : forall x xs, P x -> all X P xs -> all X P (x::xs).

Theorem forallb_all: forall X xs f,
  {forallb f xs = true <->     all X (fun x => f x = true) xs} +
  {forallb f xs = false <-> ~ (all X (fun x => f x = true) xs)}.
Proof. intros X l f.
  induction l as [|x xs].
    -  (* l = [] *)
      simpl. left. split.
        intros Htrue. apply all_nil.
        intros Hall. reflexivity.
    -  (* l = x::xs *)
      simpl. destruct (f x) eqn:Hfx.
        +  (* f x = true *)
          simpl. inversion IHxs.
            *  (* forall b f xs = true *)
              inversion H.
              left. split.
                intros Hforall. apply all_cons. apply Hfx. apply H0. apply Hforall.
                intros Hall. apply H1. inversion Hall. apply H5.
            *  (* forall b f xs = false *)
              inversion H. 
              right. split.
                  (* forall = false -> ~all *)
                  intros Hforall. unfold not.
                  intros Hall. inversion Hall.
                  apply H0 in Hforall. unfold not in Hforall.
                  assert (Hfalse := H5).
                  apply Hforall in H5. apply H5.
                  (* ~all -> forall = false *)
                  intros Hall.
                  apply H1. unfold not.
                  intros Hallxs.
                  unfold not in Hall.
                  assert (Hallxxs: all X (fun x: X => f x = true) (x::xs)).
                    apply all_cons. apply Hfx. apply Hallxs.
                  apply Hall in Hallxxs. apply Hallxxs.
        +  (* f x = false *)
          simpl. left. split.
            intros Hft. inversion Hft.
            intros Hall. inversion Hall. rewrite Hfx in H1. inversion H1.
Qed.

(** [] *)

(* ================================================================= *)
(** ** Propositions and Booleans *)

Inductive in_order_merge (X:Type) : list X -> list X -> list X -> Prop :=
  | in_order_merge_nil : in_order_merge X [] [] []
  | in_order_merge_cons1 : forall h1 t1 l2 l,
                           in_order_merge X t1 l2 l ->
                           in_order_merge X (h1::t1) l2 (h1 :: l)
  | in_order_merge_cons2 : forall h2 l1 t2 l,
                           in_order_merge X l1 t2 l ->
                           in_order_merge X l1 (h2::t2) (h2 :: l).



Theorem filter_challenge: forall X l1 l2 f l,
  in_order_merge X l1 l2 l ->
  all X (fun x => f x = true) l1 ->
  all X (fun x => f x = false) l2 ->
  filter f l = l1.
Proof.
  intros X l1 l2 f l Hmerge Hl1 Hl2.
  generalize dependent l2.
  generalize dependent l1.
  induction l as [|hl tl].
    -  (* l = [] *) intros l1 Halltrue l2 Hmerge Hallfalse.
      simpl. inversion Hmerge. reflexivity.
    -  (* l = hl :: tl *) intros l1 Halltrue l2 Hmerge Hallfalse.
      simpl. destruct (f hl) eqn:Hfhead.
        +  (* true *)
          inversion Hmerge.
          *  (* head from l1 *)
            rewrite IHtl with (l1:=t1) (l2:=l2).
            reflexivity.
            rewrite <- H0 in Halltrue.
            inversion Halltrue. apply H7.
            apply H2. apply Hallfalse.
          *  (* head from l2 *)
            rewrite <- H1 in Hallfalse.
            inversion Hallfalse.
            rewrite H in H6. rewrite H6 in Hfhead. inversion Hfhead.
        +  (* false *)
          inversion Hmerge.
          *  (* head from l1 *)
            rewrite <- H0 in Halltrue.
            inversion Halltrue.
            rewrite H in H6. rewrite H6 in Hfhead. inversion Hfhead.
          *  (* head from t2 *)
            rewrite IHtl with (l1:=l1) (l2:=t2).
            reflexivity.
            apply Halltrue.
            apply H2.
            inversion Hallfalse.
            rewrite <- H4 in H1. inversion H1.
            rewrite <- H1 in H6. inversion H6. rewrite <- H9. apply H5.
Qed.

Inductive subseq {X:Type} : (list X) -> (list X) -> Prop :=
  | subseq_empty : forall xs, subseq [] xs
  | subseq_head : forall x xs ys, subseq xs ys -> subseq (x::xs) (x::ys)
  | subseq_tail: forall x xs ys, subseq xs ys -> subseq xs (x::ys).

Theorem subseq_reflexive: forall (X:Type) (xs:list X),
  subseq xs xs.
Proof.
  intros X xs.
  induction xs.
    apply subseq_empty.
    apply subseq_head. apply IHxs.
Qed.

Theorem subseq_app: forall (X:Type) (l1 l2 l3:list X),
  subseq l1 l2 -> subseq l1 (l2 ++ l3).
Proof.
  intros X l1 l2 l3 H.
  generalize dependent l3.
  generalize dependent l1.
  induction l2 as [|h2 t2].
  - (* l2 = [] *)
    intros  l1 H l3.
    destruct l1.
      apply subseq_empty.
      inversion H.
  - (* l2 = h2 :: t2 *)
    intros l1 H l3.
    destruct l1 as [|h1 t1].
      + (* l1 = [] *)
        apply subseq_empty.
      + (* l1 = h1 :: t1 *)
        inversion H.
        * (* subseq_head *)
          simpl.  apply subseq_head. apply IHt2.
          apply H1.
        * (* subseq_tail *)
          simpl. apply subseq_tail. apply IHt2. apply H2.
Qed.

Theorem all_clause: forall X' (f:X'->bool) (h1:X') (t1 tl' l:list X') n (hl':X'),
    all X' (fun x: X' => f x = true) (h1 :: t1) ->
    subseq tl' t1 ->
    l = filter f (h1 :: t1) ->
    n = length l -> n < length (hl' :: tl') ->
    all X' (fun x0 : X' => f x0 = true) t1 /\ subseq tl' t1 /\ pred n < length tl'.
Proof.
    intros X' f' h1 t1 tl'' l'' n0 hl' Hall' Hsubseq' Hfilter' Hlen'l Hlen'l'.
      split. inversion Hall'. apply H2.
      split. apply Hsubseq'.
      destruct n0.
        -  (* n=0 *)
          rewrite Hfilter' in Hlen'l. simpl in Hlen'l. destruct (f' h1) eqn:Hfh1.
            inversion Hlen'l.
            inversion Hall'. rewrite H1 in Hfh1. inversion Hfh1.
        -  (* n=S *)
          simpl. unfold lt. unfold lt in Hlen'l'.
          simpl in Hlen'l'. apply Sn_le_Sm__n_le_m in Hlen'l'.
          apply Hlen'l'.
Qed.
 
Theorem filter_challenge_2: forall (X:Type) (f:X -> bool) (l1 l:list X) n,
  l = filter f l1 ->
  n = length l ->
  ~(exists l', all X (fun x=> f x = true) l1 /\ subseq l' l1 /\ n < length l').
Proof.
  intros X f l1 l n Hfilter Hlenl.
  unfold not.
  intros Hexists.
  generalize dependent l.
  inversion Hexists as [l'].
  intros l Hfilter Hlenl.
  inversion H as [Hall Hsubseqlenl'].
  inversion Hsubseqlenl' as [Hsubseq Hlenl'].

  assert (all_clause_tail: forall X f h1 t1 l' n' hl' tl',
    all X (fun x : X => f x = true) (h1 :: t1) ->
    l' = filter f (h1 :: t1) ->
    n' = length l' ->
    n' < length (hl' :: tl') ->
    subseq (hl' :: tl') t1 ->
    all X (fun x : X => f x = true) t1 /\ subseq (hl' :: tl') t1 /\ pred n' < length (hl' :: tl')).
    intros X' f' h1 t1 l'' n' hl tl Hall' Hfilter' Hlen'l Hlen'l' Hsubseq'.
    split.  inversion Hall'. apply H3.
    split. apply Hsubseq'.
    destruct n'.
      rewrite Hfilter' in Hlen'l. simpl in Hlen'l. destruct (f' h1) eqn:Hfh1.
        inversion Hlen'l.
        inversion Hall'. rewrite Hfh1 in H2. inversion H2.
      simpl. unfold lt. unfold lt in Hlen'l'.
      simpl in Hlen'l'. apply Sn_le_Sm__n_le_m in Hlen'l'.
      apply le_S in Hlen'l'.
      apply Hlen'l'.

  assert (predn_tl: forall X' l' f' h1' t1' n' (hl':X') tl',
                 l' = filter f' (h1' :: t1') ->
                 n' = length l' ->
                 n' < length (hl' :: tl') ->
                 all X' (fun x : X' => f' x = true) (h1' :: t1') ->
                 pred n' < length tl').
    intros X' l'' f' h1 t1 n' hl' tl' Hfilter' Hlen'l Hlen'l' Hall'.
    destruct n'.
      rewrite Hfilter' in Hlen'l. simpl in Hlen'l. destruct (f' h1) eqn:Hfh1.
        inversion Hlen'l.
        inversion Hall'. rewrite Hfh1 in H2. inversion H2.
      unfold lt. unfold lt in Hlen'l'. simpl. simpl in Hlen'l'.
      apply Sn_le_Sm__n_le_m in Hlen'l'. apply Hlen'l'.

  assert (predn_l: forall X l f h1 t1 n (hl:X) tl,
    l = filter f (h1 :: t1) ->
    n = length l ->
    n < length (hl :: tl) ->
    all X (fun x : X => f x = true) (h1 :: t1) ->
    pred n < length (hl :: tl)).
    intros X' l'' f' h1 t1 n' hl tl Hfilter' Hlen'l Hlen'l' Hall'.
    rewrite Hfilter' in Hlen'l. simpl in Hlen'l. destruct n'.
      destruct (f' h1) eqn:Hfh1.
        inversion Hlen'l.
        inversion Hall'. rewrite Hfh1 in H2. inversion H2.
    unfold lt. unfold lt in Hlen'l'. simpl. simpl in Hlen'l'.
    apply Sn_le_Sm__n_le_m in Hlen'l'. apply le_S in Hlen'l'.
    apply Hlen'l'.


  generalize dependent n.
  generalize dependent l.
  generalize dependent l'.
  induction l1 as [|h1 t1].
    -  (* l1 = [] *) intros l' Hsubseq l Hfilter n Hexists H Hlenl Hsubseqlenl' Hlenl'.
      rewrite Hfilter in Hlenl. simpl in Hlenl.
      inversion Hsubseq. rewrite <- H0 in Hlenl'.
      rewrite Hlenl in Hlenl'. inversion Hlenl'.
    -  (* l1 = h1 :: t1 *) intros l' Hsubseq l Hfilter n Hexists H Hlenl Hsubseqlenl' Hlenl'.
      inversion H as [Hall' Hsubseqlenl''].
      destruct l' as [|hl' tl'].
        +  (* l' = [] *)
          inversion Hlenl'.
        +  (* l' = hl' :: tl' *)
          inversion Hsubseq.
            *  (* subseq head *)
              apply IHt1 with (n:=pred n) (l:=(filter f t1)) (l':=tl').
              inversion Hall. apply H8.
              apply H1.
              reflexivity.
              exists tl'.
              apply all_clause with (h1:=h1) (l:=l) (hl':=hl').
              apply Hall'. apply H1. apply Hfilter. apply Hlenl. apply Hlenl'.
              apply all_clause with (h1:=h1) (l:=l) (hl':=hl').
              apply Hall'. apply H1. apply Hfilter. apply Hlenl. apply Hlenl'.
              rewrite Hfilter in Hlenl. apply (f_equal nat nat pred) in Hlenl.
              simpl in Hlenl. destruct (f h1) eqn:Hfh1.
                simpl in Hlenl. apply Hlenl.
                inversion Hall. rewrite Hfh1 in H7. inversion H7.
              split. apply H1. 
              apply predn_tl with (f':=f) (h1':=h1) (t1':=t1) (l':=l) (hl':=hl').
              apply Hfilter. apply Hlenl. apply Hlenl'. apply Hall'.
              apply predn_tl with (f':=f) (h1':=h1) (t1':=t1) (l':=l) (hl':=hl').
              apply Hfilter. apply Hlenl. apply Hlenl'. apply Hall'.
            *  (* subseq tail *)
              apply IHt1 with (n:=pred n) (l:=(filter f t1)) (l':=(hl' :: tl')).
              inversion Hall. apply H7.
              apply H2.
              reflexivity.
              exists (hl' :: tl').
              apply all_clause_tail with (h1:=h1) (l':=l).
              apply Hall'. apply Hfilter. apply Hlenl.  apply Hlenl'. apply H2.
              apply all_clause_tail with (h1:=h1) (l':=l).
              apply Hall'. apply Hfilter. apply Hlenl.  apply Hlenl'. apply H2.
              rewrite Hfilter in Hlenl. apply (f_equal nat nat pred) in Hlenl.
              simpl in Hlenl. destruct (f h1) eqn:Hfh1.
                simpl in Hlenl. apply Hlenl.
                inversion Hall. rewrite Hfh1 in H6. inversion H6.
              split. apply H2. 
              
              apply predn_l with (l:=l) (f:=f) (h1:=h1) (t1:=t1).
              apply Hfilter. apply Hlenl. apply Hlenl'. apply Hall'.
              apply predn_l with (l:=l) (f:=f) (h1:=h1) (t1:=t1).
              apply Hfilter. apply Hlenl. apply Hlenl'. apply Hall'.
Qed. (* this may benefit from a certain amount of cleaning up *)

(** [] *)
(** We've seen two different ways of encoding logical facts in Coq:
    with _booleans_ (of type [bool]), and with _propositions_ (of type
    [Prop]).

    For instance, to claim that a number [n] is even, we can say
    either
       - (1) that [evenb n] returns [true], or
       - (2) that there exists some [k] such that [n = double k].
             Indeed, these two notions of evenness are equivalent, as
             can easily be shown with a couple of auxiliary lemmas.

    We often say that the boolean [evenb n] _reflects_ the proposition
    [exists k, n = double k].  *)

Theorem evenb_double : forall k, evenb (double k) = true.
Proof.
  intros k. induction k as [|k' IHk'].
  - reflexivity.
  - simpl. apply IHk'.
Qed.


Fixpoint halfn (n : nat) : nat :=
  match n with
  | S (S n) => S (halfn n)
  | _ => O
  end.

Functional Scheme halfn_ind := Induction for halfn Sort Prop.

Theorem negb_extensionality : forall (a b : bool), negb a = negb b <-> a = b.
Proof.
  intros a b.
  split; intros H. destruct a; destruct b. reflexivity. inversion H. inversion H. reflexivity. subst. reflexivity.
Qed.

Theorem evenb_S_Sn : forall (n : nat), evenb n = evenb (S (S n)).
Proof.
  intros n. induction n. reflexivity.
  rewrite evenb_S.
  rewrite evenb_S.
  rewrite negb_extensionality. assumption.
Qed.

Theorem oddb_S: forall n : nat, oddb (S n) = negb (oddb n).
Proof.
  intros n. unfold oddb. rewrite negb_involutive. rewrite <- evenb_S. rewrite <- evenb_S_Sn. reflexivity.
Qed.

Theorem oddb_S_Sn : forall (n : nat), oddb n = oddb (S (S n)).
Proof.
  intros n. induction n. reflexivity.
  rewrite oddb_S.
  rewrite oddb_S.
  rewrite negb_extensionality. assumption.
Qed.

  

Theorem even_half_double : forall (n : nat), evenb n = true -> double (halfn n) = n.
Proof.
  intros n H.
  functional induction (halfn n).
  reflexivity.
  simpl in H. inversion H.
  simpl. rewrite IHn0. reflexivity. rewrite evenb_S_Sn. assumption.
Qed.


Theorem odd_S_half_double : forall (n : nat), oddb n = true -> S (double (halfn n)) = n.
Proof.
  intros n H.
  functional induction (halfn n).
  simpl in H. inversion H.
  reflexivity.
  simpl. rewrite IHn0. reflexivity. rewrite oddb_S_Sn. assumption.
Qed.

Theorem negb_oddb_n_evenb_n : forall n, negb (oddb n) = evenb n.
Proof.
  intros n. induction n.
  simpl. reflexivity.
  unfold oddb. rewrite negb_involutive. reflexivity.
Qed.

Theorem negb_evenb_n_oddb_n : forall n, negb (evenb n) = oddb n.
Proof.
  intros n. rewrite <- negb_extensionality. rewrite negb_involutive. rewrite negb_oddb_n_evenb_n. reflexivity.
Qed.

(** **** Exercise: 3 stars (evenb_double_conv)  *)
Theorem evenb_double_conv : forall n,
  exists k, n = if evenb n then double k
                else S (double k).
Proof.
  intros n.
  exists (halfn n).
  remember (evenb n) as t.
  destruct t.
  symmetry. apply even_half_double. symmetry. assumption.
  symmetry. apply odd_S_half_double. rewrite <- negb_extensionality. simpl. rewrite Heqt. rewrite negb_oddb_n_evenb_n. reflexivity.
Qed.

(** [] *)

Theorem even_bool_prop : forall n,
  evenb n = true <-> exists k, n = double k.
Proof.
  intros n. split.
  - intros H. destruct (evenb_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply evenb_double.
Qed.

(** Similarly, to state that two numbers [n] and [m] are equal, we can
    say either (1) that [beq_nat n m] returns [true] or (2) that [n =
    m].  These two notions are equivalent. *)

Theorem beq_nat_true_iff : forall n1 n2 : nat,
  beq_nat n1 n2 = true <-> n1 = n2.
Proof.
  intros n1 n2. split.
  - apply beq_nat_true.
  - intros H. rewrite H. rewrite <- beq_nat_refl. reflexivity.
Qed.

(** However, while the boolean and propositional formulations of a
    claim are equivalent from a purely logical perspective, they need
    not be equivalent _operationally_.  Equality provides an extreme
    example: knowing that [beq_nat n m = true] is generally of little
    direct help in the middle of a proof involving [n] and [m];
    however, if we convert the statement to the equivalent form [n =
    m], we can rewrite with it.

    The case of even numbers is also interesting.  Recall that,
    when proving the backwards direction of [even_bool_prop] (i.e.,
    [evenb_double], going from the propositional to the boolean
    claim), we used a simple induction on [k].  On the other hand, the
    converse (the [evenb_double_conv] exercise) required a clever
    generalization, since we can't directly prove [(exists k, n =
    double k) -> evenb n = true].

    For these examples, the propositional claims are more useful than
    their boolean counterparts, but this is not always the case.  For
    instance, we cannot test whether a general proposition is true or
    not in a function definition; as a consequence, the following code
    fragment is rejected: *)

Fail Definition is_even_prime n :=
  if n = 2 then true
  else false.

(** Coq complains that [n = 2] has type [Prop], while it expects an
    elements of [bool] (or some other inductive type with two
    elements).  The reason for this error message has to do with the
    _computational_ nature of Coq's core language, which is designed
    so that every function that it can express is computable and
    total.  One reason for this is to allow the extraction of
    executable programs from Coq developments.  As a consequence,
    [Prop] in Coq does _not_ have a universal case analysis operation
    telling whether any given proposition is true or false, since such
    an operation would allow us to write non-computable functions.

    Although general non-computable properties cannot be phrased as
    boolean computations, it is worth noting that even many
    _computable_ properties are easier to express using [Prop] than
    [bool], since recursive function definitions are subject to
    significant restrictions in Coq.  For instance, the next chapter
    shows how to define the property that a regular expression matches
    a given string using [Prop].  Doing the same with [bool] would
    amount to writing a regular expression matcher, which would be
    more complicated, harder to understand, and harder to reason
    about.

    Conversely, an important side benefit of stating facts using
    booleans is enabling some proof automation through computation
    with Coq terms, a technique known as _proof by
    reflection_.  Consider the following statement: *)

Example even_1000 : exists k, 1000 = double k.

(** The most direct proof of this fact is to give the value of [k]
    explicitly. *)

Proof. exists 500. reflexivity. Qed.

(** On the other hand, the proof of the corresponding boolean
    statement is even simpler: *)

Example even_1000' : evenb 1000 = true.
Proof. reflexivity. Qed.

(** What is interesting is that, since the two notions are equivalent,
    we can use the boolean formulation to prove the other one without
    mentioning the value 500 explicitly: *)

Example even_1000'' : exists k, 1000 = double k.
Proof. apply even_bool_prop. reflexivity. Qed.

(** Although we haven't gained much in terms of proof size in this
    case, larger proofs can often be made considerably simpler by the
    use of reflection.  As an extreme example, the Coq proof of the
    famous _4-color theorem_ uses reflection to reduce the analysis of
    hundreds of different cases to a boolean computation.  We won't
    cover reflection in great detail, but it serves as a good example
    showing the complementary strengths of booleans and general
    propositions. *)

(** **** Exercise: 2 stars (logical_connectives)  *)
(** The following lemmas relate the propositional connectives studied
    in this chapter to the corresponding boolean operations. *)

Lemma andb_true_iff : forall b1 b2:bool,
  b1 && b2 = true <-> b1 = true /\ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

Lemma orb_true_iff : forall b1 b2,
  b1 || b2 = true <-> b1 = true \/ b2 = true.
Proof.
  (* FILL IN HERE *) Admitted.

(** **** Exercise: 1 star (beq_nat_false_iff)  *)
(** The following theorem is an alternate "negative" formulation of
    [beq_nat_true_iff] that is more convenient in certain
    situations (we'll see examples in later chapters). *)

Theorem beq_nat_false_iff : forall x y : nat,
  beq_nat x y = false <-> x <> y.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 3 stars (beq_list)  *)
(** Given a boolean operator [beq] for testing equality of elements of
    some type [A], we can define a function [beq_list beq] for testing
    equality of lists with elements in [A].  Complete the definition
    of the [beq_list] function below.  To make sure that your
    definition is correct, prove the lemma [beq_list_true_iff]. *)

Fixpoint beq_list {A : Type} (beq : A -> A -> bool)
                  (l1 l2 : list A) : bool
  (* REPLACE THIS LINE WITH ":= _your_definition_ ." *). Admitted.

Lemma beq_list_true_iff :
  forall A (beq : A -> A -> bool),
    (forall a1 a2, beq a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, beq_list beq l1 l2 = true <-> l1 = l2.
Proof.
(* FILL IN HERE *) Admitted.
(** [] *)

(** **** Exercise: 2 stars, recommended (All_forallb)  *)
(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Tactics]: *)

Fixpoint forallb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
  | [] => true
  | x :: l' => andb (test x) (forallb test l')
  end.

(** Prove the theorem below, which relates [forallb] to the [All]
    property of the above exercise. *)

Theorem forallb_true_iff : forall X test (l : list X),
   forallb test l = true <-> All (fun x => test x = true) l.
Proof.
  (* FILL IN HERE *) Admitted.

(** Are there any important properties of the function [forallb] which
    are not captured by this specification? *)



(** **** Exercise: 4 stars, advanced (no_repeats) *)
(** The following inductively defined proposition... *)

Inductive appears_in {X:Type} (a:X) : list X -> Prop :=
  | ai_here : forall l, appears_in a (a::l)
  | ai_later : forall b l, appears_in a l -> appears_in a (b::l).

(** ...gives us a precise way of saying that a value [a] appears at
    least once as a member of a list [l]. 
    Here's a pair of warm-ups about [appears_in].
*)

Lemma appears_in_app : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x (xs ++ ys) -> appears_in x xs \/ appears_in x ys.
Proof.        
  intros X xs ys x Happ.
  generalize dependent ys.
  induction xs as [|hxs txs].
    -  (* xs = [] *) intros ys Happ. simpl in Happ. right. apply Happ.
    -  (* xs = hxs :: txs *) intros ys Happ.
      inversion Happ. left. apply ai_here.
      apply IHtxs in H0.
      inversion H0.
        left. apply ai_later. apply H2.
        right. apply H2.
Qed.

Lemma appears_in_app_l : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x xs -> appears_in x (xs ++ ys).
Proof.
  intros X xs ys x Hapxs.
  induction xs.
    inversion Hapxs.
    inversion Hapxs.
      apply ai_here.
      simpl. apply ai_later. apply IHxs. apply H0.
Qed.

Lemma appears_in_app_r : forall (X:Type) (xs ys : list X) (x:X), 
     appears_in x ys -> appears_in x (xs ++ ys).
Proof.
  intros X xs ys x Hapxs.
  induction xs.
    simpl. apply Hapxs.
    simpl. apply ai_later. apply IHxs.
Qed.

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros X l1 l2.
  induction l1.
    -  (* l1 nil *)
      simpl. reflexivity.
    -  (* l1 cons *)
      simpl. apply f_equal. apply IHl1.
Qed.


Theorem not_appears_in_app_l : forall (X:Type) (xs ys : list X) (x:X),
  ~appears_in x (xs ++ ys) -> ~ appears_in x xs.
Proof.
  intros X xs ys x.
  apply contrapositive. apply appears_in_app_l.
Qed.

Theorem appears_in_app_cons: forall (X:Type) (c:X) xs ys, appears_in c (xs ++ c :: ys).
Proof.
  intros X c xs ys.
  induction xs.
    simpl. apply ai_here.
    simpl. apply ai_later. apply IHxs.
Qed.

Lemma app_appears_in : forall (X:Type) (xs ys : list X) (x:X), 
  appears_in x xs \/ appears_in x ys ->
  appears_in x (xs ++ ys).
Proof.
  intros X xs ys x Hor.
  inversion Hor.
  -  (* appears in xs *)
    induction xs.
      inversion H.
      inversion H.
        apply ai_here.
        simpl. apply ai_later. apply IHxs. left. apply H1. apply H1.
  -  (* appears in ys *)
    generalize dependent xs.
    induction ys.
      inversion H.
      induction xs.
        intros Hor. simpl. apply H.
        intros Hor. simpl. apply ai_later. apply IHxs. right. apply H.
Qed.
    
Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.  
  intros X x l Hap.
  induction Hap.
    -  (* ai_here *) exists []. exists l. simpl. reflexivity.
    -  (* ai_later *)
      inversion IHHap as [l1].
      inversion H as [l2].
      rewrite H0.
      exists (b :: l1). exists l2.
      simpl. reflexivity.
Qed.

Lemma app_split_appears_in : forall (X:Type) (x:X) (l l1 l2:list X),
  l = l1 ++ (x::l2) -> 
  appears_in x l.
Proof.
  intros X x l l1 l2.
  generalize dependent l1.
  induction l.
    intros l1 Hsplit. destruct l1. inversion Hsplit. inversion Hsplit.
    intros l1 Hsplit.
    destruct l1.
      simpl in Hsplit. rewrite Hsplit. apply ai_here.
      simpl in Hsplit. inversion Hsplit. rewrite <- H1.
      apply IHl in H1. apply ai_later. apply H1.
Qed.

Inductive app_split {X:Type} : list X -> Prop :=
  | app_split_nil : app_split []
  | app_split_cons : forall h l1 l2, app_split (l1 ++ (h::l2)).

(** Now define a predicate [repeats] (analogous to [no_repeats] in the
   exercise above), such that [repeats X l] asserts that [l] contains
   at least one repeated element (of type [X]).  *)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeats_head : forall h t, appears_in h t -> repeats (h::t)
  | repeats_tail : forall h t, repeats t -> repeats (h::t)
.

Example test_repeats: repeats [1;2;4;2].
Proof.
  apply repeats_tail. 
  apply repeats_head. apply ai_later. apply ai_here.
Qed.

Example test_repeats2: ~ repeats [1;2].
Proof.
  unfold not.
  intros H.
  inversion H.
  inversion H1. inversion H4. inversion H1.
  inversion H4. inversion H4.
Qed.

(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Definition disjoint (X:Type) (l1 l2:list X) := forall x,
                     (appears_in x l1 -> ~appears_in x l2) /\
                     (appears_in x l2 -> ~appears_in x l1).

Inductive no_repeats {X:Type} : list X -> Prop :=
 | no_repeats_nil : no_repeats []
 | no_repeats_cons : forall (h:X) (t:list X),
                     ~(appears_in h t) ->
                     no_repeats t ->
                     no_repeats (h::t). 
Theorem no_repeats1234: no_repeats [1;2;3;4].
  apply no_repeats_cons.
  unfold not.
  intros H. inversion H. inversion H1. inversion H4. inversion H7.
  apply no_repeats_cons.
  unfold not.
  intros H. inversion H. inversion H1. inversion H4.
  apply no_repeats_cons.
  unfold not.
  intros H. inversion H. inversion H1.
  apply no_repeats_cons.
  unfold not.
  intros H. inversion H.
  apply no_repeats_nil.
Qed.

Theorem not_no_repeatstruetrue: ~no_repeats [true;true].
  unfold not.
  intros Hnr. inversion Hnr. unfold not in H1. apply H1. apply ai_here.
Qed.

(* that seems to be generally satisfactory *)

Theorem disjoint_cons_l: forall X l1 l2 h,
  disjoint X l1 l2 -> ~ appears_in h l2 -> disjoint X (h::l1) l2.
Proof.
  intros X l1 l2 h Hdisj Hap.
  unfold disjoint. unfold disjoint in Hdisj.
  intros x. assert (Hdisjx := Hdisj x). inversion Hdisjx.
  split.
    -  (* in l1 *)
      intros Hapl1. unfold not in Hap.
      inversion Hapl1.
        unfold not. apply Hap.
        unfold not. intros Hapl2. apply H0 in Hapl2.
        unfold not in Hapl2. apply Hapl2 in H2. inversion H2.
    -  (* in l2 *)
      intros Hapl2.
      inversion Hapl2.
        unfold not. intros Hapl1. inversion Hapl1. unfold not in Hap.
        rewrite H3 in Hapl2. apply Hap in Hapl2. inversion Hapl2.
        apply H in H3. unfold not in H3. apply H3 in Hapl2. inversion Hapl2.
        unfold not. intros Hapl1. inversion Hapl1.
        rewrite H4 in Hapl2. unfold not in Hap. apply Hap in Hapl2. inversion Hapl2.
        apply H0 in Hapl2. unfold not in Hapl2. apply Hapl2 in H4. inversion H4.
Qed.

Theorem disjoint_cons_r: forall X l1 l2 h,
  disjoint X l1 l2 -> ~ appears_in h l1 -> disjoint X l1 (h::l2).
Proof.
  intros X l1 l2 h Hdisj Hap.
  unfold disjoint.
  unfold disjoint in Hdisj.
  intros x. assert (Hdisjx := Hdisj x). inversion Hdisjx.
  split.
    -  (* in l1 *)
      intros Hapl1. unfold not in Hap.
      unfold not. intros Hapl2.
      inversion Hapl2.
        rewrite H2 in Hapl1. apply Hap in Hapl1. inversion Hapl1.
        apply H0 in H2. apply H2 in Hapl1. inversion Hapl1.
    -  (* in h::l2 *)
      intros Hapl2. unfold not in Hap.
      unfold not. intros Hapl1.
      inversion Hapl2.
        rewrite H2 in Hapl1. apply Hap in Hapl1. inversion Hapl1.
        apply H0 in H2. unfold not in H2. apply H2 in Hapl1. inversion Hapl1.
Qed.

Theorem appears_in_snoc: forall (X:Type) l (x1 x2 : X),
  appears_in x1 l -> appears_in x1 (l ++ [x2]).
Proof.
  intros X l x1 x2 Hap.
  apply app_appears_in.
  left. apply Hap.
Qed.
Theorem not_appears_in_snoc: forall (X:Type) l (x1 x2 : X),
  ~appears_in x1 (l ++ [x2]) -> ~appears_in x1 l.
Proof.
  intros X l x1 x2. apply contrapositive. apply appears_in_snoc.
Qed.
Theorem appears_in_app__appears_in_app_cons: forall (X:Type) (l1 l2:list X) (x y:X),
  appears_in x (l1 ++ l2) -> appears_in x (l1 ++ y :: l2).
Proof.
  intros X l1 l2 x y Hap.
  apply appears_in_app in Hap.
  inversion Hap.
  induction l1.
    inversion H.
    inversion H.
      simpl. apply ai_here.
      simpl. apply ai_later. apply IHl1. left. apply H1. apply H1.
  induction l1.
    simpl. apply ai_later. apply H.
    simpl. apply ai_later. apply IHl1. right. apply H.
Qed.
Theorem not_appears_in_app_cons__not_appears_in_app: forall (X:Type) (l1 l2:list X) (x y:X),
  ~appears_in x (l1 ++ y :: l2) -> ~appears_in x (l1 ++ l2).
Proof.
  intros X l1 l2 x y.
  apply contrapositive. apply appears_in_app__appears_in_app_cons.
Qed.
Theorem no_repeats_app_cons: forall (X:Type) l1 l2 (x:X),
  no_repeats (l1 ++ x :: l2) -> no_repeats (l1 ++ l2).
Proof.
  intros X l1 l2 x Hnr.
  induction l1. simpl. simpl in Hnr.
    inversion Hnr. apply H2.
      simpl. simpl in Hnr.
    inversion Hnr. apply IHl1 in H2.
      apply no_repeats_cons.
      apply not_appears_in_app_cons__not_appears_in_app in H1.
      apply H1. apply H2.
Qed.

   
Theorem no_repeats_appears_in_l: forall (X:Type) (l1 l2:list X) (x:X),
  appears_in x l1 -> no_repeats (l1 ++ l2) -> ~appears_in x l2.
Proof.
  intros X l1 l2 x.
  intros Hapl1.
  intros Hnr.
  unfold not.
  intros Hapl2.
  induction Hapl1.
    induction Hapl2.
      inversion Hnr. unfold not in H1. apply H1. apply appears_in_app_cons.
      apply IHHapl2. simpl. apply no_repeats_app_cons in Hnr. apply Hnr.
    apply IHHapl1. simpl in Hnr. inversion Hnr. apply H2.
Qed.
 
Theorem no_repeats_appears_in_r: forall (X:Type) (l1 l2:list X) (x:X),
  appears_in x l2 -> no_repeats (l1 ++ l2) -> ~appears_in x l1.
Proof.
  intros X l1 l2 x.
  intros Hapl2.
  intros Hnr.
  unfold not.
  intros Hapl1.
  induction Hapl2.
    induction Hapl1.
      inversion Hnr. unfold not in H1. apply H1. apply appears_in_app_cons.
      apply IHHapl1. simpl. simpl in Hnr. inversion Hnr. apply H2.
    apply IHHapl2. apply no_repeats_app_cons in Hnr. apply Hnr.
Qed.


Theorem no_repeats_in_append__disjoint: forall X l1 l2,
  no_repeats (l1 ++ l2) -> disjoint X l1 l2.
Proof.
  intros X l1 l2 Hnr.
  unfold disjoint.
  intros x.
  split.
    -  (* in l1 *) intros Hapl1.
      apply no_repeats_appears_in_l with l1.
      apply Hapl1. apply Hnr.
    -  (* in l2 *) intros Hapl2.
      apply no_repeats_appears_in_r with l2.
      apply Hapl2. apply Hnr.
Qed.

(** [] *)

(** **** Exercise: 3 stars (nostutter) *)
(** Formulating inductive definitions of predicates is an important
    skill you'll need in this course.  Try to solve this exercise
    without any help at all (except from your study group partner, if
    you have one).

    We say that a list of numbers "stutters" if it repeats the same
    number consecutively.  The predicate "[nostutter mylist]" means
    that [mylist] does not stutter.  Formulate an inductive definition
    for [nostutter].  (This is different from the [no_repeats]
    predicate in the exercise above; the sequence [1,4,1] repeats but
    does not stutter.) *)

Inductive nostutter:  list nat -> Prop :=
  | nostutter_nil : nostutter []
  | nostutter_singleton : forall n, nostutter [n]
  | nostutter_cons : forall n1 n2 l,
                      n1 <> n2 ->
                      nostutter (n2::l) ->
                      nostutter (n1::n2::l)
.

(** Make sure each of these tests succeeds, but you are free
    to change the proof if the given one doesn't work for you.
    Your definition might be different from mine and still correct,
    in which case the examples might need a different proof.
   
    The suggested proofs for the examples (in comments) use a number
    of tactics we haven't talked about, to try to make them robust
    with respect to different possible ways of defining [nostutter].
    You should be able to just uncomment and use them as-is, but if
    you prefer you can also prove each example with more basic
    tactics.  *)

Example test_nostutter_1:      nostutter [3;1;4;1;5;6].
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_2:  nostutter [].
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_3:  nostutter [5].
  Proof. repeat constructor; apply beq_nat_false; auto. Qed.

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
  Proof. intro.
  repeat match goal with 
    h: nostutter _ |- _ => inversion h; clear h; subst 
  end.
  contradiction H1; auto. Qed.


(* ================================================================= *)
(** ** Classical vs. Constructive Logic *)

(** We have seen that it is not possible to test whether or not a
    proposition [P] holds while defining a Coq function.  You may be
    surprised to learn that a similar restriction applies to _proofs_!
    In other words, the following intuitive reasoning principle is not
    derivable in Coq: *)


(** To understand operationally why this is the case, recall
    that, to prove a statement of the form [P \/ Q], we use the [left]
    and [right] tactics, which effectively require knowing which side
    of the disjunction holds.  But the universally quantified [P] in
    [excluded_middle] is an _arbitrary_ proposition, which we know
    nothing about.  We don't have enough information to choose which
    of [left] or [right] to apply, just as Coq doesn't have enough
    information to mechanically decide whether [P] holds or not inside
    a function. *)

(** However, if we happen to know that [P] is reflected in some
    boolean term [b], then knowing whether it holds or not is trivial:
    we just have to check the value of [b]. *)

Theorem restricted_excluded_middle : forall P b,
  (P <-> b = true) -> P \/ ~ P.
Proof.
  intros P [] H.
  - left. rewrite H. reflexivity.
  - right. rewrite H. intros contra. inversion contra.
Qed.

(** In particular, the excluded middle is valid for equations [n = m],
    between natural numbers [n] and [m]. *)

Theorem restricted_excluded_middle_eq : forall (n m : nat),
  n = m \/ n <> m.
Proof.
  intros n m.
  apply (restricted_excluded_middle (n = m) (beq_nat n m)).
  symmetry.
  apply beq_nat_true_iff.
Qed.

(** It may seem strange that the general excluded middle is not
    available by default in Coq; after all, any given claim must be
    either true or false.  Nonetheless, there is an advantage in not
    assuming the excluded middle: statements in Coq can make stronger
    claims than the analogous statements in standard mathematics.
    Notably, if there is a Coq proof of [exists x, P x], it is
    possible to explicitly exhibit a value of [x] for which we can
    prove [P x] -- in other words, every proof of existence is
    necessarily _constructive_. *)

(** Logics like Coq's, which do not assume the excluded middle, are
    referred to as _constructive logics_.

    More conventional logical systems such as ZFC, in which the
    excluded middle does hold for arbitrary propositions, are referred
    to as _classical_. *)

(** The following example illustrates why assuming the excluded middle
    may lead to non-constructive proofs:

    _Claim_: There exist irrational numbers [a] and [b] such that [a ^
    b] is rational.

    _Proof_: It is not difficult to show that [sqrt 2] is irrational.
    If [sqrt 2 ^ sqrt 2] is rational, it suffices to take [a = b =
    sqrt 2] and we are done.  Otherwise, [sqrt 2 ^ sqrt 2] is
    irrational.  In this case, we can take [a = sqrt 2 ^ sqrt 2] and
    [b = sqrt 2], since [a ^ b = sqrt 2 ^ (sqrt 2 * sqrt 2) = sqrt 2 ^
    2 = 2].  []

    Do you see what happened here?  We used the excluded middle to
    consider separately the cases where [sqrt 2 ^ sqrt 2] is rational
    and where it is not, without knowing which one actually holds!
    Because of that, we wind up knowing that such [a] and [b] exist
    but we cannot determine what their actual values are (at least,
    using this line of argument).

    As useful as constructive logic is, it does have its limitations:
    There are many statements that can easily be proven in classical
    logic but that have much more complicated constructive proofs, and
    there are some that are known to have no constructive proof at
    all!  Fortunately, like functional extensionality, the excluded
    middle is known to be compatible with Coq's logic, allowing us to
    add it safely as an axiom.  However, we will not need to do so in
    this book: the results that we cover can be developed entirely
    within constructive logic at negligible extra cost.

    It takes some practice to understand which proof techniques must
    be avoided in constructive reasoning, but arguments by
    contradiction, in particular, are infamous for leading to
    non-constructive proofs.  Here's a typical example: suppose that
    we want to show that there exists [x] with some property [P],
    i.e., such that [P x].  We start by assuming that our conclusion
    is false; that is, [~ exists x, P x]. From this premise, it is not
    hard to derive [forall x, ~ P x].  If we manage to show that this
    intermediate fact results in a contradiction, we arrive at an
    existence proof without ever exhibiting a value of [x] for which
    [P x] holds!

    The technical flaw here, from a constructive standpoint, is that
    we claimed to prove [exists x, P x] using a proof of
    [~ ~ (exists x, P x)].  Allowing ourselves to remove double
    negations from arbitrary statements is equivalent to assuming the
    excluded middle, as shown in one of the exercises below.  Thus,
    this line of reasoning cannot be encoded in Coq without assuming
    additional axioms. *)

(** **** Exercise: 3 stars (excluded_middle_irrefutable)  *)
(** The consistency of Coq with the general excluded middle axiom
    requires complicated reasoning that cannot be carried out within
    Coq itself.  However, the following theorem implies that it is
    always safe to assume a decidability axiom (i.e., an instance of
    excluded middle) for any _particular_ Prop [P].  Why? Because we
    cannot prove the negation of such an axiom; if we could, we would
    have both [~ (P \/ ~P)] and [~ ~ (P \/ ~P)], a contradiction. *)

Theorem excluded_middle_irrefutable:  forall (P:Prop),
  ~ ~ (P \/ ~ P).
Proof.
  (* FILL IN HERE *) Admitted.
  
(** [] *)

Theorem not_ne__eq: forall (X:Type) (x y:X),
  excluded_middle ->
  ~(x <> y) ->
  x = y.
Proof.
  intros X x y Hex H.
  apply excluded_middle_classic in Hex.
  apply Hex. apply H.
Qed.

Theorem repeats_or: forall (X:Type) (h:X) (t:list X),
  repeats t \/ appears_in h t -> repeats (h::t).
Proof.
  intros X h t Hor.
  inversion Hor.
  apply repeats_tail. apply H.
  apply repeats_head. apply H.
Qed.

Theorem and_distributes_over_or_1 : forall P Q R : Prop,
  (P \/ R) /\ (Q \/ R) -> (P /\ Q) \/ R .
Proof.
  intros P Q R H.
  inversion H.
    inversion H0.
      inversion H1.
        apply or_introl.  split. apply H2. apply H3.
        apply or_intror. apply H3.
      inversion H1.
        apply or_intror. apply H2.
        apply or_intror. apply H2.
Qed.

Theorem or_split: forall P Q R:Prop,
  excluded_middle ->
  (P \/ ~Q) /\ (R \/ Q) -> P \/ R.
Proof.
  intros P Q R Hexm H.
  inversion H as [Hpq Hrq].
  assert (HQ := Hexm Q).
  inversion HQ.
    inversion Hrq as [Hr|Hq].
      right. apply Hr.
      inversion Hpq as [Hp|Hnq].
        left. apply Hp.
        unfold not in Hnq. apply Hnq in Hq. inversion Hq.
    inversion Hrq as [Hr|Hq].
      right. apply Hr.
      unfold not in H0. apply H0 in Hq. inversion Hq.
Qed.
  

Theorem implies_to_or_neg: forall P Q:Prop,
  excluded_middle ->
  (~P -> Q) -> (P \/ Q).
Proof.
  intros P Q Hexm H.
  assert (Hito: implies_to_or).
    apply excluded_middle_implies_to_or. apply Hexm.
  assert (Hclassic: classic).
    apply excluded_middle_classic. apply Hexm.
  apply or_split with (~Q). apply Hexm.
  split.
  apply or_commut. apply Hito. intros Hnq.
  apply contrapositive in H.
  apply Hclassic in H. apply H. apply Hnq.
  apply Hexm.
Qed.

Theorem Sn_lt_Sm__n_lt_m: forall m n,
 S n < S m -> n < m.
Proof.
  intros m n Hs.
  unfold lt. unfold lt in Hs.
  apply Sn_le_Sm__n_le_m in Hs. apply Hs.
Qed.

Theorem imp_or_or: forall (A B C:Prop), (A -> B) -> A \/ C -> B \/ C.
Proof.
  intros A B C Hab Hac.
  inversion Hac.
  apply Hab in H. left. apply H.
  right. apply H.
Qed.

Theorem or_imp_or: forall (A B C:Prop), (A -> B) -> C \/ A -> C \/ B.
Proof.
  intros A B C Hab Hac.
  inversion Hac.
  left. apply H.
  right. apply Hab in H. apply H.
Qed.

Theorem implies_to_nor: forall P Q:Prop, implies_to_or -> (~P->Q) -> (P \/ Q).
Proof.
  intros P Q Hito.
  assert (H := Hito (~P) Q).
  intros Hpq.
  apply H in Hpq.
  inversion Hpq.
  assert (Hclassic: classic).
    apply implies_to_or_excluded_middle in Hito.
    apply excluded_middle_classic in Hito.
    apply Hito.
  apply Hclassic in H0. left. apply H0.
  right. apply H0.
Qed.

Theorem n_le_m__Sn_le_Sm: forall n m: nat, n <= m -> S n <= S m.
Proof.
  intros n m H. apply le_n_S. assumption.
Qed.

Theorem Sn_le_m__Sn_le_Sm: forall n m: nat, S n <= m -> S n <= S m.
Proof.
  intros n m H. right. assumption.
Qed.  

Theorem n_lt_m__Sn_lt_Sm: forall n m: nat, n < m -> S n < S m.
Proof.
  intros n m Hnm.
  unfold lt. apply n_le_m__Sn_le_Sm. unfold lt in Hnm. apply Hnm.
Qed.

Theorem le_ne_lt: forall n m, n <= m -> n <> m -> n < m.
  intros n m.
  generalize dependent n.
  induction m.
    intros n Hle Hne. destruct n.
      unfold not in Hne. assert (H0: 0 = 0). reflexivity. apply Hne in H0. inversion H0.
      inversion Hle.
    destruct n.
      intros Hle Hne. unfold lt. apply n_le_m__Sn_le_Sm. apply O_le_n.
      intros Hle Hne. apply n_lt_m__Sn_lt_Sm. apply IHm.
        apply Sn_le_Sm__n_le_m in Hle. apply Hle.
        unfold not. intros Heq. rewrite Heq in Hne. 
        assert (Hmm: S m = S m). reflexivity.
        unfold not in Hne. apply Hne in Hmm. inversion Hmm.
Qed.

Theorem lt_notltS_eq: forall n m,
  excluded_middle -> n <= m -> ~ S n <= m -> n = m.
Proof. intros n m Hex Hle Hns.
  induction (Hex (n = m)).
  apply H.
  assert (Hlt := le_ne_lt n m Hle H).
  unfold lt in Hlt. unfold not in Hns. apply Hns in Hlt. inversion Hlt.
Qed.

Theorem Sn_lt_m__n_lt_m: forall n m, S n < m -> n < m.
Proof. intros n m Hsn.
  unfold lt. apply Sn_le_Sm__n_le_m. apply Sn_le_m__Sn_le_Sm.
  unfold lt in Hsn. apply Hsn.
Qed.

Theorem l1_eq_l2__l_app_l1_eq_l_app_l2: forall (X:Type) (l l1 l2:list X),
  l1 = l2 -> l ++ l1 = l ++ l2.
Proof.
  intros X l l1 l2 H.
  rewrite H. reflexivity.
Qed.
(** [] *)


(** Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof.  intros X l1. induction l1 as [|h1 t1].
  -  (* l1 nil *)
    intros l2 Hex Hapx Hlen. destruct l2.
      +  (* l2 nil *) inversion Hlen.
      +  (* l2 cons *) inversion Hlen.
  -  (* l1 cons *)
    intros l2 Hex Hapx Hlen.
    apply repeats_or.
    destruct l2 as [|h2 t2].
      +  (* l2 = [] *)
        assert (Hapx': appears_in h1 (h1 :: t1)).
          apply ai_here.
        assert (Hapx'' := Hapx h1).
        apply Hapx'' in Hapx'.
        inversion Hapx'.
      +  (* l2 = h2::t2 *)
        apply imp_or_or with (A:=length (h2 :: t2) < length t1).
        intros Hlen'.
        apply IHt1 with (h2 :: t2).
        apply Hex. 
        intros x Hapxt1.
        assert (Hapxl1: appears_in x (h1 :: t1)).
          apply ai_later. apply Hapxt1.
        assert (Hapxl2 := Hapx x).
        apply Hapxl2 in Hapxl1. apply Hapxl1.
        apply Hlen'.
        assert (Haph1t1:=Hex (appears_in h1 t1)).
        inversion Haph1t1.
        right. apply H.
Admitted.


(** $Date: 2016-12-18 16:20:32 -0500 (Sun, 18 Dec 2016) $ *)

(** * Logic: Logic in Coq *)

Require Export MoreProp. 

(** Coq's built-in logic is very small: the only primitives are
    [Inductive] definitions, universal quantification ([forall]), and
    implication ([->]), while all the other familiar logical
    connectives -- conjunction, disjunction, negation, existential
    quantification, even equality -- can be encoded using just these.

    This chapter explains the encodings and shows how the tactics
    we've seen can be used to carry out standard forms of logical
    reasoning involving these connectives. *)

(* ########################################################### *)
(** * Conjunction *)

(** The logical conjunction of propositions [P] and [Q] can be
    represented using an [Inductive] definition with one
    constructor. *)

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q). 

(** Note that, like the definition of [ev] in a previous
    chapter, this definition is parameterized; however, in this case,
    the parameters are themselves propositions, rather than numbers. *)

(** The intuition behind this definition is simple: to
    construct evidence for [and P Q], we must provide evidence
    for [P] and evidence for [Q].  More precisely:

    - [conj p q] can be taken as evidence for [and P Q] if [p]
      is evidence for [P] and [q] is evidence for [Q]; and

    - this is the _only_ way to give evidence for [and P Q] --
      that is, if someone gives us evidence for [and P Q], we
      know it must have the form [conj p q], where [p] is
      evidence for [P] and [q] is evidence for [Q]. 

   Since we'll be using conjunction a lot, let's introduce a more
   familiar-looking infix notation for it. *)

Notation "P /\ Q" := (and P Q) : type_scope.

(** (The [type_scope] annotation tells Coq that this notation
    will be appearing in propositions, not values.) *)

(** Consider the "type" of the constructor [conj]: *)

Check conj.
(* ===>  forall P Q : Prop, P -> Q -> P /\ Q *)

(** Notice that it takes 4 inputs -- namely the propositions [P]
    and [Q] and evidence for [P] and [Q] -- and returns as output the
    evidence of [P /\ Q]. *)

(** Besides the elegance of building everything up from a tiny
    foundation, what's nice about defining conjunction this way is
    that we can prove statements involving conjunction using the
    tactics that we already know.  For example, if the goal statement
    is a conjuction, we can prove it by applying the single
    constructor [conj], which (as can be seen from the type of [conj])
    solves the current goal and leaves the two parts of the
    conjunction as subgoals to be proved separately. *)

Theorem and_example : 
  (beautiful 0) /\ (beautiful 3).
Proof.
  apply conj.
  Case "left". apply b_0.
  Case "right". apply b_3.  Qed.

(** Just for convenience, we can use the tactic [split] as a shorthand for
    [apply conj]. *)

Theorem and_example' : 
  (ev 0) /\ (ev 4).
Proof.
  split.
    Case "left". apply ev_0.
    Case "right". apply ev_SS. apply ev_SS. apply ev_0.  Qed.

(** Conversely, the [inversion] tactic can be used to take a
    conjunction hypothesis in the context, calculate what evidence
    must have been used to build it, and add variables representing
    this evidence to the proof context. *)

Theorem proj1 : forall P Q : Prop, 
  P /\ Q -> P.
Proof.
  intros P Q H.
  inversion H as [HP HQ]. 
  apply HP.  Qed.

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
    Case "left". apply HQ. 
    Case "right". apply HP.  Qed.
  

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
    Case "left". split.
      SCase "left". apply HP.
      SCase "right". apply HQ.
    Case "right". apply HR.
Qed.
(** [] *)

(** **** Exercise: 2 stars (even__ev) *)
(** Now we can prove the other direction of the equivalence of [even]
   and [ev], which we left hanging in chapter [Prop].  Notice that the
   left-hand conjunct here is the statement we are actually interested
   in; the right-hand conjunct is needed in order to make the
   induction hypothesis strong enough that we can carry out the
   reasoning in the inductive step.  (To see why this is needed, try
   proving the left conjunct by itself and observe where things get
   stuck.) *)

Theorem even__ev : forall n : nat,
  (even n -> ev n) /\ (even (S n) -> ev (S n)).
Proof.
  (* Hint: Use induction on [n]. *)
  intros n.
  induction n as [|n'].
    Case "n = 0". split.
      SCase "ev 0". intros H. apply ev_0.
      SCase "ev (S 0)". intros H. inversion H.
    Case "n = S n'". split.
      SCase "ev (S n')".
        intros H. 
        inversion IHn'. apply H1. apply H.
      SCase "ev (S (S n'))".
        intros H.
        inversion IHn'. apply ev_SS. apply H0.
        inversion H. unfold even. apply H3.
Qed.

(** [] *)



(* ###################################################### *)
(** ** Iff *)

(** The handy "if and only if" connective is just the conjunction of
    two implications. *)

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q) 
                      (at level 95, no associativity) 
                      : type_scope.

Theorem iff_implies : forall P Q : Prop, 
  (P <-> Q) -> P -> Q.
Proof.  
  intros P Q H. 
  inversion H as [HAB HBA]. apply HAB.  Qed.

Theorem iff_sym : forall P Q : Prop, 
  (P <-> Q) -> (Q <-> P).
Proof.
  (* WORKED IN CLASS *)
  intros P Q H. 
  inversion H as [HAB HBA].
  split.
    Case "->". apply HBA.
    Case "<-". apply HAB.  Qed.

(** **** Exercise: 1 star, optional (iff_properties) *)
(** Using the above proof that [<->] is symmetric ([iff_sym]) as
    a guide, prove that it is also reflexive and transitive. *)

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
    Case "P -> R". intros HP. apply HiQR. apply HiPQ. apply HP.
    Case "R -> P". intros HR. apply HiQP. apply HiRQ. apply HR.
Qed.

(** Hint: If you have an iff hypothesis in the context, you can use
    [inversion] to break it into two separate implications.  (Think
    about why this works.) *)
(** [] *)

(** Some of Coq's tactics treat [iff] statements specially, thus
    avoiding the need for some low-level manipulation when reasoning
    with them.  In particular, [rewrite] can be used with [iff]
    statements, not just equalities. *)

(* ############################################################ *)
(** * Disjunction *)

(** Disjunction ("logical or") can also be defined as an
    inductive proposition. *)

Inductive or (P Q : Prop) : Prop :=
  | or_introl : P -> or P Q
  | or_intror : Q -> or P Q. 

Notation "P \/ Q" := (or P Q) : type_scope.

(** Consider the "type" of the constructor [or_introl]: *)

Check or_introl.
(* ===>  forall P Q : Prop, P -> P \/ Q *)

(** It takes 3 inputs, namely the propositions [P], [Q] and
    evidence of [P], and returns, as output, the evidence of [P \/ Q].
    Next, look at the type of [or_intror]: *)

Check or_intror.
(* ===>  forall P Q : Prop, Q -> P \/ Q *)

(** It is like [or_introl] but it requires evidence of [Q]
    instead of evidence of [P]. *)

(** Intuitively, there are two ways of giving evidence for [P \/ Q]:

    - give evidence for [P] (and say that it is [P] you are giving
      evidence for -- this is the function of the [or_introl]
      constructor), or

    - give evidence for [Q], tagged with the [or_intror]
      constructor. *)

(** Since [P \/ Q] has two constructors, doing [inversion] on a
    hypothesis of type [P \/ Q] yields two subgoals. *)

Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". apply or_intror. apply HP.
    Case "right". apply or_introl. apply HQ.  Qed.

(** From here on, we'll use the shorthand tactics [left] and [right]
    in place of [apply or_introl] and [apply or_intror]. *)

Theorem or_commut' : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q H.
  inversion H as [HP | HQ].
    Case "left". right. apply HP.
    Case "right". left. apply HQ.  Qed.





Theorem or_distributes_over_and_1 : forall P Q R : Prop,
  P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof. 
  intros P Q R. intros H. inversion H as [HP | [HQ HR]]. 
    Case "left". split.
      SCase "left". left. apply HP.
      SCase "right". left. apply HP.
    Case "right". split.
      SCase "left". right. apply HQ.
      SCase "right". right. apply HR.  Qed.

(** **** Exercise: 2 stars (or_distributes_over_and_2) *)
Theorem or_distributes_over_and_2 : forall P Q R : Prop,
  (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H.
  inversion H.

  induction H0.
    left. apply H0.
    induction H1.
      left. apply H1.
      right. split.
        apply H0.
        apply H1.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  split.
    apply or_distributes_over_and_1.
    apply or_distributes_over_and_2.
Qed.
(** [] *)

(* ################################################### *)
(** ** Relating [/\] and [\/] with [andb] and [orb] (advanced) *)

(** We've already seen several places where analogous structures
    can be found in Coq's computational ([Type]) and logical ([Prop])
    worlds.  Here is one more: the boolean operators [andb] and [orb]
    are clearly analogs of the logical connectives [/\] and [\/].
    This analogy can be made more precise by the following theorems,
    which show how to translate knowledge about [andb] and [orb]'s
    behaviors on certain inputs into propositional facts about those
    inputs. *)

Theorem andb_prop : forall b c,
  andb b c = true -> b = true /\ c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". apply conj. reflexivity. reflexivity.
      SCase "c = false". inversion H.
    Case "b = false". inversion H.  Qed.

Theorem andb_true_intro : forall b c,
  b = true /\ c = true -> andb b c = true.
Proof.
  (* WORKED IN CLASS *)
  intros b c H.
  inversion H.
  rewrite H0. rewrite H1. reflexivity. Qed.

(** **** Exercise: 2 stars, optional (bool_prop) *)
Theorem andb_false : forall b c,
  andb b c = false -> b = false \/ c = false.
Proof. 
  intros b c H.
  destruct b.
    Case "b = true". destruct c.
      SCase "c = true". inversion H.
      SCase "c = false". right. reflexivity.
    Case "b = false". left. reflexivity.
Qed.

Theorem orb_prop : forall b c,
  orb b c = true -> b = true \/ c = true.
Proof.
  intros b c Horb.
  destruct b.
    Case "b = true". left. reflexivity.
    Case "b = false". destruct c.
      SCase "c = true". right. reflexivity.
      SCase "c = false". inversion Horb.
Qed.

Theorem orb_false_elim : forall b c,
  orb b c = false -> b = false /\ c = false.
Proof. 
  intros b c Horb.
  destruct b.
    Case "b = true". inversion Horb.
    Case "b = false". destruct c.
      SCase "c = true". inversion Horb.
      SCase "c = false". split. reflexivity. reflexivity.
Qed.
(** [] *)



(* ################################################### *)
(** * Falsehood *)

(** Logical falsehood can be represented in Coq as an inductively
    defined proposition with no constructors. *)

Inductive False : Prop := . 

(** Intuition: [False] is a proposition for which there is no way
    to give evidence. *)


(** Since [False] has no constructors, inverting an assumption
    of type [False] always yields zero subgoals, allowing us to
    immediately prove any goal. *)

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof. 
  intros contra.
  inversion contra.  Qed. 

(** How does this work? The [inversion] tactic breaks [contra] into
    each of its possible cases, and yields a subgoal for each case.
    As [contra] is evidence for [False], it has _no_ possible cases,
    hence, there are no possible subgoals and the proof is done. *)

(** Conversely, the only way to prove [False] is if there is already
    something nonsensical or contradictory in the context: *)

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.  Qed.

(** Actually, since the proof of [False_implies_nonsense]
    doesn't actually have anything to do with the specific nonsensical
    thing being proved; it can easily be generalized to work for an
    arbitrary [P]: *)

Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P contra.
  inversion contra.  Qed.

(** The Latin _ex falso quodlibet_ means, literally, "from
    falsehood follows whatever you please."  This theorem is also
    known as the _principle of explosion_. *)


(* #################################################### *)
(** ** Truth *)

(** Since we have defined falsehood in Coq, one might wonder whether
    it is possible to define truth in the same way.  We can. *)

(** **** Exercise: 2 stars, advanced (True) *)
(** Define [True] as another inductively defined proposition.  (The
    intution is that [True] should be a proposition for which it is
    trivial to give evidence.) *)

Inductive True : Prop := trivially_true. 
(** [] *)

(** However, unlike [False], which we'll use extensively, [True] is
    used fairly rarely. By itself, it is trivial (and therefore
    uninteresting) to prove as a goal, and it carries no useful
    information as a hypothesis. But it can be useful when defining
    complex [Prop]s using conditionals, or as a parameter to 
    higher-order [Prop]s. *)

(* #################################################### *)
(** * Negation *)

(** The logical complement of a proposition [P] is written [not
    P] or, for shorthand, [~P]: *)

Definition not (P:Prop) := P -> False.

(** The intuition is that, if [P] is not true, then anything at
    all (even [False]) follows from assuming [P]. *)

Notation "~ x" := (not x) : type_scope.

Check not.
(* ===> Prop -> Prop *)

(** It takes a little practice to get used to working with
    negation in Coq.  Even though you can see perfectly well why
    something is true, it can be a little hard at first to get things
    into the right configuration so that Coq can see it!  Here are
    proofs of a few familiar facts about negation to get you warmed
    up. *)

Theorem not_False : 
  ~ False.
Proof.
  unfold not. intros H. inversion H.  Qed.

Theorem contradiction_implies_anything : forall P Q : Prop,
  (P /\ ~P) -> Q.
Proof. 
  (* WORKED IN CLASS *)
  intros P Q H. inversion H as [HP HNA]. unfold not in HNA. 
  apply HNA in HP. inversion HP.  Qed.

Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not. intros G. apply G. apply H.  Qed.

(** **** Exercise: 2 stars, advanced (double_neg_inf) *)
(** Write an informal proof of [double_neg]:

   _Theorem_: [P] implies [~~P], for any proposition [P].

   _Proof_: (one way)
     We know that P holds. Therefore, not-P doesn't. Since not-P doesn't hold,
     it follows that not-not-P does hold.

   _Proof_: (another way)
     We want to prove that (not (not P)) holds. This is equivalent to proving
     that (not P) implies False.
       
     We know P holds, so (not P) is False. Since (not P) is False, proving
     that (not P) implies False is trivial and we're done.
   []
*)

(** **** Exercise: 2 stars (contrapositive) *)
Theorem contrapositive : forall P Q : Prop,
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HPQ HnQ.
  unfold not in HnQ.
  unfold not. intros HP.
  apply HPQ in HP. apply HnQ in HP. apply HP.
Qed.
(** [] *)

(** **** Exercise: 1 star (not_both_true_and_false) *)
Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof. 
  intros P. unfold not. apply contradiction_implies_anything.
Qed.
(** [] *)

(** **** Exercise: 1 star, advanced (informal_not_PNP) *)
(** Write an informal proof (in English) of the proposition [forall P
    : Prop, ~(P /\ ~P)]. *)

(*
P either holds or does not hold, but not both. For P /\ ~P to hold, P
would need to both hold and not hold. Therefore it is not the case
that P /\ ~P, and we can say it is true that ~(P /\ ~P).

These informal proofs are the hardest bit of this book.
*)

(** [] *)

Theorem five_not_even :  
  ~ ev 5.
Proof. 
  (* WORKED IN CLASS *)
  unfold not. intros Hev5. inversion Hev5 as [|n Hev3 Heqn]. 
  inversion Hev3 as [|n' Hev1 Heqn']. inversion Hev1.  Qed.

(** **** Exercise: 1 star (ev_not_ev_S) *)
(** Theorem [five_not_even] confirms the unsurprising fact that five
    is not an even number.  Prove this more interesting fact: *)

Theorem ev_not_ev_S : forall n,
  ev n -> ~ ev (S n).
Proof. 
  unfold not. intros n H. induction H. (* not n! *)
  Case "ev 1". intros H. inversion H.
  Case "ev (S (S (S n)))".
    intros HevSSS.
    apply ev_minus2 in HevSSS. simpl in HevSSS.
    apply IHev in HevSSS. apply HevSSS.
Qed.
(** [] *)

(** Note that some theorems that are true in classical logic are _not_
    provable in Coq's (constructive) logic.  E.g., let's look at how
    this proof gets stuck... *)

Theorem classic_double_neg : forall P : Prop,
  ~~P -> P.
Proof.
  (* WORKED IN CLASS *)
  intros P H. unfold not in H. 
  (* But now what? There is no way to "invent" evidence for [~P] 
     from evidence for [P]. *) 
  Abort.

(** **** Exercise: 5 stars, advanced, optional (classical_axioms) *)
(** For those who like a challenge, here is an exercise
    taken from the Coq'Art book (p. 123).  The following five
    statements are often considered as characterizations of
    classical logic (as opposed to constructive logic, which is
    what is "built in" to Coq).  We can't prove them in Coq, but
    we can consistently add any one of them as an unproven axiom
    if we wish to work in classical logic.  Prove that these five
    propositions are equivalent. *)

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

(* ########################################################## *)
(** ** Inequality *)

(** Saying [x <> y] is just the same as saying [~(x = y)]. *)

Notation "x <> y" := (~ (x = y)) : type_scope.

(** Since inequality involves a negation, it again requires
    a little practice to be able to work with it fluently.  Here
    is one very useful trick.  If you are trying to prove a goal
    that is nonsensical (e.g., the goal state is [false = true]),
    apply the lemma [ex_falso_quodlibet] to change the goal to
    [False].  This makes it easier to use assumptions of the form
    [~P] that are available in the context -- in particular,
    assumptions of the form [x<>y]. *)

Theorem not_false_then_true : forall b : bool,
  b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.  
    apply ex_falso_quodlibet.
    apply H. reflexivity.   Qed.

Theorem Sn_ne_Sm__n_ne_m: forall n m: nat,
  S n <> S m -> n <> m.
Proof.
  intros n.
  induction n.
    intros m H. destruct m.
      unfold not in H. unfold not. intros H0. apply H. reflexivity.
      unfold not in H. unfold not. intros H0Sm. inversion H0Sm.
    intros m H. destruct m.
      Case "0".
        unfold not in H.
        unfold not. intros HSn0.
        apply (f_equal nat nat S) in HSn0.
        apply H in HSn0. apply HSn0.
      Case "S".
        unfold not in H.
        unfold not. intros HSnSm.
        apply (f_equal nat nat S) in HSnSm.
        apply H in HSnSm. apply HSnSm.
Qed.

(** **** Exercise: 2 stars (false_beq_nat) *)
Theorem false_beq_nat : forall n m : nat,
     n <> m ->
     beq_nat n m = false.
Proof. 
  intros n.
  induction n as [|n'].
    Case "n = 0". intros m H. destruct m as [|m'].
      SCase "m = 0".
        simpl. apply ex_falso_quodlibet.
        unfold not in H. apply H. reflexivity.
      SCase "m = S m'".
        simpl. reflexivity.
    Case "n = 1". intros m H. destruct m as [|m'].
      SCase "m = 0".
        simpl. reflexivity.
      SCase "m = S m'".
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
      
(** **** Exercise: 2 stars, optional (ble_nat_false) *)
Theorem ble_nat_false : forall n m,
  ble_nat n m = false -> ~(n <= m).
Proof.
  intros n m H.
  unfold not. intros Hle.
  generalize dependent m.
  induction n as [|n'].
    intros m Hble Hle. destruct m.
      simpl in Hble. inversion Hble.
      simpl in Hble. inversion Hble.
    intros m Hble Hle. destruct m as [|m'].
      inversion Hle.
      apply IHn' with m'. simpl in Hble. apply Hble.
      apply Sn_le_Sm__n_le_m. apply Hle.
Qed.

(** [] *)




(* ############################################################ *)
(** * Existential Quantification *)

(** Another critical logical connective is _existential
    quantification_.  We can express it with the following
    definition: *)

Inductive ex (X:Type) (P : X->Prop) : Prop :=
  ex_intro : forall (witness:X), P witness -> ex X P.

(** That is, [ex] is a family of propositions indexed by a type [X]
    and a property [P] over [X].  In order to give evidence for the
    assertion "there exists an [x] for which the property [P] holds"
    we must actually name a _witness_ -- a specific value [x] -- and
    then give evidence for [P x], i.e., evidence that [x] has the
    property [P]. 

*)


(** Coq's [Notation] facility can be used to introduce more
    familiar notation for writing existentially quantified
    propositions, exactly parallel to the built-in syntax for
    universally quantified propositions.  Instead of writing [ex nat
    ev] to express the proposition that there exists some number that
    is even, for example, we can write [exists x:nat, ev x].  (It is
    not necessary to understand exactly how the [Notation] definition
    works.) *)

Notation "'exists' x , p" := (ex _ (fun x => p))
  (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" := (ex _ (fun x:X => p))
  (at level 200, x ident, right associativity) : type_scope.

(** We can use the usual set of tactics for
    manipulating existentials.  For example, to prove an
    existential, we can [apply] the constructor [ex_intro].  Since the
    premise of [ex_intro] involves a variable ([witness]) that does
    not appear in its conclusion, we need to explicitly give its value
    when we use [apply]. *)

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2). 
  reflexivity.  Qed.

(** Note that we have to explicitly give the witness. *)

(** Or, instead of writing [apply ex_intro with (witness:=e)] all the
    time, we can use the convenient shorthand [exists e], which means
    the same thing. *)

Example exists_example_1' : exists n, n + (n * n) = 6.
Proof.
  exists 2. 
  reflexivity.  Qed.

(** Conversely, if we have an existential hypothesis in the
    context, we can eliminate it with [inversion].  Note the use
    of the [as...] pattern to name the variable that Coq
    introduces to name the witness value and get evidence that
    the hypothesis holds for the witness.  (If we don't
    explicitly choose one, Coq will just call it [witness], which
    makes proofs confusing.) *)
  
Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm]. 
  exists (2 + m).  
  apply Hm.  Qed. 

(** **** Exercise: 1 star, optional (english_exists) *)
(** In English, what does the proposition 
      ex nat (fun n => beautiful (S n))
]] 
    mean? *)

(* There is a natural number whose successor is beautiful. *)

(** **** Exercise: 1 star (dist_not_exists) *)
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
  apply ex_intro with (witness:=x).
  apply HNPx.
  apply Hexists in He.
  inversion He.
Qed.
(** [] *)

(** **** Exercise: 2 stars (dist_exists_or) *)
(** Prove that existential quantification distributes over
    disjunction. *)

Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  Case "exists (P \/ Q) -> (exists P) \/ (exists Q)".
    intro Hexists. inversion Hexists as [x HPQ]. inversion HPQ.
    left. apply ex_intro with (witness := x). apply H.
    right. apply ex_intro with (witness := x). apply H.
  Case "(exists P) \/ (exists Q) -> exists (P \/ Q)".
    intro Hexists. inversion Hexists.
    inversion H as [Hx HP]. apply ex_intro with (witness:=Hx). left. apply HP.
    inversion H as [Hx HQ]. apply ex_intro with (witness:=Hx). right. apply HQ.
Qed.
(** [] *)

(* Print dist_exists_or. *)


(* ###################################################### *)
(** * Equality *)

(** Even Coq's equality relation is not built in.  It has (roughly)
    the following inductive definition. *)

(* (We enclose the definition in a module to avoid confusion with the
    standard library equality, which we have used extensively
    already.) *)

Module MyEquality.

Inductive eq {X:Type} : X -> X -> Prop :=
  refl_equal : forall x, eq x x.
(** Standard infix notation: *)

Notation "x = y" := (eq x y) 
                    (at level 70, no associativity) 
                    : type_scope.

(** The definition of [=] is a bit subtle.  The way to think about it
    is that, given a set [X], it defines a _family_ of propositions
    "[x] is equal to [y]," indexed by pairs of values ([x] and [y])
    from [X].  There is just one way of constructing evidence for
    members of this family: applying the constructor [refl_equal] to a
    type [X] and a value [x : X] yields evidence that [x] is equal to
    [x]. *)


(** **** Exercise: 2 stars (leibniz_equality) *)
(** The inductive definitions of equality corresponds to _Leibniz equality_: 
   what we mean when we say "[x] and [y] are equal" is that every 
   property on [P] that is true of [x] is also true of [y].  *)

Lemma leibniz_equality : forall (X : Type) (x y: X), 
 x = y -> forall P : X -> Prop, P x -> P y.
Proof.
  intros X x y Hxeqy P Px.
  induction Hxeqy. apply Px.
Qed.
(** [] *)

(** We can use
    [refl_equal] to construct evidence that, for example, [2 = 2].
    Can we also use it to construct evidence that [1 + 1 = 2]?  Yes:
    indeed, it is the very same piece of evidence!  The reason is that
    Coq treats as "the same" any two terms that are _convertible_
    according to a simple set of computation rules.  These rules,
    which are similar to those used by [Eval compute], include
    evaluation of function application, inlining of definitions, and
    simplification of [match]es.
*)

Lemma four: 2 + 2 = 1 + 3. 
Proof.
  apply refl_equal. 
Qed.

(** The [reflexivity] tactic that we have used to prove equalities up
to now is essentially just short-hand for [apply refl_equal]. *)

End MyEquality.


(* ###################################################### *)
(** * Evidence-carrying booleans. *)

(** So far we've seen two different forms of equality predicates:
[eq], which produces a [Prop], and
the type-specific forms, like [beq_nat], that produce [boolean]
values.  The former are more convenient to reason about, but
we've relied on the latter to let us use equality tests 
in _computations_.  While it is straightforward to write lemmas
(e.g. [beq_nat_true] and [beq_nat_false]) that connect the two forms,
using these lemmas quickly gets tedious. 

It turns out that we can get the benefits of both forms at once 
by using a construct called [sumbool]. *)

Inductive sumbool (A B : Prop) : Set :=
 | left : A -> sumbool A B 
 | right : B -> sumbool A B.

Notation "{ A } + { B }" :=  (sumbool A B) : type_scope.

(** Think of [sumbool] as being like the [boolean] type, but instead
of its values being just [true] and [false], they carry _evidence_
of truth or falsity. This means that when we [destruct] them, we
are left with the relevant evidence as a hypothesis -- just as with [or].
(In fact, the definition of [sumbool] is almost the same as for [or].
The only difference is that values of [sumbool] are declared to be in
[Set] rather than in [Prop]; this is a technical distinction 
that allows us to compute with them.) *) 

(** Here's how we can define a [sumbool] for equality on [nat]s *)

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left. reflexivity.
    SCase "m = S m'".
      right. intros contra. inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right. intros contra. inversion contra.
    SCase "m = S m'". 
      destruct IHn' with (m := m') as [eq | neq].
      left. apply f_equal.  apply eq.
      right. intros Heq. inversion Heq as [Heq']. apply neq. apply Heq'.
Defined. 

(** Read as a theorem, this says that equality on [nat]s is decidable:
that is, given two [nat] values, we can always produce either 
evidence that they are equal or evidence that they are not.
Read computationally, [eq_nat_dec] takes two [nat] values and returns
a [sumbool] constructed with [left] if they are equal and [right] 
if they are not; this result can be tested with a [match] or, better,
with an [if-then-else], just like a regular [boolean]. 
(Notice that we ended this proof with [Defined] rather than [Qed]. 
The only difference this makes is that the proof becomes _transparent_,
meaning that its definition is available when Coq tries to do reductions,
which is important for the computational interpretation.)

Here's a simple example illustrating the advantages of the [sumbool] form. *)

Definition override' {X: Type} (f: nat->X) (k:nat) (x:X) : nat->X:=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f. intros Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).   (* observe what appears as a hypothesis *)
  Case "k1 = k2".
    rewrite <- e.
    symmetry. apply Hx1.
  Case "k1 <> k2". 
    reflexivity.  Qed.

(** Compare this to the more laborious proof (in MoreCoq.v) for the 
   version of [override] defined using [beq_nat], where we had to
   use the auxiliary lemma [beq_nat_true] to convert a fact about booleans
   to a Prop. *)


(** **** Exercise: 1 star (override_shadow') *)
Theorem override_shadow' : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
  Case "k1 = k2". reflexivity.
  Case "k1 <> k2". reflexivity.
Qed.
(** [] *)

(* ####################################################### *)
(** ** Inversion, Again (Advanced) *)

(** We've seen [inversion] used with both equality hypotheses and
    hypotheses about inductively defined propositions.  Now that we've
    seen that these are actually the same thing, we're in a position
    to take a closer look at how [inversion] behaves...

    In general, the [inversion] tactic

    - takes a hypothesis [H] whose type [P] is inductively defined,
      and

    - for each constructor [C] in [P]'s definition,

      - generates a new subgoal in which we assume [H] was
        built with [C],

      - adds the arguments (premises) of [C] to the context of
        the subgoal as extra hypotheses,

      - matches the conclusion (result type) of [C] against the
        current goal and calculates a set of equalities that must
        hold in order for [C] to be applicable,
        
      - adds these equalities to the context (and, for convenience,
        rewrites them in the goal), and

      - if the equalities are not satisfiable (e.g., they involve
        things like [S n = O]), immediately solves the subgoal. *)

(** _Example_: If we invert a hypothesis built with [or], there are two
   constructors, so two subgoals get generated.  The
   conclusion (result type) of the constructor ([P \/ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.

   _Example_: If we invert a hypothesis built with [and], there is
   only one constructor, so only one subgoal gets generated.  Again,
   the conclusion (result type) of the constructor ([P /\ Q]) doesn't
   place any restrictions on the form of [P] or [Q], so we don't get
   any extra equalities in the context of the subgoal.  The
   constructor does have two arguments, though, and these can be seen
   in the context in the subgoal.

   _Example_: If we invert a hypothesis built with [eq], there is
   again only one constructor, so only one subgoal gets generated.
   Now, though, the form of the [refl_equal] constructor does give us
   some extra information: it tells us that the two arguments to [eq]
   must be the same!  The [inversion] tactic adds this fact to the
   context.  *)


(** **** Exercise: 1 star, optional (dist_and_or_eq_implies_and) *)  
Lemma dist_and_or_eq_implies_and : forall P Q R,
       P /\ (Q \/ R) /\ Q = R -> P/\Q.
Proof.
  intros P Q R H.
  inversion H.
  inversion H1.
  inversion H2.
  apply conj. apply H0. apply H4.
  apply conj. apply H0. rewrite H3. apply H4.
Qed.

(** [] *)




(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (all_forallb) *)
(** Inductively define a property [all] of lists, parameterized by a
    type [X] and a property [P : X -> Prop], such that [all X P l]
    asserts that [P] is true for every element of the list [l]. *)

Inductive all (X : Type) (P : X -> Prop) : list X -> Prop :=
  | all_nil : all X P []
  | all_cons : forall x xs, P x -> all X P xs -> all X P (x::xs).

(** Recall the function [forallb], from the exercise
    [forall_exists_challenge] in chapter [Poly]: *)

Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

(** Using the property [all], write down a specification for [forallb],
    and prove that it satisfies the specification. Try to make your 
    specification as precise as possible.

    Are there any important properties of the function [forallb] which
    are not captured by your specification? *)

Theorem forallb_all: forall X xs f,
  {forallb f xs = true <->     all X (fun x => f x = true) xs} +
  {forallb f xs = false <-> ~ (all X (fun x => f x = true) xs)}.
Proof. intros X l f.
  induction l as [|x xs].
    Case "l = []".
      simpl. left. split.
        intros Htrue. apply all_nil.
        intros Hall. reflexivity.
    Case "l = x::xs".
      simpl. destruct (f x) eqn:Hfx.
        SCase "f x = true".
          simpl. inversion IHxs.
            SSCase "forall b f xs = true".
              inversion H.
              left. split.
                intros Hforall. apply all_cons. apply Hfx. apply H0. apply Hforall.
                intros Hall. apply H1. inversion Hall. apply H5.
            SSCase "forall b f xs = false".
              inversion H. 
              right. split.
                SSSCase "forall = false -> ~all".
                  intros Hforall. unfold not.
                  intros Hall. inversion Hall.
                  apply H0 in Hforall. unfold not in Hforall.
                  assert (Hfalse := H5).
                  apply Hforall in H5. apply H5.
                SSSCase "~all -> forall = false".
                  intros Hall.
                  apply H1. unfold not.
                  intros Hallxs.
                  unfold not in Hall.
                  assert (Hallxxs: all X (fun x: X => f x = true) (x::xs)).
                    apply all_cons. apply Hfx. apply Hallxs.
                  apply Hall in Hallxxs. apply Hallxxs.
        SCase "f x = false".
          simpl. left. split.
            intros Hft. inversion Hft.
            intros Hall. inversion Hall. rewrite Hfx in H1. inversion H1.
Qed.

(** [] *)

(** **** Exercise: 4 stars, advanced (filter_challenge) *)
(** One of the main purposes of Coq is to prove that programs match
    their specifications.  To this end, let's prove that our
    definition of [filter] matches a specification.  Here is the
    specification, written out informally in English.

    Suppose we have a set [X], a function [test: X->bool], and a list
    [l] of type [list X].  Suppose further that [l] is an "in-order
    merge" of two lists, [l1] and [l2], such that every item in [l1]
    satisfies [test] and no item in [l2] satisfies test.  Then [filter
    test l = l1].

    A list [l] is an "in-order merge" of [l1] and [l2] if it contains
    all the same elements as [l1] and [l2], in the same order as [l1]
    and [l2], but possibly interleaved.  For example, 
    [1,4,6,2,3]
    is an in-order merge of
    [1,6,2]
    and
    [4,3].
    Your job is to translate this specification into a Coq theorem and
    prove it.  (Hint: You'll need to begin by defining what it means
    for one list to be a merge of two others.  Do this with an
    inductive relation, not a [Fixpoint].)  *)

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
    Case "l = []". intros l1 Halltrue l2 Hmerge Hallfalse.
      simpl. inversion Hmerge. reflexivity.
    Case "l = hl :: tl". intros l1 Halltrue l2 Hmerge Hallfalse.
      simpl. destruct (f hl) eqn:Hfhead.
        SCase "true".
          inversion Hmerge.
          SSCase "head from l1".
            rewrite IHtl with (l1:=t1) (l2:=l2).
            reflexivity.
            rewrite <- H0 in Halltrue.
            inversion Halltrue. apply H7.
            apply H2. apply Hallfalse.
          SSCase "head from l2".
            rewrite <- H1 in Hallfalse.
            inversion Hallfalse.
            rewrite H in H6. rewrite H6 in Hfhead. inversion Hfhead.
        SCase "false".
          inversion Hmerge.
          SSCase "head from l1".
            rewrite <- H0 in Halltrue.
            inversion Halltrue.
            rewrite H in H6. rewrite H6 in Hfhead. inversion Hfhead.
          SSCase "head from t2".
            rewrite IHtl with (l1:=l1) (l2:=t2).
            reflexivity.
            apply Halltrue.
            apply H2.
            inversion Hallfalse.
            rewrite <- H4 in H1. inversion H1.
            rewrite <- H1 in H6. inversion H6. rewrite <- H9. apply H5.
Qed.

(** [] *)

(** **** Exercise: 5 stars, advanced, optional (filter_challenge_2) *)
(** A different way to formally characterize the behavior of [filter]
    goes like this: Among all subsequences of [l] with the property
    that [test] evaluates to [true] on all their members, [filter test
    l] is the longest.  Express this claim formally and prove it. *)

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
  assert (all_clause: forall X' (f:X'->bool) (h1:X') (t1 tl' l:list X') n (hl':X'),
    all X' (fun x: X' => f x = true) (h1 :: t1) ->
    subseq tl' t1 ->
    l = filter f (h1 :: t1) ->
    n = length l -> n < length (hl' :: tl') ->
    all X' (fun x0 : X' => f x0 = true) t1 /\ subseq tl' t1 /\ pred n < length tl').
    intros X' f' h1 t1 tl'' l'' n0 hl' Hall' Hsubseq' Hfilter' Hlen'l Hlen'l'.
      split. inversion Hall'. apply H3.
      split. apply Hsubseq'.
      destruct n0.
        Case "n=0".
          rewrite Hfilter' in Hlen'l. simpl in Hlen'l. destruct (f' h1) eqn:Hfh1.
            inversion Hlen'l.
            inversion Hall'. rewrite Hfh1 in H2. inversion H2.
        Case "n=S".
          simpl. unfold lt. unfold lt in Hlen'l'.
          simpl in Hlen'l'. apply Sn_le_Sm__n_le_m in Hlen'l'.
          apply Hlen'l'.

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
    Case "l1 = []". intros l' Hsubseq l Hfilter n Hexists H Hlenl Hsubseqlenl' Hlenl'.
      rewrite Hfilter in Hlenl. simpl in Hlenl.
      inversion Hsubseq. rewrite <- H0 in Hlenl'.
      rewrite Hlenl in Hlenl'. inversion Hlenl'.
    Case "l1 = h1 :: t1". intros l' Hsubseq l Hfilter n Hexists H Hlenl Hsubseqlenl' Hlenl'.
      inversion H as [Hall' Hsubseqlenl''].
      destruct l' as [|hl' tl'].
        SCase "l' = []".
          inversion Hlenl'.
        SCase "l' = hl' :: tl'".
          inversion Hsubseq.
            SSCase "subseq head".
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
            SSCase "subseq tail".
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
    Case "xs = []". intros ys Happ. simpl in Happ. right. apply Happ.
    Case "xs = hxs :: txs". intros ys Happ.
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
  Case "appears in xs".
    induction xs.
      inversion H.
      inversion H.
        apply ai_here.
        simpl. apply ai_later. apply IHxs. left. apply H1. apply H1.
  Case "appears in ys".
    generalize dependent xs.
    induction ys.
      inversion H.
      induction xs.
        intros Hor. simpl. apply H.
        intros Hor. simpl. apply ai_later. apply IHxs. right. apply H.
Qed.
    
  
(** Now use [appears_in] to define a proposition [disjoint X l1 l2],
    which should be provable exactly when [l1] and [l2] are
    lists (with elements of type X) that have no elements in common. *)

Definition disjoint (X:Type) (l1 l2:list X) := forall x,
                     (appears_in x l1 -> ~appears_in x l2) /\
                     (appears_in x l2 -> ~appears_in x l1).

(** Next, use [appears_in] to define an inductive proposition
    [no_repeats X l], which should be provable exactly when [l] is a
    list (with elements of type [X]) where every member is different
    from every other.  For example, [no_repeats nat [1,2,3,4]] and
    [no_repeats bool []] should be provable, while [no_repeats nat
    [1,2,1]] and [no_repeats bool [true,true]] should not be.  *)

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

(** Finally, state and prove one or more interesting theorems relating
    [disjoint], [no_repeats] and [++] (list append).  *)

Theorem disjoint_cons_l: forall X l1 l2 h,
  disjoint X l1 l2 -> ~ appears_in h l2 -> disjoint X (h::l1) l2.
Proof.
  intros X l1 l2 h Hdisj Hap.
  unfold disjoint. unfold disjoint in Hdisj.
  intros x. assert (Hdisjx := Hdisj x). inversion Hdisjx.
  split.
    Case "in l1".
      intros Hapl1. unfold not in Hap.
      inversion Hapl1.
        unfold not. apply Hap.
        unfold not. intros Hapl2. apply H0 in Hapl2.
        unfold not in Hapl2. apply Hapl2 in H2. inversion H2.
    Case "in l2".
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
    Case "in l1".
      intros Hapl1. unfold not in Hap.
      unfold not. intros Hapl2.
      inversion Hapl2.
        rewrite H2 in Hapl1. apply Hap in Hapl1. inversion Hapl1.
        apply H0 in H2. apply H2 in Hapl1. inversion Hapl1.
    Case "in h::l2".
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
    Case "in l1". intros Hapl1.
      apply no_repeats_appears_in_l with l1.
      apply Hapl1. apply Hnr.
    Case "in l2". intros Hapl2.
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
(** [] *)

(** **** Exercise: 4 stars, advanced (pigeonhole principle) *)
(** The "pigeonhole principle" states a basic fact about counting:
   if you distribute more than [n] items into [n] pigeonholes, some 
   pigeonhole must contain at least two items.  As is often the case,
   this apparently trivial fact about numbers requires non-trivial
   machinery to prove, but we now have enough... *)

(** First a pair of useful lemmas (we already proved these for lists
    of naturals, but not for arbitrary lists). *)

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2. 
Proof. 
  intros X l1 l2.
  induction l1.
    Case "l1 nil".
      simpl. reflexivity.
    Case "l1 cons".
      simpl. apply f_equal. apply IHl1.
Qed.

Lemma appears_in_app_split : forall (X:Type) (x:X) (l:list X),
  appears_in x l -> 
  exists l1, exists l2, l = l1 ++ (x::l2).
Proof.
  intros X x l Hap.
  induction Hap.
    Case "ai_here". exists []. exists l. simpl. reflexivity.
    Case "ai_later".
      inversion IHHap as [l1].
      inversion H as [l2].
      rewrite H0.
      exists (b :: l1). exists l2.
      simpl. reflexivity.
Qed.

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

(** Now here's a way to formalize the pigeonhole principle. List [l2]
   represents a list of pigeonhole labels, and list [l1] represents an
   assignment of items to labels: if there are more items than labels,
   at least two items must have the same label.  You will almost
   certainly need to use the [excluded_middle] hypothesis. *)

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

Theorem move_forall_out_of_or: forall (X:Type) (x:X) (P:X->Prop) (Q:Prop),
  excluded_middle ->
  (forall (x:X), (P x \/ Q)) -> 
  ((forall (x:X), (P x)) \/ Q).
Proof.
  intros X x P Q Hexm H.
  apply implies_to_or_neg.
  apply Hexm.
  intros HPx.
  unfold not in HPx.
  apply Hdm. unfold not.
  split.
  assert (Hx := H x).
  inversion Hx.

Theorem pigeonhole_principle: forall (X:Type) (l1 l2:list X),
  excluded_middle -> 
  (forall x, appears_in x l1 -> appears_in x l2) -> 
  length l2 < length l1 -> 
  repeats l1.  
Proof.  intros X l1. induction l1 as [|h1 t1].
  Case "l1 nil".
    intros l2 Hex Hapx Hlen. destruct l2.
      SCase "l2 nil". inversion Hlen.
      SCase "l2 cons". inversion Hlen.
  Case "l1 cons".
    intros l2 Hex Hapx Hlen.
    apply repeats_or.
    destruct l2 as [|h2 t2].
      SCase "l2 nil".
        assert (Hapx' := Hapx h1).
        assert (Hapxl1 := ai_here h1 t1).
        apply Hapx' in Hapxl1. inversion Hapxl1.
      SCase "l2 cons".
        assert (Ih := IHt1 t2). 
        replace (repeats t1) with ((forall x : X, appears_in x t1 -> appears_in x t2) /\ (length t2 < length t1)).
        apply and_distributes_over_or_1.
        split.
        apply Ih in Hex. pply IHt1 with (l2:=t2).
        apply Hex.
        intros x' Hapx'.
        apply Hapx in Hapx'.
        assert (Hex' := Hex (x = x')).
        inversion Hex'.
        SSCase "x = x'".
          assert (Hex'' := Hex (x = h1)). inversion Hex''.
            SSSCase "x = h1".

(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)


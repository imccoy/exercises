(** * MoreCoq: More About Coq *)

Require Export Poly.

(** This chapter introduces several more Coq tactics that,
    together, allow us to prove many more theorems about the
    functional programs we are writing. *)

(* ###################################################### *)
(** * The [apply] Tactic *)

(** We often encounter situations where the goal to be proved is
    exactly the same as some hypothesis in the context or some
    previously proved lemma. *)

Theorem silly1 : forall (n m o p : nat),
     n = m  ->
     [n;o] = [n;p] ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  rewrite <- eq1.
  (* At this point, we could finish with 
     "[rewrite -> eq2. reflexivity.]" as we have 
     done several times above. But we can achieve the
     same effect in a single step by using the 
     [apply] tactic instead: *)
  apply eq2.  Qed.

(** The [apply] tactic also works with _conditional_ hypotheses
    and lemmas: if the statement being applied is an implication, then
    the premises of this implication will be added to the list of
    subgoals needing to be proved. *)

Theorem silly2 : forall (n m o p : nat),
     n = m  ->
     (forall (q r : nat), q = r -> [q;o] = [r;p]) ->
     [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2. 
  apply eq2. apply eq1.  Qed.

(** You may find it instructive to experiment with this proof
    and see if there is a way to complete it using just [rewrite]
    instead of [apply]. *)

(** Typically, when we use [apply H], the statement [H] will
    begin with a [forall] binding some _universal variables_.  When
    Coq matches the current goal against the conclusion of [H], it
    will try to find appropriate values for these variables.  For
    example, when we do [apply eq2] in the following proof, the
    universal variable [q] in [eq2] gets instantiated with [n] and [r]
    gets instantiated with [m]. *)

Theorem silly2a : forall (n m : nat),
     (n,n) = (m,m)  ->
     (forall (q r : nat), (q,q) = (r,r) -> [q] = [r]) ->
     [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2. apply eq1.  Qed.

(** **** Exercise: 2 stars, optional (silly_ex) *)
(** Complete the following proof without using [simpl]. *)

Theorem silly_ex : 
     (forall n, evenb n = true -> oddb (S n) = true) ->
     evenb 3 = true ->
     oddb 4 = true.
Proof.
  intros H1 H2.
  apply H1. apply H2.
Qed.
(** [] *)

(** To use the [apply] tactic, the (conclusion of the) fact
    being applied must match the goal _exactly_ -- for example, [apply]
    will not work if the left and right sides of the equality are
    swapped. *)

Theorem silly3_firsttry : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  simpl.
  (* Here we cannot use [apply] directly *)
Abort.

(** In this case we can use the [symmetry] tactic, which switches the
    left and right sides of an equality in the goal. *)

Theorem silly3 : forall (n : nat),
     true = beq_nat n 5  ->
     beq_nat (S (S n)) 7 = true.
Proof.
  intros n H.
  symmetry.
  simpl. (* Actually, this [simpl] is unnecessary, since 
            [apply] will do a [simpl] step first. *)  
  apply H.  Qed.         

(** **** Exercise: 3 stars (apply_exercise1) *)
(** Hint: you can use [apply] with previously defined lemmas, not
    just hypotheses in the context.  Remember that [SearchAbout] is
    your friend. *)

Theorem rev_injective : forall (X : Type) (l1 l2 : list X),
  rev l1 = rev l2 -> l1 = l2.
Proof.
  intros X l1 l2 H.
  rewrite <- rev_involutive.
  rewrite <- H.
  rewrite rev_involutive.
  reflexivity.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
     l = rev l' ->
     l' = rev l.
Proof.
  intros l l' H.
  rewrite <- (rev_involutive nat l').
  apply rev_injective.
  rewrite rev_involutive.
  rewrite rev_involutive.
  symmetry.
  apply H.
Qed.
(** [] *)

(** **** Exercise: 1 star, optional (apply_rewrite) *)
(** Briefly explain the difference between the tactics [apply] and
    [rewrite].  Are there situations where both can usefully be
    applied?
  If we have A implies B, and we want to prove B, apply lets us do this
  by proving that A holds (and therefore B). Rewrite won't let you do that.
*)
(** [] *)


(* ###################################################### *)
(** * The [apply ... with ...] Tactic *)

(** The following silly example uses two rewrites in a row to
    get from [[a,b]] to [[e,f]]. *)

Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  rewrite -> eq1. rewrite -> eq2. reflexivity.  Qed.

(** Since this is a common pattern, we might
    abstract it out as a lemma recording once and for all
    the fact that equality is transitive. *)

Theorem trans_eq : forall (X:Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2. rewrite -> eq1. rewrite -> eq2. 
  reflexivity.  Qed.

(** Now, we should be able to use [trans_eq] to
    prove the above example.  However, to do this we need
    a slight refinement of the [apply] tactic. *)

Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2. 
  (* If we simply tell Coq [apply trans_eq] at this point,
     it can tell (by matching the goal against the
     conclusion of the lemma) that it should instantiate [X]
     with [[nat]], [n] with [[a,b]], and [o] with [[e,f]].
     However, the matching process doesn't determine an
     instantiation for [m]: we have to supply one explicitly
     by adding [with (m:=[c,d])] to the invocation of
     [apply]. *)
  apply trans_eq with (m:=[c;d]). apply eq1. apply eq2.   Qed.

(**  Actually, we usually don't have to include the name [m]
    in the [with] clause; Coq is often smart enough to
    figure out which instantiation we're giving. We could
    instead write: [apply trans_eq with [c,d]]. *)

(** **** Exercise: 3 stars, optional (apply_with_exercise) *)
Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o). 
Proof.
  intros n m o p H1 H2.
  apply trans_eq with m.
  apply H2.
  apply H1.
Qed.
(** [] *)


(* ###################################################### *)
(** * The [inversion] tactic *)

(** Recall the definition of natural numbers:
     Inductive nat : Type :=
       | O : nat
       | S : nat -> nat.
    It is clear from this definition that every number has one of two
    forms: either it is the constructor [O] or it is built by applying
    the constructor [S] to another number.  But there is more here than
    meets the eye: implicit in the definition (and in our informal
    understanding of how datatype declarations work in other
    programming languages) are two other facts:

    - The constructor [S] is _injective_.  That is, the only way we can
      have [S n = S m] is if [n = m].

    - The constructors [O] and [S] are _disjoint_.  That is, [O] is not
      equal to [S n] for any [n]. *)

(** Similar principles apply to all inductively defined types: all
    constructors are injective, and the values built from distinct
    constructors are never equal.  For lists, the [cons] constructor is
    injective and [nil] is different from every non-empty list.  For
    booleans, [true] and [false] are unequal.  (Since neither [true]
    nor [false] take any arguments, their injectivity is not an issue.) *)

(** Coq provides a tactic called [inversion] that allows us to exploit
    these principles in proofs.
 
    The [inversion] tactic is used like this.  Suppose [H] is a
    hypothesis in the context (or a previously proven lemma) of the
    form
      c a1 a2 ... an = d b1 b2 ... bm
    for some constructors [c] and [d] and arguments [a1 ... an] and
    [b1 ... bm].  Then [inversion H] instructs Coq to "invert" this
    equality to extract the information it contains about these terms:

    - If [c] and [d] are the same constructor, then we know, by the
      injectivity of this constructor, that [a1 = b1], [a2 = b2],
      etc.; [inversion H] adds these facts to the context, and tries
      to use them to rewrite the goal.

    - If [c] and [d] are different constructors, then the hypothesis
      [H] is contradictory.  That is, a false assumption has crept
      into the context, and this means that any goal whatsoever is
      provable!  In this case, [inversion H] marks the current goal as
      completed and pops it off the goal stack. *)

(** The [inversion] tactic is probably easier to understand by
    seeing it in action than from general descriptions like the above.
    Below you will find example theorems that demonstrate the use of
    [inversion] and exercises to test your understanding. *)

Theorem eq_add_S : forall (n m : nat),
     S n = S m ->
     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.  Qed.

Theorem silly4 : forall (n m : nat),
     [n] = [m] ->
     n = m.
Proof.
  intros n o eq. inversion eq. reflexivity.  Qed.

(** As a convenience, the [inversion] tactic can also
    destruct equalities between complex values, binding
    multiple variables as it goes. *)

Theorem silly5 : forall (n m o : nat),
     [n;m] = [o;o] ->
     [n] = [m].
Proof.
  intros n m o eq. inversion eq. reflexivity. Qed.

(** **** Exercise: 1 star (sillyex1) *) 
Example sillyex1 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = z :: j ->
     y :: l = x :: j ->
     x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H2. reflexivity.
Qed.
(** [] *)

Theorem silly6 : forall (n : nat),
     S n = O ->
     2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

Theorem silly7 : forall (n m : nat),
     false = true ->
     [n] = [m].
Proof.
  intros n m contra. inversion contra.  Qed.

(** **** Exercise: 1 star (sillyex2) *)
Example sillyex2 : forall (X : Type) (x y z : X) (l j : list X),
     x :: y :: l = [] ->
     y :: l = z :: j ->
     x = z.
Proof.
  intros X x y z l j contra H2.
  inversion contra.
Qed.
(** [] *)

(** While the injectivity of constructors allows us to reason
    [forall (n m : nat), S n = S m -> n = m], the reverse direction of
    the implication is an instance of a more general fact about
    constructors and functions, which we will often find useful: *)

Theorem f_equal : forall (A B : Type) (f: A -> B) (x y: A), 
    x = y -> f x = f y. 
Proof. intros A B f x y eq. rewrite eq.  reflexivity.  Qed. 

(** Here's another illustration of [inversion].  This is a slightly
    roundabout way of stating a fact that we have already proved
    above.  The extra equalities force us to do a little more
    equational reasoning and exercise some of the tactics we've seen
    recently. *)

Theorem length_snoc' : forall (X : Type) (v : X)
                              (l : list X) (n : nat),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros X v l. induction l as [| v' l'].
  Case "l = []". intros n eq. rewrite <- eq. reflexivity.
  Case "l = v' :: l'". intros n eq. simpl. destruct n as [| n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      apply f_equal. apply IHl'. inversion eq. reflexivity. Qed.


(** **** Exercise: 2 stars, optional (practice) *)
(** A couple more nontrivial but not-too-complicated proofs to work
    together in class, or for you to work as exercises.  They may
    involve applying lemmas from earlier lectures or homeworks. *)
 

Theorem beq_nat_0_l : forall n,
   beq_nat 0 n = true -> n = 0.
Proof.
  intros n H.
  destruct n.
    reflexivity.
    inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
   beq_nat n 0 = true -> n = 0.
Proof.
  intros n H.
  destruct n.
    reflexivity.
    inversion H.
Qed.
(** [] *)


(* ###################################################### *)
(** * Using Tactics on Hypotheses *)

(** By default, most tactics work on the goal formula and leave
    the context unchanged.  However, most tactics also have a variant
    that performs a similar operation on a statement in the context.

    For example, the tactic [simpl in H] performs simplification in
    the hypothesis named [H] in the context. *)

Theorem S_inj : forall (n m : nat) (b : bool),
     beq_nat (S n) (S m) = b  ->
     beq_nat n m = b. 
Proof.
  intros n m b H. simpl in H. apply H.  Qed.

(** Similarly, the tactic [apply L in H] matches some
    conditional statement [L] (of the form [L1 -> L2], say) against a
    hypothesis [H] in the context.  However, unlike ordinary
    [apply] (which rewrites a goal matching [L2] into a subgoal [L1]),
    [apply L in H] matches [H] against [L1] and, if successful,
    replaces it with [L2].
 
    In other words, [apply L in H] gives us a form of "forward
    reasoning" -- from [L1 -> L2] and a hypothesis matching [L1], it
    gives us a hypothesis matching [L2].  By contrast, [apply L] is
    "backward reasoning" -- it says that if we know [L1->L2] and we
    are trying to prove [L2], it suffices to prove [L1].  

    Here is a variant of a proof from above, using forward reasoning
    throughout instead of backward reasoning. *)

Theorem silly3' : forall (n : nat),
  (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
     true = beq_nat n 5  ->
     true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H. apply eq in H. symmetry in H. 
  apply H.  Qed.

(** Forward reasoning starts from what is _given_ (premises,
    previously proven theorems) and iteratively draws conclusions from
    them until the goal is reached.  Backward reasoning starts from
    the _goal_, and iteratively reasons about what would imply the
    goal, until premises or previously proven theorems are reached.
    If you've seen informal proofs before (for example, in a math or
    computer science class), they probably used forward reasoning.  In
    general, Coq tends to favor backward reasoning, but in some
    situations the forward style can be easier to use or to think
    about.  *)

(** **** Exercise: 3 stars (plus_n_n_injective) *)
(** Practice using "in" variants in this exercise. *)
(*
Theorem plus_n_n : forall n,
  n + n = 0 -> n = 0.
Proof.
  intros n H.
  induction n.
    reflexivity.
    simpl in H. rewrite plus_n_Sm in H.
*)

Theorem plus_n_n_injective : forall n m,
     n + n = m + m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
    Case "n = 0". intros m H.
      induction m as [|m'].
        simpl. reflexivity.
        simpl in H. inversion H.
    Case "n = S n'". intros m.
      induction m as [|m'].
        SCase "m = 0". intros H. simpl in H. inversion H.
        SCase "m = S m'".
          intros H.
          rewrite (IHn' m').
          reflexivity.
          simpl in H.
          rewrite <- plus_n_Sm in H.
          rewrite <- plus_n_Sm in H.
          inversion H.
          reflexivity.
Qed.
    (* Hint: use the plus_n_Sm lemma *)
(** [] *)

(* ###################################################### *)
(** * Varying the Induction Hypothesis *)

(** Sometimes it is important to control the exact form of the
    induction hypothesis when carrying out inductive proofs in Coq.
    In particular, we need to be careful about which of the
    assumptions we move (using [intros]) from the goal to the context
    before invoking the [induction] tactic.  For example, suppose 
    we want to show that the [double] function is injective -- i.e., 
    that it always maps different arguments to different results:  
    Theorem double_injective: forall n m, double n = double m -> n = m. 
    The way we _start_ this proof is a little bit delicate: if we 
    begin it with
      intros n. induction n.
]] 
    all is well.  But if we begin it with
      intros n m. induction n.
    we get stuck in the middle of the inductive case... *)

Theorem double_injective_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction n as [| n'].
  Case "n = O". simpl. intros eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". intros eq. destruct m as [| m'].
    SCase "m = O". inversion eq.
    SCase "m = S m'".  apply f_equal. 
      (* Here we are stuck.  The induction hypothesis, [IHn'], does
         not give us [n' = m'] -- there is an extra [S] in the
         way -- so the goal is not provable. *)
      Abort.

(** What went wrong? *)

(** The problem is that, at the point we invoke the induction
    hypothesis, we have already introduced [m] into the context -- 
    intuitively, we have told Coq, "Let's consider some particular
    [n] and [m]..." and we now have to prove that, if [double n =
    double m] for _this particular_ [n] and [m], then [n = m].

    The next tactic, [induction n] says to Coq: We are going to show
    the goal by induction on [n].  That is, we are going to prove that
    the proposition

      - [P n]  =  "if [double n = double m], then [n = m]"

    holds for all [n] by showing

      - [P O]              

         (i.e., "if [double O = double m] then [O = m]")

      - [P n -> P (S n)]  

        (i.e., "if [double n = double m] then [n = m]" implies "if
        [double (S n) = double m] then [S n = m]").

    If we look closely at the second statement, it is saying something
    rather strange: it says that, for a _particular_ [m], if we know

      - "if [double n = double m] then [n = m]"

    then we can prove

       - "if [double (S n) = double m] then [S n = m]".

    To see why this is strange, let's think of a particular [m] --
    say, [5].  The statement is then saying that, if we know

      - [Q] = "if [double n = 10] then [n = 5]"

    then we can prove

      - [R] = "if [double (S n) = 10] then [S n = 5]".

    But knowing [Q] doesn't give us any help with proving [R]!  (If we
    tried to prove [R] from [Q], we would say something like "Suppose
    [double (S n) = 10]..." but then we'd be stuck: knowing that
    [double (S n)] is [10] tells us nothing about whether [double n]
    is [10], so [Q] is useless at this point.) *)

(** To summarize: Trying to carry out this proof by induction on [n]
    when [m] is already in the context doesn't work because we are
    trying to prove a relation involving _every_ [n] but just a
    _single_ [m]. *)

(** The good proof of [double_injective] leaves [m] in the goal
    statement at the point where the [induction] tactic is invoked on
    [n]: *)

Theorem double_injective : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". simpl. intros m eq. destruct m as [| m'].
    SCase "m = O". reflexivity.
    SCase "m = S m'". inversion eq. 
  Case "n = S n'". 
    (* Notice that both the goal and the induction
       hypothesis have changed: the goal asks us to prove
       something more general (i.e., to prove the
       statement for _every_ [m]), but the IH is
       correspondingly more flexible, allowing us to
       choose any [m] we like when we apply the IH.  *)
    intros m eq.
    (* Now we choose a particular [m] and introduce the
       assumption that [double n = double m].  Since we
       are doing a case analysis on [n], we need a case
       analysis on [m] to keep the two "in sync." *)
    destruct m as [| m'].
    SCase "m = O". 
      (* The 0 case is trivial *)
      inversion eq.  
    SCase "m = S m'".  
      apply f_equal. 
      (* At this point, since we are in the second
         branch of the [destruct m], the [m'] mentioned
         in the context at this point is actually the
         predecessor of the one we started out talking
         about.  Since we are also in the [S] branch of
         the induction, this is perfect: if we
         instantiate the generic [m] in the IH with the
         [m'] that we are talking about right now (this
         instantiation is performed automatically by
         [apply]), then [IHn'] gives us exactly what we
         need to finish the proof. *)
      apply IHn'. inversion eq. reflexivity. Qed.

(** What this teaches us is that we need to be careful about using
    induction to try to prove something too specific: If we're proving
    a property of [n] and [m] by induction on [n], we may need to
    leave [m] generic. *)

(** The proof of this theorem has to be treated similarly: *)

(** **** Exercise: 2 stars (beq_nat_true) *)
Theorem beq_nat_true : forall n m,
    beq_nat n m = true -> n = m.
Proof.
  intros n.
  induction n as [|n'].
    Case "n = 0". intros m H.
      destruct m as [|m'].
        reflexivity.
        simpl in H. inversion H.
    Case "n = S n'". 
      intros m H.
      destruct m as [|m'].
        simpl in H. inversion H.
        simpl in H. rewrite (IHn' m'). reflexivity. apply H.
Qed.
        
(** [] *)

(** **** Exercise: 2 stars, advanced (beq_nat_true_informal) *)
(** Give a careful informal proof of [beq_nat_true], being as explicit
    as possible about quantifiers. *)

(* we prove that, for all n and m, if beq_nat n m = true then n = m.
  The proof is by induction on n.
  When n is 0, the only way beq_nat n m = true can be true is if m = 0.
    Therefore, m = 0 and n = m.
  In the inductive case, n is S n' and we know for all m, beq_nat n' m = true
    implies n' = m. We wish to prove that for all m, beq_nat (S n') m = true
    implies that S n' = m.
  When m = 0, beq_nat (S n') m is never going to be true, so the consequent
    doesn't matter.
  When m = S m', we need to prove S n' = S m'. 
    We know (by setting m = m' in the induction hypothesis) that
    beq_nat n' m' = true implies n' = m', and therefore we can substitute n'
    for m in the statement we wish to prove as long as we can also prove
    beq_nat n' m' = true. This substitution makes the thing we want to prove trivial.
  Now we ned to prove beq_nat n' m' = true. But we already have an assumption that
    beq_nat (S n') (S m') = true, which from the definition of beq_nat can be changed
    to an assumption that beq_nat n' m' = true.
  The thing we need to prove is now trivially true according to our assumptions, so
    we're done.

  I am not very good at this.
*)

(** [] *)


(** The strategy of doing fewer [intros] before an [induction] doesn't
    always work directly; sometimes a little _rearrangement_ of
    quantified variables is needed.  Suppose, for example, that we
    wanted to prove [double_injective] by induction on [m] instead of
    [n]. *)

Theorem double_injective_take2_FAILED : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. induction m as [| m'].
  Case "m = O". simpl. intros eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq. 
  Case "m = S m'". intros eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'".  apply f_equal.
        (* Stuck again here, just like before. *)
Abort.

(** The problem is that, to do induction on [m], we must first
    introduce [n].  (If we simply say [induction m] without
    introducing anything first, Coq will automatically introduce
    [n] for us!)   *)

(** What can we do about this?  One possibility is to rewrite the
    statement of the lemma so that [m] is quantified before [n].  This
    will work, but it's not nice: We don't want to have to mangle the
    statements of lemmas to fit the needs of a particular strategy for
    proving them -- we want to state them in the most clear and
    natural way. *)

(**  What we can do instead is to first introduce all the
    quantified variables and then _re-generalize_ one or more of
    them, taking them out of the context and putting them back at
    the beginning of the goal.  The [generalize dependent] tactic
    does this. *)

Theorem double_injective_take2 : forall n m,
     double n = double m ->
     n = m.
Proof.
  intros n m. 
  (* [n] and [m] are both in the context *)
  generalize dependent n.
  (* Now [n] is back in the goal and we can do induction on
     [m] and get a sufficiently general IH. *)
  induction m as [| m'].
  Case "m = O". simpl. intros n eq. destruct n as [| n'].
    SCase "n = O". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "m = S m'". intros n eq. destruct n as [| n'].
    SCase "n = O". inversion eq.
    SCase "n = S n'". apply f_equal.
      apply IHm'. inversion eq. reflexivity. Qed.

(** Let's look at an informal proof of this theorem.  Note that
    the proposition we prove by induction leaves [n] quantified,
    corresponding to the use of generalize dependent in our formal
    proof.

_Theorem_: For any nats [n] and [m], if [double n = double m], then
  [n = m].

_Proof_: Let [m] be a [nat]. We prove by induction on [m] that, for
  any [n], if [double n = double m] then [n = m].

  - First, suppose [m = 0], and suppose [n] is a number such
    that [double n = double m].  We must show that [n = 0].

    Since [m = 0], by the definition of [double] we have [double n =
    0].  There are two cases to consider for [n].  If [n = 0] we are
    done, since this is what we wanted to show.  Otherwise, if [n = S
    n'] for some [n'], we derive a contradiction: by the definition of
    [double] we would have [double n = S (S (double n'))], but this
    contradicts the assumption that [double n = 0].

  - Otherwise, suppose [m = S m'] and that [n] is again a number such
    that [double n = double m].  We must show that [n = S m'], with
    the induction hypothesis that for every number [s], if [double s =
    double m'] then [s = m'].
 
    By the fact that [m = S m'] and the definition of [double], we
    have [double n = S (S (double m'))].  There are two cases to
    consider for [n].

    If [n = 0], then by definition [double n = 0], a contradiction.
    Thus, we may assume that [n = S n'] for some [n'], and again by
    the definition of [double] we have [S (S (double n')) = S (S
    (double m'))], which implies by inversion that [double n' = double
    m'].

    Instantiating the induction hypothesis with [n'] thus allows us to
    conclude that [n' = m'], and it follows immediately that [S n' = S
    m'].  Since [S n' = n] and [S m' = m], this is just what we wanted
    to show. [] *)

(** **** Exercise: 3 stars (gen_dep_practice) *)

(** Prove this by induction on [l]. *)

Theorem index_after_last: forall (n : nat) (X : Type) (l : list X),
     length l = n ->
     index n l = None.
Proof.
  intros n X l H.
  generalize dependent n.
  induction l as [|h t].
    Case "l = []". intros n H. simpl in H. rewrite <- H. reflexivity.
    Case "l = h :: t".
      intros n H.
      destruct n.
        SCase "n = 0". simpl H. inversion H.
        SCase "n = S n'".
          simpl.
          rewrite IHt.  reflexivity. 
          simpl in H.  inversion H.  reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (index_after_last_informal) *)
(** Write an informal proof corresponding to your Coq proof
    of [index_after_last]:
 
     _Theorem_: For all sets [X], lists [l : list X], and numbers
      [n], if [length l = n] then [index n l = None].
 
     _Proof_:
     The proof proceeds by induction on [l].

     When [l] is the empty list, simplifying the assumption [length l = n] 
     gets us [length [] = n] and therefore [n = 0]. Simplifying
     [ index 0 [] ] gets us [ None ] and we've established [ index n l = None]
     when l is the empty list and [n = length l].

     In the inductive case, [l = h :: t] and for all n, if [length t = n]
     then [index n t = None].
     We need to prove that if [length h :: t = n] then [index n (h :: t) = None].

     When [n = 0], this is easy. [length h :: t] will never equal [n], so the antecedent
     never happens.

     When [n = S n'], we want to prove that if [length h :: t = S n'] then
     [ index (S n') (h :: t) = None ]. We can simplify the assumption
     to [S (length t) = S n'], which means we can assume [n' = length t].
     Simplifying the goal, we get [index n' t = None]. Picking n' in the inductive
     hypothesis, we get that if [length t = n'] then [index n' t = None], which is
     to say that we can now assume the thing that we're trying to prove and are done.

     Maybe I'm improving?
[]
*)

(** **** Exercise: 3 stars, optional (gen_dep_practice_more) *)
(** Prove this by induction on [l]. *)

Theorem length_snoc''' : forall (n : nat) (X : Type) 
                              (v : X) (l : list X),
     length l = n ->
     length (snoc l v) = S n. 
Proof.
  intros n X v l H.
  destruct l as [|h t].
    Case "l = []". simpl. inversion H. reflexivity.
    Case "l = h :: t".
      destruct n as [|n'].
        SCase "n = 0". simpl in H. inversion H.
        SCase "n = S n'".
          simpl. apply f_equal. simpl in H.
          rewrite (length_snoc' X v t n').
          reflexivity.
          inversion H. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (app_length_cons) *)
(** Prove this by induction on [l1], without using [app_length]. *)

Theorem length_app_singleton: forall X (l : list X) (x : X), 
  length (l ++ [x]) = S (length l).
Proof.
  intros X l x.
  induction l.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_nil : forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l.
    simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem app_length_cons : forall (X : Type) (l1 l2 : list X) 
                                  (x : X) (n : nat),
     length (l1 ++ (x :: l2)) = n ->
     S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x.
  induction l1 as [|h1 t1].
    Case "l1 = []". intros n H. simpl.  simpl in H. rewrite H. reflexivity.
    Case "l1 = h1 :: t1".
      intros n H.
      destruct n as [|n'].
        SCase "n = 0". simpl in H. inversion H.
        SCase "n = S n'".
          simpl. rewrite (IHt1 n').
          reflexivity.
          simpl in H. inversion H. reflexivity.
Qed.
 
(** [] *)

(** **** Exercise: 4 stars, optional (app_length_twice) *)
(** Prove this by induction on [l], without using app_length. *)

Theorem app_length_twice : forall (X:Type) (n:nat) (l:list X),
     length l = n ->
     length (l ++ l) = n + n.
Proof.
  intros X n l.
  generalize dependent n.
  induction l as [|h t].
    Case "l = []". intros n H.
      simpl. simpl in H. rewrite <- H. reflexivity.
    Case "l = h :: t".
      intros n H.
      destruct n as [|n'].
        SCase "n = 0". inversion H.
        SCase "n = S n'".
          simpl. rewrite plus_Sn_r.
          rewrite <- (IHt n').
          apply f_equal.
          symmetry.
          apply (app_length_cons X t t h). (* is this cheating? the question says
                                              not to use app_length, but this is
                                              app_length_cons... *)
          reflexivity.
          inversion H.
          reflexivity.
Qed.



(** [] *)

(* ###################################################### *)
(** * Using [destruct] on Compound Expressions *)

(** We have seen many examples where the [destruct] tactic is
    used to perform case analysis of the value of some variable.  But
    sometimes we need to reason by cases on the result of some
    _expression_.  We can also do this with [destruct].

    Here are some examples: *)

Definition sillyfun (n : nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
  else false.

Theorem sillyfun_false : forall (n : nat),
  sillyfun n = false.
Proof.
  intros n. unfold sillyfun. 
  destruct (beq_nat n 3).
    Case "beq_nat n 3 = true". reflexivity.
    Case "beq_nat n 3 = false". destruct (beq_nat n 5).
      SCase "beq_nat n 5 = true". reflexivity.
      SCase "beq_nat n 5 = false". reflexivity.  Qed.

(** After unfolding [sillyfun] in the above proof, we find that
    we are stuck on [if (beq_nat n 3) then ... else ...].  Well,
    either [n] is equal to [3] or it isn't, so we use [destruct
    (beq_nat n 3)] to let us reason about the two cases. 

    In general, the [destruct] tactic can be used to perform case
    analysis of the results of arbitrary computations.  If [e] is an
    expression whose type is some inductively defined type [T], then,
    for each constructor [c] of [T], [destruct e] generates a subgoal
    in which all occurrences of [e] (in the goal and in the context)
    are replaced by [c].

*)

(** **** Exercise: 1 star (override_shadow) *)
Theorem override_shadow : forall (X:Type) x1 x2 k1 k2 (f : nat->X),
  (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
    reflexivity.
    reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (combine_split) *)
(** Complete the proof below *)

Theorem combine_split : forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) ->
  combine l1 l2 = l.
Proof.
  intros X Y l l1 l2.
  generalize dependent l.
  generalize dependent l2.
  induction l1 as [|h1 t1].
    Case "l1 = []". induction l2 as [|h2 t2].
      SCase "l2 = []".
        intros l H.
        destruct l. simpl. reflexivity.
        destruct p. simpl in H. destruct (split l). inversion H.
      SCase "l2 = h2 :: t2".
        intros l H. destruct l. inversion H.
        simpl in H. destruct p. destruct (split l). inversion H.
    Case "l1 = h1 :: t1". induction l2 as [|h2 t2].
      SCase "l2 = []".
        intros l H. destruct l.  simpl in H. inversion H.
        destruct p. simpl in H. destruct (split l). inversion H.
      SCase "l2 = h2 :: t2".
        intros l H.
        simpl. destruct l  as [|h t].
          SSCase "l = []". inversion H.
          SSCase "l = h :: t".
            rewrite (IHt1 t2 t).
            simpl in H. destruct h. destruct (split t). inversion H.  reflexivity.
            simpl in H. destruct h. destruct (split t). inversion H. reflexivity.
Qed.
(* I am left with the strangest feeling that there may perhaps be a better way. *)
 
(** [] *)

(** Sometimes, doing a [destruct] on a compound expression (a
    non-variable) will erase information we need to complete a proof. *)
(** For example, suppose
    we define a function [sillyfun1] like this: *)

Definition sillyfun1 (n : nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
  else false.

(** And suppose that we want to convince Coq of the rather
    obvious observation that [sillyfun1 n] yields [true] only when [n]
    is odd.  By analogy with the proofs we did with [sillyfun] above,
    it is natural to start the proof like this: *)

Theorem sillyfun1_odd_FAILED : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3).
  (* stuck... *)
Abort.

(** We get stuck at this point because the context does not
    contain enough information to prove the goal!  The problem is that
    the substitution peformed by [destruct] is too brutal -- it threw
    away every occurrence of [beq_nat n 3], but we need to keep some
    memory of this expression and how it was destructed, because we
    need to be able to reason that since, in this branch of the case
    analysis, [beq_nat n 3 = true], it must be that [n = 3], from
    which it follows that [n] is odd.

    What we would really like is to substitute away all existing
    occurences of [beq_nat n 3], but at the same time add an equation
    to the context that records which case we are in.  The [eqn:]
    qualifier allows us to introduce such an equation (with whatever
    name we choose). *)

Theorem sillyfun1_odd : forall (n : nat),
     sillyfun1 n = true ->
     oddb n = true.
Proof.
  intros n eq. unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  (* Now we have the same state as at the point where we got stuck
    above, except that the context contains an extra equality
    assumption, which is exactly what we need to make progress. *)
    Case "e3 = true". apply beq_nat_true in Heqe3.
      rewrite -> Heqe3. reflexivity.
    Case "e3 = false".
     (* When we come to the second equality test in the body of the
       function we are reasoning about, we can use [eqn:] again in the
       same way, allow us to finish the proof. *)
      destruct (beq_nat n 5) eqn:Heqe5. 
        SCase "e5 = true".
          apply beq_nat_true in Heqe5.
          rewrite -> Heqe5. reflexivity.
        SCase "e5 = false". inversion eq.  Qed.


(** **** Exercise: 2 stars (destruct_eqn_practice) *)
Theorem bool_fn_applied_thrice : 
  forall (f : bool -> bool) (b : bool), 
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct b eqn:Hb.
    Case "b = true". destruct (f true) eqn:Hft.
      SCase "f true = true". rewrite Hft. rewrite Hft. reflexivity.
      SCase "f true = false". destruct (f false) eqn:Hff.
        SSCase "f false = true". rewrite Hft. reflexivity.
        SSCase "f false = false". rewrite Hff. reflexivity.
    Case "b = false". destruct (f false) eqn:Hff.
      SCase "f false = true". destruct (f true) eqn:Hft.
        SSCase "f true = true". rewrite Hft. reflexivity.
        SSCase "f true = false". rewrite Hff. reflexivity.
      SCase "f false = false".
        rewrite Hff. rewrite Hff. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars (override_same) *)
Theorem override_same : forall (X:Type) x1 k1 k2 (f : nat->X),
  f k1 = x1 -> 
  (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f H.
  unfold override.
  destruct (beq_nat k1 k2) eqn:Heqk1k2.
  Case "beq_nat k1 k2 = true". 
    rewrite <- H.
    apply beq_nat_true in Heqk1k2. 
    rewrite Heqk1k2.
    reflexivity.
  Case "beq_nat k1 k2 = false".
    reflexivity.
Qed.
    
(** [] *)

(* ################################################################## *)
(** * Review *)

(** We've now seen a bunch of Coq's fundamental tactics.  We'll
    introduce a few more as we go along through the coming lectures,
    and later in the course we'll introduce some more powerful
    _automation_ tactics that make Coq do more of the low-level work
    in many cases.  But basically we've got what we need to get work
    done.

    Here are the ones we've seen:

      - [intros]: 
        move hypotheses/variables from goal to context 

      - [reflexivity]:
        finish the proof (when the goal looks like [e = e])

      - [apply]:
        prove goal using a hypothesis, lemma, or constructor

      - [apply... in H]: 
        apply a hypothesis, lemma, or constructor to a hypothesis in
        the context (forward reasoning)

      - [apply... with...]:
        explicitly specify values for variables that cannot be
        determined by pattern matching

      - [simpl]:
        simplify computations in the goal 

      - [simpl in H]:
        ... or a hypothesis 

      - [rewrite]:
        use an equality hypothesis (or lemma) to rewrite the goal 

      - [rewrite ... in H]:
        ... or a hypothesis 

      - [symmetry]:
        changes a goal of the form [t=u] into [u=t]

      - [symmetry in H]:
        changes a hypothesis of the form [t=u] into [u=t]

      - [unfold]:
        replace a defined constant by its right-hand side in the goal 

      - [unfold... in H]:
        ... or a hypothesis  

      - [destruct... as...]:
        case analysis on values of inductively defined types 

      - [destruct... eqn:...]:
        specify the name of an equation to be added to the context,
        recording the result of the case analysis

      - [induction... as...]:
        induction on values of inductively defined types 

      - [inversion]:
        reason by injectivity and distinctness of constructors

      - [assert (e) as H]:
        introduce a "local lemma" [e] and call it [H] 

      - [generalize dependent x]:
        move the variable [x] (and anything else that depends on it)
        from the context back to an explicit hypothesis in the goal
        formula 
*)

(* ###################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 3 stars (beq_nat_sym) *)
Theorem beq_nat_sym : forall (n m : nat),
  beq_nat n m = beq_nat m n.
Proof.
  intros n.
  induction n as [|n'].
    Case "n = 0". intros m. destruct m as [|m'].
      simpl. reflexivity.
      simpl. reflexivity.
    Case "n = S n'". intros m. destruct m as [|m'].
      simpl. reflexivity.
      SCase "m = S m'".
        simpl. rewrite IHn'. reflexivity.
Qed.
 
(** [] *)

(** **** Exercise: 3 stars, advanced, optional (beq_nat_sym_informal) *)
(** Give an informal proof of this lemma that corresponds to your
    formal proof above:

   Theorem: For any [nat]s [n] [m], [beq_nat n m = beq_nat m n].

   Proof:
   
   The proof proceeds by induction on n.

   For the n = 0 case, it is trivial: either m = 0, in which case 
     [beq_nat n m] and [beq_nat m n] are both true, or m = S m, in
     which case they are both false.

   For the inductive case, where [n = S n'], we have an induction hypthosesis
     of [beq_nat n' m = beq_nat m n'] for all m, and wish to prove
     [beq_nat (S n') m = beq_nat m (S n')].

   In the case where m = 0, this is trivial. [beq_nat (S _) 0] and [beq_nat 0 (S _)]
     are both false.
   When [m = S m'], we need to prove [beq_nat (S n') (S m') = beq_nat (S m') (S n')],
     which simplifies to [beq_nat n' m' = beq_nat m' n'], which follows directly from
     the induction hypothesis.
[]
 *)

(** **** Exercise: 3 stars, optional (beq_nat_trans) *)
Theorem beq_nat_trans : forall n m p,
  beq_nat n m = true ->
  beq_nat m p = true ->
  beq_nat n p = true.
Proof.
  intros n.
  induction n as [|n'].
    Case "n = 0". intros m.
      destruct m as [|m'].
        SCase "m = 0". intros p Hnm Hmp. rewrite Hmp. reflexivity.
        SCase "m = S m'". intros p Hnm Hmp. inversion Hnm.
    Case "n = S n'". intros m.
      destruct m as [|m'].
        SCase "m = 0". intros p Hnm Hmp. inversion Hnm.
        SCase "m = S m'". intros p Hnm Hmp.
          destruct p as [|p'].
            SSCase "p = 0".  inversion Hmp.
            SSCase "p = S p'".
              simpl. rewrite (IHn' m' p').
              reflexivity.
              simpl in Hnm. rewrite Hnm. reflexivity.
              simpl in Hmp. rewrite Hmp. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (split_combine) *)
(** We have just proven that for all lists of pairs, [combine] is the
    inverse of [split].  How would you formalize the statement that
    [split] is the inverse of [combine]?

    Complete the definition of [split_combine_statement] below with a
    property that states that [split] is the inverse of
    [combine]. Then, prove that the property holds. (Be sure to leave
    your induction hypothesis general by not doing [intros] on more
    things than necessary.  Hint: what property do you need of [l1]
    and [l2] for [split] [combine l1 l2 = (l1,l2)] to be true?)  *)

Definition split_combine_statement : Prop :=
  forall X Y (l : list (X * Y)) l1 l2,
  length l1 = length l2 ->
  combine l1 l2 = l ->
  split l = (l1, l2).

Theorem split_combine : split_combine_statement.
Proof.
  intros X Y l l1 l2 Hlen Hcomb.
  generalize dependent l. generalize dependent l2.
  induction l1 as [|h1 t1].
    Case "l1 = []".
      destruct l2 as [|h2 t2].
        SCase "l2 = []".
          intros Hlen l Hcomb.
          simpl in Hcomb. rewrite <- Hcomb.
          simpl. reflexivity.
        SCase "l2 = h2 :: t2".
          intros Hlen l Hcomb.
          simpl in Hlen. inversion Hlen.
    Case "l1 = h1 :: t1".
      intros l2 Hlen.
      destruct l2 as [|h2 t2].
        SCase "l2 = []".
          intros l Hcomb.
          simpl in Hlen. inversion Hlen.
        SCase "l2 = h2 :: t2".
          intros l Hcomb.
          simpl in Hcomb.
          rewrite <- Hcomb.
          simpl. destruct (split (combine t1 t2)) eqn:Hsc.
          simpl in Hlen. inversion Hlen.
          rewrite (IHt1 t2 H0 (combine t1 t2)) in Hsc.
          inversion Hsc.
          reflexivity. reflexivity.
Qed.

(** [] *)

(** **** Exercise: 3 stars (override_permute) *)
Theorem override_permute : forall (X:Type) x1 x2 k1 k2 k3 (f : nat->X),
  beq_nat k2 k1 = false ->
  (override (override f k2 x2) k1 x1) k3 = (override (override f k1 x1) k2 x2) k3.
Proof.
  intros X x1 x2 k1 k2 k3 f H.
  unfold override.
  destruct (beq_nat k1 k3) eqn:Hk13.
    Case "beq_nat k1 k3 = true".
      destruct (beq_nat k2 k3) eqn: Hk23.
        SCase "beq_nat k2 k3 = true".
          apply beq_nat_true in Hk13. rewrite Hk13 in H.
          apply beq_nat_true in Hk23. rewrite Hk23 in H.
          rewrite <- beq_nat_refl in H. inversion H.
        SCase "beq_nat k2 k3 = false".
          reflexivity.
    Case "beq_nat k1 k3 = false".
      destruct (beq_nat k2 k3) eqn: Hk23.
        SCase "beq_nat k2 k3 = true".
          reflexivity.
        SCase "beq_nat k2 k3 = false".
          reflexivity.
Qed.

(** [] *)

(** **** Exercise: 3 stars, advanced (filter_exercise) *)
(** This one is a bit challenging.  Pay attention to the form of your IH. *)

Theorem filter_exercise : forall (X : Type) (test : X -> bool)
                             (x : X) (l lf : list X),
     filter test l = x :: lf ->
     test x = true.
Proof.
  intros X test x l lf H.
  generalize dependent lf. 
  induction l as [|h t].
    Case "l = []". intros lf H. inversion H.
    Case "l = h :: t". intros lf H.
      simpl in H. destruct (test h) eqn:Hth.
        SCase "test h = true".
          inversion H. rewrite H1 in Hth. rewrite Hth. reflexivity.
        SCase "test h = false".
          apply IHt with lf. rewrite H. reflexivity.
Qed.

(* a bit challenging? You don't say? My head feels well-acquainted with 
 * a lemon whose best friend is Mr Brick. *)

(** [] *)

(** **** Exercise: 4 stars, advanced (forall_exists_challenge) *)
(** Define two recursive [Fixpoints], [forallb] and [existsb].  The
    first checks whether every element in a list satisfies a given
    predicate:
      forallb oddb [1;3;5;7;9] = true

      forallb negb [false;false] = true
  
      forallb evenb [0;2;4;5] = false
  
      forallb (beq_nat 5) [] = true
    The second checks whether there exists an element in the list that
    satisfies a given predicate:
      existsb (beq_nat 5) [0;2;3;6] = false
 
      existsb (andb true) [true;true;false] = true
 
      existsb oddb [1;0;0;0;0;3] = true
 
      existsb evenb [] = false
    Next, define a _nonrecursive_ version of [existsb] -- call it
    [existsb'] -- using [forallb] and [negb].
 
    Prove that [existsb'] and [existsb] have the same behavior.
*)

Fixpoint forallb {X: Type} (f:X -> bool) (xs:list X) : bool :=
  match xs with
  | [] => true
  | h :: t => andb (f h) (forallb f t)
  end.

Fixpoint existsb {X: Type} (f:X -> bool) (xs:list X) : bool :=
  match xs with
  | [] => false
  | h :: t => orb (f h) (existsb f t)
  end.

Definition existsb' {X: Type} (f:X -> bool) (xs: list X) : bool :=
  negb (forallb (fun x => negb (f x)) xs).

Theorem existsbs : forall (X : Type) (f: X -> bool) (l : list X),
  existsb f l = existsb' f l.
Proof.
  intros X f l.
  induction l as [|h t].
    Case "l = []".
      reflexivity.
    Case "l = h :: t".
      simpl. rewrite IHt.
      destruct (f h) eqn:Ifh.
        simpl. unfold existsb'. simpl. rewrite Ifh. simpl. reflexivity.
        simpl. unfold existsb'. simpl. rewrite Ifh. simpl. reflexivity.
Qed.

(** [] *)

(* $Date: 2013-07-17 16:19:11 -0400 (Wed, 17 Jul 2013) $ *)




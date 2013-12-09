(** * Prop: Propositions and Evidence *)

Require Export MoreCoq.

(** In previous chapters, we have seen many examples of factual
    claims (_propositions_) and ways of presenting evidence of their
    truth (_proofs_).  In particular, we have worked extensively with
    _equality propositions_ of the form [e1 = e2], with
    implications ([P -> Q]), and with quantified propositions 
    ([forall x, P]).  

    This chapter will take us on a first tour of the
    propositional (logical) side of Coq.
    In particular, we will expand our repertoire of primitive
    propositions to include _user-defined_ propositions, not just
    equality propositions (which are more-or-less "built in" to Coq). 
*)


(* ##################################################### *)
(** * Inductively Defined Propositions *)

(**  As a running example, let's
    define a simple property of natural numbers -- we'll call it
    "[beautiful]." *)

(** Informally, a number is [beautiful] if it is [0], [3], [5], or the
    sum of two [beautiful] numbers.  

    More pedantically, we can define [beautiful] numbers by giving four
    rules:

       - Rule [b_0]: The number [0] is [beautiful].
       - Rule [b_3]: The number [3] is [beautiful]. 
       - Rule [b_5]: The number [5] is [beautiful]. 
       - Rule [b_sum]: If [n] and [m] are both [beautiful], then so is
         their sum. *)

(** We will see many definitions like this one during the rest
    of the course, and for purposes of informal discussions, it is
    helpful to have a lightweight notation that makes them easy to
    read and write.  _Inference rules_ are one such notation: *)
(**
                              -----------                               (b_0)
                              beautiful 0
                              
                              ------------                              (b_3)
                              beautiful 3

                              ------------                              (b_5)
                              beautiful 5    

                       beautiful n     beautiful m
                       ---------------------------                      (b_sum)
                              beautiful (n+m)   
*)

(** Each of the textual rules above is reformatted here as an
    inference rule; the intended reading is that, if the _premises_
    above the line all hold, then the _conclusion_ below the line
    follows.  For example, the rule [b_sum] says that, if [n] and [m]
    are both [beautiful] numbers, then it follows that [n+m] is
    [beautiful] too.  If a rule has no premises above the line, then
    its conclusion hold unconditionally.

    These rules _define_ the property [beautiful].  That is, if we
    want to convince someone that some particular number is [beautiful],
    our argument must be based on these rules.  For a simple example,
    suppose we claim that the number [5] is [beautiful].  To support
    this claim, we just need to point out that rule [b_5] says so.
    Or, if we want to claim that [8] is [beautiful], we can support our
    claim by first observing that [3] and [5] are both [beautiful] (by
    rules [b_3] and [b_5]) and then pointing out that their sum, [8],
    is therefore [beautiful] by rule [b_sum].  This argument can be
    expressed graphically with the following _proof tree_: *)
(**
         ----------- (b_3)   ----------- (b_5)
         beautiful 3         beautiful 5
         ------------------------------- (b_sum)
                   beautiful 8   
    Of course, there are other ways of using these rules to argue that
    [8] is [beautiful], for instance:
         ----------- (b_5)   ----------- (b_3)
         beautiful 5         beautiful 3
         ------------------------------- (b_sum)
                   beautiful 8   
*)

(** **** Exercise: 1 star (varieties_of_beauty) *)
(** How many different ways are there to show that [8] is [beautiful]? *)

(* Infinitely many. It's beautiful because 5 and 3 are beautiful. 3 is beautiful
   just because it is, but also because 3 and 0 are beautiful, and because 3 and 0
   and 0 are beautiful, and so on and so forth. *)
(** [] *)

(** In Coq, we can express the definition of [beautiful] as
    follows: *)

Inductive beautiful : nat -> Prop :=
  b_0   : beautiful 0
| b_3   : beautiful 3
| b_5   : beautiful 5
| b_sum : forall n m, beautiful n -> beautiful m -> beautiful (n+m).


(** The first line declares that [beautiful] is a proposition -- or,
    more formally, a family of propositions "indexed by" natural
    numbers.  (That is, for each number [n], the claim that "[n] is
    [beautiful]" is a proposition.)  Such a family of propositions is
    often called a _property_ of numbers.  Each of the remaining lines
    embodies one of the rules for [beautiful] numbers.

    The rules introduced this way have the same status as proven 
    theorems; that is, they are true axiomatically. 
    So we can use Coq's [apply] tactic with the rule names to prove 
    that particular numbers are [beautiful].  *)

Theorem three_is_beautiful: beautiful 3.
Proof.
   (* This simply follows from the rule [b_3]. *)
   apply b_3.
Qed.

Theorem eight_is_beautiful: beautiful 8.
Proof.
   (* First we use the rule [b_sum], telling Coq how to
      instantiate [n] and [m]. *)
   apply b_sum with (n:=3) (m:=5).
   (* To solve the subgoals generated by [b_sum], we must provide
      evidence of [beautiful 3] and [beautiful 5]. Fortunately we
      have rules for both. *)
   apply b_3.
   apply b_5.
Qed.

(** As you would expect, we can also prove theorems that have
hypotheses about [beautiful]. *)

Theorem beautiful_plus_eight: forall n, beautiful n -> beautiful (8+n).
Proof.
  intros n B.
  apply b_sum with (n:=8) (m:=n).
  apply eight_is_beautiful.
  apply B.
Qed.
  

(** **** Exercise: 2 stars (b_timesm) *)
Theorem b_timesm: forall n m, beautiful n -> beautiful (m*n).
Proof.
  intros n m H.
  induction m.
    simpl. apply b_0.
    simpl. apply b_sum. apply H. apply IHm.
Qed.
(** [] *)


(* ####################################################### *)
(** ** Induction Over Evidence *)

(** Besides _constructing_ evidence that numbers are beautiful, we can
    also _reason about_ such evidence. *)

(** The fact that we introduced [beautiful] with an [Inductive]
    declaration tells Coq not only that the constructors [b_0], [b_3],
    [b_5] and [b_sum] are ways to build evidence, but also that these
    two constructors are the _only_ ways to build evidence that
    numbers are beautiful. *)

(** In other words, if someone gives us evidence [E] for the assertion
    [beautiful n], then we know that [E] must have one of four shapes:

      - [E] is [b_0] (and [n] is [O]),
      - [E] is [b_3] (and [n] is [3]), 
      - [E] is [b_5] (and [n] is [5]), or 
      - [E] is [b_sum n1 n2 E1 E2] (and [n] is [n1+n2], where [E1] is
        evidence that [n1] is beautiful and [E2] is evidence that [n2]
        is beautiful). *)
    
(** This permits us to _analyze_ any hypothesis of the form [beautiful
    n] to see how it was constructed, using the tactics we already
    know.  In particular, we can use the [induction] tactic that we
    have already seen for reasoning about inductively defined _data_
    to reason about inductively defined _evidence_.

    To illustrate this, let's define another property of numbers: *)

Inductive gorgeous : nat -> Prop :=
  g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3+n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5+n).

(** **** Exercise: 1 star (gorgeous_tree) *)
(** Write out the definition of [gorgeous] numbers using inference rule
    notation.

                           gorgeous n               gorgeous n
---------------       --------------------      --------------------
  gorgeous 0            gorgeous (3 + n)          gorgeous (5 + n)



[]
*)


(** **** Exercise: 1 star (gorgeous_plus13) *)
Theorem gorgeous_plus13: forall n, 
  gorgeous n -> gorgeous (13+n).
Proof.
  intros n H.
  apply g_plus3.
  apply g_plus5.
  apply g_plus5.
  apply H.
Qed.
(** [] *)

(** It seems intuitively obvious that, although [gorgeous] and
    [beautiful] are presented using slightly different rules, they are
    actually the same property in the sense that they are true of the
    same numbers.  Indeed, we can prove this. *)

Theorem gorgeous__beautiful : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros n H.
   induction H as [|n'|n'].
   Case "g_0".
       apply b_0.
   Case "g_plus3". 
       apply b_sum. apply b_3.
       apply IHgorgeous.
   Case "g_plus5".
       apply b_sum. apply b_5. apply IHgorgeous. 
Qed.

(** Notice that the argument proceeds by induction on the _evidence_ [H]! *) 

(** Let's see what happens if we try to prove this by induction on [n]
   instead of induction on the evidence [H]. *)

Theorem gorgeous__beautiful_FAILED : forall n, 
  gorgeous n -> beautiful n.
Proof.
   intros. induction n as [| n'].
   Case "n = 0". apply b_0.
   Case "n = S n'". (* We are stuck! *)
Abort.

(** The problem here is that doing induction on [n] doesn't yield a
    useful induction hypothesis. Knowing how the property we are
    interested in behaves on the predecessor of [n] doesn't help us
    prove that it holds for [n]. Instead, we would like to be able to
    have induction hypotheses that mention other numbers, such as [n -
    3] and [n - 5]. This is given precisely by the shape of the
    constructors for [gorgeous]. *)




(** **** Exercise: 2 stars (gorgeous_sum) *)
Theorem gorgeous_sum : forall n m,
  gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [|n'|n'].
    Case "g_0". simpl. apply Hm.
    Case "g_plus3". rewrite <- plus_assoc. apply g_plus3. apply IHHn.
    Case "g_plus5'". rewrite <- plus_assoc. apply g_plus5. apply IHHn.
Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (beautiful__gorgeous) *)
Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n H.
  induction H.
    Case "b_0". apply g_0.
    Case "b_3". apply g_plus3. apply g_0.
    Case "b_5". apply g_plus5. apply g_0.
    Case "b_plus". apply gorgeous_sum. apply IHbeautiful1. apply IHbeautiful2.
Qed.
      

(** [] *)

(** **** Exercise: 3 stars, optional (g_times2) *)
(** Prove the [g_times2] theorem below without using [gorgeous__beautiful].
    You might find the following helper lemma useful. *)

Lemma helper_g_times2 : forall x y z, x + (z + y)= z + x + y.
Proof.
  intros x y z.
  rewrite plus_assoc. replace (x + z) with (z + x).
  reflexivity. rewrite plus_comm. reflexivity.
Qed.
 
Theorem g_times2: forall n, gorgeous n -> gorgeous (2*n).
Proof.
   intros n H. simpl. 
   induction H.
     Case "g_0". simpl. apply g_0.
     Case "g_plus3".
       rewrite plus_0_r.
       rewrite <- plus_assoc.
       apply g_plus3.
       rewrite helper_g_times2.
       rewrite <- plus_assoc.
       apply g_plus3.
       rewrite plus_0_r in IHgorgeous.
       apply IHgorgeous.
     Case "g_plus5".
       rewrite plus_0_r.
       rewrite <- plus_assoc.
       apply g_plus5.
       rewrite helper_g_times2.
       rewrite <- plus_assoc.
       apply g_plus5.
       rewrite plus_0_r in IHgorgeous.
       apply IHgorgeous.
Qed.
(** [] *)


(* ####################################################### *)
(** ** From Boolean Functions to Propositions *)

(** In chapter [Basics] we defined a _function_ [evenb] that tests a
    number for evenness, yielding [true] if so.  We can use this
    function to define the _proposition_ that some number [n] is
    even: *)

Definition even (n:nat) : Prop := 
  evenb n = true.

(** That is, we can define "[n] is even" to mean "the function [evenb]
    returns [true] when applied to [n]."  

    Note that here we have given a name
    to a proposition using a [Definition], just as we have
    given names to expressions of other sorts. This isn't a fundamentally
    new kind of proposition;  it is still just an equality. *)

(** Another alternative is to define the concept of evenness
    directly.  Instead of going via the [evenb] function ("a number is
    even if a certain computation yields [true]"), we can say what the
    concept of evenness means by giving two different ways of
    presenting _evidence_ that a number is even. *)

Inductive ev : nat -> Prop :=
  | ev_0 : ev O
  | ev_SS : forall n:nat, ev n -> ev (S (S n)).

(** This definition says that there are two ways to give
    evidence that a number [m] is even.  First, [0] is even, and
    [ev_0] is evidence for this.  Second, if [m = S (S n)] for some
    [n] and we can give evidence [e] that [n] is even, then [m] is
    also even, and [ev_SS n e] is the evidence. *)

(** **** Exercise: 1 star (double_even) *)

Theorem double_even : forall n,
  ev (double n).
Proof.
  intros n.
  induction n.
    simpl. apply ev_0.
    simpl. apply ev_SS. apply IHn.
Qed.
(** [] *)


(** *** Discussion: Computational vs. Inductive Definitions *)

(** We have seen that the proposition "[n] is even" can be
    phrased in two different ways -- indirectly, via a boolean testing
    function [evenb], or directly, by inductively describing what
    constitutes evidence for evenness.  These two ways of defining
    evenness are about equally easy to state and work with.  Which we
    choose is basically a question of taste.

    However, for many other properties of interest, the direct
    inductive definition is preferable, since writing a testing
    function may be awkward or even impossible.  

    One such property is [beautiful].  This is a perfectly sensible
    definition of a set of numbers, but we cannot translate its
    definition directly into a Coq Fixpoint (or into a recursive
    function in any other common programming language).  We might be
    able to find a clever way of testing this property using a
    [Fixpoint] (indeed, it is not too hard to find one in this case),
    but in general this could require arbitrarily deep thinking.  In
    fact, if the property we are interested in is uncomputable, then
    we cannot define it as a [Fixpoint] no matter how hard we try,
    because Coq requires that all [Fixpoint]s correspond to
    terminating computations.

    On the other hand, writing an inductive definition of what it
    means to give evidence for the property [beautiful] is
    straightforward. *)




(** **** Exercise: 1 star (ev__even) *)
(** Here is a proof that the inductive definition of evenness implies
    the computational one. *)

Theorem ev__even : forall n,
  ev n -> even n.
Proof.
  intros n E. induction E as [| n' E'].
  Case "E = ev_0". 
    unfold even. reflexivity.
  Case "E = ev_SS n' E'".  
    unfold even. apply IHE'.  
Qed.

(** Could this proof also be carried out by induction on [n] instead
    of [E]?  If not, why not? *)

(* yes? *)

Theorem ev__even' : forall n,
  ev n -> even n.
Proof.
  intros n E. induction n as [|n'].
  Case "n = 0". unfold even. reflexivity.
  Case "n = S n'". unfold even. unfold even in IHn'.
    destruct n' as [|n''] eqn:Heqn.
      inversion E.
      simpl.
Abort.

(* um, nope. The inductive hypothesis and the assumptions in the
   environment all talk about ev or even, but if you proceed
   by induction on [n] then you end up needing to talk about evenb.

   If that wasn't enough, induction on n moves in steps of one. But to
   talk usefully in terms of ev or even, you need it to move in steps of 2
   (from [S (S n)] to [n]).

   Not entirely convinced why these are critical issues rather than issues to
   be overcome.
 *)
(** [] *)

(** The induction principle for inductively defined propositions does
    not follow quite the same form as that of inductively defined
    sets.  For now, you can take the intuitive view that induction on
    evidence [ev n] is similar to induction on [n], but restricts our
    attention to only those numbers for which evidence [ev n] could be
    generated.  We'll look at the induction principle of [ev] in more
    depth below, to explain what's really going on. *)

(** **** Exercise: 1 star (l_fails) *)
(** The following proof attempt will not succeed.
     Theorem l : forall n,
       ev n.
     Proof.
       intros n. induction n.
         Case "O". simpl. apply ev_0.
         Case "S".
           ...
   Intuitively, we expect the proof to fail because not every
   number is even. However, what exactly causes the proof to fail?

(* There's no way to relate [S n] (as opposed to [S (S n)]) to any constructor of [ev] *)
*)
(** [] *)

(** **** Exercise: 2 stars (ev_sum) *)
(** Here's another exercise requiring induction. *)

Theorem ev_sum : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros n m evn evm.
  induction (evn).
    Case "evn = ev_0".
      induction evm.
        SCase "evm = ev_0".
          simpl. apply ev_0.
        SCase "evm = ev_SS".
          simpl. apply ev_SS. apply evm.
    Case "evn = ev_SS".
      induction evm.
        SCase "evm = ev_0".
          simpl. rewrite plus_0_r. apply ev_SS. apply evn.
        SCase "evm = ev_SS".
          simpl. apply ev_SS. apply IHevn.
Qed.
Theorem ev_sum' : forall n m,
   ev n -> ev m -> ev (n+m).
Proof. 
  intros n m evn evm.
  induction (evn).
    Case "evn = ev_0".
      simpl. apply evm.
    Case "evn = ev_SS".
      simpl. apply ev_SS. apply IHevn.
Qed. (* that's a much better way, methinks *)
 
(** [] *)


(* ####################################################### *)
(** ** [Inversion] on Evidence *)

(** Another situation where we want to analyze evidence for evenness
    is when proving that, if [n] is even, then [pred (pred n))] is
    too.  In this case, we don't need to do an inductive proof.  The
    right tactic turns out to be [inversion].  *)

Theorem ev_minus2: forall n,
  ev n -> ev (pred (pred n)). 
Proof.
  intros n E.
  inversion E as [| n' E'].
  Case "E = ev_0". simpl. apply ev_0. 
  Case "E = ev_SS n' E'". simpl. apply E'.  Qed.

(** **** Exercise: 1 star, optional (ev_minus2_n) *)
(** What happens if we try to use [destruct] on [n] instead of [inversion] on [E]? *)

Theorem ev_minus2': forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct n as [|n'] eqn:Hn.
    Case "n = 0". simpl. apply E.
    Case "n = S n'".  simpl. Abort.

(* What happens? We get sad. Because ev talks in terms of S (S (n)), and destruct
 * only lets us move in single steps of [S].
 *)
(** [] *)


(** Another example, in which [inversion] helps narrow down to
the relevant cases. *)

Theorem SSev__even : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E. 
  inversion E as [| n' E']. 
  apply E'. Qed.

(** These uses of [inversion] may seem a bit mysterious at first.
    Until now, we've only used [inversion] on equality
    propositions, to utilize injectivity of constructors or to
    discriminate between different constructors.  But we see here
    that [inversion] can also be applied to analyzing evidence
    for inductively defined propositions.

    (You might also expect that [destruct] would be a more suitable
    tactic to use here. Indeed, it is possible to use [destruct], but 
    it often throws away useful information, and the [eqn:] qualifier
    doesn't help much in this case.)    

    Here's how [inversion] works in general.  Suppose the name
    [I] refers to an assumption [P] in the current context, where
    [P] has been defined by an [Inductive] declaration.  Then,
    for each of the constructors of [P], [inversion I] generates
    a subgoal in which [I] has been replaced by the exact,
    specific conditions under which this constructor could have
    been used to prove [P].  Some of these subgoals will be
    self-contradictory; [inversion] throws these away.  The ones
    that are left represent the cases that must be proved to
    establish the original goal.

    In this particular case, the [inversion] analyzed the construction
    [ev (S (S n))], determined that this could only have been
    constructed using [ev_SS], and generated a new subgoal with the
    arguments of that constructor as new hypotheses.  (It also
    produced an auxiliary equality, which happens to be useless here.)
    We'll begin exploring this more general behavior of inversion in
    what follows. *)


(** **** Exercise: 1 star (inversion_practice) *)
Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros N H.
  inversion H.
  inversion H1.
  apply H3.
Qed.

(** The [inversion] tactic can also be used to derive goals by showing
    the absurdity of a hypothesis. *)

Theorem even5_nonsense : 
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1. inversion H3. Qed.
(** [] *)

(** **** Exercise: 3 stars, advanced (ev_ev__ev) *)
(** Finding the appropriate thing to do induction on is a
    bit tricky here: *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m Hevnm Hevn.
  induction Hevn.
    Case "ev_0". simpl in Hevnm. apply Hevnm.
    Case "ev_SSn".
      simpl in Hevnm.
      apply IHHevn.
      inversion Hevnm.
      apply H0.
Qed.
(** [] *)

(** **** Exercise: 3 stars, optional (ev_plus_plus) *)
(** Here's an exercise that just requires applying existing lemmas.  No
    induction or even case analysis is needed, but some of the rewriting
    may be tedious. *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  assert (Hnm' := Hnm).
  assert (Hnp' := Hnp).
  assert (Hmp := Hnm).
  apply (ev_sum (n+m) (n+p)) in Hmp.
  simpl in Hmp.
  rewrite <- plus_assoc in Hmp.
  replace (m + (n + p)) with (n + (m + p)) in Hmp.
  rewrite plus_assoc in Hmp.
  rewrite plus_assoc in Hmp.
  replace (n + n) with (double n) in Hmp.
  apply ev_ev__ev with (m:=(m+p)) in Hmp.
  apply Hmp.
  rewrite <- plus_assoc.
  rewrite <- plus_assoc.
  replace (m + (p + (m + p))) with (double (m + p)).
  apply ev_sum.
  apply double_even.
  apply double_even.
  rewrite plus_assoc.
  rewrite double_plus. reflexivity.
  apply double_plus.
  rewrite plus_assoc. rewrite plus_assoc. rewrite <- plus_comm.
  rewrite <- plus_comm. replace (n+m) with (m+n). reflexivity.
  rewrite plus_comm. reflexivity.
  apply Hnp.
Qed.
(** [] *)





(* ####################################################### *)
(** * Additional Exercises *)

(** **** Exercise: 4 stars (palindromes) *)
(** A palindrome is a sequence that reads the same backwards as
    forwards.

    - Define an inductive proposition [pal] on [list X] that
      captures what it means to be a palindrome. (Hint: You'll need
      three cases.  Your definition should be based on the structure
      of the list; just having a single constructor
    c : forall l, l = rev l -> pal l
      may seem obvious, but will not work very well.)
 
    - Prove that 
       forall l, pal (l ++ rev l).
    - Prove that 
       forall l, pal l -> l = rev l.
*)

Inductive pal {X:Type} : (list X) -> Prop :=
  | pal_empty : pal (@nil X)
  | pal_singleton : forall x, pal [x]
  | pal_app : forall x l, pal l -> pal ((x :: l) ++ [x]).


Theorem pal_rev_eq: forall (X:Type) (l: list X),
  pal l -> l = rev l.
Proof.
  intros X l H.
  induction H.
    Case "pal_empty". simpl. reflexivity.
    Case "pal_singleton". simpl. reflexivity.
    Case "pal_app".
      simpl. rewrite <- snoc_appends.
      rewrite rev_snoc. rewrite <- IHpal.
      simpl. reflexivity.
Qed.

(* snoc_appends: snoc l v = l ++ v
   snoc_with_append: snoc(l1 ++ l2) v = l1 ++ (snoc l2 v)
   rev_snoc: rev (snoc s v) = v :: (rev s)
   *)

Theorem cons_app: forall (X:Type) (l1 l2: list X) (v : X),
  (v :: l1) ++ l2 = v :: (l1 ++ l2).
Proof.
  intros X l1 l2 v.
  induction l1 as [|h1 t1].
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

(*
Theorem cons_app3: forall (X:Type) (l1 l2 l3: list X) (v : X),
  (v :: l1) ++ l2 ++ l3 = v :: (l1 ++ l2) ++ l3.
Proof.
  intros X l1 l2 l3 v.
  rewrite cons_app.
*)

Theorem app_ass: forall (X:Type) (l1 l2 l3: list X),
  l1 ++ (l2 ++ l3) = (l1 ++ l2) ++ l3.
Proof.
  intros X l1 l2 l3.
  induction l1 as [|h1 t1].
    Case "l1 = []". simpl. reflexivity.
    Case "l1 = h1 :: t1".
      simpl. rewrite IHt1. reflexivity.
Qed.

Theorem pal_app_rev:
  forall (X:Type) (l:list X), pal (l ++ rev l).
Proof.
  intros X l.
  induction l as [|h t].
  Case "l = []". simpl. apply pal_empty.
  Case "l = h :: t". simpl.
    rewrite snoc_appends.
    rewrite app_ass.
    apply pal_app.
    apply IHt.
Qed.
(** [] *)

(** **** Exercise: 5 stars, optional (palindrome_converse) *)
(** Using your definition of [pal] from the previous exercise, prove
    that
     forall l, l = rev l -> pal l.
*)

Theorem app_dup: forall (X: Type) (l1 l2: list X),
  l1 = l2 -> l1 ++ l1 = l2 ++ l2.
Proof. intros X l1 l2 H.
  rewrite H. reflexivity.
Qed.

Theorem pal_pal_rev: forall (X: Type) (l: list X),
  pal l -> pal (rev l).
Proof.  intros X l H.
  assert (H1 := H).  apply pal_rev_eq in H.
  rewrite <- H.
  apply H1.
Qed.

Theorem pal_pal_dup: forall (X: Type) (l: list X),
  pal l -> pal (l ++ l).
Proof. intros X l H.
  assert (H1 := H). apply pal_rev_eq in H1.
  replace (l ++ l) with (l ++ rev l).
  apply pal_app_rev.
  rewrite <- H1. reflexivity.
Qed.


  (*
Theorem pal_rev_eq: forall (X:Type) (l: list X),
  pal l -> l = rev l.
Theorem pal_app_rev:
  forall (X:Type) (l:list X), pal (l ++ rev l).
  *)

Definition tail {X:Type} (l:list X) :=
  match l with
  | [] => []
  | h :: t => t
  end.

Theorem cons_tail: forall (X:Type) (l t:list X) (h:X),
  h :: t = l -> t = tail l.
Proof. intros X l t h H.
  rewrite <- H. unfold tail. reflexivity.
Qed.

Theorem app_end: forall (X:Type) (l tt:list X) (h0 h th:X),
  h0 :: th :: tt = l ++ [h] -> Some h = hd_opt (rev (th::tt)).
Proof. intros X l tt h0 h th H.
  destruct l as [|lh lt].
    simpl in H. inversion H.
  simpl in H. inversion H.
  rewrite H2. rewrite <- snoc_appends. rewrite rev_snoc.
  simpl. reflexivity.
Qed.

Theorem pal_app_rev_middle:
  forall (X:Type) (l:list X) (x: list X), pal x -> pal (l ++ x ++ rev l).
Proof.
  intros X l x H.
  induction l as [|h t].
  Case "l = []". simpl. rewrite app_nil. apply H.
  Case "l = h :: t". simpl.
    rewrite snoc_appends.
    replace (t ++ x ++ rev t ++ [h]) with ((t ++ x ++ rev t) ++ [h]).
    apply pal_app.
    apply IHt.
    rewrite <- app_ass. rewrite <- app_ass. reflexivity.
Qed.

Fixpoint take {X:Type} (n:nat) (l:list X) : (list X) :=
  match n with
  | 0 => []
  | S n' => match l with
            | [] => []
            | h :: t => h :: take n' t
            end
  end.


Fixpoint drop {X:Type} (n:nat) (l:list X) : (list X) :=
  match n with
  | 0 => l
  | S n' => match l with
            | [] => []
            | h :: t => drop n' t
            end
  end.

Fixpoint half_w (n:nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (half_w n')
  end.

Definition half (n:nat) : nat :=
  match evenb n with
  | true => half_w n
  | false => half_w (pred n)
  end.

Definition middle {X:Type} (l:list X) : list X :=
  if evenb (length l)
  then []
  else take 1 (drop (half (length l)) l).
Example middle_ex1: middle [1;2;3] = [2].
Proof. unfold middle. simpl. reflexivity. Qed.
Example middle_ex2: middle [1;2] = [].
Proof. unfold middle. simpl. reflexivity. Qed.

Definition first_half {X:Type} (l:list X) : list X :=
  take (half (length l)) l.
Definition second_half {X:Type} (l:list X) : list X :=
  rev (take (half (length l)) (rev l)).

Theorem take_whole_list: forall (X:Type) (l:list X),
  take (length l) l = l.
Proof.
  induction l. simpl. reflexivity.
    simpl. rewrite IHl. reflexivity.
Qed.

Theorem pal_take_one: forall (X:Type) (l:list X),
  pal (take 1 l).
Proof.
  intros X l.
  destruct l.
    simpl. apply pal_empty.
    simpl. apply pal_singleton.
Qed.

Theorem rev_length: forall (X:Type) (l:list X),
  length (rev l) = length l.
Proof.
  intros X l.
  induction l.
    simpl. reflexivity.
    simpl. apply length_snoc'. apply IHl.
Qed.

Theorem minus_0_r: forall (n:nat),
  n-0 = n.
Proof.
  intros n.
  destruct n.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem pred_eq_minus_Sm: forall (n m: nat),
  n - S m = pred (n - m).
Proof.
  intros n. induction n.
    intros m. simpl. reflexivity.
    intros m. simpl. destruct m.
      simpl. rewrite minus_0_r. reflexivity.
      rewrite IHn. reflexivity.
Qed.

Theorem drop_rev_take: forall (X:Type) (l:list X) (n:nat),
  drop n l = rev (take (length l - n) (rev l)).
Proof.
  intros X l n.
  generalize dependent l.
  induction n as [|n'].
    Case "n = 0".
      intros l.
      simpl.
      rewrite minus_0_r.
      rewrite <- rev_length.
      rewrite take_whole_list.
      rewrite rev_involutive.
      reflexivity.
    Case "n = S n'".
      intros l.
      destruct l as [|h t] eqn:Hl.
        simpl. reflexivity.
      simpl. rewrite snoc_appends.
      assert (Htakepred: forall Y (j:list Y) (m o:nat) (x:Y), o > m -> take (S(o - S m)) (x :: j) = x :: take (o - S m) j).
        intros Y j m o x Hbound.
        simpl. reflexivity.
      assert (H: forall Y (j k:list Y) m, take (length j - m) (j ++ k) = take (length j - m) j).
        intros Y j k m.
        induction j.
        simpl. reflexivity.
        destruct m as [|m'] eqn:Hm. simpl. rewrite minus_0_r in IHj. rewrite IHj. reflexivity.
        simpl.
        rewrite pred_eq_minus_Sm in IHj.
        destruct (length j - m').
          simpl. reflexivity.
          simpl. simpl in IHj. rewrite IHj. reflexivity.
      rewrite <- rev_length.
      rewrite H. rewrite IHn'. rewrite rev_length. reflexivity.
Qed.

Theorem rev_eq_split_halves: forall {X:Type} (l:list X),
  l = rev l ->
  first_half l = rev (second_half l).
Proof.
  intros X l Hrev.

  unfold first_half.
  unfold second_half.
  rewrite rev_involutive.
  rewrite <- Hrev.
  reflexivity.
Qed.

Theorem app_snoc: forall {X:Type} (l1 l2:list X) (e:X),
  l1 ++ snoc l2 e = snoc (l1 ++ l2) e.
Proof.
  intros X l1 l2 e.
  induction l1. simpl. reflexivity.
    simpl. rewrite IHl1. reflexivity.
Qed.

Theorem rev_rev_app: forall {X:Type} (l1 l2:list X),
  rev l2 ++ rev l1 = rev (l1 ++ l2).
Proof.
  intros X l1.
  induction l1 as [|h1 t1].
   simpl. intros l2. rewrite app_nil. reflexivity.
   intros l2. simpl. rewrite app_snoc. rewrite IHt1. reflexivity.
Qed.
Theorem take_drop_app: forall {X:Type} (l:list X) (n:nat),
  take n l ++ drop n l = l.
Proof.
  intros X l n.
  generalize dependent l.
  induction n as [|n'].
    simpl. reflexivity.
    destruct l.
      simpl. reflexivity.
      simpl. rewrite IHn'. reflexivity.
Qed.

Theorem dropn_dropSn_app: forall {X:Type} (l:list X) (n:nat),
  (take 1 (drop n l)) ++ (drop (S n) l) = drop n l.
Proof.
  intros X l n.
  generalize dependent l.
  induction n as [|n'].
    intros l. simpl. destruct l.
      simpl. reflexivity.
      simpl. reflexivity.
    intros l. destruct l.
      simpl. reflexivity.
      replace (drop (S n') (x :: l)) with (drop n' l).
      replace (drop (S n' + 1) (x :: l)) with (drop (n' + 1) l).
      rewrite IHn'. reflexivity.
      simpl. reflexivity.
      simpl. reflexivity.
Qed.

Theorem subnplusn: forall (n m:nat),
  ble_nat n m = true ->
  m - n + n = m.
Proof.
  intros n.
  induction n.
    intros m H. rewrite plus_0_r. rewrite minus_0_r. reflexivity.
    intros m H. induction m.
      inversion H.
      simpl. rewrite plus_Sn_r. apply f_equal. apply IHn.
      inversion H. reflexivity.
Qed.

Theorem plusn_eq_plusn: forall (n m o:nat),
  n + o = m + o -> n = m.
Proof.
  intros n m o H.
  generalize dependent n.
  generalize dependent m.
  induction o.
    Case "o = 0".
      intros n m H. rewrite plus_0_r in H.  rewrite plus_0_r in H. apply H.
    Case "o = S o".
      intros n m H. rewrite plus_Sn_r in H. rewrite plus_Sn_r in H. inversion H.
      apply IHo in H1.
      apply H1.
Qed.


Theorem oddb_Sn__negb_oddb_n: forall (n:nat),
  oddb (S n) = negb (oddb n).
Proof.
  induction n.
    simpl. reflexivity.
    replace (oddb (S (S n))) with (oddb n).
    rewrite IHn.
    rewrite negb_involutive. reflexivity.
    reflexivity.
Qed.

Theorem oddb_n__evenb_Sn: forall (n:nat),
  oddb n = evenb (S n).
Proof.
  intros n.
  replace (evenb (S n)) with (negb (negb (evenb (S n)))).
  rewrite <- evenb_n__oddb_Sn.
  induction n.
    simpl. reflexivity.
    rewrite evenb_n__oddb_Sn. simpl.
    rewrite <- IHn. apply oddb_Sn__negb_oddb_n.
    rewrite negb_involutive. reflexivity.
Qed.

Theorem oddb_Sn__evenb_n: forall (n:nat),
  oddb (S n) = evenb n.
Proof.
  intros n.
  destruct n.
    simpl. reflexivity.
  rewrite <- oddb_n__evenb_Sn.
  reflexivity.
Qed.

Theorem oddb__neg_evenb: forall (n:nat),
  oddb n = negb (evenb n).
Proof.
  intros n.
  induction n.
    simpl. reflexivity.
  rewrite <- evenb_n__oddb_Sn.
  rewrite oddb_Sn__negb_oddb_n.
  rewrite IHn.
  rewrite negb_involutive. reflexivity.
Qed.

Theorem evenb__neg_oddb: forall (n:nat),
  evenb n = negb (oddb n).
Proof.
  intros n.
  rewrite oddb__neg_evenb.
  rewrite negb_involutive.
  reflexivity.
Qed.

Theorem evenb_n_implies_oddb_n_negb: forall (n:nat) (b:bool),
  evenb n = b -> oddb n = negb b.
Proof.
  intros n b H.
  rewrite oddb__neg_evenb. rewrite H. reflexivity.
Qed.

Theorem oddb_n_implies_evenb_n_negb: forall (n:nat) (b:bool),
  oddb n = b -> evenb n = negb b.
Proof.
  intros n b H.
  rewrite evenb__neg_oddb. rewrite H. reflexivity.
Qed.


Theorem half_Sn_even: forall (n:nat),
  evenb n = true -> half (S n) = half n .
Proof.
  intros n H.
  unfold half.
  rewrite H.
  rewrite evenb_n__oddb_Sn.
  simpl.
  rewrite H. simpl. reflexivity.
Qed.

Theorem half_Sn_odd: forall (n:nat),
  evenb n = false -> half (S n) = S (half n).
  intros n H.
  unfold half.
  rewrite H.
  rewrite <- oddb_n__evenb_Sn.
  apply evenb_n_implies_oddb_n_negb in H.
  rewrite H. simpl.
  induction n.
    inversion H.
    simpl. reflexivity.
Qed.

Theorem n___half_n_plus_half_n: forall (n:nat),
  n = half n + half n + (if evenb n then 0 else 1).
Proof.
  intros n.
  induction n.
    simpl. reflexivity.
    destruct (evenb n) eqn:Hevn.
      Case "even".
        rewrite <- oddb_n__evenb_Sn.
        assert (Hodd := Hevn).
        apply evenb_n_implies_oddb_n_negb in Hodd.
        rewrite Hodd. simpl.
        rewrite half_Sn_even.
        simpl.
        rewrite plus_0_r in IHn.
        rewrite <- IHn.
        rewrite plus_comm. simpl. reflexivity.
        apply Hevn.
      Case "false".
        rewrite <- oddb_n__evenb_Sn.
        assert (Hodd := Hevn).
        apply evenb_n_implies_oddb_n_negb in Hodd.
        rewrite Hodd. simpl.
        rewrite half_Sn_odd.
        simpl.
        rewrite plus_0_r. rewrite plus_Sn_r.
        replace (S n) with (S (half n + half n + 1)).
        rewrite plus_comm. simpl. reflexivity.
        rewrite <- IHn.
        reflexivity.
        apply Hevn.
Qed.

Theorem ble_m_n__m_Sn: forall (n m:nat),
  ble_nat m n = true -> ble_nat m (S n) = true.
  intros m n H.
  generalize dependent m.
  induction n.
    simpl. reflexivity.
    simpl. destruct m. 
      intros H. simpl in H. inversion H.
      intros H. simpl in H. rewrite IHn. reflexivity. apply H.
Qed.

Theorem ble_nat_half_n_n__true: forall (n:nat),
  ble_nat (half n) n = true.
Proof.
  intros n.
  induction n.
    simpl. reflexivity.
    destruct (evenb n) eqn:Hevn.
      Case "even".
        rewrite half_Sn_even. simpl.
        apply ble_m_n__m_Sn in IHn. rewrite IHn. reflexivity.
        apply Hevn.
      Case "odd".
        rewrite half_Sn_odd. simpl.
        apply IHn. apply Hevn.
Qed.
 
Theorem ble_nat_S_half_n_n__true: forall (n:nat),
  evenb n = false ->
  ble_nat (S (half n)) n = true.
Proof.
  intros n H.
  destruct n as [|n'] eqn:Hn.
    inversion H.
  assert (H' := H).
  rewrite <- oddb_n__evenb_Sn in H'.
  rewrite half_Sn_even. simpl.
  rewrite ble_nat_half_n_n__true.
  reflexivity.
  rewrite evenb__neg_oddb.
  rewrite H'. reflexivity.
Qed.

 
Theorem split_halves_app_even: forall {X:Type} (l:list X),
  l = rev l ->
  even (length l) ->
  l = first_half l ++ (rev (first_half l)).
Proof.
  intros X l Hrev Hev.
  assert (Hh := Hrev). apply rev_eq_split_halves in Hh.
  apply (f_equal (list X) (list X) rev) in Hh.
  rewrite rev_involutive in Hh. rewrite Hh.
  unfold second_half.
  replace (half (length l)) with (length l - half (length l)).
  rewrite <- drop_rev_take.
  unfold first_half.
  rewrite take_drop_app. reflexivity.
  apply plusn_eq_plusn with (half (length l)).
  rewrite subnplusn.
  replace (half (length l) + half (length l)) with (half (length l) + half (length l) + (if evenb (length l) then 0 else 1)).
  rewrite <- n___half_n_plus_half_n. reflexivity.
  inversion Hev. rewrite H0. rewrite plus_0_r. reflexivity.
  apply ble_nat_half_n_n__true.
Qed.

Theorem split_halves_app_odd: forall {X:Type} (l:list X),
  l = rev l ->
  evenb (length l) = false ->
  l = first_half l ++ middle l ++ (rev (first_half l)).
Proof.
  intros X l Hrev Hodd.
  assert (Hh := Hrev). apply rev_eq_split_halves in Hh.
  apply (f_equal (list X) (list X) rev) in Hh.
  rewrite rev_involutive in Hh. rewrite Hh.
  unfold second_half.
  replace (half (length l)) with (length l - (half (length l) + 1)).
  rewrite <- drop_rev_take.
  unfold first_half.
  unfold middle.
  rewrite Hodd.
  rewrite plus_Sn_r.
  rewrite plus_0_r.
  rewrite dropn_dropSn_app.
  rewrite take_drop_app. reflexivity.
  apply plusn_eq_plusn with (half (length l) + 1).
  rewrite subnplusn.
  replace (half (length l) + (half (length l) + 1)) with (half (length l) + half (length l) + (if evenb (length l) then 0 else 1)).
  rewrite <- n___half_n_plus_half_n. reflexivity.
  rewrite Hodd. rewrite plus_assoc. reflexivity.
  rewrite plus_Sn_r. rewrite plus_0_r.
  apply ble_nat_S_half_n_n__true.
  apply Hodd.
Qed.
    

Theorem evenb__even: forall n,
  evenb n = true -> even n.
Proof.
  intros n H.
  unfold even.
  apply H.
Qed.

Theorem rev_pal_eq: forall (X: Type) (l: list X),
  l = rev l -> pal l.
Proof. intros X l H.
  destruct (evenb (length l)) eqn:Hevn.
    Case "even".
      rewrite split_halves_app_even.
      apply pal_app_rev.
      apply H.
      apply evenb__even. apply Hevn.
    Case "odd".
      rewrite split_halves_app_odd.
      unfold middle.
      rewrite Hevn.
      apply pal_app_rev_middle.
      apply pal_take_one.
      apply H.
      apply Hevn.
Qed.

Fixpoint last_element {X:Type} (xs:list X) : list X :=
  match xs with
  | [] => [] 
  | [x] => [x]
  | x::xs' => last_element xs'
  end.

Fixpoint without_last_element {X:Type} (xs:list X) : (list X) :=
  match xs with
  | [] => []
  | [_] => []
  | x::xs' => x::(without_last_element xs')
  end.

Theorem match_app_singleton: forall (X Y:Type) (l:list X) (v:X) (no yes:Y),
  match l ++ [v] with
  | [] => no
  | h :: t => yes
  end = yes.
Proof.
  intros X Y l v no yes.
  destruct l.
    simpl. reflexivity.
    simpl. reflexivity.
Qed.

Theorem snoc_last_element: forall (X: Type) (l1 l2: list X) (v:X),
  snoc l1 v = l2 -> last_element l2 = [v].
Proof.
  intros X l1 l2 v H.
  rewrite snoc_appends in H.
  generalize dependent l2.
  induction l1 as [|h1 t1].
    Case "l1 = []". intros l2 H. rewrite <- H. reflexivity.
    Case "l1 = h1 :: t1".
      intros l2 H.
      rewrite <- H.
      simpl. rewrite match_app_singleton.
      destruct l2.
        simpl in H. inversion H.
      inversion H.
      apply IHt1. reflexivity.
Qed.

Theorem snoc_without_last_element: forall (X:Type) (l1 l2: list X) (v:X),
  snoc l1 v = l2 -> l1 = without_last_element l2.
Proof.
  intros X l1 l2 v H.
  rewrite snoc_appends in H.
  generalize dependent l2.
  induction l1 as [|h1 t1].
    intros l2 H. Case "l1 = []". rewrite <- H. simpl. reflexivity.
    intros l2 H. Case "l1 = h1 :: t1".
      rewrite <- H. simpl. rewrite match_app_singleton.
      rewrite <- IHt1 with (t1 ++ [v]).
      reflexivity.
      reflexivity.
Qed.

Theorem snoc_rev: forall (X:Type) (l:list X) (v:X),
  snoc (rev l) v = rev (v :: l).
Proof.
  intros X l v. simpl. reflexivity.
Qed.

Theorem cons_without_last_element: forall (X:Type) (t:list X) (v h:X),
  v :: without_last_element (h :: t) = without_last_element (v :: h :: t).
Proof.
  intros X l v h.
   simpl. reflexivity.
Qed.

Theorem last_element_cons: forall (X:Type) (t:list X) (v h:X),
  last_element (v :: h :: t) = last_element (h :: t).
Proof.
  intros X t v h.
  simpl. reflexivity.
Qed.

Theorem last_element_app: forall (X:Type) (l:list X) (v:X),
  last_element(l ++ [v]) = [v].
Proof.
  intros X l v.
  induction l.
    simpl. reflexivity.
    simpl. rewrite IHl. rewrite match_app_singleton. reflexivity.
Qed.


Theorem without_last_element_rebuild: forall (X:Type) (l:list X),
  l = without_last_element l ++ last_element l.
Proof.
  intros X l. induction l.
    simpl. reflexivity.
    destruct l.
      simpl. reflexivity.
      rewrite <- cons_without_last_element.
      rewrite cons_app. rewrite last_element_cons.
      rewrite <- IHl. reflexivity.
Qed.

Theorem rev_pal_eq': forall (X: Type) (l: list X),
  l = rev l -> pal l.
Proof. intros X l H.
  destruct (rev l) as [|rh rt] eqn:Hrevl.
    Case "rev l = []".
      rewrite H. apply pal_empty.
    Case "rev l = rh :: rt".
      destruct l as [|lh lt].
         SCase "l = []".
           apply pal_empty.
         SCase "l = lh :: lt".
           assert (Hrevl' := Hrevl).
           simpl in Hrevl.
           rewrite <- H in Hrevl.
           apply snoc_last_element in Hrevl.
           simpl in Hrevl'.
           apply snoc_without_last_element in Hrevl'.
           rewrite <- H in Hrevl'.
           assert (Hmiddle: rev (without_last_element lt) = without_last_element lt).
             destruct lt.
               simpl. reflexivity.
               apply snoc_without_last_element with lh.
               rewrite snoc_rev.
               rewrite cons_without_last_element.
               rewrite <- Hrevl'.
               rewrite rev_involutive.
               reflexivity.
           assert (Hlt: lh::lt = (without_last_element (lh::lt)) ++ [lh]).
             rewrite <- Hrevl.
             rewrite <- without_last_element_rebuild. reflexivity.
           rewrite Hlt.
           destruct lt.
             simpl.
             apply pal_singleton.
           rewrite <- cons_without_last_element in Hlt.
           rewrite <- cons_without_last_element.
           induction (lh::x::lt) as [|mh mt].
             inversion H.
           assert (Hlastmt: last_element mt = [lh]).
             destruct mt.
               simpl in Hlt. inversion Hlt. destruct lt.
                 inversion H2.
                 inversion H2.
               rewrite last_element_cons in Hrevl. apply Hrevl.
           apply IHmt in Hlastmt.
           apply Hlastmt.
           Abort. (* I had hoped this way might be shorter, but I
                     can't persuade coq to take the inductive approach that I want *)



(** [] *)

(** **** Exercise: 4 stars, advanced (subsequence) *)
(** A list is a _subsequence_ of another list if all of the elements
    in the first list occur in the same order in the second list,
    possibly with some extra elements in between. For example,
    [1,2,3]
    is a subsequence of each of the lists
    [1,2,3]
    [1,1,1,2,2,3]
    [1,2,7,3]
    [5,6,1,9,9,2,7,3,8]
    but it is _not_ a subsequence of any of the lists
    [1,2]
    [1,3]
    [5,6,2,1,7,3,8]

    - Define an inductive proposition [subseq] on [list nat] that
      captures what it means to be a subsequence. (Hint: You'll need
      three cases.)

    - Prove that subsequence is reflexive, that is, any list is a
      subsequence of itself.  

    - Prove that for any lists [l1], [l2], and [l3], if [l1] is a
      subsequence of [l2], then [l1] is also a subsequence of [l2 ++
      l3].

    - (Optional, harder) Prove that subsequence is transitive -- that
      is, if [l1] is a subsequence of [l2] and [l2] is a subsequence
      of [l3], then [l1] is a subsequence of [l3].  Hint: choose your
      induction carefully!
*)

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
  Case "l2 = []".
    intros  l1 H l3.
    destruct l1.
      apply subseq_empty.
      inversion H.
  Case "l2 = h2 :: t2".
    intros l1 H l3.
    destruct l1 as [|h1 t1].
      SCase "l1 = []".
        apply subseq_empty.
      SCase "l1 = h1 :: t1".
        inversion H.
        SSCase "subseq_head".
          simpl.  apply subseq_head. apply IHt2.
          apply H1.
        SSCase "subseq_tail".
          simpl. apply subseq_tail. apply IHt2. apply H2.
Qed.


Theorem subseq_l1_l2__subseq_l1_c_l2: forall (X:Type) (c:X) (l1 l2:list X),
  subseq l1 l2 -> subseq l1 (c::l2).
Proof.
  intros X c l1 l2 H.
  apply subseq_tail. apply H.
Qed.

Theorem app_cons: forall (X:Type) (l1 l2:list X) (v:X),
  l1 ++ (v :: l2) = (l1 ++ [v]) ++ l2.
Proof.
  intros X l1 l2 v.
  induction l1.
    simpl. reflexivity.
    simpl. rewrite IHl1. reflexivity.
Qed.

Theorem subseq_c_l1_l2__subseq_l1_l2: forall (X:Type) (c:X) (l1 l2:list X),
  subseq (c::l1) l2 -> subseq l1 l2.
Proof.
  intros X c l1 l2 H.
  generalize dependent c.
  generalize dependent l1.
  induction l2.
    intros l1 c H. inversion H.
    intros l1 c H. inversion H. apply subseq_l1_l2__subseq_l1_c_l2. apply H1.
      apply subseq_l1_l2__subseq_l1_c_l2. apply IHl2 in H2. apply H2.
Qed.

Theorem subseq_transitive: forall (X:Type) (l1 l2 l3:list X),
  subseq l1 l2 -> subseq l2 l3 -> subseq l1 l3.
Proof.
  intros X l1 l2 l3 H1 H2.
  generalize dependent l1.
  induction H2.
    intros l1 H1. destruct l1.
      apply subseq_empty.
      inversion H1.
    intros l1 H1.  inversion H1.
      apply subseq_empty. apply subseq_head. apply (IHsubseq xs0). apply H3.
      apply IHsubseq in H3. apply (subseq_l1_l2__subseq_l1_c_l2 X x) in H3. apply H3.
    intros l1 H1.
      apply IHsubseq in H1. apply (subseq_l1_l2__subseq_l1_c_l2 X x) in H1. apply H1.
Qed.

      (** [] *)


(** **** Exercise: 2 stars, optional (R_provability) *)
(** Suppose we give Coq the following definition:
    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 : forall n l, R n l -> R (S n) (n :: l)
      | c3 : forall n l, R (S n) l -> R n l.
    Which of the following propositions are provable?

    - [R 2 [1,0]]
    - [R 1 [1,2,1,0]]
    - [R 6 [3,2,1,0]]
*)
(*

  R 0 []
  R 1 [0]
  R 1 []
  R 2 [1;0]
  R 2 [1]
  R 2 [0]
  R 2 []
  R 3 [2;1;0]
  R 3 [2;1]
  R 3 [2;0]
  R 3 [2]
  R 3 [1;0]
  R 3 [1]
  R 3 [0]
  R 3 []
  R 4 [3;2;1;0]
  R 4 [3;2;1]
  R 4 [3;2;0]
  R 4 [3;2]
  R 4 [3;1;0]
  R 4 [3;1]
  R 4 [3;0]
  R 4 [3]
  R 4 [2;1;0]
  R 4 [2;1]
  R 4 [2;0]
  R 4 [2]
  R 4 [1;0]
  R 4 [1]
  R 4 [0]
  R 4 []

  R n l is valid if l is a subsequence of ((n-1)..0]. So the first
    and third examples are valid.

*)
(** [] *)


(* $Date: 2013-07-01 18:48:47 -0400 (Mon, 01 Jul 2013) $ *)



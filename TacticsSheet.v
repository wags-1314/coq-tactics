(*** Tactics Cheatsheet ***)

(** * [intros] *)
(** [intros] moves hypotheses/variables from goal to context. *)

Example intros__test : forall P,
    P -> P.
Proof.
  intros P H. (* First intros application removes the 
                 universal quantifier. The next application
                 moves the first part of the conditional
                 as a hypothesis. *)
  apply H.
Qed.



(** * [reflexivity] *)
(** [reflexivity] finishes a proof if a equality is reached i.e. [x = x]. *)

Example reflexivity__test : forall n : nat,
    n = n.
Proof.
  intros n.
  reflexivity. (* finishes the proof now that the goal is of form [x = x] *)
Qed.



(** * [simpl] *)
(** [simpl] simplifies computations in a goal *)

Example simpl__test : forall n : nat,
    0 + n = n.
Proof.
  intros n.
  simpl. (* by the definition of addition in natural numbers, 0 + n can be 
            simplified to n. [simpl] just simplifies 0 + n. *)
  reflexivity.
Qed.

(** [simpl] can not simplify further an expression that can not be computed from
the definition of the function in the expression *)

Example simpl__fail : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  simpl. (* n + 0 in the goal remains n + 0, because it can not be simplified 
           further by the definition of addition of natural numbers*)
Abort.

(** [simpl in H] applies [simpl] in the hypothesis [H] *)

Example simpl__test2 : forall n : nat,
    0 + n = n -> n = n.
Proof.
  intros n H.
  simpl in H. (* H: 0 + n = n becomes H: n = n *)
  reflexivity.
Qed.



(** * [rewrite] *)
(** [rewrite H] uses an equality [H: x = y] to rewrite the goal *)
(** [rewrite H1 in H2] uses equality [H1] to rewrite in the hypothesis *)
(** [->] or [<-] can be used to specify the direction of rewriting *)

Example rewrite__test : forall m n o : nat,
    m = n -> n = o -> m = o.
Proof.
  intros m n o.
  intros H1 H2.
  rewrite <- H1 in H2. (* replaces m with n in [H2] *)
  rewrite -> H2. (* replaces m with o in the goal *)
  reflexivity.
Qed.



(** * [destruct] *)
(** [destruct term as ... eqn:H] splits an inductively defined [term] into different
    subgoals. Analogous to proof by cases. [eqn:H] saves H as the current case *)

Example destruct__test : forall b : bool,
    andb b true = b.
Proof.
  intros b.
  destruct b eqn:H.
  - (* here b = true *)
    simpl. reflexivity.
  - (* here b = false *)
    simpl. reflexivity.
Qed.



(** * [induction] *)
(** [induction] allows us to prove by induction on an inductively defined type *)

Example induction__test : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  (* [induction] generates two subgoals:
     - Case 1: n = 0
     - Case 2: Induction Hypothesis assuming the goal is true for n'
               and a goal whith S(n') *)
  induction n as [| n' IHn'].
  - (* Base Case : 0 *)
    simpl. reflexivity.
  - (* Inductive Case. IHn': n' + 0 = n' to prove S n' + 0 = S n' *)
    simpl. rewrite IHn'. reflexivity.
Qed.



(** * [assert] *)
(** [assert (H: e)] is used to introduce local lemmas *)

Example assert__test : forall n : nat,
    n + 0 = n.
Proof.
  intros n.
  assert (H: 0 + n = n).
  { simpl. reflexivity. }
  (* now [H: 0 + n = n] appears in context *)
Abort.

(** * [unfold] *)
(** [unfold] opens up a definition in the goal or in a hypothesis. It is different 
    from [simpl] because [unfold] midlessly opens up a definition like a macro, whil
    e [simpl] tries to simplify the expression *)

Definition square n : nat := n * n.


Example unfold__test : square 5 = 25.
Proof.
  unfold square. (* [square 5] is replaces with [5 * 5] *)
  simpl. reflexivity.
Qed.

(** * [apply] *)
(** [apply] applies a hypothesis or lemma  on the goal *)
(** If the hypothesis/lemma is of the form H: A -> B and the goal is B, [apply H]
    would will replace B with A, because as we know A implies B it is sufficient to
    prove A in order to prove B. *)

Example assert__test1 : forall A B : Prop,
    (A -> B) -> A -> B.
Proof.
  intros A B H1 H2.
  apply H1. (* H1 : A -> B and the goal is B. so [apply H1] changes the goal to A *)
  apply H2. (* H2 is A, and because the goal is already a hypothesis, we can stop 
               the proof here *)
Qed.

(** [apply H1 in H2] applies the hypothesis/lemma [H1] on the hypothesis [H2]. If
    [H1] is of the form A -> B and [H2] is A, then [H2] is replaced with B,
    because we know A -> B and we know A, therefore we can infer B *)

Example assert__test2 : forall A B : Prop,
    (A -> B) -> A -> B.
Proof.
  intros A B H1 H2.
  apply H1 in H2. (* H1 is A -> B and H2 is A, so apply replaces H2 with B *)
  apply H2.
Qed.



(** * [symmetry] *)
(** [symmetry] changes [x = y] to [y = x]. It is used in conjunction with [apply] 
    because [apply] cannot match [x = y] with [y = x] *)

Example symmetry__test : forall n m : nat,
    n = m -> m = n.
Proof.
  intros n m H1.
  (* apply H1 would fail here *)
  symmetry.
  apply H1.
Qed.



(** * [injection] *)
(** [injection H] reasons on the equalities of values of inductively defined types. 
    If H is S n = S m, then [injection H] would generate a new hypothesis [n = m] *)

Inductive Silly : Type :=
  Funny (n m: nat).

Example injection__test: forall a b c d : nat,
    Funny a b = Funny c d -> a = c.
Proof.
  intros a b c d H1.
  injection H1 as H2 H3. (* [injection] generates two new hypothesis [a = c] and 
                            [b = c] *)
  apply H2.
Qed.



(** * [discriminate] *)
(** [discriminate H] will prove any goal if the context contains a trivially false equality *)

Example discriminate__test : forall n : nat,
    0 = S n -> 2 + 2 = 5.
Proof.
  intros n H.
  discriminate. (* 0 can never equal S n *)
Qed.

(** * [generalize dependent] *)
(** [generalize dependent] moves a variable or hypothesis from the context back into the goal *)

Example generalize_dependent__test : forall n m : nat,
    n = m -> m = n.
Proof.
  intros n m.
  generalize dependent n. (* brings back n into the goal *)
Abort.


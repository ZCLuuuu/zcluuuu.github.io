---
layout: post
title:  "Propositional Logics in Coq"
categories: [Software-Foundations]
description: Propositional logic calculus, FP programming with Propositions. 
---

* TOC
{:toc}
This post is a study note from series [software foundation](https://softwarefoundations.cis.upenn.edu/), containing my solutions to the exercises and the summary of the content.
## Logical Claims - `Prop` Type
Coq is a typed language, in which logical claims also belongs to a type, the type of *propositions*. Formally, the built-in type `Prop` contains all propositions.

Propositions are also first-class entities that can be manipulated in all the same way as any of the other types in Coq. 

We can also have *parameterized* propositions, which take arguments and return a proposition. 
```coq
Definition is_three (n : nat) : Prop :=
  n = 3.
Check is_three : nat -> Prop.
```
## Propositional Logics
### Conjunction
The *conjunction* or *logical and* for proposition A and B is written $A \land B$. In Coq, the notation for conjunction is `A /\ B`. 

{:.note}
>Not that `/\` is not equal to `&&`. The former one is the connection of propositions, while the later one is the connection for booleans. Later we'll see the differences between propositions and booleans. 
>
>Besides, the `/\` is just a notation for `and: prop -> prop -> prop`.

To reason propositions in conjunctive form, we need to look at the left and right part of the proposition and make sure both are provable. In Coq, the built-in `split` tactic takes this responsibility.

```coq
(** exercise `and_exercise` *)
Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros.
  split.
  - destruct n.
    + reflexivity.
    + discriminate H.
  - destruct m.
    + reflexivity.
    + rewrite add_comm in H. discriminate H.
  Qed.
```

Conversely, if there is a conjunction $A \land B$ in the hypothesis, a simple `desctruct` achieves separate A and B. 
```coq
(* exercise `and_assoc` *)
Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R [HP [HQ HR]].
  split. split.
  - apply HP.
  - apply HQ.
  - apply HR.
  Qed.
```

Conjunctions are commutative and associative. 

### Disjunction
Two propositions $A \lor B$ is disjunctive when either A or B is true. 

To use disjunctive hypothesis in a proof, we proceed by case analysis, which can be done by the `destruct` tactic.  
Oppositely, to prove a disjunction, it suffices to show that one of its sides hold, which can be done via the tactics `left` and `right`.

```coq
(** Exercise: (or_commut)*)
Theorem or_commut : forall P Q : Prop,
  P \/ Q  -> Q \/ P.
Proof.
  intros P Q [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.  
```

### Falsehood and Negation
The *negation* or *logic not* statement $\lnot P$ says P is not true. Coq defines *logic not* formally as
```coq
Definition not (p: Prop) := P -> False.

Notation "~ x" := (not x).
```
where *False* is not the bool value `false`, instead, it is an interesting un-provable proposition. It is similar to the concept of "contradiction" in computer science or math lessons. If we have a False in the hypothesis, we are justified to prove anything, because we believe in this consistent universe, there is no such thing as contradiction (Principle of Explosion). Coq accepts any theorems immediately when reading a `False` in the hypothesis. 

> ex falso quodlibet (Latin) - "From falsehood follows whatever you want." 

The way Coq defines *logic not* explains how we can use it, that is, by the tactic `intros`.   

```coq
(** Exercise (not_implies_our_not) *)
Theorem not_implies_our_not : forall (P:Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  intros P HP Q Premise.
  apply HP in Premise.
  destruct Premise.
  Qed.
```

{:.note}
> The example `not_implies_our_not` shows the Principle of Explosion in formal symbolic logics: 
>
> $\lnot P \to (\forall Q,~P\to Q)$. For any statements _P_ and _Q_, if _P_ and not-_P_ are both true, then it logically follows that _Q_ is true.

Other interesting examples include the classic contrapositive rule: $(P \rightarrow Q) \rightarrow (\neg Q \rightarrow \neg P)$
```coq
(** Exercise (contrapositive) *)
Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q HP HQ.
  unfold not.
  intros HPG.
  unfold not in HQ.
  apply HQ.
  apply HP.
  apply HPG.
Qed.
```

And the de-Morgan's law: $\neg (P \land Q) \equiv (\neg P \lor \neg Q)$
```coq
(** Exercise (de_morgan_not_or) *)
Theorem de_morgan_not_or : forall (P Q : Prop),
    ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  intros.
  unfold not in H.
  split.
  - unfold not. intros HP. apply H. apply or_introl. apply HP.
  - unfold not. intros HQ. apply H. apply or_intror. apply HQ.
Qed.
```
### Truth
There is a `True` as a counterpart for `False`, but it is used relatively rarely, since it is both trivial to prove as a goal, or as a hypothesis. 

### Logical Equivalence
The *logical equivalence* is often referred as "if and only if" or simply "iff". Just like *negation*, Coq doesn't provide a special definition for iff, instead iff is defined as 
```coq
Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
```
To prove a logical equivalence $P \iff Q$ as a goal. we need to show both $P \to Q$ and $Q \to P$. The tactic `split` can split an iff statement to two such subgoals.

```coq
(** Exercise (or_distributes_over_and) *)
Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros.
  split.
  intros H. destruct H. split.
  - left. apply H.
  - left. apply H.
  - split. 
    + right. apply H.
    + right. apply H.
  - intros [HPQ HPR]. destruct HPQ as [HP | HQ].
    + left. apply HP.
    + destruct HPR as [HP' | HR].
      * left. apply HP'.
      * right. split. apply HQ. apply HR.
Qed.
```
Conversely, to use a logical equivalence hypothesis, it is acceptable to simply use `rewrite` or `apply`. 
### Existential Quantification
Another common basic logical connection is *existential quantification*. 

$\exists x, P x$ there is some x that let the property $P~x$ holds true. The value `x` is called a *witness*. 

A *constructive proof* is the only allowed style to prove an existential claim in Coq. That means we need to give Coq a specific value and convince Coq this value does hold the property that we want to prove. The `exists` tactic is responsible for this purpose. Conversely, the tactic `destruct` is used to obtain the witness in a existential hypothesis.

```coq
(** Exercise (dist_exists_or) *)
Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
   intros X P Q.
   split.
   - intros [xw [HP | HQ]]. 
    + left. exists xw. apply HP.
    + right. exists xw. apply HQ.
   - intros [[xwp HP] | [xwq HQ]].
    + exists xwp. left. apply HP.
    + exists xwq. right. apply HQ.
Qed.
```

## Programming with Propositions
### Parameterized Proposition
As we mentioned that propositions are just a type just like `nat`. As we can do programming with `nat`, we can also do programming with `Prop`. An especially useful example is `In`
```coq
Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x' :: l' => x' = x \/ In x l'
  end.
```

The function `In: A -> list A -> Prop` checks whether a specific element is in a list. 

The example `In_app_iff` verify one property of `In`: "if an element is in a list, in which the list can be partitioned to 2 parts, the element must be either in the first part or the second part".
```coq
(** Exercise (In_app_iff) *)
Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l. split.
  {
    induction l.
    - simpl. intros H. right. apply H.
    - simpl. intros [H1 | H2].
      + left. left. apply H1.
      + apply IHl in H2. apply or_assoc. right. apply H2.
  }
  {
    induction l.
    - simpl. intros [|H]. contradiction H. apply H.
    - simpl. intros H. apply or_assoc in H. destruct H.
      + left. apply H.
      + right. apply IHl. apply H.  
  }
  Qed.
```

The theorem `In_map_iff` states and verified another property of `In`
```coq
(** Exercise (In_map_iff) *)
Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y. split.
  (* direction -> *)
  {
    induction l.
    - simpl. intros []. (* nonsensical premise `In y [ ]` *)
    - simpl. intros [H1 | H2].
      + exists x. split. apply H1. left. reflexivity.
      + apply IHl in H2. destruct H2 as [x' H]. exists x'. 
        split. apply H. right. apply H.
  }
  (* direction <- *)
  { intros [x [H1  H2]].  rewrite <- H1. apply In_map. apply H2. }
Qed.
```

Similarly, we can defined a function `All`, which tests all members of a list posses a property, and then prove it.

```coq
(** Exercise (All) *)
Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | x' :: l' => P x' /\ All P l'
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split.
  {
    intros H. induction l as [| h t].
    - reflexivity.
    - simpl. simpl in H. split.
      + apply H. left. reflexivity.
      + apply IHt. intros. apply H. right. apply H0. 
  }
  {
    intros H1 x H2. induction l as [| h t].
    - simpl in H2. contradiction H2.
    - simpl in H1. simpl in H2. destruct H1. destruct H2.
      + rewrite <- H1. apply H.
      + apply IHt. apply H0. apply H1.
  }
  Qed.
```

### Applying Propositions
Coq treats proofs as first-class objects, which means the tactic `apply` can be used to apply a theorem as it it were a function i.e. applying it to values and hypotheses with matching types.
```coq
Check add_comm: forall n m : nat, n + m = m + n.

Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_comm.
  (* specialize add_comm with [n m] is assigned as [y z] *)
  rewrite (add_comm y z). 
  reflexivity.
Qed.
```
A more explicit (perhaps redundant, as there is no ambiguity and readability issue) grammar is the *with clause*:
```coq
rewrite add_comm with (n:=y) (m:=z).
```

## Booleans vs Propositions
The foremost difference between booleans as propositions is *decidability*. 
**Booleans are decidable**, in the sense of we can have a terminating procedure deciding whether a Boolean expression is true or not. 
**Propositions are undecidable**. We can have a function `nat -> Prop` representing the properties like "the nth Turing machine halts".

{:.note}
> The Halting Problem is an example of undecidable problems. It ask whether a Turing Machine (computer program) will eventually halt at a given input. The undecidability is given by Alan Turing with a contradiction proof. For more information, please visit: [Halting Problem](https://en.wikipedia.org/wiki/Halting_problem) 

As a result, booleans can be used with `match` but a proposition can't, as booleans are always computable. However, you can't have a program in this style:
```plain
on input n and w.
if the nth Turing Machine halts on input w:
	print "It halts"
```

Another difference is that propositions work with `rewrite` and `apply` while booleans can't.

Since Boolean expressions are a subset of Propositions, there are some propositions that are decidable. In most case, these decidable subset of propositions have equivalent Boolean expressions. 
```coq
Example even_42_bool : even 42 = true.
Proof. reflexivity. Qed.

(* Even: fun x : nat => exists n : nat, x = double n *)
Example even_42_prop : Even 42.
Proof. unfold Even. exists 21. reflexivity. Qed.
```
We say that the boolean computation `even 42` is *reflected* in the truth of the proposition `Even 42`. If we have a reflective boolean computation, it must holds that the proposition is decidable. It is commonly observed that prove a boolean equation is far more easy than prove a proposition, thanks to the decidability. 

A notable nuance is the difference between `=?` and `=`, where the former is a boolean computation, while the later tells a proposition.

The example `even_double_conv` verifies the reflection relation.
```coq
(** Exercise (even_double_conv) *)
Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  (* Hint: Use the [even_S] lemma from [Induction.v]. *)
  intros.
  induction n.
  - exists 0. reflexivity.
  - destruct IHn.
    rewrite even_S.
    destruct (even n).
    + simpl. exists x. rewrite H. reflexivity.
    + simpl. exists (S x). rewrite H. reflexivity.
Qed. 

Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n. split.
  - intros H. destruct (even_double_conv n) as [k Hk].
    rewrite Hk. rewrite H. exists k. reflexivity.
  - intros [k Hk]. rewrite Hk. apply even_double.
Qed.

```

Here's another example. The function `eqb_list` checks if the equality of elements of some properties in two lists. Then we verify the correctness of it.
```coq
(*Exercise (eqb_list) *)
Fixpoint eqb_list {A : Type} (eqb : A -> A -> bool)
                  (l1 l2 : list A) : bool :=
  match l1 with
    | [] => match l2 with 
      | [] => true
      | h2::t2 => false
      end
    | h1::t1 => match l2 with
      | [] => false
      | h2::t2 => (eqb h1 h2) && (eqb_list eqb t1 t2)
      end
  end.

Theorem eqb_list_true_iff :
  forall A (eqb : A -> A -> bool),
    (forall a1 a2, eqb a1 a2 = true <-> a1 = a2) ->
    forall l1 l2, eqb_list eqb l1 l2 = true <-> l1 = l2.
Proof.
  (* note that l2 stays in generalized  *)
  intros A eqb H l1.
  induction l1 as [| h1 t1 IH].
  {
    split.
    destruct l2.
    - reflexivity.
    - intros HC. discriminate HC.
    - intros H'. rewrite <- H'. reflexivity.   
  }
  {
    split.
    - destruct l2.
      + discriminate.
      + intros H'. 
        (* Be brave to use the definition of function! 
          This is the very step that examines the function is well-defined. *)
        unfold eqb_list in H'. 
        apply andb_true_iff in H'.
        destruct H' as [H0 H1]. apply IH in H1. apply H in H0.
        rewrite H0, H1. reflexivity.
    - intros H'. destruct l2.
      + discriminate.
      + injection H' as H0 H1.
        simpl.
        apply andb_true_iff. split.
        * apply H, H0.
        * apply IH, H1. 
  }
  Qed.
```

## The Logic of Coq
The logical core of Coq is called the *Calculus of Inductive Constructions*. As far as I'm concerned, it is a more rigorous system than paper-and-pencil mathematics, as the absence of two common principles: the **functional extensionality** and the **exclude middle**.
### Functional Extensionality
The principle for functional extensionality says that
$\forall x, (f~x = g~x) \to f=g$  - two functions are equal if they produce the same output on every possible input.

Since functional extensionality is not in the logical core of Coq, some obvious propositions are not provable (decidable).
```coq
Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
   (* Stuck *)
Abort.
```

However, we can add this principle if we like and prove the once-stuck theorem.
```coq
Axiom functional_extensionality : forall {X Y: Type}
                                    {f g : X -> Y},
  (forall (x:X), f x = g x) -> f = g.
  
Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality. intros x.
  apply add_comm.
Qed.
```

Defining something as an `Axiom` is to make Coq accept it without proof. It can be dangerous if the axiom is *inconsistent*. An inconsistent axiom ruins the whole logic system. But fortunately, mathematicians already prove that functional extensionality if consistent.  

{:.note}
>An axiom $\Phi$ is inconsistent informally means there is some proposition P that both $P$ and $\lnot P$ is provable by $\Phi$ (a contradiction)

Another example of using functional extensionality: the function `rev_append` reverse a list, but in a tail-recursive manner. We verify it equal to the old one (`rev`).
```coq
(** Exercise (tr_rev_correct) *)
Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.

Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].

Lemma tr_rev_connection: forall X (l1 l2: list X),
  rev_append l1 l2 = rev_append l1 [ ] ++ l2.
Proof.
  intros X l1.
  induction l1.
  + reflexivity.
  + intros l2. simpl. rewrite (IHl1 (x::l2)). rewrite (IHl1 [x]).
    rewrite <- app_assoc. simpl. reflexivity.
Qed.

Lemma tr_rev_immediate: forall X (l: list X) (x: X) ,
  rev_append l [x] = rev_append l [ ] ++ [x].
Proof.
  induction l as [| a l1].
  + simpl; reflexivity.
  + intros. simpl. rewrite IHl1. rewrite <- app_assoc.
    simpl. rewrite (tr_rev_connection). reflexivity.
Qed.
  
Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l. induction l.
  - reflexivity.
  - simpl.
    rewrite <- IHl.
    unfold tr_rev.
    simpl. apply tr_rev_immediate.
Qed.
```
### Exclude Middle
The principal of Exclude Middle is 
$\forall P, P \lor \lnot P$  - for any proposition P, either P is true or not-P is true.

The foremost reason why Coq does not include it maybe because, apparently, it only works with decidable propositions. Another fact that Coq does not like it is that with Exclude Middle, we are able to prove something without actually construct it (for example, see the [Non-constructive proofs over the infinite]).

[Non-constructive proofs over the infinite]: https://en.wikipedia.org/wiki/Law_of_excluded_middle#Non-constructive_proofs_over_the_infinite

But we can always add it if we want:
```
Definition excluded_middle := forall P : Prop,
  P \/ ~ P.
```

This example demonstrate a safer way to use an unprovable axiom, that is, to put it in the hypothesis:
```coq
(** Exercise (not_exists_dist) *)

Theorem not_exists_dist :
  excluded_middle ->
  forall (X:Type) (P : X -> Prop),
    ~ (exists x, ~ P x) -> (forall x, P x).
Proof.
  intros em X P H x.
  Check excluded_middle = forall P : Prop, P \/ ~ P.
  destruct (em (P x)).
  - apply H0.
  - unfold not in H. destruct H.
    exists x. apply H0.
Qed. 
```

## Summary
This post shows the propositional logic calculus in Coq, how to program with it, and the logic core of Coq. Hope you like it.
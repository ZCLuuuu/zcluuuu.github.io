---
layout: post
title:  "Basic Proofs and FP [Coq]"
categories: [Software Foundations]
description: Study Notes on what is software validation, proofers and basic programming
---

Introduction: I am studying the online book [software foundations](https://softwarefoundations.cis.upenn.edu/). Then I decide to write something about it for me to better understand this toy from a learner's perspective. I'm happy if these articles can help you.

## Basic Ideas

### Validation
**Validation**: mathematical techniques for specifying and reasoning about properties of software and tools for helping validate these properties.

### Logic
Logic studies the field of proofs.
> Proofs are unassailable arguments for the truth of particular propositions

the fundamental tools of _inductive proof_ are ubiquitous in all of computer science.

### Proof Assistant
2 types:
* _Automated theorem provers_: give them a proposition and they return either true or false. Often domain limited. e.g. SAT solvers, model checkers
* _Proof assistants_: automate the routine aspects of proofs, while depending on human guidance for more difficult aspects. e.g. Isabelle, Coq

Applications of Coq:
* Modelling programming languages
* Developing formally certified software (and hardware)
* Play functional programming in a realistic environment
* Make mathematical proofs

### Functional Programming
Origin: Church's lambda-calculus.
Most basic tenet of FP: as much as possible, computation should be pure.
Why FP:
- it makes programs **easier to understand** and reason about
- functional programs are often much **easier to parallelize** and physically distribute
-  it serves as a bridge between logic and computer science. **i.e. proofs are programs**

## Features of FP in General
* **No side effects**: think a program is just a concrete method for computing a mathematical function
* Functions as the **first class values**
* Others: **algebraic data types** and **pattern matching**

## Data and Functions in Coq
Coq has extremely small built-in features but high flexibility for building types.

A simple coq program shows the ability of Coq to *enumerate type*:

```coq
Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d: day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => monday
  | saturday => monday
  | sunday => monday
  end.

Example test_next_weekday:
  (next_weekday (next_weekday saturday)) = tuesday.

Proof. simpl. reflexivity. Qed.
```
This program ask coq to verify the assertion (that the second weekday after Saturday is Tuesday)
Note the last sentence simply ask Coq to verity the assertion by proving both sides are evaluate to the same thing.
### Example: Boolean Function
This example walks through basic Coq features.
Coq  does not have built-in Boolean type, but it's easy to define one:
```coq
Inductive bool : Type :=
  | true
  | false.
```
Implement Boolean function by *pattern matching*:
```coq
Definition andb (b1:bool) (b2:bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.
```

The function can also be implemented by *conditioned statement*
```coq
Definition andb (b1:bool) (b2:bool) : bool :=
  if b1 then b2
  else false.
```
Since `bool` type is defined by ourself, Coq actually regards all inductively defined type with exact 2 clauses as Boolean type, and the first clause is evaluated to True.
Use `Check` command to printout the type of an expression
```coq
Check true.
(* true: bool *)
```
## Constructor
An `Inductive` defines a set of *constructors* and grouping them into a new named type. Constructors are functions can take arguments as well.
```coq
Inductive rgb : Type :=
  | red
  | green
  | blue.

Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | primary _ => false
  | _ => true
  end.

Example test_primary: (monochrome (primary green)) = false.
Proof. simpl. reflexivity. Qed.

Definition isRed (c : color) : bool :=
  match c with
  | primary red => true
  | _ => false
  end.

Example test_red: (isRed (primary red)) = true.
Proof. simpl. reflexivity. Qed.
```
In this example, `primary` can take an argument typed `rgb`. In function `monochrome`, we match a `primary` with any variable it holds. While in `isRed`, we only match `primary` includes a specific type `red`.

Constructors can be group in a *module* to create a distinct namespace:
```coq
Module Playground.
  Definition foo : rgb := blue.
End Playground.
Definition foo : bool := true.
Check Playground.foo : rgb.
Check foo : bool.
```

A constructor that takes more than 1 parameters is considered to be a *tuple*
```coq
Inductive bit : Type := B1 | B0.
Inductive nybble : Type := bits (b0 b1 b2 b3 : bit).
Check (bits B1 B0 B1 B0):nybble.

Definition all_zero (nb : nybble) : bool :=
  match nb with
  | (bits B0 B0 B0 B0) => true
  | (bits _ _ _ _) => false
  end.
Compute (all_zero (bits B0 B0 B0 B0)).
```
here we call `nybble`  a tuple type with 4 bits.
## Numbers
Natural numbers in Coq have a very concise definition:
```coq
Inductive nat : Type :=
  | O
  | S (n : nat).
```
Here the constructor `S` receives another constructor for nat. In the case, 0 is represent by O, 1 by S O, 2 by S (S O). This kind of representation is called `unary representation`

Algebra Calculations can be  implemented by pattern match:
```coq
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

Example p32: (plus 3 2) = 5.
Proof. simpl. reflexivity. Qed.
```
* `(n m : nat)` just means `(n : nat) (m : nat)` for convenience.
* `Fixpoint` declares a recursive function

Another example is the factorial calculation: `n! = n(n-1)...1`
```coq
Fixpoint factorial (n: nat) : nat :=
  match n with
  | O => S O
  | S n' => mult n (factorial n')
  end.
```

Coq support `Notation` for better reading:
```coq
Notation "x + y" := (plus x y)
```

Another example shows comparing 2 natural numbers. `leb` test if `n` is equal to or less than `m`:
```coq
Fixpoint leb (n m : nat) : bool :=
  match n with
  | O => true
  | S n' =>
      match m with
      | O => false
      | S m' => leb n' m'
      end
  end.

Example test_leb: leb 2 4 = true.
Proof. simpl. reflexivity. Qed.
```
## Proof by simplification
We use *simplification proof* so far. It just means simplify both sides of the equation, then use *reflexivity* to check that both sides contain identical values.

Look at a more interesting example. We can make a theorem states that for all natural number n, n+0 equals to n.

```coq
Theorem plus_O_n: forall n: nat, 0 + n = n.

Proof.
  intros m. simpl. reflexivity. 
Qed.
```
* `Theorem` keyword does nothing more than `Example` we use. It's just for readability. Other keywords include `Lemma`, `Fact`, `Remark
* `Intros m` introduces n from the quantifier in to the context of the proof. In particular, it renames `n` in the quantifier to `m` in the proof.
* `simpl` means simplify the both sides of the equation. 
* `reflexivity` checks the equality of both sides of the equation. In fact, `reflexivity` does the simplification jobs as well so it doesn't require `simpl` put in front of it. But `simpl` can help developers understand what happened after simplification.   
* The key words `intros`, `simpl` and `reflexivity` are examples of *tactics*. A tactic is a command that is used between Proof and Qed to guide the process of the proof.

## Proof by Rewriting
The `rewrite` tactic replace the simple to proof the equation. Example:
```coq
Theorem plus_id_exercise : forall n m o : nat,
  n = m -> m = o -> n + m = m + o.

Proof.
  intros n m o. (* 1 *)
  intros H1 H2. (* 2 *)
  rewrite -> H1. (* 3 *)
  rewrite -> H2. (* 4 *)
  reflexivity. (* 5 *)
Qed.
```
1 moves variables m n o into context. 2 introduces two hypothesis into context. 3 and 4 **rewrite the equation from left to right by the 2 assumptions**.
1. In the beginning, the equation is: $n + m = m + o$
2. After rewrite by the first assumption $n=m$, the equation became $m + m = m + o$
3. After rewrite by the second assumption $m = o$, the equation became $o + o = o + o$
4. Finally, use reflexivity tactic to check if the both sides of the equation is equal.
Note: The arrow `->` means "implies" in the theorem while note the rewrite direction in the proof. For example, if 4 is write as
```coq
rewrite <- H2
```
The equation is rewrited from right to left, becoming $m + m = m + m$
The `rewrite` is able to also refer to other theorems (or lemmas, facts...) to make a proof.

## Proof by Case Analysis
Many proofs need proofer to think different case. This kind of proof is `Case Analysis`.
```coq
Theorem plus_1_neq_0 : forall n : nat,
  (n + 1) =? 0 = false.
Proof.
  intros n. destruct n as [| n'] eqn:E.
  - reflexivity.
  - reflexivity. Qed.
```
This theorem states that for every natural number n, n+1 is not equal to 0.  The proof is by case analysis. By the definition of `nat`, there are 2 cases (constructors) which are enumerated in the `as` clause. `as [| n']` is read as "for the 2 constructors of `nat`, assign the `n'` as the name of the parameter of second constructor". After `destruct`, the proof is spitted into 2 subgoals - for n = O and for n = S n', we want to have $(n+1) =? 0$ for each case.  The 2 subgoals is proved in 2 parts, marked with `-` bullet symbols, with a simple reflexivity proof respectively.  

Note:
- The `as` clause can be omitted if no constructor need to bind variables or no need to specify the name of binding variables.
- It is legit to use `destruct` inside a subgoal, generating yet more proof obligation
- Besides `-`, `+` and `*` are also standard bullet symbols. use braces `{}` to enclose sub-proofs are also acceptable

This example shows how to combine case analysis together with rewrite
```coq
Theorem andb_true_elim2 : forall b c : bool,
andb b c = true -> c = true.
Proof.
  intros b c H. destruct c eqn:E.
  (* c = true *)
  - reflexivity.
  (* c = false *)
  (* note that the assumption H becomes "(and b false) = true"*)
  - rewrite <- H.
    (* rewrite "false = true" to "false = (and b false)"*)
    destruct b eqn:Eb.
    + reflexivity.
    + reflexivity.
Qed.
```
Also, this example shows how to use a "false assumption" to avoid a "false goal" (contradiction).

Because `intros` + `destruct` is so common in a proof, there is a simplified grammar for case analysis - `intros []`, i.e. introduce a variable and destruct it. Using this grammar to make the same proof:
```coq
Theorem andb_true_elim2 : forall b c : bool,
andb b c = true -> c = true.
Proof.
  (* introduct b and c then destruct then into 4 cases:
   (true, true), (true, false), (false, true), (false, false)  *)
  intros [] []. 
  (* goal: true = true. *)
  - reflexivity.
  (* goal: false = true *)
  (* The goal is a contradiction. Need to replace the right side "true" by the assumption "and b c = true".*)
  - intros H. rewrite <- H. reflexivity.
  (* goal: true = true *)
  - reflexivity.
  (* goal: false = true *)
  - intros H. rewrite <- H. reflexivity.
Qed.
```

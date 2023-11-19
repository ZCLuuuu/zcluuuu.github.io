---
layout: post
title:  "Reasoning Proofs with Basic Data Structures"
categories: [Software-Foundations]
description: Pair, List, Map, Options
---
This note refers to the the online book series [software foundation].
## Pair
In *inductive* type definition, constructors can take arbitrary number of parameters. 

For example, here is a pair type: 
```coq
Inductive natprod : Type :=
  | pair (n1 n2 : nat).
```
We can also give a notation for this type
```coq
Notation "( x , y )" := (pair x y).
```
Example for using pair
```coq
Definition fst (p : natprod) : nat :=
  match p with
  | (x,y) ⇒ x
  end.
  
Example fst1: fst (3,5) = 3.
```
Pair is an extremely basic type but illustrates the idea of how data structure is like in Coq.
## List
The most common list type is given
```coq
Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
```
This definition can be read:
Any `natlist` type is either empty `nil`, or is composed by a number with another `natlist`.

Similarly, we can define notations parse rules for list
```coq
Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

(* These 3 definitions are identical *)
Definition mylist1 := 1 :: (2 :: (3 :: nil)).
Definition mylist2 := 1 :: 2 :: 3 :: nil.
Definition mylist3 := [1;2;3].
```

The operation on list follows a recursive style. e.g. get the length of a list:
```coq
Fixpoint length (l:natlist) : nat :=
  match l with
  | nil ⇒ O
  | h :: t ⇒ S (length t)
  end.
```

A more non-trivial example of operations on list is `nonzeros`, which filter 0 out of a list. (From exercise)
```coq
Fixpoint nonzeros (l:natlist) : natlist:=
  match l with
    | nil => nil
    | n::l' => match n with
      | O => nonzeros l'
      | h => h::(nonzeros l')
      end
    end.

Example test_nonzeros:
  nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  reflexivity. Qed.
```
### Bag
A *bag* is another data structure, which is like a set but an element can appear multiple times. A naïve implementation of bag is list.
```coq
Definition bag := natlist.
```

This function `count` counts how many target items in a bag:
```coq
Fixpoint count (v : nat) (s : bag) : nat :=
  match s with
    | nil => O
    | n::s' => if eq_nat v n then S ( count v s') else count v s'
  end.
  
Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  simpl. reflexivity. Qed.
Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  simpl. reflexivity. Qed.
```

Here we gives a proof related to bag and count function to show how to reason data structure in coq
```coq
(* adding an element makes the count increase by 1 *)
Theorem add_inc_count: forall n: nat, forall s: bag, 
  count n (n::s) = S (count n s).
Proof.
  intros n s.
  destruct s as [| s'].
  + simpl. rewrite -> eq_self. reflexivity.
  + simpl. rewrite -> eq_self. reflexivity. 
Qed.
```
where `eq_self` states that a natural number equal to itself
```coq
Lemma eq_self: forall n: nat, eq_nat n n = true.
```

It's hard to just read the proof and figure out how the proof works without an Coq session. For example, the proof for both subgoals seems to be identical, but it's not in fact. We can translate it into a informal proof:

- Theorem: for all natural number n, for all bag s, count n (n::s) = S (count n s).
	Proof by considering the 2 possible constructors of s.
	
	First let s to be `nil`, we want to prove that
	
	`count n \[n\] = S (count n \[\ ])`
	
	by the definition of count, the above equation is equivalent to 
	
	`(if eq_nat n n then 1 else 0) = 1`
	
	This equation can be made true by applying the eq_self theorem.
	
	Then we consider s to be `n::s'`, we want to show that 
	
	`count n (n :: s' :: s) = S (count n (s' :: s))`
	
	Similarly, we use the definition of count to extend the equation. then we will find the expression `eq_nat n n` again. Then follow `eq_self` theorem we can make the both side to be identical.

Another example shows the "proofs by induction" tactics applying on structured data. `natlist` has 2 constructors: `nil` or `cons`, which can be used to make induction proof because a list has only 2 possible form: either empty or `cons` applies to another list. By induction, we need to show that
- P holds true when `l` is `nil`
- P holds true when `l` is consists of some number `n` and a smaller list `l'`, given P holds true for `l'`

```coq
(* reverse a list *)
Fixpoint rev (l:natlist) : natlist :=
  match l with
  | nil => nil
  | h :: t => rev t ++ [h]
  end.

(* The reverse of the concatenation of 2 lists is the concatenation of 2 reversed lists in reverse order*)
Theorem rev_app_distr: forall l1 l2 : natlist,
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros l1 l2.
  destruct l2 as [| l2'].
  - (* rev (l1 ++ [ ]) = rev [ ] ++ rev l1 *) rewrite -> rev_emp. reflexivity.
  - (* rev (l1 ++ l2' :: l2) = rev (l2' :: l2) ++ rev l1 *) 
   induction l1 as [| n1 l1' IHl1].
    + (* rev ([ ] ++ l2' :: l2) = rev (l2' :: l2) ++ rev [ ] *) 
    rewrite -> app_nil_r. simpl. reflexivity.
    + (* rev ((n1 :: l1') ++ l2' :: l2) = rev (l2' :: l2) ++ rev (n1 :: l1') *)
    simpl. 
    rewrite IHl1. 
    rewrite app_assoc.
    reflexivity.
  Qed.
```
where the lemmas are:
```coq
Lemma rev_emp: forall l: natlist, rev (l ++ [ ]) = rev l.
Lemma app_nil_r : forall l : natlist, l ++ [] = l.
```
Although I make the comments on the branches, but it's still hard to follow. It is way easier to see what's going on if you are reading the proof in an interactive Coq session. In this proof, we have 2 extra lemmas. The good practice for lemmas is to make it as general as possible. 

[Software Foundation]:https://softwarefoundations.cis.upenn.edu/lf-current/Lists.html

### Search command

To build a big proof, the common way is to split it to be several small lemmas. But it is sometimes difficult to remember the names of those lemmas. The `Search` command can search lemma in the context by a given pattern.

```coq
Search rev.
Search (_ + _ = _ + _).
Search (_++_).
```

## Map
A map is a type of data structure that map an id (or a *key*) to a value. 

We give a definition of map in coq:
```coq
Inductive id : Type := Id (n : nat).

Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).
```
Here the `id` is simply a `nat` internally. But by introducing another name, we make the type more **readable** and **flexible** if we want to change the implementation in the future.

The declaration of `partial_map` can be read: " There are 2 ways to construct a `partial_map`: either an empty or combines a k-v pair with a `partial_map`"

There are 2 operations regarding a map: put (update) and get (find):
```coq
Definition update (d : partial_map)(x : id) (value : nat): partial_map :=
  record x value d.

Fixpoint find (x : id) (d : partial_map) : natoption :=
  match d with
  | empty ⇒ None
  | record y v d' ⇒ if eqb_id x y
                     then Some v
                     else find x d'
  end.
```
There might be some confusion about why the `update` is just put a new record on the original map, instead of checking if there is an existing key. It is my understanding that **it doesn't matter** in this context because the `find` function always returns the first item that it found. If there is a need for `delete` function, it is also compatible because the implementation of `delete` can just delete all the same keys.  

## Options

`Option` is a common FP pattern that explicitly distinguish null values and non-null values by providing a responsive "container" for the value. This design pattern is so popular that even Java has an [Optional](https://docs.oracle.com/javase/8/docs/api/java/util/Optional.html)  class as well.

Here is the practice of `Option` in coq
```coq
Inductive natoption : Type :=
  | Some (n : nat)
  | None.
```

If there is a non-null value, we say there is "Some" value; Otherwise, there is "None" value. This pattern is even more useful in coq since it doesn't have build-in `null` object as many programming languages do.
Here's an example using `natoption` inductive type to write a safer function:
```coq
Definition hd_error (l : natlist) : natoption :=
  match l with 
    | nil => None
    | n::l => Some n
  end.
```
The `hd_error` function returns the first element of list `l`. If the list is empty, it gives a "None"; elsewise, it gives "Some" value. 
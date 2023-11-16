---
layout: post
title:  "Induction, Sub-theorems and Informal Proof [Coq]"
categories: [Software_Foundations]
description: Study Notes of software validation
---
## Proof by Induction
As we know that "proof P(n) by induction" is:
1. Proof that P(0) holds
2. Proof that **if P(n-1) holds**, P(n) holds as well on n > 1
Note that in step 2, there is an assumption P(n-1) holds

One example for induction proof follows:
```coq
Theorem add_0_r_firsttry : forall n:nat, n + 0 = n.
```
This theorem cannot be proved by simplicity because the +(notation of `plus` function) is defined by match:
```coq
Fixpoint plus (n : nat) (m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.
```
One cannot use the definition of `plus` to simplify `n + 0` since `n` is an arbitrary number. Destruction does not work either for the similar reason. Induction proof of this theorem provides:
```coq
Proof.
intros n. induction n as [| n' IHn'].
- (* n = 0 *) reflexivity.
- (* n = S n' *) simpl. rewrite -> IHn'. reflexivity. 
Qed.
```
The power of induction is that apart from the case analysis, we can also introduce an *induction hypothesis*. In the induction clause `induction n as [|n' IHn']`, `n'` is the param for the second constructor just like the `destruct` tactic does; we also introduce a hypothesis `IHn'` into the context:
```coq
IHn': n' + 0 = n'
```
The hypothesis said the P holds true for P(n-1). Then it is able to rewrite the equation using this hypothesis to make it equals.

For reference: the definition of `nat`:
```coq
Inductive nat : Type := O | S (n : nat).
```

Here we have another example: given a function that doubles the value, verify it sure does the job.
```coq
Fixpoint double (n:nat) :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n .
Proof.
    intros n. induction n as [| n' iHn']. (* iHn': double n' = n' + n' *)
    (* n=0; goal: double 0 = 0 + 0 *) 
    - simpl. reflexivity.
    (* n=S n'; goal: double (S n') = S n' + S n' *)
    - simpl. rewrite -> iHn'. rewrite plus_n_Sm. reflexivity.
Qed.
```
where `plus_n_Sm` states that for $n+m+1 = n + (m + 1)$
```coq
Theorem plus_n_Sm : forall n m : nat, S (n + m) = n + (S m).
```
The first case is trivial. On the second case, we run `double` first by using `simpl` tactic to replace `double (S n')` with `S (S (double n'))`.  Then it is able to use the induction hypothesis holds for `n'` to replace `double` function by `n' + n'`.

## Sub-Theorems
It is a common pattern to refer to another theorem within a theorem. Coq provides a grammar that allows programmers to do this "proofs within proofs" trick.

```coq
Theorem mult_0_plus' : forall n m : nat,
  (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H: n + 0 + 0 = n).
    (* proof to the asserted theorem *)
    { rewrite add_comm. simpl. rewrite add_comm. reflexivity. }
    (* rewrite by the asserted theorem *)
  rewrite -> H.
  reflexivity. Qed.
```

## Formal & Informal Proof
What are we writing are *formal proofs*, in which the readers are programs, like Coq. There are some differences comparing to *informal proofs*, which are human-readable. 
- In formal proof, the state of each step is **implicit**, while informal proof could reminds the readers several times where things stand.
- It is required to follow the exact definition of tactics in formal proof. In informal proof, the proof is written in **natural language**, and can be flexible for different level of readers. 
For learners, a good practice is to translate the formal proof into an informal one.

Example:
```coq
Theorem add_comm : forall n m : nat,
  n + m = m + n.
Proof.
  intros n m. induction n as [| n' iHn']. 
  - simpl. rewrite -> add_n_O. reflexivity.
  - simpl. rewrite <- plus_n_Sm. rewrite -> iHn'. reflexivity.
Qed. 
```

Translated informal proof:
- Theorem: for all n and m, n + m = m + n

	Proof by induction on n.
	- First, suppose n = 0, we want to show that

	    0 + m = m + 0.
          
      For the left side, we use the definition of +. 
        
        0 + m = m.

      For the right side, we learned from `add_n_O` theorem that 
      
      for all n, n + 0 = n. 
      
      Thus it can be re-wrote to
      
      m + 0 = m. 
      
      The both side equals.
	- Second, suppose n = S n' and n' + m = m + n', we want to show that 
	    
      S n' + m = m + S n'

	  For the left side. we have 

      S n' + m = S(n' + m)

      By the definition of operator +. From `plus_n_Sm` theorem we learned 
    
      forall n m : nat, S (n + m) = n + (S m).

      We can rewrite the right side by the `plus_n_Sm` theorem:

      m + S n' = S (m + n').
    
	    Use the induction hypothesis, this follows from
	  
      S (m + n') = S(n' + m).

	    Which is identical to the left side. Qed.

The style of this proof is a little pedantic tho, but it's valid. This example shows that the formal proof can be translated into an informal proof which is often the case when doing math.
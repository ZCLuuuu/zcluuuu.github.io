---
layout: post
title:  Brief Introduction to Quantum Computing
categories: [Quantum_Computing]
description: A highly overview of quantum computing without math.
---

I took Quantum Software Fundamentals (COMP90084) subject in the University of Melbourne in 2023 s2. This subject is my first, and perhaps the only exposure to quantum computing in my life, so I decided to write a summary. All the content related to quantum computing contains huge bunch of math, which I really don't like for new-comers to read. So I'll try my best to make this article out of math pedantic.

## What is Quantum Computing
For short: a quantum computer is a computer that takes advantage of quantum mechanical phenomena. (from [Wikipedia: quantum computing](https://en.wikipedia.org/wiki/Quantum_computing))

But it's may still confusing. For many students and programmers, maybe the main difficulty for them to understand quantum computing is the **vague understanding of *computing***. When talking about computing, it always related to a "hardware stereotype" about CPU, RAM, Disk... 

To better understanding quantum computing, it's best to first figure out - what is computing? This question involves the inspiring study of computation models back to the last century. The most famous model is the *Turing Machine*.

![Turing Machine, Form Wikipedia](https://upload.wikimedia.org/wikipedia/commons/4/4b/State_diagram_3_state_busy_beaver_2B.svg)
<center>Turing Machine, From Wikipedia</center>

In brief, a Turing machine has a tape to store a string of symbol, a movable header to read or write information on the tape, and a set of states and rules of transition between these states. For a problem to compute, we just encode the problems as a string and let the Turing Machine runs on it. When the accepting state is reached, the machine output an "yes" . It is a really simple model but people found out that **all the possible computations are equivalent to some types of Turing machines**. We give the idea of Turing machine to point out that **the idea of computation is not restricted to a specific kind of physical realization.** 

In 2001, a famous paper [Computational capacity of the universe] from MIT quantifies the amount of information that all types of physical system in the universe can register and performs. Citing the paper, I want to make 2 points:
- **All physical systems that transform and process information have the potential to compute**. i.e. be a "computer". The popular "computer" we are talking about is actually "Digital Electronic Computer", which is based on some physical systems - mainly semiconductors physics. Anyway, it is not reasonable to say that semiconductors are the only possible way to implement a computer in the universe.
- **The universe has a limited capacity of computation.** No matter what kind of physical systems, there are always some limits. You can't expect the quantum computers do everything as well as classic computers.

## What's the hype?
So, what's the difference between computers based on quantum mechanical (quantum computers) and semiconductors (classic computers)? The answer roots in the nature of quantum mechanics. Unlike a semiconductor which has only 2 possible states:  1 or 0, a quantum can have a **superposition** of many states. That means it is possible to store and process more information in a unit of time . For example, the famous [double-slit experiment](https://en.wikipedia.org/wiki/Double-slit_experiment) is an example that **a single photon can be at the superposition of every possible location.**

![Double Silt Exp](https://upload.wikimedia.org/wikipedia/commons/c/cd/Double-slit.svg)
<center>Double Silt Experiment, From Wikipedia</center>

The tempting idea is that if we can exploit this physical mechanics to build a computer that can be at **a superposition of states** at a single time, instead of at only one state, the power of computation can be much stronger. This conjures the idea of [Nondeterministic Turing machine](https://en.wikipedia.org/wiki/Nondeterministic_Turing_machine), which is the possible solver for [NP-problem](https://en.wikipedia.org/wiki/P_versus_NP_problem). (Spoiler: as far as scientists know, quantum computers are not equivalent to NP, but still much stronger than conventional deterministic Turing machine in solving many problems).

However, after a measurement, **a quantum state will collapse** and we can only measure one state at a time. If you remember the double-silt experiment, when the researchers measure the position of the photon, the interference wave is gone completely. Thus in quantum computing, the most common output is a distribution, which is acquired by computing for many times and record the results. 

Finally, to make computation possible, we must find **a way to "manipulate" the current state**. In fact, the double-silt experiment is an example of how can we manipulate the quantum state -  let the light pass two silts - then we have quantum that in a specific state which can display some pattern on the screen.  Of course, there are many other advanced way to manipulate the quantum states. Name a few: Ion traps that use laser pulse to manipulate ions, optical photon quantum computers that use optical elements  like beam splitters, phase shifters, and mirrors.
## Popular Quantum Computing Applications
### Factoring Big Integer (Shor's Algorithm)
Perhaps the most popular one of quantum algorithm is the Shor's Algorithm. All the hypes of "quantum computing will break all the current digital security systems" on the internet is based on this algorithm. In fact, it can't really break every cypher. It can only break those cryptosystem which are based on the fact that **finding the factors of a big integer is hard**, like the [RSA](https://en.wikipedia.org/wiki/RSA_(cryptosystem)#Key_generation). As we said quantum computers have their own limitation. 
### Quantum Key Distribution
Since a qubit would collapse after measurement, it is an inherently counter for eavesdropping. Any eavesdropper in the channel will destroy the superposition state and cannot rebuild it. The Quantum Key Distribution is a protocol to use a quantum channel to distributed secrete keys for 2 agents that want to establish a secure communication channel (e.g. SSL) 

### Quantum Search (Grover’s Algorithm)
The quantum search algorithm can find a particular item in a collection using just $O(\sqrt N)$ times, which is much lower than $O(N)$ in classic computers. Roughly speaking, the main reason why quantum search can be so fast is that we can have all the possible solutions in a superposition of quantum states. A quantum operation (manipulation of quantum states) can be applied to the superposition and amplify the right solution after that.   

### Quantum Machine Learning
Machine learning models are often need a huge resources of computation. Many researchers on now working on using quantum computers to speed up machine learning.  

Popular ones are:
- Quantum PCA: use quantum computer to find the principal components of a data set.
- Quantum Kernel: perform kernel method in SVM on quantum computers
- Variational Quantum Classifier: utilizes quantum circuits to learn the pattern of data and perform classification.
- Quantum Convolutional Neural Network: use the idea of convolutional neural networks to build a machine learning model in quantum computers.

![qcnn](https://pennylane.ai/961b9be93a38a37064a639ec5370297a/qcnn.svg)

<center>QCNN, From Pennylane </center>
It's really hard to explain the details of these algorithms and machine learning models. For better understanding, proper work on math is required. 

## Math Taster
I want to use this section to show that the math in quantum computing in most occasions is just simple linear algebra.

For a more formal definition, a **qubit** (a bit in quantum system) can be represented by a single qubit system, where the bit is in a superposition of 0 and 1

$$\ket{\psi} = \alpha\ket{0} + \beta\ket{1}$$

where the coefficients $\alpha, \beta$ is related to the possibility of the state.  (Here the $\ket{\psi}$ is the ket-notation. It's just a conventional notation for quantum states. It does not have other sophisticated meaning.)
Similarly a multi-qubit systems can be in a superposition of many states

$$
\ket{\psi} = b_0 \ket{b_0} + b_1 \ket{b_1} + ... + b_n \ket{b_n}
$$

An operation on the quantum state is represented by a Unitary matrix

$$\ket{\Psi(t+1)} = U\ket{\Psi(t)}$$

The possibility of find the quantum state in a specific state in measurement is related to the coefficient:

$$p(x_i) = \frac{\vert c_i \vert}{\sum_j \vert c_j \vert}$$

See, it's easy. For anyone who is confident with undergraduate linear algebra knowledge, I recommend to take a few subjects about quantum computing. The math can not tear you apart, and this field is quite interesting. Really feed one's curiosity typically if you like sci-fi matters or a computation theory hunger.  

[Computational capacity of the universe]: https://arxiv.org/abs/quant-ph/0110141
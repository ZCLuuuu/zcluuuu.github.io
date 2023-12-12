---
layout: post
title:  "Review papers notes"
categories: [Fuzz]
description: Record my questions about the three papers and try to figure out my research interests. 
---

In this post, I conclude with points I think I need to read more and questions I encountered. I hope I'm not in the wrong direction, for example, getting trapped in things too detailed for a beginner.

# Impressions of the Three Papers

I learned fuzz-related concepts, significant fuzzers' genealogy tracing, design decisions at each stage of model fuzzer, and important conferences from [The Art, Science, and Engineering of Fuzzing: A Survey](https://arxiv.org/pdf/1812.00140.pdf). I view this paper as such an index of fuzzing techniques that I need to keep diving into it as long as I study fuzzing. Aside from some questions that arise when reading, I found important fuzzers that I need to study to help me gain a deeper understanding of fuzzing. 

This paper [Fuzzing: Challenges and Reflections](https://mboehme.github.io/paper/IEEESoftware20.pdf) is more recent and provides more information on fuzzing deployment in the industry, including the fuzzers adopted by the industry, the communities of fuzzing user, and the questions the industry hope to have breakthroughs. 

From the paper [Software Bug Detection: Challenges and Synergies](https://drops.dagstuhl.de/storage/04dagstuhl-reports/volume13/issue03/23131/DagRep.13.3.92/DagRep.13.3.92.pdf), I learned about leading researchers and groups in the fuzzing field and their recent focus. Tracking them would help me find good work and keep pace with fuzzing development.

# Questions To Be Solved

My understanding of the fuzzing field is not yet as comprehensive as I would like it to be. The questions I've outlined in this section might seem basic, but I include them for my mentor to track my progress.

Some of these questions I might be able to answer through further reading, conducting experiments, and dedicating more time to study. Others represent potential tasks or areas of exploration; I'm still considering whether to invest time in these. I will label them accordingly for clarity.

## Concept-related

1. A fuzzer seems to be able to test if a PUT violates different security policies. But a bug oracle is meant to determine whether a given execution of the PUT violates a specific security policy. Does that mean a fuzzer has multiple bug oracles embedded and switch between them?
2. Through reading academic papers, I have become familiar with concepts like 'seed', 'configuration', 'approximation',' Block-based Mutation', and 'Bernoulli trials'. However, due to a lack of practical experience, these ideas still feel abstract and somewhat intangible to me

> Might be solved by studying a specific fuzzer. By reading the first two papers, I found BFF (Black box), AFL (Grey box), and honggfuzz (Grey box) are important. But I'm not sure how to study them.

3. In the Fuzz Genealogy, there are more fuzzers for File PUTs. Does that mean the file PUTs are more important or easier to study or there are more problems arising there? Why there are only a few fuzzers for concurrency and no more grey box fuzzer after 2012?
4. It's said static instrumentation generally imposes less runtime overhead than dynamic instrumentation. Is this monotony always true no matter the scale of application? Is there data on the relationship between the cost of fuzzer and different design decisions made?
5. I took a glance at the document of Enforceable Security Policies and felt like set theory is important to describe some theories.\
6. Considering fuzzing has to deal with checksums, does that mean fuzz testing could be carried out without organizations' permission? How to avoid fuzz testing from being a kind of DDOS attack?
7. Does the completeness below mean no false negatives? And soundness means no false positives? We have different warning levels from 0 to 4 in Visual Studio, can we say some compromise soundness and some compromise completeness?

> However, as expected, this completeness comes with a higher average overhead of 116% [160]. CaVer [133], TypeSan [96] and HexType [113] instrument programs during compilation so that they can detect bad-casting in C++ type casting.



## Methodology-related

1. There are four major security conferences and three software engineering conferences, and a lot of work gets published annually there. Also, in the fuzzing field, there are numerous research groups that we could keep track of. Are there other sources? How to decide what kind of work we should read and how to allocate our time. The strategy might be different for a beginner, a researcher, and a developer in the industry.
2. The Fuzzer Genealogy includes fuzzers in GitHub with over 100 stars. How to judge whether a fuzzer is worth using? Would the threshold be too low?
3. Should we be familiar with different exploitation ways of vulnerabilities in order to develop fuzzers? Is it possible to detect complicated attacking ways (e.g. step by step, attack based on information from previous steps) with fuzzing.

## Curiosity

some are related to specific techniques and some are about challenges, I haven't decided whether and what I should devote time to.

### Specific technique

1. QEMU is mentioned as a dynamic instrumentation tool. I used it as simply a VM before and I'm curious about how it works for fuzzing at the binary level. 
2. Neural and Learn&Fuzz use a neural network-based machine learning technique to learn a model from a given set of test files and generate test cases from the inferred model. Does it achieve better efficiency? Can the method be applied to other scenarios? Why and why not?
3. KameleonFuzz detects successful XSS attacks by parsing test cases with a real web browser, extracting the Document Object Model tree, and comparing it against manually specified patterns that indicate a successful XSS attack. I'm curious about the patterns.
4. The exploitable plugin for GDB is mentioned as an exploitability ranking system. Curious about under which scenarios would it be used.

### Challenges

1. Structure-aware and grammar-based fuzzing as well as the integration of static analysis and symbolic execution with grey box fuzzing.
2. Study the utility of GPUs and other means of efficient parallelization.
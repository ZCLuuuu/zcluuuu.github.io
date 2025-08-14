---
layout: post
title:  "Fortran - DO CONCURRENT"
categories: [Compiler]
description: This is a research proposal. 
---

> ## Abstract
>
> This project aims to extend GNU Fortran's support for the `DO CONCURRENT` construct by enabling actual parallel execution using the OpenMP infrastructure. With the OpenMP 6.0 specification introducing support for the `!$omp loop` directive on `DO CONCURRENT`, we seek to integrate this capability into GCC. The project focuses on parsing and lowering of OpenMP directives and `DO CONCURRENT` constructs and related clauses, and on leveraging GNU's runtime library `libgomp` to support parallel execution. These enhancements will align GNU Fortran with Fortran 2018/202X standards and benefit parallel scientific applications.
>
> ## Introduction
>
> OpenMP is a popular directive-based API for parallelizing code to run on multi-core CPUs. Meanwhile, standard programming languages like C and Fortran have also begun to introduce built-in features to help compilers parallelize code. One such feature is Fortran’s `DO CONCURRENT` construct, which can be seen as an accessible alternative for expressing parallelism. However, its current implementation depends heavily on the compiler's ability to auto-parallelize the code.
>
> The good news is that it's now possible to leverage both approaches. Recently, OpenMP released version 6.0, introducing support for applying the OpenMP `loop` construct to Fortran `DO CONCURRENT`. This signals potential for GCC to better integrate Fortran-native concurrency with OpenMP’s parallel infrastructure. By supporting this new OpenMP feature, GNU Fortran users will be able to manually parallelize their code when using `DO CONCURRENT`.
>
> This project originates from the GNU community and specifically aims to improve the GNU Fortran compiler’s support for `DO CONCURRENT`. Currently, GNU Fortran can recognize `DO CONCURRENT` syntax, but execution is still serial. The main goal of this project is to enable real parallel execution of `DO CONCURRENT` loops.
>
> To achieve this, we break the goal into several sub-tasks and focus on the most essential ones for this GSoC project. We will further explain each in the proposed solution section. To help readers unfamiliar with Fortran, it's useful to note that the `DO CONCURRENT` construct can include a `MASK` clause to selectively execute some loop iterations. To manually enable parallelization, users can combine `DO CONCURRENT` with OpenMP directives like `!$omp loop`. If OpenMP directives are not used, and parallelism is still desired, one can rely on compiler auto-parallelization by passing command-line flags such as those described in Task 3.
>
> - Task 1: Handling `DO CONCURRENT` loops in the generic OpenMP code, possibly starting without `MASK` support and only for those annotated with `!$omp loop`.
> - Task 2: Extending support to include `MASK` or optimizing loop bounds accordingly.
> - Task 3: Supporting parallelization without `!$omp loop` using the `-fdo-concurrent=` flag (e.g., “none”, “omp”, or “parallel”, similar to `-ftree-parallelize-loops=n`).
>
> Here is a possible example of a `DO CONCURRENT` loop using OpenMP `!$omp loop`, with a `MASK` clause and locality specifiers `LOCAL_INIT`, compliant with Fortran 2018+ and OpenMP 6.0 syntax:
>
> ```
> program test_mask_locality
>   implicit none
>   integer :: i, a(100), b(100), t
> 
>   b = [(i, i=1,100)]
>   t = 50
> 
>   !$omp parallel
>   !$omp loop
>   do concurrent (i = 1:100, b(i) > t) local_init(a)
>     a(i) = b(i) * 2
>   end do
>   !$omp end loop
>   !$omp end parallel
> 
>   print *, "Finished conditional concurrent execution"
> end program test_mask_locality
> ```
>
> Our goal is for GNU Fortran to successfully parse and execute such code, leveraging the OpenMP infrastructure to run it in parallel. By enabling this, we will be able to support state-of-the-art applications—for example, some neural network training and deployment infrastructure like Fiats.
>
> ## Background
>
> The `DO CONCURRENT` construct was first introduced in the Fortran 2008 standard [1] to express loop-level parallelism, indicating that each iteration of the loop is independent. It was inspired by the earlier `FORALL` construct and provided a clearer semantic model for potential parallel execution [1][2]. Later revisions of the standard have enhanced its capabilities: Fortran 2018 [3][4] added locality specifiers such as `LOCAL`, `LOCAL_INIT`, and `SHARED`, and introduced the `MASK` clause for conditionally executing iterations. The upcoming Fortran 202X draft [5] proposes further improvements, including explicit support for `REDUCE` clauses, making `DO CONCURRENT` better aligned with parallel programming needs.
>
> On the OpenMP side, OpenMP 6.0 (August 2024) added initial support for applying `!$omp loop` to `DO CONCURRENT`. This marked the beginning of integrating Fortran-native concurrency with OpenMP parallelization infrastructure [6].
>
> GNU Fortran currently supports `DO CONCURRENT` syntax and offers some parsing support for newer Fortran 2018 and 202X clauses. Basic execution of `DO CONCURRENT` is serial, and parallel execution is only possible through auto-parallelization with the `-ftree-parallelize-loops=` flag, which is not specific to `DO CONCURRENT` semantics [8]. A draft patch has added clause parsing and lowering support for `LOCAL`, `LOCAL_INIT`, and `REDUCE`, but there is no integration with OpenMP infrastructure yet.
>
> Additionally, several limitations remain. There is no support for `type-spec` in loop headers or runtime execution of the `MASK` clause. The `REDUCE` clause is parsed but not yet lowered for actual parallelism. The handling of `LOCAL` and `LOCAL_INIT` remains incomplete. 
>
> Other major Fortran compilers have varying levels of support for `DO CONCURRENT`. Intel Fortran (ifort/ifx) offers parallel execution using auto-parallelization and supports locality clauses, but does not yet support applying `!$omp loop` to `DO CONCURRENT`. NVIDIA’s nvfortran supports both serial and GPU/CPU parallel execution for `DO CONCURRENT`, but like Intel, it lacks support for the OpenMP loop directive on these constructs. LLVM Flang provides partial parsing support for `DO CONCURRENT`, but OpenMP integration, including `!$omp loop`, locality clauses, and `MASK` support, is still under development [7].
>
> ## Proposed Solution
>
> In the GNU Compiler Collection (GCC), the compilation process proceeds through several stages from language-specific parsing to machine-dependent code generation. These include the parsing pass, gimplification pass, Tree SSA passes, and RTL passes. For this project, we primarily focus on the parsing pass and related front-end transformations for the Fortran language. Since OpenMP loop constructs have been supported in GCC since version 10, no additional integration with the OpenMP runtime library is needed for `!$omp loop` constructs.
>
> The Fortran front end transforms source code into a private representation, referred to as `gfc_*` structures [9], which is then lowered to GENERIC and subsequently to GIMPLE. Below are the implementation strategies for each subtask:
>
> 1. Handling `DO CONCURRENT` loops in the generic OpenMP code
>    - Handle the case where the !$omp loop directive appears alongside DO CONCURRENT. Extend the Fortran front end to represent this in its internal AST.
>    - In the GNU Fortran front end, each statement is represented by a `gfc_code` structure, which contains an `op` member indicating the statement type. The `EXEC_OMP_LOOP` type is already defined in `gfortran.h` and should be associated with the `DO CONCURRENT` loop body in the front end’s private representation by wrapping the `EXEC_DO_CONCURRENT` node with an `EXEC_OMP_LOOP` node. This structure maintains the semantic relationship and allows proper lowering to OpenMP parallel constructs.
>    - After lowering to intermediate representations, rely on GCC’s existing infrastructure to map the OpenMP `loop` directive to built-in functions, which the backend then expands into `libgomp` runtime API calls. Since support for OpenMP loop constructs has been present since GCC 10, no additional extension to GCC’s OpenMP support is required. However, we still need to carefully handle the front-end representation so that the backend selects the correct corresponding `libgomp` routine to ensure that the generated code accurately reflects the semantics of the `DO CONCURRENT` loop, especially in the presence of clauses like `MASK` or `LOCAL_INIT`.
> 2. Extending support to include `MASK` or optimizing loop bounds accordingly
>    - Integrate parsing and semantic support for the `MASK` clause into the `DO CONCURRENT` construct.
>    - Adapt the existing internal representation to handle this new clause and ensure proper handling during lowering.
> 3. Supporting parallelization without  `!$omp loop` using the `-fdo-concurrent=`flag
>    - Enable the compiler to choose a backend parallelization strategy using libgomp based on this flag, even when no OpenMP directive is explicitly written.
>    - Implement parsing and configuration handling for the `-fdo-concurrent=` flag, accepting options enabling modes like:
>      - `none`: representing the current serial execution of `DO CONCURRENT`.
>      - `omp`: instructing the compiler to generate OpenMP loop-associated ASTs in the front end even if no explicit OpenMP directive is present, similar to what is done in Task 1 when handling `!$omp loop` together with `DO CONCURRENT`.
>      - `parallel`: targeting pthread-based parallelization, potentially similar to or building upon the existing `-ftree-parallelize-loops=n` infrastructure, relying on inserting `GIMPLE_OMP_PARALLEL`, `GIMPLE_OMP_FOR`, and `OMP_ATOMIC` codes and leveraging the OpenMP expansion machinery [10]. Other modes can also be explored depending on the final design.
>
> ## Timeline
>
> **May 8 – June 1 (Community Bonding Period)**
>
> - Get to know mentors, read documentation, and familiarize myself with the GNU Fortran codebase and `DO CONCURRENT` implementation by tracing ChangeLogs and problem reports, and by exploring the compilation process through debugging with GDB or other recommended tools.
> - Refine the proposed solution and evaluation matrix with my mentor. Clarify the midterm and final evaluation processes.
> - Understand the workflow of building, testing, Git practices, and establish a communication and process management plan.
>
> **Week 1 (June 2 – 8)**
>
> - Based on an understanding of the `DO CONCURRENT` lowering process, design data structures and analyze potential side effects.
> - Define key testing checkpoints.
> - Implement support for handling the `!$omp loop` directive when used with `DO CONCURRENT`, initially without considering related clauses.
>
> **Week 2 (June 9 – 15)**
>
> - Continue implementing support for `!$omp loop` used with `DO CONCURRENT`. Extend the Fortran front end to represent this in its internal AST, and trace how this will be processed throughout the middle-end and back-end.
> - Perform partial testing of this basic front-end support.
>
> **Week 3 (June 16 – 22)**
>
> - Analyze the transition from the Fortran front-end AST to GENERIC and GIMPLE intermediate representations. Handle code transformations through to the middle-end.
> - Verify if appropriate OpenMP routines from `libgomp` are being used to generate parallel code.
> - Conduct testing and address any side effects or bugs.
>
> **Week 4 (June 23 – 29)**
>
> - Conduct periodic documentation and reflect on the development workflow.
> - Continue testing and bug fixing.
>
> **Week 5 (June 30 – July 6)**
>
> - Continue debugging and improving stability.
> - Integrate parsing and semantic support for the `MASK` clause.
> - Modify the internal representation and handle `MASK` during lowering.
>
> **Week 6 (July 7 – 13)**
>
> - Test the `MASK` implementation and analyze the parsing process across the front-end and backend. Perform a diff comparison with earlier phases.
> - Continue debugging and improving stability.
>
> **Week 7 (July 14 – 18 – 18:00 UTC, Midterm Evaluation Deadline)**
>
> - Summarize development progress and submit the midterm evaluation report.
>
> **Week 8 (July 21 – 27)**
>
> - Estimate and plan time for testing and evaluation.
> - For testing, we plan to use NIST Fortran 7 Test Suite, LAPACK Test Suite [11]
> - For benchmarking, we plan to use Polyhedron Fortran compiler benchmarks and Livermore Fortran Kernels test. [11]
> - Implement support for parsing the `-fdo-concurrent=` flag (e.g., `none`, `omp`, `parallel`).
> - Conduct testing and bug fixing.
>
> **Week 9 – 10 (July 28 – August 10)**
>
> - Implement the `omp` mode for the `-fdo-concurrent=` flag.
> - Extend the front end to generate OpenMP-related AST structures to enable parallelization without `!$omp loop`, while still leveraging the `omp loop` infrastructure for `DO CONCURRENT`.
> - Perform testing and bug fixing.
> - Analyze the `-ftree-parallelize-loops` implementation for insights.
>
> **Week 11 – 12 (August 11 – 24)**
>
> - implement the parallel mode for -fdo-concurrent= flag
> - code to implement the functionality similar or based on ftree-loop-parallelization implementation
> - Finalize testing and evaluations.
> - Document results and identify areas for enhancement.
>
> **August 25 – September 1 - 18:00 UTC**
>
> - Complete testing, evaluation, and documentation of the project. 
>
> ## About Me
>
> **Name**: Chenlu Zhang
>
> **University**: University of Melbourne
>
> **Personal Email**: [zhanglv0413@gmail.com](mailto:zhanglv0413@gmail.com)
>
> **University Email**: [chenluz2@student.unimelb.edu.au](mailto:chenluz2@student.unimelb.edu.au)
>
> **GitHub Page**: https://zcluuuu.github.io/
>
> **Time Zone**: Melbourne VIC (GMT+11)
>
> **Residence**: Melbourne, Australia
>
> **Preferred Language for Communication**: English
>
> **Skills and Accomplishments**:
>
> - I previously worked on implementing a GCC optimization prefetching pass for an Alpha-like computer architecture. Evidence of the project is available here: [WIPO Patent Link](https://patentscope.wipo.int/search/en/detail.jsf?docId=CN394162518&_cid=P12-LME6CJ-12597-1)
> - I documented my understanding in a blog post: [Compiler Prefetch Optimization](https://zcluuuu.github.io/compiler/2022/10/01/Compiler-PrefetchOptimization.html)
> - Note: Both documents are originally written in Chinese, and my understanding of compilation is still developing.
>
> **Interests**: My personal interest lies in bridging the gap between hardware and software. I’m especially interested in understanding how specific hardware designs affect compilation and can help optimize machine code generation. For instance, the latency between registers, cache, and memory directly influences the optimal prefetch distance for each memory hierarchy level.
>
> ### References:
>
> [1] Fortran 2008 Standard (ISO/IEC 1539-1:2010), https://j3-fortran.org/doc/year/10/10-007.pdf
>
> [2] WG5 N1891: Rationale for DO CONCURRENT, https://wg5-fortran.org/N1851-N1900/N1891.pdf
>
> [3] Fortran 2018 Standard (J3/18-007r1), https://j3-fortran.org/doc/year/18/18-007r1.pdf
>
> [4] WG5 N2145: Summary of Fortran 2018, [https://web.archive.org/web/20201104010129/https://isotc.iso.org/livelink/livelink/nfetch/-8919044/8919782/8919787/19480687/ISO%2DIECJTC1%2DSC22%2DWG5_N2145_Summary_of_Fortran_2018.pdf?nodeid=19441669&vernum=1](https://web.archive.org/web/20201104010129/https://isotc.iso.org/livelink/livelink/nfetch/-8919044/8919782/8919787/19480687/ISO-IECJTC1-SC22-WG5_N2145_Summary_of_Fortran_2018.pdf?nodeid=19441669&vernum=1)
>
> [5] J3 22-007: Fortran 202X Draft Working Document, https://mailman.j3-fortran.org/pipermail/j3/attachments/20220202/5ac916c1/attachment-0001.pdf
>
> [6] OpenMP TR12 Draft (August 2024), https://www.openmp.org/wp-content/uploads/openmp-TR12.pdf
>
> [7] Intel OpenMP Support, https://www.intel.com/content/www/us/en/developer/articles/technical/fortran-language-and-openmp-features-in-ifx.html; Clang OpenMP Support, https://clang.llvm.org/docs/OpenMPSupport.html
>
> [8] PR83064: Auto-parallelization limitations for DO CONCURRENT, https://gcc.gnu.org/bugzilla/show_bug.cgi?id=83064
>
> [9] Internals of Fortran 2003 OOP Features: https://gcc.gnu.org/onlinedocs/gfc-internals/gfc_005fcode.html
>
> [10] Automatic parallelization in GCC: https://gcc.gnu.org/wiki/AutoParInGCC
>
> [11] GNU Fortran Internals: [https://gcc.gnu.org/onlinedocs](
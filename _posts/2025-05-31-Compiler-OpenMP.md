---
layout: post
title:  "Enhance OpenACC Support"
categories: [Compiler]
description: This is a research proposal. 
---

## Introduction

 OpenACC is a directive-based parallel programming model designed for heterogeneous HPC hardware. However, GCC currently only partially supports the features specified in OpenACC 2.6: some directives are not parsed at all, some are parsed at the front end but are not lowered to generate the appropriate runtime API calls, and the runtime library implementation in GCC is also incomplete. This project aims to address these gaps by proposing feasible solutions to enhance GCC’s OpenACC support to more closely align with the official specification.

 

## Background

 OpenACC is a parallel programming model for heterogeneous HPC hardware, abstracted into two parts: the host and the attached parallel accelerator, such as a GPU. It provides compiler directives (e.g., in C/C++: `#pragma acc directive-name [clause-list]`) that allow users to specify compute-intensive regions of a program to be offloaded to an accelerator or executed on multiple host cores under the control of a host thread. The **execution model** is host-directed: the host thread manages memory allocation on the accelerator, initiates data transfers, sends code and arguments to the device, queues tasks, waits for completion, retrieves results, and deallocates memory. A key aspect of OpenACC is its **memory model**: accelerator memory is often separate from host memory, requiring explicit data transfers handled by the OpenACC runtime through underlying system calls such as direct memory access (DMA) transfers. Nowadays, most accelerators include caches, and OpenACC requires the compiler to manage these caches [1].

 GCC parses code containing OpenACC directives written in C/C++ or Fortran and uses the OpenMP runtime API routines from the `libgomp` library—developed by GCC—to implement the functionality of each directive. At runtime, `libgomp` can look up and launch an offload function when given a target function address [3]. These target functions are linked to `libgomp` plugins, which are loaded from the standard dynamic linker path. For example, the plugin for Intel MIC devices uses `liboffloadmic.so`, while the plugin for NVIDIA PTX devices uses `libcuda.so` [2]. These loaded plugins rely on third-party, target-specific libraries to perform low-level interactions with accelerator devices. In short, `libgomp` is designed to be independent of specific accelerator architectures—it exposes a generic interface and delegates all target-dependent functionality to plugins. These plugins are developed collaboratively by the GNU community and hardware vendors.

 

## Project Goals and Tasks

 GCC currently only partially supports the features specified in OpenACC 2.6. This project aims to enhance GCC's OpenACC support in the following areas:

 **1. OpenACC** `acc_memcpy_device` **Runtime API Routine**

 The `acc_memcpy_device` routine, which transfers data between two device addresses on the same device, is not yet implemented in GCC's OpenACC runtime. It has both synchronous and asynchronous forms and must handle cases such as null pointers and invalid `async` values.

 To design this function, we first study the implementation pattern of existing routines—`acc_memcpy_to_device` and `acc_memcpy_from_device`—which handle host-device memory transfers. These provide a useful reference for introducing a similar mechanism for device-to-device copies.

 The implementation will primarily involve modifications to several key files within the `libgomp` directory. These include files that define runtime APIs, manage memory operations, and provide plugin hooks. The implementation details are in the [Appendix-acc_memcpy_device](#acc_memcpy_device-modified-files-overview) at the end of the document.

 - `libgomp/libgomp.map` 
 - `libgomp/openacc.h`, `openacc_lib.h`
 - `libgomp/oacc-mem.c` 
 - `libgomp/libgomp.h` 
 - `libgomp/target.c` 
 - `libgomp/oacc-host.c` 
 - `libgomp/libgomp-plugin.h` 
 - `libgomp/plugin/plugin-nvptx.c`
 - `libgomp/plugin/plugin-gcn.c` 

 These plugins dynamically resolve runtime API symbols (e.g., via `dlsym()` from `libcuda.so`), use macros like `CUDA_CALL` for error handling, and rely on helper routines like `nvptx_attach_host_thread_to_device` to ensure the host thread is correctly associated with a device context.

 

 **2. Support for** `init`**,** `shutdown`**, and** `set` **Directives**

 These directives are currently unsupported at the front-end level in GCC, even though their corresponding runtime APIs—`acc_init`, `acc_shutdown`, `acc_set_device_type`, and their async queue variants—are implemented. The goal here is to add parsing support in the front end to map these directives to the appropriate built-in functions. In GCC, front ends map OpenACC directives to `BUILT_IN_GOACC_*` entries defined in `gcc/omp-builtins.def`, and the back end expands these into runtime API calls. This task involves analyzing and extending front-end source files, taking inspiration from the implementation of the `wait` directive. Relevant files include:

 - `gcc/c-family/c-omp.cc`
 - `gcc/c/c-parser.cc`
 - `gcc/cp/parser.cc`
 - `gcc/fortran/trans-openmp.cc`
 - `gcc/omp-builtins.def`
 - `gcc/omp-oacc-kernels-decompose.cc`

 

 

 **3. Make the OpenACC** **cache** **Directive Actually Do Something**

 Currently, the `cache` directive in OpenACC is parsed at the front end, but not used for any optimization purposes, such as data prefetching or moving data to low-latency memory (e.g., L1/L2/L3 cache or GPU cache [5]). We can leverage existing prefetch support in GCC, such as the middle-end `aprefetch` pass, which analyzes nested loop structures and inserts `__builtin_prefetch` calls in GIMPLE for the innermost loop. These are later expanded by the backend `expand` pass to target-specific prefetch instructions based on the ISA. On CPUs, `__builtin_prefetch` is typically mapped to prefetch instructions in the CPU ISA. By enabling options like `-fopenacc` and setting proper flags, we can also define a customized `__builtin_prefetch_openacc` call and write new RTL templates to map prefetch calls to GPU-specific instructions—if such instructions exist for the target architecture. This will be discussed at the end of this section.

 To be more specific about how we can leverage existing infrastructure: when the `OACC_CACHE` directive is lowered to GIMPLE via `gimplify_oacc_cache`, we can insert `__builtin_prefetch_openacc` calls at appropriate locations using `gimple_build_call` and `gsi_insert_before` in the `aprefetch` pass located in `tree-ssa-loop-prefetch.cc`. These built-ins will then be picked up by the backend RTL expansion pass. However, to the best of my knowledge, there is currently no backend support for expanding prefetch instructions for GPU targets. Therefore, additional backend work is needed to implement the necessary RTL patterns or instruction selection hooks for GPU architectures.

 Aside from the `aprefetch` pass enabled by the `-fprefetch-loop-arrays` option, GCC also provides several tuning parameters via `--param`, such as `prefetch-latency`, `simultaneous-prefetches`, and `sched-autopref-queue-depth` [7], to control how aggressive or conservative the prefetching should be. All of these parameters influence the `aprefetch` pass's analysis of loop structure, so they generally require no special handling from us. However, they may restrict how many prefetch instructions can be issued effectively. These limitations stem from hardware resource models. Since we're manually issuing software prefetch instructions, we can avoid complex modeling for now and focus on building the basic infrastructure. This differs from hardware prefetching, which is handled automatically by the processor and may interact with software prefetching. While understanding this interaction is useful, it is beyond the scope of this project and can be considered in future work.

 Both AMD and NVIDIA GPUs support ISA-level prefetching, which simplifies implementing OpenACC’s `cache` directive. For AMD CDNA GPUs [8], prefetch behavior can be achieved using load instructions like `BUFFER_LOAD_DWORD` with cache-control flags (e.g., SC1, SC0, NT). Similarly, NVIDIA GPUs support dedicated prefetch instructions in the PTX ISA [9], such as `prefetch.global.L1 [a]` and `prefetchu.L1 [a]`, which allow prefetching to various cache levels and memory spaces. These capabilities enable the GCC RTL backend to map `__builtin_prefetch_openacc` to the appropriate target instructions, depending on the GPU architecture. However, if the available GPU instructions are insufficient to cover all prefetching use cases, we should consider falling back to runtime API routines from `libgomp`, such as `acc_memcpy_device`, to manually manage data movement.

 For cache directive support—e.g., for the NVIDIA NVPTX backend—modifications will mainly involve the following files. The implementation details are in [Appendix_cache](#cache-directive-support-modified-files-overview).

 - `config/nvptx/nvptx.opt`
 - `config/nvptx/nvptx.md`
 - `gcc/params.opt`
 - `gcc/builtin.def`
 - `gcc/builtin.c`
 - `gcc/ipa-pure-const.c`
 - `gcc/target-insns.def`
 - `gcc/tree-ssa-loop-prefetch.c`

 

 **4. OpenACC** `bind` **Clause Support**

 This section introduces what the `bind` clause does in OpenACC, analyzes how the existing GCC infrastructure supports `routine` directives, and proposes a path for implementing full `bind` clause support.

 The `bind` clause in OpenACC lets you link a device function to a host function name using the `routine` directive. This means you should define one function for the host and a separate one for the device. When calling the function on the device inside an OpenACC compute region, the device version you specified with `bind` will be used. For example:

 ```
 #pragma acc routine worker bind(sum1)
 int sum(int, float *);
 
 int sum(int n,float *A)
 {
 	int i;
 	float s=0.0f;
 	for(i=0;i<n;i++){
 		s=s+A[i];
 	}
 	return s;
 }
 
 #pragma acc routine worker 
 int sum1(int n,float *A)
 {
 	int i;
 	float s=0.0f;
 	#pragma acc loop vector reduction(+:s)
 	for(i=0;i<n;i++){
 		s=s+A[i]+2;
 	}
 	return s;
 }
 ```

 By default, when a function is declared with `#pragma acc routine`, the compiler generates two versions of the function: one for the host and one for the target device. The `bind` clause modifies this behavior by directing the compiler to use the device version of an alternative function—`sum1` in this case—when the function is called within an OpenACC compute region.

 This means that:

 - If the function `sum` is called from host code, the host implementation of `sum` will be invoked.
 - If the same function `sum` is called from within an OpenACC parallel region, the device code for `sum1` will be used instead.

 This mechanism allows for greater flexibility in mapping host-visible API functions to optimized or device-specific versions, facilitating performance tuning or usage of hand-optimized GPU code.

 Additionally, the `bind` clause can reference a CUDA device function, enabling integration with low-level CUDA kernels or library routines when compiling OpenACC code for NVIDIA GPUs.

 Related GCC Files and Functions:

 - `gcc/omp-general.cc`
   - `oacc_build_routine_dims`: Generates attributes for parallelism level.
   - `oacc_verify_routine_clauses`: Verifies and normalizes routine clauses.
 - `gcc/c/c-parser.c`: `c_finish_oacc_routine` calls `oacc_verify_routine_clauses`.
 - `gcc/cp/parser.c`: `cp_finalize_oacc_routine` calls `oacc_verify_routine_clauses`.
 - `gcc/fortran/f95-lang.c` and `trans-decl.c`: Handle OpenACC routine clauses via attribute logic.

 To implement support for the bind clause in GCC:

 - Clause Parsing Integration: Extend the parser to recognize and store the bind clause during front-end processing.
 - Function Binding Mechanism: Add logic to map the host function name to the target device function as specified in the bind clause.
 - Host-Device Code Generation: Study how the host version of the function is generated and invoked. GCC uses two compilers during offloading: one for the host and one for the accelerator. After parsing, the backend expands functions to separate addresses.
 - Linking Investigation: Investigate whether linking affects this mapping. Specifically, study the generation and role of:
   - `.gnu.lto_.offload_table`: IR for declarations from the host compiler.
   - `.gnu.offload_lto_.offload_table`: IR for declarations from the accelerator compiler.

 

 **5. OpenACC** `device_type` **Clause**

 In this section, we first introduce what the `device_type` clause does and highlight its features. We then analyze GCC’s current implementation of similar clauses, outlining a potential approach for implementing `device_type`.

 The `device_type` clause in OpenACC enables developers to fine-tune execution behavior per target architecture (e.g., NVIDIA or AMD GPUs) within the same directive. The allowed clauses following `device_type` differ by directive: for compute constructs (parallel, kernels), valid clauses include `async`, `wait`, `num_gangs`, `num_workers`, and `vector_length`; for loop constructs, valid clauses include `gang`, `worker`, `vector`, `seq`, `independent`, `auto`, and `tile` [1]. There should also be checks for the legality of these inputs. If clauses behave similarly across directives, this would simplify implementation, but the specification does not confirm this uniformly. A manual analysis is required to determine consistent clause behaviors across different constructs.

 Our goal is to design an implementation strategy for `device_type` that generalizes across different constructs, integrating with GCC's modular clause handling system.

 GCC's current implementation of OpenACC clauses is highly modular—many constructs share clause parsing and offloading logic. By tracing the ChangeLog of the `gomp-4_0-branch` and analyzing existing clauses like `num_gangs`, we can understand which macros, clause parsing logic, and backend interfaces need to be added to support the new clause to set values for variables per device. For `diretive_type` , it can get parsed in the front end for C/C++ and Fortran, lowered through AST, GENERIC, and GIMPLE, and values for each device are stored until the backend determines the target. At that point, unrelated clauses can be discarded during expansion. After this filtering, we simply follow the existing logic for setting clause values as seen in other parts of the OpenACC implementation.

 The default values for device-related clauses are not hardcoded. They can be explicitly set by users in directives, overridden by environment variables such as `GOMP_OPENACC_DIM`, or computed dynamically at runtime [11]. For example, in `plugin-nvptx.c`, CUDA driver APIs (like `cuDeviceGetAttribute`) are used to query hardware capabilities—such as the number of registers per multiprocessor, threads per block, and shared memory. These values are then used to compute optimal defaults for execution configuration. By tracing patches that fetch and set these values—such as how `GOMP_OPENACC_DIM` is parsed and applied—we gain insights into how values specified in directives are preserved and utilized throughout the compilation process.

 

## Timeline

 **May 8 – June 1 (Community Bonding Period)**

 - Get to know mentors, read documentation, and familiarize myself with the GCC OpenACC-related codebase and the `libgomp` implementation by tracing ChangeLogs and problem reports, and by exploring the compilation process through debugging with GDB or other recommended tools.
 - Refine the proposed solution and evaluation matrix with my mentor. Clarify the midterm and final evaluation processes.
 - Understand the workflow of building, testing, Git practices, and establish a communication and process management plan.
 - Set up a testing environment with AMD or Nvidia GPU support, and define key testing checkpoints for each subtask.

 **Week 1 (June 2 – 8)**

 - Based on an understanding of the OpenACC directive lowering process, implement support for the `init`, `shutdown`, and `set` directives.
 - Design test cases, and test and debug the functionality of the `init`, `shutdown`, and `set` directives.
 - Investigate OpenACC runtime API routine implementation logic.

 **Week 2 (June 9 – 15)**

 - Implement support for the OpenACC `acc_memcpy_device` runtime API routine.
 - Design test cases, and test and debug the `acc_memcpy_device` routine.

 **Week 3 (June 16 – 23)**

 - Test and debug the previously implemented features.

 **Week 4 – 5 (June 30 – July 6)**

 - Examine the feasibility of the current plan for using GPU prefetching ISA to support the `cache` directive.
 - Add middle-end and backend support for the `cache` directive.
 - Conduct periodic documentation and reflect on the development workflow.
 - Continue testing and bug fixing.
 - For the `cache` directive, in addition to validating correctness, we also need to evaluate performance impacts. This includes measuring potential improvements or regressions introduced by caching behavior. Benchmarks such as SPEC CPU2006, SPEC CPU2017, and STREAM can be used to assess runtime performance and memory throughput under different cache directive configurations. The experiments can take hours to days depending on the benchmark suite and system configuration.

 **Week 6 (July 7 – 13)**

 - Continue debugging and improving stability.
 - Benchmark the `cache` directive.
 - Understand the function binding and linking mechanism in GCC, then detail the implementation pathway for the `bind` clause.

 **Week 7 (July 14 – 18, Midterm Evaluation Deadline: 18:00 UTC)**

 - Summarize development progress and submit the midterm evaluation report.

 **Week 8 – 9 (July 21 – August 3)**

 - Estimate and plan time for testing and evaluation.
 - Extend the parser to recognize and store the `bind` clause during front-end processing.
 - Add logic to map the host function name to the target device function as specified in the `bind` clause.
 - Implement support for the `bind` clause.

 **Week 10 (August 4 – 10)**

 - Analyze whether clauses following the `device_type` clause behave similarly across different directives and implement legality checks.
> - Analyze the implementation logic for `num_gangs`, which involves value setting for devices, to understand which macros, clause parsing logic, and backend interfaces need to be added to support setting variable values per device.

 **Week 11 – 12 (August 11 – 24)**

 - Implement support for the `device_type` clause.
 - Finalize testing and evaluations.
 - Document results and identify areas for enhancement.

 **August 25 – September 1 (Final Submission Deadline: 18:00 UTC)**

 Complete testing, evaluation, and documentation of the project.

 

## About Me

 **Name**: Chenlu Zhang

 **University**: University of Melbourne

 **Personal Email**: [zhanglv0413@gmail.com](mailto:zhanglv0413@gmail.com)

 **University Email**: [chenluz2@student.unimelb.edu.au](mailto:chenluz2@student.unimelb.edu.au)

 **GitHub Page**: https://zcluuuu.github.io/

 **Time Zone**: Melbourne VIC (GMT+11)

 **Residence**: Melbourne, Australia

 **Preferred Language for Communication**: English

 **Skills and Accomplishments**:

 - I previously worked on implementing a GCC optimization prefetching pass for an Alpha-like computer architecture. Evidence of the project is available here: [WIPO Patent Link](https://patentscope.wipo.int/search/en/detail.jsf?docId=CN394162518&_cid=P12-LME6CJ-12597-1)
 - I documented my understanding in a blog post: [Compiler Prefetch Optimization](https://zcluuuu.github.io/compiler/2022/10/01/Compiler-PrefetchOptimization.html)
 - Note: Both documents are originally written in Chinese, and my understanding of compilation is still developing.

 **Interests**: My personal interest lies in bridging the gap between hardware and software. I’m especially interested in understanding how specific hardware designs affect compilation and can help optimize machine code generation. For instance, the latency between registers, cache, and memory directly influences the optimal prefetch distance for each memory hierarchy level.

 

## Appendix

### acc_memcpy_device: Modified Files Overview

 - `libgomp/libgomp.map` declares exported symbols, making `acc_memcpy_device` available for dynamic linking.
 - `libgomp/openacc.h`, `openacc_lib.h`, and `openacc.f90` provide the C/C++ and Fortran interfaces for OpenACC runtime routines.
 - `libgomp/oacc-mem.c` implements the core memory transfer logic and will be extended with a new function for device-to-device transfers.
 - `libgomp/libgomp.h` declares the `gomp_device_descr` structure, where new function hooks for device-to-device copies will be added.
 - `libgomp/target.c` implements low-level support routines like `gomp_device_copy`, and will host the new `gomp_copy_dev2dev` function.
 - `libgomp/oacc-host.c` registers host fallback implementations using `memcpy`.
 - `libgomp/libgomp-plugin.h` defines the standard plugin function prototypes, which will include `GOMP_OFFLOAD_dev2dev`.
 - Plugin source files `libgomp/plugin/plugin-nvptx.c` and `libgomp/plugin/plugin-gcn.c` implement the device-specific logic for NVIDIA and AMD GPUs, respectively. These will be extended to support device-to-device transfers and register the new hook.

### Cache Directive Support: Modified Files Overview

 - `config/nvptx/nvptx.opt`: Define device-related command-line options and corresponding flags.
 - `config/nvptx/nvptx.md`: Define RTL templates.
 - `gcc/params.opt`: Define common command-line options with parameters.
 - `gcc/builtin.def`: Define macros like `BUILT_IN_PREFETCH` and corresponding built-in functions like `__builtin_prefetch()`.
 - `gcc/builtin.c`: Implement functions like `expand_builtin_prefetch()` to support `__builtin_prefetch()` behavior.
 - `gcc/ipa-pure-const.c`: Add `BUILT_IN_PREFETCH` handling in the switch structure of `builtin_safe_for_const_function_p`.
 - `gcc/target-insns.def`: Define RTL template prototypes for built-in operations such as `__builtin_prefetch()`.
 - `gcc/tree-ssa-loop-prefetch.c`: Handle loop-based memory prefetching transformations.

 

## References

 [1] OpenACC Specification: https://www.openacc.org/specification

 [2] OpenACC Host Compiler Compilation Process: https://gcc.gnu.org/wiki/Offloading#Compilation_process

 [3] Improving OpenACC kernels support in GCC: https://gcc.gnu.org/wiki/cauldron2017?action=AttachFile&do=get&target=OpenACC+kernels.pdf

 [4] Issue with acc_memcpy_device: https://forums.developer.nvidia.com/t/issue-with-acc-memcpy-device/135977

 [5] NVIDIA-Kepler-GK110-Architecture-Whitepaper.pdf: https://www.nvidia.com/content/dam/en-zz/Solutions/Data-Center/tesla-product-literature/NVIDIA-Kepler-GK110-GK210-Architecture-Whitepaper.pdf

 [6] Data Prefetch Support: https://gcc.gnu.org/projects/prefetch.html

 [7]  Options That Control Optimization: https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html

 [8] "AMD Instinct MI200" Instruction Set Architecture: https://www.amd.com/content/dam/amd/en/documents/instinct-tech-docs/instruction-set-architectures/instinct-mi200-cdna2-instruction-set-architecture.pdf

 [9] NVIDIA PTX ISA: https://docs.nvidia.com/cuda/pdf/ptx_isa_8.5.pdf

 [10] [openacc] Document GOMP_OPENACC_DIM: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=85129

 [11] [gomp4] adjust num_gangs and add a diagnostic for unsupported num_workers: https://gcc.gnu.org/legacy-ml/gcc-patches/2017-02/msg00834.html

 [12] OpenACC routine bind: https://forums.developer.nvidia.com/t/openacc-routine-bind/133968
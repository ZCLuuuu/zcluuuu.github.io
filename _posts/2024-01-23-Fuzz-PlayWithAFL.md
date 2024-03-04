---
layout: post
title:  "Play with Fuzzers"
categories: [Fuzz]
description: Learn AFL structure by doing exercises from GitHub. Relate it with fuzzing generic algorithm. Compare AFLSmart++, AFLSmart, and AFL.
---

In this post, I first conclude what I learned from each exercises (how they relate to the first paper).

## GitHub exercises (how to use + how it works)

first introduce the abstract workflow, then by doing GitHub exercises, relate concepts with the real world implements. 

### Fuzzer workflow And Dynamic instrumentation workflow

![fuzzerworkflow](C:\Users\11980\Documents\Homepage\zcluuuu.github.io\_posts\images\FuzzerWorkflow.jpg)

![fuzzeralg](C:\Users\11980\Documents\Homepage\zcluuuu.github.io\_posts\images\FuzzerAlg.png)



### Exercise 1 Xpdf

> preparation:  build-essential (compiler,make...)

1. Create workspace

2. Download package of program to be tested

   > wget tar.gz
   >
   > tar -xvfx	

3. Build and install package(set prefix in cmd line to Makefile) (Source code is availalbe:set CC/CXX/LD_LIBRARY_PATH(TODO: extend))(in this stage, AFL not related)

   > preprocess: 
   >
   > 1. seed selection(TODO: what is the diff between seed 123 and corpus)
   > 2. program instrumentation: static+dynamic instrumentation(TODO: figure out what happened here)
   >
   > 

4. Download seed corpus (choose initial test case)

5. Use program under test, feel its function

   > pdftotext inputfile outputfile

6. Use AFL instrumentation to build the PUT(TODO: Learn more about clang/llvm)

7. run the fuzzer(TODO: what did the fuzzer do)

   > 1. cmd line perception and the reason to set it
   >    1. output: how to understand the output directory

8. Reproduce the error

   > 1. find the crash test case under out/crash
   > 2. compile the put(clear afl version and build debug version)
   > 3. bt
   > 4. The PUT comes from real world examples so just check out the 

### Exercise 2 Libexif

TODO: how to debug a PUT with a lib

1. static vs dynamic linking

   > linux ldd: dynamic library
   >
   > During compilation, you specify the static library (usually a `.a` file in Unix-like systems) to the linker. The linker then includes this library's code in the final executable. (in my previous work libc.a libm.a idfference led to efficiency difference bec vldd diff)
   >
   > objdump -d *.a > /tmp/1
   >
   >  Dynamic linking involves linking your program against a shared library (`.so` file in Unix-like systems). Unlike static linking, the library code isn't included in the executable. Instead, the program loads the library at runtime.

2. first install the lib, then install the application

   > include lib share + bin
   >
   > **System Libraries**: The application may still be dynamically linked against system libraries (like libc, libm, etc.) and other dependencies that were not part of the software you built. This is a common scenario since many applications rely on standard system libraries, which are typically available as shared libraries.

![enable-shared=no](C:\Users\11980\Documents\Homepage\zcluuuu.github.io\_posts\images\enable-shared-no-ldd-dynamic.png)

3. instrument the library

   > Getting error: Target binary is not instrumented
   >
   > CC=xxxx ./conf (temp env)

### exercise 4

TODO: how to interpret the lcov report

TODO: why we don't use gdb in asan? why we just let it run

## Questions (about research interest)

Why and how AFL could be applied to web application (stateful )



## Reflection

1. Paper reading: add questions to notes will help speed up
2. Clear how to visualize this week's work: write post and decide catalogue

## Log

1. waste time on env (install afl and ide manually in ubuntu, actually docker and gdb is enough)
2. kept the fuzzer running and dealt with unimelb cloud service, after communicating with wentao, I realized that I can interupt the fuzzer after first clash appeared
3. would like to read the source code of afl and then know each directory's main purpose
4. 
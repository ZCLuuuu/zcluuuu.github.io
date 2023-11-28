---
layout: post
title:  "Operator Applications [CPP]"
categories: [C++]
description: Those confusing stuff.
---

* TOC
{:toc}

## Member Access Operators
One of the most confusing operators families are the member access operators:
- subscript `[]`
- indirection `*`
- address-of `&`
- member-of-object `.`
- member-of-pointer `->`
It's often confused which operators are suitable to use. Fortunately, compilers and IDE are very good at telling the types and largely ease the pain. 

## Manual Memory Management by Operators
One way to manually manage *free store* (which is also known as *heap* in CPP, but I don't really like this ambiguous name) is to overload the operator `new`.

### Motivation
Each time program invokes `new` , what it actually happens is CPP asks the OS to allocate a new free store in memory (`HeapAlloc` on Windows or `malloc` on Unix). In some settings, free store allocations simply involve too much latency - i.e. high-frequency trading so one may want to avoid it. A general way to do this is to allocate a big space on the launch of the program and then allocate to variables who need storage. 

### Memory Fragmentation and Buckets
Manage the memory is a surprisingly complicated task. One of the issue is *Memory Fragmentation*. Memory fragmentation is a problem when the allocation and deallocation of blocks of memory lead to a state where available memory is divided into small, disjoint segments, which are not able to be allocate to a large object even if the capacity of them is enough.
![Memory Fragmentation](https://upload.wikimedia.org/wikipedia/commons/thumb/4/4a/External_Fragmentation.svg/2560px-External_Fragmentation.svg.png)
<center>Memory Fragmentation, From Wikipedia</center>

One way to tackle it is to chop memory into *buckets*, which are fixe-sized blocks in memory. The OS will not allocate memory fewer than the size of a bucket.  This scheme prevents memory fragmentation to some extent, but with an overhead with possible(and very likely) waste of memory.

### Free Store Operators
There are four operators that are needed to be overload to implement manual memory management:
```cpp
void* operator new(size_t);
void operator delete(void*);
void* operator new[](size_t);
void operator delete(void*);
```
Note that the return type of `new` and the parameter type of `delete` is  `void*`. It means that the free store operators deal in raw, uninitialized memory.
```cpp
include <cstddef>
#include <new>

struct Bucket {
  const static size_t data_size{ 4096 };
  std::byte data[data_size];
};

struct Heap {
  void* allocate(size_t bytes) {
    if(bytes > Bucket::data_size)
      throw std::bad_alloc();
    for(size_t i{}; i < n_heap_buckets; i++) {
      if(!bucket_used[i]) {
        bucket_used[i] = true; // 6
        return buckets[i].data;
      }
    }
    throw std::bad_alloc();
  }

  void free(void* p) {
    for(size_t i{}; i < n_heap_buckets; i++) {
      if(buckets[i].data == p) {
        bucket_used[i] = false; // 7
        return;
      }
    }
  }
  static const size_t n_heap_buckets{ 10 }; // 4
  Bucket buckets[n_heap_buckets]{};
  bool bucket_used[n_heap_buckets]{}; // 5
};

Heap heap; // 1

void* operator new(size_t n_bytes) { // 2
  return heap.allocate(n_bytes);
}

void operator delete(void* p) { // 3
  return heap.free(p);
}
```
Line 1 create the heap at the namespace scope. Its lifetime begins when the program starts. Line 2 and 3 overloads the `new` and `delete` operators in the namespace; Now if one use `new` and `delete`, dynamic memory management will use `heap` instead. In `heap`, the memory is chop into 10 buckets (line 4). The information whether the bucket is allocated is recorded in an array of `bool` (line 5 6 7). 

The other parts of the program can use the pre-allocated memory of `heap` by using the `new` and `delete` operators now. When there is no free bucket left, `heap` can tells the main program by the `std::bad_alloc` exceptions.
```cpp
int main() {
  printf("Buckets:   %p\n", heap.buckets);
  auto breakfast = new unsigned int{ 0xC0FFEE };
  auto dinner = new unsigned int{ 0xDEADBEEF };
  printf("Breakfast: %p 0x%x\n", breakfast, *breakfast);
  printf("Dinner:    %p 0x%x\n", dinner, *dinner);
  delete breakfast;
  delete dinner;
  try {
    while(true) {
      new char;
      printf("Allocated a char.\n");
    }
  } catch(const std::bad_alloc&) {
    printf("std::bad_alloc caught.\n");
  }
}

```

### Placement Operators
Another interesting set of operators that can manage memory is the *Placement Operators*.
```cpp
void* operator new(size_t, void*);
void operator delete(size_t, void*);
void* operator new[](size_t, void*);
void operator delete[](size_t, void*);
```
Although they are similar to free store operators, placement operators are used to construct objects in arbitrary memory. 
```cpp
#include <iostream>
#include <new>  // Required for placement new

class MyClass {
public:
    MyClass(const char* tag) {
        strcpy_s(this->tag, tag);
        this->tag[strlen(tag)] = 0;
        std::cout << this->tag << ":Constructor of MyClass called." << std::endl;
    }
    ~MyClass() {
        std::cout << this->tag << ":Destructor of MyClass called." << std::endl;
    }
private:
    char tag[3]{};
};

int main() {
    const auto classSize = sizeof(MyClass);
    // Allocate a buffer to store 3 objects
    char buffer[3 * classSize];

    // Construct objects in the buffer
    MyClass* myObject1 = new (&buffer) MyClass("o1");
    MyClass* myObject2 = new (&buffer[classSize]) MyClass("o2");
    MyClass* myObject3 = new (&buffer[classSize * 2]) MyClass("o3");

    // deallocate the memory
    myObject2->~MyClass();
    myObject3->~MyClass();
    myObject1->~MyClass();
    return 0;
}
```
In this example, we use placement operators to construct objects in the buffer which is allocated at the beginning of the program. To de-allocate the memory, programmers must call the object's destructor directly and exactly once. The output shows 
```plain
o1:Constructor of MyClass called.
o2:Constructor of MyClass called.
o3:Constructor of MyClass called.
o2:Destructor of MyClass called.
o3:Destructor of MyClass called.
o1:Destructor of MyClass called.
```

## Precedence and Evaluation Order
A fact: CPP language standard explicitly defines the precedence of operators (e.g. In the expression `a + b*c`, the product operator has higher precedence than the sum operator), but **it does not define the evaluation order**. This is because the language wants to give compiler writers to find clever optimization opportunities.

For example:
```cpp
stop() + drop() * roll()
```
It is not guaranteed that the evaluation order is : `drop()`, `roll()`, `stop()`. 

Some exceptions are:
- `a && b` and `a || b` guarantees that a evaluate before b.
- `a ? b :c` guarantees that a evaluate before b and c
- `a,b,c` guarantees that the order is a, then b, then c.

## Type Conversions
Operators often involve type conversions in CPP. And unfortunately, CPP is overzealous to do conversions implicitly. It's not a good idea and programmers should pay attention to it.

### Integer Promotion
Integer promotion refers to the process when a smaller integer (such as `char`, `short`, and in some cases `bool`) encounters an operator that evaluate outside its range, then it is "promoted" to a larger integer type. 
```cpp
char a = 10;
char b = 20;
auto result = a * b;
std::cout << "Type of result: " << typeid(result).name() << std::endl; 
// Type of result: int
```

### Silent Truncation
When a number is assigned to a variable which cannot represent it, it be will *silently truncated*. 
```cpp
#include <cstdint>
#include <cstdio>

int main() {
  // 0b111111111 = 511
  uint8_t x = 0b111111111; // 255
  int8_t y = 0b111111111; // Implementation defined.
  printf("x: %u\ny: %d", x, y);
}
```
- If the destination is `unsigned`, the result is as many bits as it can fits.
- If the destination is `signed`, the result is undefined.

### Conversion to bool
Pointers, integers and float-point numbers can be implicitly converted to bool. The conversion is `true` is the value is nonzero.

### Pointers to `void*`
Pointers can always be implicitly converted to `void*`.

### Explicit Type Conversion
Braced Initialization ensures that only safe conversions are allowed. This is why modern CPP prefers braced initialization. 
```cpp
int main() {
  int32_t a = 100;
  int64_t b{ a };
  if(a == b)
    printf("Non-narrowing conversion!\n");
  int32_t c{ b }; // Bang!
}
```
In this situation, *explicit type conversions* are needed. 

One way is *C-Style Casts*, which is dangerous and not recommended. You need to ensure what is in the memory and what's the behaviour of a specific compiler.
```cpp
void trainwreck(const char* read_only) {
  auto as_unsigned = (unsigned char*)read_only;
}
```

A more civil way is to use `reinterpret_cast` or `static_cast`
```cpp
int* ptr = new int(10);
char* chPtr = reinterpret_cast<char*>(ptr);

double d = 10.5;
int i = static_cast<int>(d);
```
The `reinterpret_cast` is used for low-level reinterpreting of the bit pattern of an object, while `static_cast` performs conversions according to the language's conversion rules and is safer in comparison.

To use `static_cast` in user-defined class, one needs to implement *User-Defined Type Conversion*:
```cpp
class Celsius {
    float temp;

public:
    Celsius(float t) : temp(t) {}
    // Conversion operator to convert Celsius to Fahrenheit
    operator float() const {
        return temp * 1.8f + 32;
    }
};

int main() {
    Celsius degree_c{ 26.0 };
    auto degree_f = static_cast<float>(degree_c);
    printf("Degree Fahrenheit: %f", degree_f);
}
```
In this example, class `Celsius` defines a conversion to float Fahrenheit and the program employs `static_cast` to perform casting.

## Summary

This article discussed 2 topics: memory management and type conversions, which are great examples of how operators are used in modern CPP.
---
layout: post
title:  "Types and References in CPP"
categories: [C++]
description: Data Type, Pointers, Addresses and Object initialization
---

## Types
### The `size_t` type
Use the `size_t` type to encode size of objects. It is guaranteed to store the maximum size of objects getting by `sizeof` operator.

```cpp
#include <cstddef>
#include <cstdio>

size_t size_c = sizeof(char);
```
`size_t` lives in `<cstddef>`.

Usage: get number of elements in an array
```cpp
short array[] = { 104, 105, 32 };
size_t n_elements = sizeof(array) / sizeof(short);
```
### Class & Struct
* The main difference between a class and a struct is the default access level.  Class is `private` by default while a struct is `public` by default.
* Structs are called PODs (plain old data) by some programmers.

### Initialization
These 4 methods are initialize variables to 0.

```cpp
int a = 0;
int b{};
int c = {};
int d; // maybe
```
Using braces `{}` is called *braced initialization*, which is a C++ standard. An equal symbol is not required and should be avoided by modern C++ community.
```cpp
struct PodStruct {
	uint64_t a;
	char b[256];
	bool c;
};

int main() {
	PodStruct initialized_pod{ 42, "hello" };
}
```
A fully featured class is *always initialized*, which is to make sure there is at least a default constructor. 
The reason why parentheses initialization `()` is the syntax has ambiguous grammar (overlapped with function declaration).
```cpp
struct Taxonomist { --snip-- };

int main() {
	Taxonomist t8(); // might not be parsed as initialization
}
```
Narrowing Conversions is not allowed in braced initialization, which is another nice feature.
A general rule: **use braced initializer everywhere**. (except for some C++ stdlib)

The *member Initializer Lists* grammar is the primary mechanism for initializing class members 
```cpp
struct Avout {
	const char* name;
	long apert;

	Avout(const char* name, long year_of_apert)
		: name{ name }, apert{ year_of_apert } {
	}
	void announce() const {
		printf("My name is %s and my next apert is %d.\n", name, apert);
	}
}
```
Member initialization execute before the constructor's body. This design simplifies the extra trivial work and ensures validity of all members before constructor executes.
## Reference
### Address and Pointers

An address in x86 is 4 bytes (32-bit), while in x86 is 8 bytes (64-bits) 
The *address space layout randomization* design by OSs guarantees the address `&` get each time is random.
Use `&` to get address, but dereference operator, the pointer declaration, and multiplication all use asterisks `*`. Shit language designs.
Modern C++ recommends using member-of-pointer operator (`->`) to dereference and access a member, that is to say, these 2 lines are of same effects:
```cpp
ClockOfTheLongNow* clock_ptr = &clock;

clock_ptr->get_year(); // 1
(*clock_ptr*).get_year(); // 2
```
C++ has a feature: an array can *decay* to a pointer.
```cpp
#include <cstdio>

struct College {
	char name[256];
};

void print_name(College* college_ptr) {
	printf("%s College\n", college_ptr->name);
}

int main() {
	College best_colleges[] = { "unimelb", "RMIT", "Monash" };
	print_name(best_colleges);
}
```
This feature is quite dangerous because I expected a point of class `College`, but an array can be passed as the parameter. To avoid ambiguousness, it is a convention to use 2 arguments for an array argument: one pointer for the array, one for the array length.

C++ allows *pointer arithmetic*, which makes pointers to be dangerous. Move pointer to access unassigned memory will cause *undefined behaviour*.

```cpp
char lower[] = "abc?e";
*(lower + 7) = 'g'; // buffer overflow
```

### Special Pointers
- *void pointer* `void*` for irrelevant pointed-to type situation. Pointer arithmetic and dereference is forbidden for void pointers. 
- `std::byte` pointer use to interact with raw memory. Examples include copying raw data, encryptions.
- `nullptr` is a special literal that indicates point to nothing. there is an implicit conversion from pointers to bool. Pointers that is not `nullptr`  can be converted to `true`.

### Reference
References are generally safer than pointers. They cannot be assigned to null, and cannot be `reseated`.
```cpp
void add_year(ClockOfTheLongNow& clock) { // pass by reference 
	clock.set_year(clock.get_year() + 1);  // No deref operator needed 
}
```
Note that the difference between *passing by reference* and *passing by value* still applies even the argument is an object of a class in C++.

### Use of Pointers and References
- Pointers are flexible, and can be reassigned. In many applications like linked list it is necessary to use pointers.
- Otherwise, use reference as much as possible. 

### Const correctness
The keyword `cost` roughly means "I promise not to modify". And it's a good tool while using pointers.
const parameter prevents modifying pointed-to. 
```cpp
void petruchio(const char* shrew) { 
	printf("Fear not, sweet wench, they shall not touch thee, %s.",shrew); 
	shrew[0] = "K";  // Compiler error! The shrew cannot be tamed. 
}
```
const (member) methods prevent the function modifying 

### type `auto`
The compiler can do some induction for type automatically.  Not something really impressive though. As a general rule, use auto always.

```cpp
auto the_answer { 42 }; // int 
auto foot { 12L }; // long 
auto rootbeer { 5.0F }; 
auto cheese { "string" }; // char[7]

auto year { 2019 }; // int 
auto& year_ref = year;
```
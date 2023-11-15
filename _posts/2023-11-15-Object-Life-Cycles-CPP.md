---
layout: post
title:  "Object Life Cycles in CPP"
categories: [C++]
description: "Principals of objects life cycle; good practice: exceptions, RAII, copy and move operations"
---

## Memory Storage Duration
Every object need storage. 
- *allocation*: Reserve storage for objects 
- *deallocation*: release the object's storage
- *storage duration*: the duration between allocation and deallocation
- *lifetime*: bound by the storage duration. begins once its constructor complete. ends before a destructor invoked. 

### Automatic Storage Duration
*Local variables* is allocated at the beginning of an enclosing code block, and its deallocated at the end of the block. Regular variables and function parameters are local variables.
### Static Storage Duration
*Static variables* is allocated at namespace scope, being allocated when the program starts and deallocated when the program stops Their storage duration is called *static storage duration*.
The most common static variables are declared using `static` or `extern` keywords at root scope. The feature of `extern` is that it can be accessed by other *translation units*.
```cpp
static int rat_things_power = 200;

int main() {
 //...
}
```
Local static variables can only be accessed in a function scope, but their lifetimes begin once the first invocation.
```cpp
void func() {
	static int power = 200; // A local static variable
}
```
*Static members* are very similar to static variables but only need to use the scope resolution operator `::` to access them.
*Thread-local variables* have thread storage duration, which simply indicates each thread has its own copy of a variable. Any variables with *static storage duration* can be make thread-local by adding `thread_local` keywords. This design makes multi-thread programming much safer.
```cpp
void func() {
	static thread_local int power = 200; // A local static variable
}
```
### Dynamic Storage Duration
A *new expression* allocates a dynamic object and returns the address of that variable at the run time. The way to deallocate them is to use `delete`.
```cpp
int* my_int_ptr = new int;

//...

delete my_int_ptr;
```
Note that the value contained in memory where deleted object resided is undefined. Some compilers will not erase the memory for performance sake. Programmers have to implement a custom destructor to zero out sensitive information. 
Programmers also need to make sure that dynamic objects that allocated are also deallocated. A *memory leak* is a failure that the memory is no longer needed but the isn't released by the program.
## Normal Object Life Cycle
1. static global variable constructed
2. thread-local variable constructed
3. local variable constructed
4. dynamic variable constructed
5. local variable destructed
6. thread-local variable destructed
7. static global variable destructed

## Exceptions
One way to jump out of normal object life cycle is to use exceptions. When an exception is thrown, it's *in flight*. When there is an in flight exception, the program stops normal execution and search for an exception handler. Objects fall out of scope are destroyed immediately. 
The grammar of throwing exceptions and handling exceptions have nothing unique comparing to other languages.  There is only one thing need to note that the recommended exception is `std::runtime_error` which is declared in `stdexcept.h`, along with other standard exception classes.
```cpp
#include <stdexcept>

void forget(int x) {
	if(x <= 0) {
		throw std::runtime_error("x should be no less than 0")
	}
	printf("Forgot 0x%x\n", x)
}

int main() {
	try{
		forget(3);
		forget(0); // exception here
		forget(2); // not being execute
	} catch (const std::runtime_error* e) {
		printf(e.what());
	}
}
```
Error messages, call stack frame are expected to be find in an exception. Re-throw an exception is allowed in C++ as well.
### `noexcept` keyword
A function marked `noexcept` makes a rigid contract that there is guaranteed to be no exception happened.
```cpp
bool is_odd(int x) noexcept {
	return 1 == (x % 2);
}
```
But the compiler will not check for your implementation. If there is an exception within a function marked `noexcept`, the program will abort immediately, cannot being recovered.
### Throwing in destructors
There is an interesting case of exception throwing - destructor exception.
```cpp
struct CyberdyneSeries800 {
  CyberdyneSeries800() {
    printf("I'm a friend of Sarah Connor.");
  }
  ~CyberdyneSeries800() {
    throw std::runtime_error{ "I'll be back." };
  }
};

int main() {
  try {
    CyberdyneSeries800 t800;
    throw std::runtime_error{ "Come with me if you want to live." };
  } catch(const std::exception& e) {
    printf("Caught exception: %s\n", e.what());
  }
}
```
By the rules of exception, an *in flight* exception will cause the objects within the original scope being destroyed. But the destructor throws an exception again. How can runtime handle 2 in flight exceptions? The answer is it can't - just abort. 
### Exceptions vs Error Codes
A well accepted pattern is to only use exceptions when **errors cannot be handled locally**. On the other hand, if the error **can be dealt with locally** or is **expected to happen** by some probabilities, generally return an error code.
### Exception and Performance
> Use of exception handling leads to programs that are faster when they execute normally
> -- *Optimized C++* 

Using exceptions to handle errors are elegant but sometimes slower than alternative approaches (Those commonly used in C or legacy C++), but one make huge gains in robustness and maintainability by employ exceptions. It's only when an exception is thrown that you pay overhead.
## Object Life Cycle in Action - `SimpleString`
The `SimpleString` class is a basic model that combines resource managing and usage of exceptions:

```cpp
#include <cstdio>
#include <cstring>
#include <stdexcept>

struct SimpleString {
  SimpleString(size_t max_size)
      : max_size{ max_size }
      , length{} {
    if(max_size == 0) {
      throw std::runtime_error{ "Max size must be at least 1." };
    }
    buffer = new char[max_size];
    buffer[0] = 0;
  }
  ~SimpleString() {
    delete[] buffer;
  }
  void print(const char* tag) const {
    printf("%s: %s", tag, buffer);
  }
  bool append_line(const char* x) {
    const auto x_len = strlen(x);
    if(x_len + length + 2 > max_size)
      return false;
    strncpy(buffer + length, x, max_size - length);
    length += x_len;
    buffer[length++] = '\n';
    buffer[length] = 0;
    return true;
  }

  private:
  size_t max_size;
  char* buffer;
  size_t length;
};
```
### RAII
As the the constructor and destructor shows, resources (dynamic memory storage) is managed by the lifecycle of object. The design pattern is recognized as *resource acquisition is initialization* or *RAII* in modern C++.

For example, there is another class `SimpleStringOwner` that employs `SimpleString`:
```cpp
struct SimpleStringOwner {
  SimpleStringOwner(const char* x)
      : string{ 10 } {
    if(!string.append_line(x)) {
      throw std::runtime_error{ "Not enough memory!" };
    }
    string.print("Constructed");
  }
  ~SimpleStringOwner() {
    string.print("About to destroy");
  }

  private:
  SimpleString string;
};
```
The implementation of `SimpleStringOwner` does not need to take care of the storage resource using by `SimpleString` since it follows the RAII pattern. 

Another benefit of RAII is that if any exception is thrown, RAII objects in the original scope are destroyed so that the related resources are released. 

Note that **members are constructed before the enclosing object's constructor**, and **destroyed after the object's destructor is invoked**.
### String Manipulate
* `strlen` is used to get the length of a string.
* `strncpy` copy a string to a destination. Note that this function need to be used very careful. Wrong uses including forgetting the *null-terminator* in the source string, not enough space for destination string all lead to undefined behaviours. 
	```cpp
	char *strncpy(char *dest, const char *src, size_t n);
	```
- The program manually maintain a `\0` at the end of the string. Though it is easy to implement but many programmers simply forget. 

### Exceptions and Error Code
The `SimpleString` class throws `runtime_error` when there is no enough buffer in the constructor, while use error code in `append_line` function to indicate if the operations are executed successfully.  This design is idiomatic in CPP: In the former one, the error cannot be handled locally (The constructor cannot know why it is invoked with 0 space), On the other hand, the later can handles error properly.

## Copy Semantics
In C++, a copy happens when 
* An `=` symbol is used (copy assignment)
* A copy constructor is called:
	* Explicitly invoke the copy constructor
	* A function with *pass-by-value* parameter is invoked. 
	* A function with *pass-by-value* return-value is finished.

By default, C++ makes copies by *member-wise clone*, which means each member gets copied into its corresponding destination.  
```cpp
struct Point { int x, y; };

Point make_transpose(Point p) { // copy the point p
	int tmp = p.x;
	p.x = p.y;
	p.y = p.x;
	return p; // copy again
}

int main(){
	Point a{ 1, 2 };
	Point b{ 3, 4 };
	Point c = make_transpose(b);
	b=a; // explicitly copy
}
```

For fundamental and POD types (Plain Old Data, such as the `Point` class), the copy is straightforward and generally safe. But for those class which has related resources, this default copy semantic is dangerous. Take the `SimpleString` class as an example:
```cpp
int main(){
	SimpleString a {"Hello Mate"};
	SimpleString b {"Good day"};
	b = a; // copy a
}
```
Remember that the `char* buffer` member in `SimpleString` is referred to an address at dynamic storage. Now `a` and `b` have the exactly same `buffer` member that points to the same space. When one of them is destructed, `buffer` will be freed. If the another attempts to read or write to it, you'll have undefined behaviour! This error is commonly called *use after free*. Similarly, an another error is *double free*.

As talked in the beginning, there are 2 ways to customize copy semantics. The first one is the *copy constructor*, which creates a copy and assign it to a brand-new object:
```cpp
struct SimpleString{
	SimpleString(const SimpleString& other) // copy constructor
	    : max_size{ other.max_size }
	    , buffer{ new char[other.max_size] } // make a new space
	    , length{ other.length } {
	  std::strncpy(buffer, other.buffer, max_size); // copy original value
	}
}
```
The second one is the copy operator `=`
```cpp
struct SimpleString{
	SimpleString& operator=(const SimpleString& other) {
	  if(this == &other)
	    return *this;
	  const auto new_buffer = new char[other.max_size]; //allocate new resource
	  delete[] buffer; // free orignal resource
	  buffer = new_buffer;
	  length = other.length;
	  max_size = other.max_size;
	  std::strncpy(buffer, other.buffer, max_size); // make copy
	  return *this;
	}
}
```
It is recommend that programmers should explicitly define the copy assignment operator and the copy constructor **for every class that owns a resource**. If no custom behaviour is needed, one can use `default` keyword.
```cpp
struct Point {
  int x, y;

  Point(const Point& other) = default;
  Point& operator = (const Point& other) = default;
};
```
Another useful keyword is `delete` which tells the compiler to suppress the copy behaviours. Many resources including a network connection or a file should be designed to not allowed to be copied.
When implementing copy semantics, following criteria helps:
- **Correctness**: make sure the copy is in a legal state (class invariants)
- **Independence**: original and copy shouldn't change each other's state during modification
- **Equivalence**: The original and the copy should be the same.

### Move instead of Copy
At the semantic level, a copy is to make an equivalent, independent copy of original object, while move is to *transfer ownership* of resources from one object to another. The main reason for using move is to avoid the cost of copy.
After the move, the original object should be put in a special state called the *move-from state*, which only allows 2 operations: reassign or destruct. In consequence, the class invariants aren't satisfied in this state. Thus, move is quite dangerous.

at the implementation level, The *move constructors* distinguish them from the copy constructors by taking *rvalue reference*.
```cpp
SimpleString(SimpleString&& other) noexcept
    : max_size(other.max_size)
    , buffer(other.buffer)
    , length(other.length) {
  other.length = 0;
  other.buffer = nullptr;
  other.max_size = 0;
}
```
This example shows that the move constructor just copy the pointer to the storage, then assign the original object to be at the *copied-from* state: assign buffer pointer to `nullptr`, and reset other members to 0.

Note that the move constructor only takes right value. This is a safeguard that prevents program accidently perform a move. The only way to convert a lvalue to a rvalue is to use `std::move` (from \<utility\> header)
```cpp
int main() {
  SimpleString a{ 50 };
  a.append_line("We apologise for the inconvenience");
  a.print("a");
  SimpleString b{ std::move(a) }; // use the move constructor
  b.print("b");
  a.print("a"); // a is empty
}
// a: We apologise for the inconvenience
// b: We apologise for the inconvenience
// a: (null)
```
Note that the `std::move` only convert a left value to a right value.(Another shit naming from the legacy C++ designs. They should really name it `std:rvalue`). This example shows only the copy constructor is invoked on lvalue only when programmers explicitly use `std::move`. 

Similarly, we can have *move assignment* instead of *copy assignment*. The difference is also that move assignment takes rvalue.
```cpp
SimpleString& operator=(SimpleString&& other) {...}
```

### Compiler-Generated Methods
The compiler generate these 5 methods by default:
- the destructor
- the copy constructor
- the move constructor
- the copy assignment
- the move assignment
But the auto generated results are not guaranteed to work well. To eliminate this implicit complexity, setting them to `default` or `delete` if the operation is not allowed is a good idea.
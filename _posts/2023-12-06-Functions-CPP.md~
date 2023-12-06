---
layout: post
title:  "CPP Functions"
categories: [C++]
description: As functions are the most common structure in a program, it's worth a visit to it. 
---

* TOC
{:toc}
There are many gadgets playing with functions in CPP. As functions are the most common structure in a program, it's worth a visit to it. 

## Function Declarations
Function declarations have the following familiar form:
```plain
prefix return-type func-name(arguments) suffix;
```

There are two types of *modifiers* to functions, which alter a function's behavior in some ways. But there isn't a clear standard why certain modifiers appear as prefixes or suffixes. I believe it's just another historical burden of CPP. 

### Prefix Modifiers

|Name|Meaning|
|--|--|
|`static`|The function isn't a member of a class.|
|`virtual`|The method can be overridden.|
|`override`|The method is intended to override a virtual method.|
|`constexpr`|The function should be evaluated at compile time.|
|`[[noreturn]]` \*|The function won't return for optimization.|
|`inline` \*|Inline the function for optimization.|

- The modifier `[[noreturn]]` is not the same with return type `void`, but with control flow not return to the caller anymore. e.g. a function that exits or loop forever. 
- The modifier `inline` tells the compiler to inline the function, which means there is no cost for function call procedure (place arguments in call stack - jump and call - jump back when done). The size of binary would increase as the function code is not reusable anymore.    

### Suffix Modifiers

|Name|Meaning|
|--|--|
|`noexcept`|The function never throw an exception.|
|`const`|The function wouldn't modify an instance of its class.|
|`final`\*|The function cannot be overridden.|
|`volatile`\*|A method can be invoked on volatile objects|

- The difference between `virtual`, `final` and default (no such two modifiers)
	- `virtual` methods are invoked by object types
	- methods by default, are invoked by reference types
	- `final` methods give error when you try to declare a same name method in child class. The `final` modifier encourage the compiler to perform a type of optimization called `devirtualization`.
- If an object is `volatile`, the compiler must treat all accesses to it as visible side effects. It roughly means no optimization (e.g. re-order) applied.

### Automatic Return Type
Return types can be `auto`. But it's mainly used in templates as a regular function should provide return type for readability. 

When `auto` is used in the return type of template functions, it can be paired with a `decltype` expression.

```cpp
template <typename X, typename Y>
auto add(X x, Y y) -> decltype(x + y) {
  return x + y;
}

int main() {
  auto my_double = add(100., -10);
  printf("decltype(double + int) = double; %f\n", my_double);

  auto my_uint = add(100U, -20);
  printf("decltype(uint + int) = uint; %u\n", my_uint);

  auto my_ulonglong = add(char{ 100 }, 54'999'900ull);
  printf("decltype(char + ulonglong) = ulonglong; %llu\n", my_ulonglong);
}

```
### Overload Resolution
*Overload resolution* is the process that the compiler executes when matching a function invocation with a proper implementation by the function declaration.
1. The compiler will look for an exact type match.
2. The compiler will try to use built-in promotion rules (e.g. `int` to `long`) to find a match.
3. The compiler will try to use user-defined type conversion to find a match
4. The compiler will look for a variadic function.

## Variadic Functions
A variadic function can take a undetermined number of parameters. A canonical example is the function `printf`, which accepts any number of parameters.

You declare variadic functions by placing `...` as the final parameter. To access variadic parameters, it is needed to use `<cstdarg>`.

```cpp
#include <cstdarg>

int sum(size_t n, ...) {
  va_list args;
  va_start(args, n);
  int result{};
  while(n--) {
    auto next_element = va_arg(args, int);
    result += next_element;
  }
  va_end(args);
  return result;
}

int main() {
  printf("The answer is %d.", sum(6, 2, 4, 6, 8, 10, 12));
}
```

Note that variadic arguments are not type-safe, and the number of elements must be tracked separately. These two facts make this language feature not that attractive.  A more interesting usage of variadic arguments is in templates. 

### Variadic Templates
A classic example of variadic is the function `sum`, which calculates a list of numbers. The template `sum` absorbs the first argument, then pack the reminder into `args`. It halts until there is only one argument left. This trick is called *compile-time recursion*.

```cpp
template <typename T>
constexpr T sum(T x) {
  return x;
}

template <typename T, typename... Args>
constexpr T sum(T x, Args... args) {
  return x + sum(args...);
}

int main() {
  printf("The answer is %d.", sum(2, 4, 6, 8, 10, 12));
}

```

There are two advantages for variadic template over regular variadic functions:
- You can use `sizeof(args)` to obtain the parameter pack's size.
- You can invoke a function with `...` to expands the parameter pack.

## Function Pointers
In *functional programming*, one major concept is to pass a function as a parameter to another function. It can be done with function pointers in C++.

Unfortunately, the grammar for function pointers are extremely ugly. 
```cpp
float add(float a, int b) {
  return a + b;
}

float subtract(float a, int b) {
  return a - b;
}

int main() {
  const float first{ 100 };
  const int second{ 20 };

  float (*operation)(float, int){}; // a function pointer
  
  operation = &add;
  printf("%g + %d = %g\n", first, second, operation(first, second));

  operation = &subtract;
  printf("%g - %d = %g\n", first, second, operation(first, second));
}
```

As a result, it is encouraged to use type aliases to program with function pointers.
```cpp
using operation_func = float(*)(float, int);
```

### `std::function`
A more modern generic function pointer is the `std::function` template. 
```plain
std::function<return-type(arg-type-1, arg-type-2, etc.)>
```

## Function Objects
A user-defined type can be made invocable by implementing the function-call operator `operator()()`. Accordingly, an object with function-call operator is called *function object*.

An interesting example follows:
```cpp
struct CountIf {
  CountIf(char x) : x{ x } {}
  
  size_t operator()(const char* str) const {
    size_t index{}, result{};
    while(str[index]) {
      if(str[index] == x)
        result++;
      index++;
    }
    return result;
  }

  private:
  const char x;
};

int main() {
  CountIf s_counter{ 's' }; // count how many 's' are there in a string.
  auto sally = s_counter("Sally sells seashells by the seashore.");
}
```

The example is actually a practice for *partial applications*, which is yet another important concept in functional programming. 

Apart from partial applications, function-call operators are commonly used in `std` libraries as well.

## Lambda Expressions
A more fancy and modern way to write functions is the *lambda expressions*. I am glad that CPP is willing to adapt more functional programming styles. The syntax for lambda expression is 
```plain
[captures] (parameters) modifiers -> return-type {body}
```
Only captures and the body are required.

Each lambda expression has a direct analogue in a function object. Especially, the member variables in a function object are analogous to a lambda's capture. Thus, there is no additional functionality for lambda expression comparing to old-fashioned ways, but it only provides aesthetics. 

This example defines the famous higher-order function [fold](https://en.wikipedia.org/wiki/Fold_(higher-order_function)), which is also called `reduce` in many other languages. The function `fold` describes a process that apply a combining operation on a list. 
```cpp
#include<cstdio>

template<typename Fn, typename In, typename Out>
constexpr Out fold(Fn function, In* input, size_t length, Out initial)
{
	auto accumulation = initial;
	for (size_t i = 0; i < length; i++)
	{
		accumulation = function(input[i], accumulation);
	}
	return accumulation;
}

int main() {
	int data[]{ 100, 200, 300, 400, 500 };
	size_t data_len = 5;
	auto sum = fold([](auto x, auto y) { return x + y; }, data, data_len, 0);
	printf("Sum: %d\n", sum);

	auto maximum = fold([](auto x, auto y) { return x > y ? x : y; }, data, data_len, 0);
	printf("Maximum: %d\n", maximum);

	auto numOfG200 = fold([](auto x, auto y) { return x > 200 ? y + 1 : y; }, data, data_len, 0);
	printf("Number of Elements greater than 200: %d\n", numOfG200);
}
```
By define different types of lambda expression, we make use of `fold` for different purposes: calculating the sum, the maximum and counting the number of elements greater than 200. It is easy to comprehend the elegant of lambdas for its readability and succinctness.

## Summary
The topics we mentioned are:
- Function declarations, including modifiers and  overload resolution
- Variadic functions
- Function Pointers
- Function objects and lambda expressions.
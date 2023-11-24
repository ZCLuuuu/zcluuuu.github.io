---
layout: post
title:  "Templates in CPP"
categories: [C++]
description: Templates, Concepts and Polymorphism
---

* TOC
{:toc}

If name only one most distinctive feature of CPP, I would probably say **Compile-time Polymorphism**, that is, the use of **templates**. Although there are many junks in the language, but the designers of CPP did a great job devising templates.  

## Basic Usage of Templates
A template is a **class** or **function** with **template parameters**, which can stand in for any types. The basic idea of template is that, rather than copy and paste similar classes and functions, you just need to write a single template, and the **compiler generates new instances** when it encounters a new combination of types. Therefore, the process of **instantiations** are executed in the **compiling stage**, instead of runtime stage.

### Template Functions
The function `mean` compute the average value of an array of items. To accommodate different types (int, long, double...), it employs a template parameter `T`.
```cpp
template <typename T>
T mean(const T* values, size_t length) {
  T result{};
  for(size_t i{}; i < length; i++) {
    result += values[i];
  }
  return result / length;
}
```
The usage of `mean`:
```cpp
int main() {
  const double nums_d[]{ 1.0, 2.0, 3.0, 4.0 };
  const auto result1 = mean<double>(nums_d, 4);
  printf("double: %f\n", result1);

  const float nums_f[]{ 1.0f, 2.0f, 3.0f, 4.0f };
  const auto result2 = mean<float>(nums_f, 4);
  printf("float: %f\n", result2);

  const size_t nums_c[]{ 1, 2, 3, 4 };
  const auto result3 = mean<size_t>(nums_c, 4);
  printf("size_t: %zd\n", result3);
}
```
We can see that the template parameter is applied `double`, `float` and `size_t` correspondingly to accommodate different types of arrays. In compiling stage, the compiler would generate 3 overloading `mean` functions. 

### Template Classes
The `SimpleUniquePointer` is an RAII wrapper for objects which use storage, which is a "prototype" of the stdlib's `std::unique_ptr`.
```cpp
template <typename T>
struct SimpleUniquePointer {
  SimpleUniquePointer() = default;
  SimpleUniquePointer(T* pointer)
      : pointer{ pointer } {}
  ~SimpleUniquePointer() {
    if(pointer) delete pointer; // 1
  }
  SimpleUniquePointer(const SimpleUniquePointer&) = delete; // 2
  SimpleUniquePointer& operator=(const SimpleUniquePointer&) = delete; // 3
  SimpleUniquePointer(SimpleUniquePointer&& other) noexcept // 4
      : pointer{ other.pointer } {
    other.pointer = nullptr;
  }
  SimpleUniquePointer& operator=(SimpleUniquePointer&& other) noexcept { // 5
    if(pointer)
      delete pointer;
    pointer = other.pointer;
    other.pointer = nullptr;
    return *this;
  }
  T* get() {
    return pointer;
  }

  private:
  T* pointer;
};
```
In 1, it makes sure that when `SimpleUniquePointer` object is destructed, the resource is recycled. Marks 2 and 3 explicitly declare that `SimpleUniquePointer` do not support copy construction and copy assignments, which is a good practice to force a single ownership of the point-to object. Marks 4 5 implement the move constructor and move assignments.

With `SimpleUniquePointer`, it is more easy to handle free-store-allocated objects:
```cpp
auto ptr_numbers = SimpleUniquePointer(new int[36]);
auto ptr_string = SimpleUniquePointer(new char[15]);
```

Another concrete example by tracing the life cycle of objects:
```cpp
struct Tracer {
  Tracer(const char* name)
      : name{ name } {
    printf("%s constructed.\n", name);
  }
  ~Tracer() {
    printf("%s destructed.\n", name);
  }

  private:
  const char* const name;
};

void consumer(SimpleUniquePointer<Tracer> consumer_ptr) {
  printf("(cons) consumer_ptr: 0x%p\n", consumer_ptr.get());
}

int main() {
  auto ptr_a = SimpleUniquePointer<Tracer>(new Tracer{ "ptr_a" });
  printf("(main) ptr_a: 0x%p\n", ptr_a.get());
  consumer(std::move(ptr_a)); // 1
  printf("(main) ptr_a: 0x%p\n", ptr_a.get());
}
```
With output:
```plain
ptr_a constructed.
(main) ptr_a: 0x0000020E8F422190
(cons) consumer_ptr: 0x0000020E8F422190
ptr_a destructed.
(main) ptr_a: 0x0000000000000000
```
In 1, the `ptr_a` is moved to the argument `consumer_ptr` of consumer. After the execution of `consumer`, `consumer_ptr` is out of scope thus be recycled, where we observe the value `ptr_a` be reset to 0.
### Type Deduction
You are not always require to provide the type parameters if the compiler can guess it from the context.  For example, the previous usage of `mean` can be simplified to 
```cpp
const double nums_d[]{ 1.0, 2.0, 3.0, 4.0 };
  const auto result1 = mean(nums_d, 4); // no need to give <double> parameter
  printf("double: %f\n", result1);
```

## Concepts 
Technically, for the `mean` function discussed in the previous section, it cannot accept *any type*. There are a few silent requirement for `T`:
- It is default constructable.
- It should supports `+` (plus operator)
- It should supports `/` (divide by integers)
CPP don't perform these type checking by default. If wrong type is feed to `mean`, for example, a `char`, templates might blow up until very late in the compilation process, given extremely notorious error message. And **you cannot know whether the compilation can be successful until you compile it**.

There are many makeshift for this problem, but all of them are not really satisfactory. It was until very recently (C++20) that the *concepts* come on the stage. *Concepts* provides a formal way to constrain template parameters.  

Before delving into the example, it is worth noticing that concepts feature is new to C++ standard specification, and different compilers can have different implementation progress. This post mainly discusses the MSVC compilers according to [this article](https://devblogs.microsoft.com/cppblog/c20-concepts-are-here-in-visual-studio-2019-version-16-3/) from MS C++ team.

This concept find out if `T::value` can be implicitly convert to bool
```cpp
#include <concepts>

template<typename T>
concept has_bool_value_member = requires { { T::value } -> std::convertible_to<bool>; };

struct S3 {};
struct S4 { static constexpr bool value = true; };
struct S5 { static constexpr S3 value{}; };

static_assert(!has_bool_value_member<S3>);
static_assert(has_bool_value_member<S4>);
static_assert(!has_bool_value_member<S5>);
```
The `std::convertible_to` is a standard concept in `<concept>` header. There are many other standard library concepts as well: [\<concept\>](https://www.open-std.org/jtc1/sc22/wg21/docs/papers/2018/p0898r3.pdf). We can also make use of [Standard library header <type_traits> (C++11)](https://en.cppreference.com/w/cpp/header/type_traits) as concepts as well:

```cpp
#include <type_traits>

template<typename T> concept Averagable = 
	is_add_supported<T> && std::is_default_constructible<T>::value;
// is_default_constructible is from <type_traits>
```

As we can see, **a concept is also a template**. It is more easy to think **concept as a *predicate*:** if a set of template parameters meets the criteria of a given concept, the concept evaluates to `true` at compile time.

The `requires` keyword forms a requirement expression, which is a predicate. It is acceptable to combine multiple predicates:
```cpp
template<typename T> concept is_numeral =
	requires (T i) { i + i; } && // T must support add operator
	requires (T i) { i / size_t{ 1 }; }; // T must support divide (by integer) operator
```

To use a concept in functions, add an requirement expression in the signature of the function:
```cpp
// This concept tests whether 't + u' is a valid expression
template<typename T, typename U>
concept can_add = requires(T t, U u) { t + u; };

// The function is only a viable candidate if 't + u' is a valid expression
template<typename T, typename U> requires can_add<T, U>
auto add(T t, U u)
{
	return t + u;
}
```

### Preconcepts Makeshift
Before C++20, concepts aren't a part of the standard. Programmers often make use of  `static_assert` as makeshifts.

A `static_assert` make an assertion that evaluates at compile time. If an assertion fails, the compiler will issue an error and stop compiling. 
```cpp
#include <type_traits>

template <typename T>
T mean(T* values, size_t length) {
	static_assert(std::is_default_constructible(), 
		"Type must be default constructible.");
	// ...
}
```
It is ugly though, but it is a legit makeshift for those working on old version of compilers. 

## Non-type parameters
Apart from template type parameters, C++ templates support *non-type parameters* as well, also called value parameters.
```cpp
template <size_t Index, typename T, size_t Length>
T& get(T (&arr)[Length]) {
  static_assert(Index < Length, "Out of bounds access");
  return arr[Index];
}
```
The `Length` parameter is a non-type parameters, which can be used to initialize different `get` functions:
```
int fib[]{ 1, 1, 2, 0 };
printf("%d %d %d ", get<0>(fib), get<1>(fib), get<2>(fib)); // 1 1 2
```

## Templates as template parameters
A template can be a template parameter. 
```cpp
template<typename T, template<typename, int> class Arr>
class MyClass2
{
    T t; //OK
    Arr<T, 10> a;
};
```

## Polymorphism at Runtime vs Compile Time
Compile time polymorphism has more advantages: higher performance, more predictable and more readable. It is generally commended to use runtime polymorphism (templates). But sometimes you won't know the types used with your code until runtime. In such cases, use runtime polymorphism instead. 

## Example: function `mode`
The mode of a series of values is the value that appears most commonly. The implementation follows:
```cpp
#include <map>
#include <type_traits>

template <typename T>
T mode(const T* values, size_t length) requires std::is_integral<T>::value {
	if (length == 0) {
		return 0;
	}
	std::map<T, int> countMap;
	for (size_t i = 0; i < length; i++)
	{
		auto it = countMap.find(values[i])

		if (it != countMap.end()) it->second += 1;
		else countMap[values[i]] = 1;
	}

	const std::pair<const T, int>* maxpair{nullptr};
	for (const auto& pair : countMap) {
		if (maxpair == nullptr || pair.second > maxpair->second)
			maxpair = &pair;
	}

	return maxpair != nullptr ? maxpair->first : 0;
}

int main() {
	int x1[]{-20, -20, 100, 100, -20, 5123 };
	printf("The mode of x1 is %d\n", mode(x1, 6));

	short x2[]{ 30, 0, 100, 400, 30, 5123 };
	printf("The mode of x2 is %d\n", mode(x2, 6));

	// will indeed fail because the associated constraints are not satisfied
	//double x3[]{ 30.0, 0, 100, 400, 30, 5123 };
	//printf("The mode of x3 is %f\n", mode(x3, 6));
}
```
- Use template to accommodate both `int[]`  and `short[]`.
- Use concepts to check type - The requirement expression examines if the supplied type is an integer.
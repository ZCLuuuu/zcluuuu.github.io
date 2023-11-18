---
layout: post
title:  "Runtime Polymorphism in CPP"
categories: [C++]
description: Pure Virtual Classes as Interfaces, Runtime Polymorphism by Composition
---
## Polymorphism
Polymorphism means code that allows programmers **write only once** but is able to **reuse with different types**. Ideally, polymorphism yields **loosely coupled** and **highly reusable** code.
C++ offers 2 types of polymorphism:
- **Compile-time polymorphic** code incorporates different types at compile time.
- **Runtime-polymorphic** code incorporates different types at runtime. 
Which approach to choose depends on **what stage** you can **determine the type**. That is, if it is only at the run time that the target type can be determined, then you should consider using runtime-polymorphism. 

## Runtime Polymorphism

### Motivation
Logging is a big thing in programming. Suppose there are many types of loggers:
- `ConsoleLogger` - which simply log information to console
- `FileLogger` - which record log info into a local file
- `RemoteLogger` - which send the log info to a remote server

Imaging a service at an online bank system that is implemented with only `ConsoleLogger`
```cpp
struct ConsoleLogger {
  void log_transfer(long from, long to, double amount) {
    printf("%ld -> %ld: %f\n", from, to, amount);
  }
};

struct Bank {
  void make_transfer(long from, long to, double amount) {
    logger.log_transfer(from, to, amount);
  }
  ConsoleLogger logger;
};

int main() {
  Bank bank;
  bank.make_transfer(1000, 2000, 49.95); // log to console: 1000 -> 2000: 49.95
}
```
where `Bank` class (notionally) implement the transaction, while `ConsoleLogger` is responsible for making logs. This is generally good design because the responsibility of each class is dividable.

But one day, a new requirement states that at the runtime, the service need to be able to switch to another kind of logger (i.e. to sent the log to a remote server for auditing).  Then this code is broken because programmers need to edit it to adapt to a new type of logger. In this case, one should consider runtime-polymorphism. 
### Composition vs Inheritance
There are 2 styles of runtime polymorphism in C++. ***Object composition*** is a design pattern where a class **contains a reference** to another class types, which is commonly accepted as a modern C++ style. Alternatively, an antiquated style called ***implementation inheritance*** achieves polymorphism by building **hierarchies of classes**. The reasons why the once-popular inheritance is considered deprecated are mainly:
- It is easy to encounter shit legacy code.
- It's hard to reason about what happened without look at each ancestor on the hierarchy.

In fact, in my experience being a developer, it's extremely rare for me to encounter any polymorphism that only can to be implemented by complex class hierarchies. Some popular recent-designed programming languages like Golang and Rust even don't support this mechanism.

Thus, we're only going to talk about **object composition** in this article.

## Interfaces
An *interface* is **a shared contract** between those classes that implement it and those classes that consume it, which is a common design pattern in software engineering.  Interfaces are **stringent** in the sense of consumers can only use the method defined in the interface, and implementations must obey the explicitly defined signatures. In this way,  interfaces promote **highly reusable and loosely coupled code**. 

Sadly, there is no `interface` keyword in C++ (another archaisms programmers have to deal with). Alternatively, communities often refer **pure virtual classes** to "interfaces" in C++. 

```c++
struct Logger {
  virtualu ~Logger() = default;
  virtual void log_transfer(long from, long to, double amount) = 0;
};

struct ConsoleLogger : Logger {
  void log_transfer(long from, long to, double amount) override {
    printf("%ld -> %ld: %f\n", from, to, amount);
  }
};
```

### Derived Classes
Derived classes inherit non-private members from their base classes. But it is sometimes a bad idea to use inheritance because it can easily yield hard-to-reason-about code. But here we use this mechanism for our interface, that's ok.

### Virtual Methods
The `virtual` keyword permit a derived class to override the base methods, but implement or not is optional. It is the  `=0` suffix require a derived class to implement the method. A `virtual` method with a `=0` suffix is called **pure virtual methods**.

Base classes that only contain pure-virtual methods are referred to as **pure-virtual classes**.

Finally, you can't instantiate a class containing any pure virtual methods.

### Virtual Destructors
Lastly there is one thing that is worth mentioned. In the above code, we can see that the destructor is declared `virtual`. It is optional, but the reason why we need to do this is because a quirky C++ feature that if **the destructor is invoked by reference type** (or pointer type) during destruction. Here's an example to interpret this idea.

Consider this piece of code:
```cpp
struct BaseClass {
  ~BaseClass() {
    printf("~BaseClass() invoked.\n");
  };
};

struct DerivedClass : BaseClass {
 ~DerivedClass() {
   printf("~DerivedClass() invoked.\n");
 }
};

int main() {
 BaseClass* x{ new DerivedClass{} };
 delete x; 
}
```
Guess which destructor is invoked? It is actually `~BaseClass()`  because x is a pointer to `BasicClass`. This shit design causes so many hard-to-reason bugs. So it is recommended to declare a virtual destructor even if it does nothing. (using the `default` keyword).

## Using interfaces
As a consumer, we are now free of taking care of which specific type of Logger that we need to use, by only deal in references or pointers to interfaces. 

Here is the solution to the motivation problem:
```cpp
// interface
struct Logger {
  virtual ~Logger() = default;
  virtual void log_transfer(long from, long to, double amount) = 0;
};

// implementation 1
struct ConsoleLogger : Logger {
  void log_transfer(long from, long to, double amount) override {
    printf("[cons] %ld -> %ld: %f\n", from, to, amount);
  }
};

// implementation 2
struct RemoteLogger : Logger {
  void log_transfer(long from, long to, double amount) override {
    printf("[remote] %ld,%ld,%f\n", from, to, amount);
  }
};

struct Bank {
  // set the logger at runtime in the constructor
  Bank(Logger& logger): logger{ logger } {}  
  
  void make_transfer(long from, long to, double amount) {
    logger.log_transfer(from, to, amount);
  }

  private:
  Logger& logger; // reference to interface
};
```

The program now can determine which `Logger` is going to use in the runtime at the constructor of the  `Bank` class. This pattern is sometimes called *Constructor Injection*. Alternatively, another style is *Property Injection*, which use a method to set the logger property. The difference between these 2 styles is that whether the type of logger can be **changed in the lifetime of the object**. And of course, it is ok to combine 2 styles for a more flexible implementation. 

Note that the compiler cannot know ahead of time how much memory to allocate for the underlying type. Otherwise, it would be better off using templates.

## Summary
- Polymorphism
- Runtime Polymorphism vs Compile-time Polymorphism
- Pure Virtual Classes as Interfaces
- Runtime Polymorphism by Composition
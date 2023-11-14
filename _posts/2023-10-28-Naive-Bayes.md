---
layout: post
title:  Simple Theory of Naive Bayes Classifier
categories: [MachineLearning]
description: The math foundation
---

## Basic Bayesian Decision Theory

Suppose in a data set, there are N distinct class labels, that is:

$$
y = \{ c_1, c_2, ...c_n\}
$$

What we want to do now is to calculate which class is the most probable one, that is:

$$
h^* = \arg\max_{c\in y} P(c|x)
$$

P(c\|x) is the posterior probability of given instance $ x = \{x_1,x_2, ..., x_d\} $, the probability of x to be c. The function argmax means we want to output the class $ c \in \{ c_1, c_2, ...c_n\} $ which gives the highest posibility.

According to bayes’ theorem, $P(c\|x)$ can be written as

$$
P(c|x) = \frac{P(c)P(x|c)}{P(x)}
$$

Because P(x) is the probability of the probability of instance being x, which is a fixed value and doesn’t have an impact on the problem we want to solve (to determine which class c is of highest probability). As we don’t want to know the actual probability of x being c( we just want to know the highest one), we can omit calculate P(x):

$$
\hat{c} = \arg\max_{c \in y} P(c)P(x|c) 
$$

I interpret this formula to be:

“Given an observation x, find the class c, which can maximize the likelihood ‘x being the class c’.”  

Because x contains many features x = $[x_1, x_2, ..., x_m]$ ,thus

$$
\hat{c} = \arg\max P(x_1, x_2, ..., x_m|c)P(c)
$$

We can just use the frequency of c as P(c), it’s a efficiently computable way to do that. What really matter is $ P(x\|c) $. If every instance in the dataset has d binary attributes, there are 2^d combination of attributes. The probability of one instance with a label c being a specific attributes $x = \{x_1,x_2, ..., x_m\}$ is hard to estimate.

## Naive Bayes Classifier Theory

Because P(x\|c) is hard to get, the naive bayes classifier make an assumption to reduce this problem to another rather easy one: **Assume** 

- **all attributes of instance are independent,** so we can transform the object faction
    
     
    
    $$
    \hat{y} = \arg\max_{y \in y} P(y)P(x|y) = \arg\max_{y \in y} P(x,y)
    $$
    
    and we can estimate P(x\|y) to be
    

$$
P(x_1, x_2, ..., x_m|y) = P(x_1|y)P(x_2|y)...P(x_m|y) = \prod_{m=1}^PP(x_m|y)
$$

- **continuous attributes comply the Gaussian Distribution.**
    
    $$
    \begin{equation}
        f(x|\mu, \sigma^2) = \frac{1}{\sqrt{2\pi\sigma^2}} \exp\left(-\frac{(x-\mu)^2}{2\sigma^2}\right)
    \end{equation}
    $$
    
    where 
    
    - $\mu$ is the mean of the distribution
    - $\sigma^2$ is the variance of the distribution.
- The distribution of data in the training set is the same as the distribution of data in the test set

With this assumption, we can easily estimate

$$
P(x|c) = \prod_{m=1}^PP(x_m|c)
$$

So that

$$
P(x,y) =P(y)\prod_m^M P(x_m|y)
$$

A really simple idea to implement P

- For discrete features, $ P(x_i\|c) $ is the frequency of instances which has a class c and has the attribute x_i.
    
    $$
    P(x_i|c) = \frac{|D_{c,x_i}|}{|D_c|}
    $$
    
    where $\|D_{c,x_i}\|$ is simply the number of instances with class c and attribute c_i.
    
- For continuous features, we assume these features comply gaussian distribution, thus we can use the formular to calculate its possibility.

 Thus, the calculation of naive bayes classifier can be quite simple.

## Types of NB Classifier

We are going to build a classifier for $x \rightarrow y$, where x is an observation of instance and y is the class

### Gaussian Naive Bayes

**Apply if features of x are numerical (real-valued) and y is binary.**

For each y, calculate

$$
p(x,y) = p(y)\prod_m^M p(x|y)\\
=BN(y|\phi)\prod_m^M N(x|\psi=\{\mu_{m,y}, \delta_{m,y}\})
$$

where BN is the probability of y under bernoulli distribution and N is the probability of x under gaussian distribution. 

Find the distribution:

[Distribution](https://www.notion.so/Distribution-09f29a398a8c4520b5566df8f440e754?pvs=21)

Find the y which maximize p(x,y)

### Bernoulli Naive Bayes

**Apply if features of x are binary and y is binary**

Similar to gaussian naive bayes, the object function is:

$$
p(x,y) = p(y)\prod_m^M p(x|y)\\
=BN(y|\mu_y)\prod_m^M BN(x|\mu_x)
$$

### Categorical Naive Bayes

**Apply if features of x are and y are categorical**

$$
p(x,y) = p(y)\prod_m^M p(x|y)\\
=Cat(y|\phi)\prod_m^M Cat(x|\psi)
$$

where Cat is the categorical distribution probability. In practice, one can just count the instances in the dataset to get the probability

$$
Cat(y) = \frac{count(y)}{N}
$$

## Smoothing

Even in Naive Bayes Classifier, chances are there could be not enough instance has a specific value of feature and a class (unseen features). Thus some of the $ P(x_i\|c) $ could be 0, which is a destroyer to our classifier because $ \prod_{i=0}^dP(x_i\|c) $ will be 0 if one of the term is 0.

Smoothing is a technique to solve this problem. The most common one is Laplacian correction, which simply add one to the numerator:

$$
P(x_i|c) = \frac{|D_{c,x_i}| + 1}{|D_c|}
$$

This technique can avoid $ \|D_{c,x_i}\| $ being 0.
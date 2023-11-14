---
layout: post
title:  Simple Theory of Naive Bayes Classifier
categories: [Machine Learning]
description: The math foundation
---

## Probabilistic Model

We want to predict the most probable class $\hat{y}$ of an observation x: 

$$
\hat{y} = \arg\max_{y\in Y} P(y|x)
$$

With Bayes’s theorem, the object becomes:

$$
\hat{y} = \arg\max_{y\in Y} \frac{P(x|y)P(y)}{P(x)}\\
 =\arg\max_{y\in Y} P(x|y)P(y) \tag{P(x) is fixed}
$$

This equation means that we transform the task of “finding the possibility of instance being class y when x observed” to “finding the frequency of x in data set under class y” 

Finally, make the **conditional independence assumption** that features are assumes to be independent.(The probability of independent events are the product of each combined.) 

$$
\hat{y} = \arg\max_{y\in Y} P(y)\prod_{m=1}^M P(x_m|y) \tag1
$$

### NB as a classifier

Training Phase: Calculate each P(y_i) and P(x_m \| y_i)

Testing Phase: Equation 1

### NB as a generative model

```bash
Input: generate N instances, each instance has M features
Model = for i in {1...N} do:
	generate label y[i] from P(y)
	for feature m in {1...M} do:
		generate feature x[m] from P(m, y[i])
```

## NB Variants

Naive Bayes estimate P(x_m\|y) based on feature type

- Gaussian Naive Bayes:
    - For real-valued numerical features
    - Estimating P(x_m \| y) by normal distribution
- Bernoulli Naive Bayes
- Categorical Naive Bayes
    - **Estimating P(x_m \| y) simply by counting**

### Maximum Likelihood Estimating

Naive Bayes learn parameters by MLE. For example, in Gaussian Naive Bayes, the parameter mean and standard deviation are learned by applying MLE. 

### Smoothing

Problem: In Categorical Naive Bayes, if any term P(x_m \| y) = 0, then P(y\|x) =0. (No such class-feature combination)

Solution: 

1. Epsilon Smoothing: Replace any P(x_m \| y) = 0 with a very small number epsilon < 1/N
2. Laplace Smoothing: Add a constant to each feature count
    
    $$
    P(x_m=j|y=k)=\frac{\alpha + count(y=k,x_m=j)}{M\alpha + count(y=k)}
    $$
    
    where M is the number of possible values of target feature
    
    Issues:
    
    - Change drastically when there are few instances
    - Reduce Variance because it reduces sensitive to individual observations
    - Add bias because we can’t get a true MLE

Continuous (Gaussian) features do not have issue with unseen data, but we may get 0 standard deviation in extreme case, which requires smoothing as well but uncommon than categorical features. 

## Implementation of NB

- Use dictionaries for counting
- Choose a type of smoothing
- Use log-transformation to avoid underflow

## Summary

Pros:

- easy to build, train and test
- easy to scale with high dimensional feature space
- reasonably explainable

Cons:

- Naive assumption
- Smoothing introduces bias
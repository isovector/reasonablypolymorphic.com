---
layout: post
title: "Review: Information Effects"
date: 2017-08-08 22:37
comments: true
tags: papers, review, james, sabry, haskell, reversible computing
---

One of the most exciting papers I've read in a long time is James and Sabry's
[Information Effects][paper]. It starts with the hook "computation is a physical
process which, like all other physical processes, is fundamentally reversible,"
and it goes from there. If that doesn't immediately pull you in, perhaps some of
the subsequent PL jargon will -- it promises a "typed, universal, and
reversible computation model in which information is treated as a linear
resource".

[paper]:

I don't know about you, but I was positively shaking with anticipation at this
point. That's one heck of an abstract.

After some philosophy and overview of the paper, James and Sabry dive into the
appetizer in a section titled "Thermodynamics of Computation and Information".
They give the following definition:

> DEFINITION 2.2 (Entropy of a variable). Let $b$ be a (not necessarily finite)
> type whose values are labeled $b_1$, $b_2$, $\ldots$. Let $\xi$ be a random
> variable of type $b$ that is equal to $b_i$ with probability $p_i$. The
> entropy of $\xi$ is defined as $- \sum p_i \log{p_i}$.

and the following, arguably less inspired definition:

> DEFINITION 2.3 (Output entropy of a function). Consider a function `f : a ->
> b` where `b` is a (not necessarily finite) type whose values are labeled
> $b_1$, $b_2$, $\ldots$. The output entropy of the function is given by $- \sum
> q_j \log{q_j}$ where $q_j$ indicates the probability of the function to have
> value $b_j$.

We can say now that a function is reversible if and only if the entropy of its
arguments is equal to the entropy of its output. Which is to say that the gain
in entropy across the function is 0.

Of course, as astute students of mathematics we know that reversibility of a
function is equivalent to whether that function is an isomorphism. While this is
how we will prefer to think of reversibility, the definition in terms of entropy
brings up interesting philosophical questions we will get to later.


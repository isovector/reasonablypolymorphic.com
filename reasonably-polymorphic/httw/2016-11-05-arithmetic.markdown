---
layout: post
title: Arithmetic
date: 2016-11-05 12:12
comments: true
tags:
---

In the last chapter we discussed the derivation of how to represent numbers in
our machine diagrams. However, the *representing* something is meaningless if
you don't have any means of interacting with that thing. In this chapter we will
come up with a way of working with numbers, and quickly see how our diagrams sag
under the weight of the new loads we demand of them.

[TODO]: and then what?

Now that we have a notion of numbers, there are two natural things we might want
to use them for: adding two numbers together, and describing how many times we
want some "action" done. Because we don't yet have a notion of what an "action"
might be (remember, our machine diagrams never change, once they've been given
their inputs), it seems more prudent to look into adding two numbers together.

Just like when we started looking for a way of representing numbers, our
approach will be to study how adding numbers works *in a symbolic sense.* Asking
about some kind of *meaning* behind adding two numbers can't possibly be a
fruitful endeavor, since we can't teach our diagrams about meaning.

This approach is know as being **syntactic** in nature, which means it follows
the *structure* of what the problem "looks like". Syntax is in strict dichotomy
with **semantics**, which describe the *meaning and interpretation* of
something.

A useful intuition behind syntax and semantics is that syntax exists *in the
world*, and semantics exist *in our minds*. Obviously, syntax is going to be the
easier thing to work with in most cases.

> Takeaway: Syntax is the factual structure of something, while semantics is the
> interpretation we put on that structure.

The divide between syntax and semantics requires a much deeper philosophical
dive than we will devote to it here today, but we'll discuss it in the next
interlude. In particular, the interplay between syntax and semantics goes a long
way to answering some of our earlier philosophical questions behind "why does
any of this work?"

But I digress. The question we're asking is "how does addition between numbers
work?" and furthermore, "what does addition look like on a syntactic level?"

The good news is that you already know the answer to both of these things. Pop
quiz: using a pen and paper, compute the answer to $1243+412$. I'll give you a
second.

Done? Good. Unless you're a math wizard, your approach to computing this sum
probably looked something like filling in this table, one column at a time:

|   |   |   |   |   |
|---|---|---|---|---|
|   | 1 | 2 | 4 | 3 |
| + | 0 | 4 | 1 | 2 |
|   |   |   |   |   |
|&nbsp;|&nbsp;|&nbsp;|&nbsp;|&nbsp;|

The approach is this: starting from the right, add the two symbols together
(which you've memorized), fill that symbol into the bottom line in the same
column, and repeat with the column to the left of it.

Make no mistake, this computation we've performed was *purely syntactic*. You
didn't have to know anything about numbers to do it. In fact, if we completely
jumbled up all symbols with ones you'd never seen before, and gave you a book
about how to add any two of these new symbols, you'd still do just fine.
]
Let's do one more example, just to a

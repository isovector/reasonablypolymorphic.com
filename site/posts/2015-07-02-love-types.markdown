---
layout: post
title: How I Learned to Stop Worrying and Love the Type System
date: 2015-07-02 10:47
comments: true
tags: haskell, technical
---

> This post marks my intended shift to more technical topics; the target
> audience is people with some programming experience. However, if you're
> otherwise interested, feel free to skip the technical bits and see what you
> think!

## I

A pretty common "soft" question in software interviews is "what's your favorite
programming language, and why?" I have no idea what the interviewer intends to
tease out with such a question, but historically my answer has always been along
the lines of:

> "C++. Why? Because when I get something working, I feel like a god. It just
> puts so much power at my fingertips."

How's that for being overly controlling? I actually *enjoyed* the tedium of
writing copy constructors, keeping track of the ownership of my pointers, and
*especially* in writing fancy templated data structures. If you haven't had the
pleasure of writing a fancy templated data structure, they often look something
like this:


```c++
template<class TItem>
class ScopedPool {
public:
  template<class... TCtorArgs>
  class Object {
  public:
    explicit Object(
      ScopedPool<TItem> &pool,
      TCtorArgs&&... ctorArgs)
    {
      ptr_ =
        objs.empty()
        ? std::make_unique<TItem>(std::forward<TCtorArgs>(ctorArgs)...)
        : std::move(objs.top());
```

Yes, once upon a time, I actually *wrote* that unholy thing, and perhaps more
surprisingly, I even knew what it did. I've been programming for about a decade,
and things like this were the only challenges I'd face when working on projects;
gnarly pieces of software that *really made me think*.

Then, about a year ago, I discovered Haskell and dove in. It felt like
power-lifting for my brain, and all of a sudden, programming was fun again. Even
the most trivial programs gave me a hard time in Haskell. I'm not here to
discuss Haskell in general today; it just happens to be why I've been thinking
about type systems so much lately.

For me, the most interesting feature of Haskell is that if your program
type-checks, there's a good chance it will do what you want. There are no
segfaults, no race conditions, and no memory stomps to worry about. Also, the
type-checker is really, really picky, which probably helps. In my opinion, this
kind of really picky type-checking is exactly what modern programming needs.

Of course, C++ and Haskell's type-systems are both Turing-complete, so
*technically* they are equally powerful. And as we all know, being *technically*
right is the best kind of being right. That being said, if you are the type of
person who is going to try make this argument, try to suspend your disbelief,
and hopefully I'll convince you that I might be onto something here.

<!--more-->



## II

I do most of my blogging while in coffee shops, mainly because I need a constant
stream of caffeine to stay productive. Unfortunately, that means there is a
tangible cost to me writing. Let's say I want to figure out how much I have to
pay to get a blog post done, where do I begin?

Well a good first strategy is to write down any variables I have:

$$
\begin{alignedat}{2}
p &= 2.5 \text{Є / cup}\qquad& \text{(price per coffee)} \\\\
b &= 3 \text{days / post}\qquad& \text{(duration of post)} \\\\
n &= 400 \text{mg / day}\qquad& \text{(necessaary caffeine)} \\\\
c &= 100 \text{mg / cup}\qquad& \text{(caffeine per coffee)} \\\\
v &= 250 \text{ml / cup}\qquad& \text{(volume of cup)}
\end{alignedat}
$$

And then, work backwards. Given that I want my result to be in terms of $\text{Є
/ post}$, I start by looking at $p$ and $b$, which are $\text{unit}(p\cdot b) =
\text{Є} \cdot \text{days / cup / post}$. Good start, now it's just a matter of
multiplying and dividing out the other variables I know in an attempt to get
those extra units to cancel.

In the end, it works out that:

$$
p\cdot b\cdot n \mathbin{/} c = 30 \text{Є / post}
$$

which has the right units. And is actually a lot of money to be paying for
coffee! Notice that I didn't end up using $v$ whatsoever -- just
because you have some piece of information doesn't always mean it will be
useful!

You'll also notice that I found this answer through purely *mechanical* means,
there was no insight necessary. Just multiply terms through and pay attention to
what units the final result has. When the units become right, there's a pretty
good chance that my answer is correct.

What's going on here is we're using the units as a type system to ensure our
answer is coherent. The units are doing work for us by ensuring we're not doing
anything stupid, and additionally, they help guide us to the right answer, even
if we don't know what we're doing.

If you're coming from an imperative background, this might strike you as being a
contrived metaphor, but I don't think it is. As we'll see later, when you're
dealing with highly-parametric types, lots of times getting the right
implementation *is* just slapping things together until you get the right type.

But let's not get ahead of ourselves.



## III

Before we dive too deeply into Haskell's type system, we need to first take a
moment to discuss Haskell's type notation. Concrete types, like in Java, always
begin with a capital letter (eg. `Int` is the type of the integers).

Functions of one argument are typed as `a -> b` (in this case, taking a `a` and
returning a `b`). So far, so good, but functions of higher [arity] might take a
little while to get used to:

[arity]: https://en.wikipedia.org/wiki/Arity

A function taking two `a`s and returning a `b` is typed as `a -> a -> b`,
**not** `(a, a) -> b`, as you might expect. Turns out, there is a really good
reason for this weird syntax, which bears diving into.  Take for example, the
Haskell function which performs addition:

```haskell
add :: Int -> Int -> Int
add x y = x + y
```

You might be tempted to write this in C++11 as:

```c++
int add(int x, int y) {
    return x + y;
}

// usage: add(3, 4) == 7
```

but you'd be wrong. In fact it is closer to:

```c++
std::function<int(int)> add(int x) {
    // return an anonymous function of type `int(int)`
    return [x](int y) { return x + y; };
}

// usage: add(3)(4) == 7
```

Which is to say, `add` is a function which takes an integer, and returns a
function which takes the other integer. This becomes more evident when we add
braces to our original type signature: `Int -> (Int -> Int)`. Our function,
`add`, is a function which takes an `Int` and returns another function of type
`Int -> Int`.

There are two implications to this: we can partially apply functions (this is
known as [currying][curry] in the literature), and functions are first-class
values in Haskell.

[curry]: https://en.wikipedia.org/wiki/Currying

Now, that is not to say that all types must be definite. Take for example, the
polymorphic function `head`, which returns the first element of a list, and is
typed as `[a] -> a`. Here, `a` is a type-variable, which can refer to any other
type it please. The equivalent C++ of course, is something like:

```c++
template<class T>
T head(const std::list<T>& list) {
    return list.front();
}
```

So far, nothing special, type-variables seem to correspond directly to template
parameters, but this is not in fact the case. You may have noticed that our
earlier `add` function was too specific; addition is defined over all numeric
types (not just `Int`), so instead let's rewrite it as:

```haskell
add :: (Num a) => a -> a -> a
add x y = x + y
```

Here, `(Num a)` acts as a *constraint* over `a`, informing you and the compiler
(but mostly you -- the compiler is really good at type inference), that this
function is defined over any *numeric* `a` types. You can do something similar
in C++ with [SFINAE][sfinae] or maybe with traits, but it's not nearly as
elegant.

[sfinae]: https://en.wikipedia.org/wiki/Substitution_failure_is_not_an_error

In effect, what we are doing here with Haskell's constraints is informing the
type system of the *semantics* of `add`, while a SFINAE solution is dependent on
*syntax*: it will work for any case in which `operator+` is in scope, regardless
of whether this is actually meaningful.



## IV

Because Haskell encourages you to write functions as general as possible (in C++
this reads as "write lots and lots of templates"), we get lots of abstract
functions. It might surprise you to learn that abstract functions are usually
*more informative* than their specialized counterparts, and it is herein that
I think Haskell's type system really shines through. As was the case with
dimensional analysis, looking at generalized types gives us a lot of analytic
power.

Consider a function of the type `[Int] -> Int` (a function from a list of `Ints`
to a single `Int`). It's not very clear what this function is doing; there are
at least four non-trivial implementations for it (`length`, `sum`, `head`,
`last`, and probably others).

Instead, if we change the type of our hypothetical function to `[a] -> Int`
(from a homogeneous list of *any* type to an `Int`), there becomes only one
non-trivial implementation: the `length` function. It *has* to be, since there's
no way to get an `Int` out of the list any other way.

Let's consider another hypothetical function, one of type `(a -> Bool) -> [a] ->
[a]` (a function which takes a predicate on the type variable `a`, a list of
`a`s, and returns a list of `a`s). The only reasonable interpretation of this
function is that the predicate is being used to determine whether or not to keep
each element in the list. There are a few possible implementations, but you will
already have a good idea of what would be necessary: iterating through the list
and applying the predicate as you go.

To really drive this point home, let's look at the function of type `a -> a`. I
say "the function" because there is exactly one possible implementation of this
function. Why? Well, what do we know about the parameters to this function?
Absolutely nothing. While in C++ we could assume that `a` has a default value,
or equality, or something, we can make no such assumptions here. In fact, `a`
could have zero possible values (ie. be isomorphic to type `Void`), and thus be
non-instantiable. Since we have no means of *creating* an `a` value, the *only
possible implementation* of this function is to return our parameter as-is:

```haskell
id :: a -> a
id x = x
```

So what does this tell us? Lots of times, if you know the type of a function,
you get the implementation for free; just like with dimensional analysis, we can
get answers through a purely mechanical means of combining the types we have
until we get the type we need. Cool!

## V

"But wait," says the skeptic! "The `<algorithm>` header already gives us a lot
of these reusable, abstract functions. Don't all your arguments apply to C++ as
well?"

Of course, this is not to say that C++ doesn't have similar things. The
`<algorithm>` header is indeed pretty comparable for most of the use-cases we've
looked at so far. However, this does not hold in general, as C++ is much less
specific about its types.

Let's take `transform` from `<algorithm>` for example, which comes with the
ultra crusty type signature:

```c++
template<
    class InputIterator,
    class OutputIterator,
    class UnaryOperation>
OutputIterator transform (
    InputIterator,
    InputIterator,
    OutputIterator,
    UnaryOperation);
```

There are a few issues with this function, but the most egregious is that its
type doesn't convey any information (in Haskell it would be `a -> a -> b -> c ->
b`, with some implicit constraints based on what template expansion allows).

Compare the equivalent function in Haskell: `(a -> b) -> [a] -> [b]` (a function
for turning `a`s into `b`s, and a list of `a`s). Much more concise, and
significantly more informative.

It's easy to see that just because you can get the C++ version to compile, you
have no guarantees it is going to actually *work*. As a matter of fact, the
documentation explicitly mentions this:

> Exceptions: <br />
> Throws if any of the function calls, the assignments or the
> operations on iterators throws. <br />
> **Note that invalid arguments cause *undefined behavior*.**

The C++ version is unsafe, unintuitive, and frankly, not very helpful.

There are two major (if related) things to take away from this: **types strongly
inform implementation** and, because of that, **a type signature usually implies
its use-cases**. These happen to be exceptionally useful properties.



## VI

The point I've been trying to make is twinfold: many polymorphic functions have
very few reasonable implementations, and that Haskell's types convey a lot of
information to the programmer. These properties lend themselves to *a big,
[searchable][hoogle] standard library*.

For example, the other week I wanted the functional equivalent to a traditional
`while` loop. The defining characteristics of a `while` loop are: a predicate
for stopping, an operation to transform states from one iteration to the next,
and a starting state. `while` loops seemed like something that ought to already
exist in Haskell, so I decided to look around a bit before implementing it
myself.

I went to [Hoogle][hoogle] ("Google" for Haskell), and searched for [the
function signature I was looking for][search], namely `(a -> Bool) -> (a -> a)
-> a -> a`. Sure enough, at the top of the list, there it was: `until` -- the
function that did exactly what I wanted.

[search]: https://www.haskell.org/hoogle/?hoogle=%28a%20-%3E%20Bool%29%20-%3E%20%28a%20-%3E%20a%29%20-%3E%20a%20-%3E%20a

And I find this is usually the case when I'm writing Haskell. Almost all of the
effort comes from figuring out *exactly* how I'm trying to transform my types.
Once that's sorted, it's just a matter of hoogling for the right functions and
composing them together. There's a surprisingly little amount of *actual code*
being written.

What I take away from this is that Haskell allows you to focus much more on
*what you're trying to do*, rather than *stringing plumbing around to get
everything working*. The abstractions exist at a high-enough level that you
never actually deal with storage or iteration or any of the nitty gritty
details. It's the complete opposite of my historical control-freak attitude
towards C++, and it's a spectacular feeling.

[hoogle]: https://www.haskell.org/hoogle/

<hr />

**Thanks** for Josh Otto for reading drafts of this post.


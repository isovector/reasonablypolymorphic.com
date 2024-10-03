---
layout: post
title: monoids
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

There's a common anti-pattern I see in beginner-to-intermediate Haskell
programmers that I wanted to discuss today. It's the tendency to conceptualize
the *creation* of an object by *repeated mutation.* Often this takes the form of
repeated insertion into an empty container, but comes up under many other guises
as well.

This anti-pattern isn't particularly surprising in its prevalence; after all, if
you've got the usual imperative brainworms, this is just *how things get built.*
The gang of four "builder pattern" is exactly this; you can build an empty
object, and setters on such a thing change the state *but return the object
itself.* Thus, you build things by chaning together setter methods:

```java
Foo myFoo = new Foo().setBar().setQux(17).setZap(true);
```

Even if you don't ascribe to the whole OOP design principle thing, you're still
astronomically likely to think about building data structures like this:

```java
Doodad doodad = new Doodad;
foreach (Widget widget in widgets) {
  doodad.addWidget(widget);
}
```

To be more concrete, maybe instead of doodads and widgets you have `BST`s and
`Node`s. Or dictionaries and key-value pairs. Or graphs and edges. Anywhere you
look, you'll probably find examples of this sort of code.

Maybe you're thinking to yourself "I'm a hairy-chested functional programmer and
I scoff at patterns like these." That might be true, but perhaps you too are
guilty of writing code that looks like:

```haskell
foldr
    (\(k, v) m -> Map.insert k v m)
    Map.empty
  $ toKVPairs something
```

Just because it's dressed up with functional combinators *doesn't mean* you're
not still writing C code. To my eye, the great promise of functional programming
is its potential for conceptual clarity, and repeated mutation will always fall
short of the mark.

The complaint, as usual, is that repeated mutation tells you *how* to build
something, rather than focusing on *what* it is you're building. An algorithm
cannot be correct in the absence of intention---after all, you must know what
you're trying to accomplish in order to know if you succeeded. What these
builder patterns, for loops, and `foldr`s all have in common is that they are
algorithms for strategies for building something.

But you'll notice none of them come with comments. And therefore we can only
ever guess at what the original author intended, based on the context of the
code we're looking at.

I'm sure this all sounds like splitting hairs, but that's because the examples
so far have been extremely simple. But what about this one?

```haskell
cgo :: (a -> (UInt, UInt)) -> [a] -> [NonEmpty a]
cgo f = foldr step []
  where
    step a [] = [pure a]
    step a bss0@((b :| bs) : bss)
      | let (al, ac) = f a
      , let (bl, bc) = f b
      , al + 1 == bl && ac == bc
            = (a :| b : bs) : bss
      | otherwise = pure a : bss0
```

which I found by grepping through `haskell-language-server` for `foldr`, and
then mangled to remove the suggestive variable names. What does this one do?
Based solely on the type we can presume it's using that function to partition
the list somehow. But how? And is it correct? We'll never know---and the
function doesn't even come with any tests!


## It's Always Monoids

The shift in perspective necessary here is to reconceptualize
building-by-repeated-mutation as building-by-combining. Rather than chiseling
out the object you want, instead find a way of gluing it together from simple,
obviously-correct pieces.

The notion of "combining together" should evoke in you a cozy warm fuzzy
feeling. Much like being in a secret pillow form. You must come to be one with
the monoid. Once you have come to embrace monoids, you will have found inner
programming happiness. Monoids are a sacred, safe place, at the fantastic
intersection of "overwhelming powerful" and yet "hard to get wrong."

As an amazingly fast recap, a monoid is a collection of three things: some type
`m`, some value of that type `mempty`, and binary operation over that type `(<>)
:: m -> m -> m`, subject to a bunch of laws:

```haskell
∀a. mempty <> a = a = a <> mempty
∀a b c. (a <> b) <> c = a <> (b <> c)
```

which is to say, `mempty` does nothing and `(<>)` doesn't care where you stick
the parentheses.

If you're going to memorize any *particular* example of a monoid, it better be
this one:

```haskell
instance Monoid b => Monoid (a -> b) where
  mempty = \a -> mempty
  f <> g = \a -> f a <> g a
```

That is, any function whose codomain is a monoid is itself a monoid. The `mempty
:: a -> b` of such a thing maps all values `a` to `mempty :: b`, while `(<>)`
combines values in the codomain pointwise.

The reason to memorize *this* `Monoid` instance is that it's the monoid instance
that every data structure is trying to be. Recall that *almost all* data
structures are merely different encodings of functions, designed to make some
operations more efficient than they would otherwise be.

Don't believe me? A `Map k v` is an encoding of the function `k -> Maybe v`
optimized to efficiently query which `k` values map to `Just` something.


---
layout: post
title: Theorems for Free Redux
date: 2025-10-09 11:27
comments: true
tags: foo, bar
---

A reader recently got in touch with me regarding my 2017 blog post [Review:
Theorems for Free](/blog/theorems-for-free/).
He had some questions about the paper/my review, and upon revisiting it,
I realized that I had no idea how the paper worked anymore.

So I decided to rehash my understanding, and came up with something much
conceptually clearer about what is happening and why.

A quick summary of *Theorems for Free*:

> For any polymorphic type, we can generate a law that must hold for any value
> of that type.

One the examples given is for the function `length :: forall a. [a] -> Int`,
which states that `forall f l. length (fmap f l) = length l`---namely, that
`fmap` doesn't change the length of the list.

*Theorems for Free* gives a roundabout and obtuse set of rules for computing
these free theorems. But, as usual, the clarity of the idea is obscured by the
encoding details.

The actual idea is this:

> Parametrically-polymorphic functions can't branch on the specific types they
> are instantiated at.

Because of this fact, functions must behave the same way, regardless of the
type arguments passed to them. So all of the free theorems have the form
"replacing the type variables *before* calling the function is the same as
replacing the type variables *after* calling the function."

What does it mean to replace a type variable? Well, if we want to replace a type
variable `a` with `a'`, we will generate a fresh function `f :: a -> a'`, and
then stick it wherever we need to.

For example, given the function `id :: a -> a`, we generate the free theorem:

```haskell
forall f a.
  f (id a) = id (f a)
```

or, for the function `fromJust :: Maybe a -> a`, we get:

```haskell
forall f ma.
  f (fromJust ma) = fromJust (fmap f ma)
```

This scheme also works for functions in multiple type parameters. Given the
function `swap :: (a, b) -> (b, a)`, we must replace both `a` and `b`, giving
the free theorem:

```haskell
forall
    (f :: a -> a')
    (g :: b -> b')
    (p :: (a, b))
  swap (bimap f g p) = bimap g f (swap p)
```

In the special case where there are no type parameters, we don't need to do
anything. This is what's happening in the `length` example given in the
introduction.

Simple stuff, right? The obfuscation in the paper comes from the actual
technique given to figure out where to apply these type substitutions. The paper
is not fully general here, in that it only gives rules for the `[]` and `(->)`
type constructors (if I recall correctly.) These rules are further obscured in
that they inline the definitions of `fmap`, rather than writing `fmap`
directly.[^before-typeclasses] But for types in one variable, `fmap` is exactly
the function that performs type substitution.

[^before-typeclasses]: Perhaps this paper predates typeclasses? Very possible.

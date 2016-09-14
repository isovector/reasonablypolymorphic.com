---
layout: post
title: Dependent Data Types a la Carte
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

##

To be honest with you, my approach to [procedurally generating RPG
stories][stories] has been stymied until very recently. Recall the command
functor:

```haskell
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | forall x y. Interrupt (Free StoryF x) (Free StoryF y) (y -> a)
              | -- whatever else
```

This recursively defined `Interrupt` command has caused more than its fare share
of grief. The idea is that it should represent one potential line of action
being interrupted by another. The semantics are rather hazy, but this should
result in grafting the `Free StoryF y` monad somewhere inside of the `Free
StoryF x` monad. Once we've done whatever analysis on the original story, we can
then forget that the `Interrupt` bit was ever there in the first place.

In effect, we want this:

```haskell
data StoryF' a = Change Character ChangeType (ChangeResult -> a)
               | -- whatever else

runInterrupt :: StoryF a -> StoryF' a
runInterrupt = -- ???
```

where `runInterrupt`'s job is to remove any instances of the `Interrupt` command
from our story -- replacing them with the "canonical" version of what actually
happened.

Of course, we could just remove all of the `Interrupt` data constructors from
our `Free StoryF a` object, and rely on convention to keep track of that for us.
However, if you're like me, whenever the phrase "by convention" is used, big
alarm bells should go off in your head. Convention isn't enforced by the
compiler, and so anything maintained "by convention" is highly suspect to bugs.

What would make our lives better is if we could define `StoryF` and `StoryF'`
somehow in terms of one another, so that there's no hassle to keep them in sync
with one another. Even better, in the future, maybe we'll want to remove or add
other constructors as we interpret our story.

What we really want to be able to do is to mix and match individual constructors
into one larger data structure, which we can then transform as we see fit.

Fortunately for us, the machinery for this has already been built. It's
Swierstra's [Data Types a la Carte][dtalc] (henceforth *DTalC*) -- essentially a
set of combinators capable of composing data types together, and tools for
working with them in a manageable way.

Unfortunately for us, as far as I can tell, Data Types a la Carte isn't powerful
enough to allow us to *remove* constructors.

This post presents a variation which is.

But first, we'll discuss *DTalC* as it is described in the original paper, in
order to get a feeling for the approach and where the problems might lie. If
you know how *DTalC* works already, consider skipping to the next heading.



## Data Types a la Carte

Data Types a la Carte presents a novel strategy for building data types out of
other data types with kind[^1] `* -> *`. A code snippet is worth a thousand words,
so let's dive right in. Our `StoryF` command functor as described above would
instead be represented like this:

[^1]: For the uninitiated, kinds are to types as types are to values -- a kind
is the "type" of a type. For example, `Functor` has kind `* -> *` because it
doesn't become a real type until you apply a type to it (`Functor Int` is a
type, but `Functor` isn't).

```haskell
data ChangeF    a = Change Character ChangeType (ChangeResult -> a)
data InterruptF a = forall x y.
                    Interrupt (Free StoryF x) (Free StoryF y) (y -> a)

type StoryF = ChangeF :+: InterruptF
```

Here, `(:+:)` is the type operator which composes data types together into a sum
type (there is a corresponding `(:*:)` for products, but we're less interested
in it today.)

Because the kindedness of `(:+:)` lines up with that of the data types it
combines, we can nest `(:+:)` arbitrarily deep:

```haskell
type Something = Maybe :+: Either Int :+: (,) Bool :+: []
```

In this silly example, `Something a` *might* be any of the following:

* `Maybe a`
* `Either Int a`
* `(Bool, a)`
* `[a]`

but we can't be sure which. We will arbitrary decide that `(:+:)` is
right-associative -- although it doesn't matter in principle (sums are
monoidal), part of our implementation will depend on this fact.

Given a moment, if you're familiar with Haskell, you can probably figure out
what the machinery must look like:

```haskell
data (f :+: g) a = InL (f a)
                 | InR (g a)
                 deriving Functor
infixr 8 :+:
```

`(:+:)` essentially builds a tree of data types, and then you use some
combination of `InL` and `InR` to find the right part of the tree to use.

However, in practice, this becomes annoyingly painful and tedious; adding new
data types can completely shuffle around your internal tree structure, and
unless you're careful, things that used to compile will no longer.

But fear not! Swierstra has got us covered!

```haskell
class (Functor sub, Functor sup) => sub :<: sup where
  inj :: sub a -> sup a
```

This class (and its instances) say that `f :<: fs`  means that the data type `f`
is nestled somewhere inside of the big sum type `fs`. Furthermore, it gives us a
witness to this fact, `inj`, which lifts our small data type into our larger
one. With some clever instances of this typeclass, `inj` will expand to exactly
the right combination of `InL` and `InR`s.

These instances are:

```haskell
instance Functor f => f :<: f where
  inj = id

instance (Functor f, Functor g) => f :<: (f :+: g) where
  inj = InL

instance {-# OVERLAPPABLE #-}
         (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = InR . inj
```

The first one states "if there's nowhere left to go, we're here!". The second:
"if our desired functor is on the left, use `InL`". The third is: "otherwise,
slap a `InR` down and keep looking".

And so, we can now write our smart constructors in the style of:

```haskell
change :: (ChangeF :<: fs) => Character -> ChangeType -> Free fs ChangeResult
change c ct = liftF . inj $ Change c ct id
```

which will create a `Change` constructor in any data type which supports it
(witnessed by `ChangeF :<: fs`).

Astute readers will notice immediately that the structural induction carried out
by `(:<:)` won't actually find the desired functor in any sum tree which isn't
right-associative, since it only ever recurses right. This unfortunate fact
means that we must be *very careful* when defining *DTalC* in terms of type
aliases.

In other words: **we must adhere to a strict convention in order to ensure our
induction will work correctly.**

[stories]:
[dtalc]:

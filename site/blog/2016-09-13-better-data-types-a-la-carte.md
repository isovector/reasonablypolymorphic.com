---
layout: post
title: Better Data Types a la Carte
date: 2016-09-13 23:51
comments: true
tags: haskell, rpg, dsl, data types a la carte, semantics
---

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
Swierstra's [Data Types a la Carte][dtalc] (henceforth DTalC) -- essentially
a set of combinators capable of composing data types together, and tools for
working with them in a manageable way.

Unfortunately for us, Data Types a la Carte isn't as type-safe as we'd like it
to be. <del>Additionally, it's missing (though not *fundamentally*) the
primitives necessary to remove constructors.</del>[^3]

[^3]: EDIT 2016-09-14: After re-reading the paper, it turns out that it
describes (though doesn't implement) this functionality.

This post presents a variation of DTalC which *is* type-safe, and contains the
missing machinery.

But first, we'll discuss DTalC as it is described in the original paper, in
order to get a feeling for the approach and where the problems might lie. If
you know how DTalC works already, consider skipping to the next heading.



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
means that we must be *very careful* when defining DTalC in terms of type
aliases.

In other words: **we must adhere to a strict convention in order to ensure our
induction will work correctly.**



## Better Data Types a la Carte

The problem, of course, is caused by the fact that DTalC can be constructed in
ways that the structural induction can't handle. Let's fix that by constraining
how DTalCs are constructed.

At the same time, we'll add the missing inverse of `inj`, namely `outj :: (f :<:
fs) => fs a -> Maybe (f a)`[^2], which we'll need later to remove constructors,
but isn't fundamentally restricted in Swiestra's method.

[^2]: I couldn't resist the fantastic naming opportunity.

On the surface, our structural induction problem seems to be that we can only
find data types in right-associative trees. But since right-associative trees
are isomorphic to lists, the real flaw is that we're not just using lists in the
first place.

With the help of `{-# LANGUAGE DataKinds #-}`, we can lift lists (among other
term-level things) to the type level. Additionally, using `{-# LANGUAGE
TypeFamilies #-}`, we're able to write *type-level* functions -- functions which
operate on and return types!

We define a type class with an associated data family:

```haskell
class Summable (fs :: [* -> *]) where
    data Summed fs :: * -> *
```

Here `fs` is a *type*, as is `Summed fs`. Take notice, however, of the explicit
kind annotations: `fs` is a list of things that look like `Functor`s, and
`Summed fs` looks like one itself.

Even with all of our fancy language extensions, a type class is still just a
type class. We need to provide instances of it for it to become useful. The
obvious case is if `fs` is the empty list:

```haskell
instance Summable '[] where
    data Summed '[] a = SummedNil Void
                      deriving Functor
```

The funny apostrophe in `'[]` indicates that what we're talking about is an
empty type-level list, rather than the type-constructor for lists. The
distinction is at the kind level: `'[] :: [k]` for all kinds `k`, but `[] :: *
-> *`.

What should happen if we try to join zero data types together? This is obviously
crazy, but since we need to define it to be *something* we make it wrap `Void`.
Since `Void` doesn't have any inhabitants at the term-level, it is
unconstructible, and thus so too is `SummedNil`.

But what use case could an unconstructible type possibly have? By itself,
nothing, but notice that `Either a Void` *must* be `Right a`, since the `Left`
branch can never be constructed. Now consider that `Either a (Either b Void)` is
isomorphic to `Either a b`, but has the nice property that its innermost data
constructor is always `Left` (finding the `a` is `Left`, and finding `b` is
`Right . Left`).

Let's move to the other case for our `Summable` class -- when `fs` isn't empty:

```haskell
instance Summable (f ': fs) where
    data Summed (f ': fs) a = Here (f a)
                            | Elsewhere (Summed fs a)
```

`Summed` for a non-empty list is either `Here` with the head of the list, or
`Elsewhere` with the tail of the list. For annoying reasons, we need to specify
that `Summed (f ': fs)` is a `Functor` in a rather obtuse way:

```haskell
instance Summable (f ': fs) where
    data Summed (f ': fs) a = Functor f => Here (f a)
                            | Elsewhere (Summed fs a)

{-# LANGUAGE StandaloneDeriving #-}
deriving instance Functor (Summed fs) => Functor (Summed (f ': fs))
```

but this now gives us what we want. `Summed fs` builds a nested sum-type from a
type-level list of data types, and enforces (crucially, *not* by convention)
that they form a right-associative list. We now turn our attention to building
the `inj` machinery *a la* Data Types a la Carte:

```haskell
class Injectable (f :: * -> *) (fs :: [* -> *]) where
    inj :: f a -> Summed fs a
```

We need to write instances for `Injectable`. Note that there is no instance
`Injectable '[] fs`, since `Summable '[]` is unconstructible.

```haskell
instance Functor f => Injectable f (f ': fs) where
    inj = Here

instance {-# OVERLAPPABLE #-} Injectable f fs => Injectable f (g ': fs) where
    inj = Elsewhere . inj
```

These instances turn out to be *very inspired* by the original DTalC.  This
should come as no surprise, since the problem was with our construction of
`(:+:)` -- which we have now fixed --  rather than our induction on `(:<:)`.

At this point, we could define an alias between `f :<: fs` and `Injectable f
fs`, and call it a day with guaranteed correct-by-construction data types a la
carte, but we're not quite done yet.

Remember, the original reason we dived into all of this mumbo jumbo was in order
to *remove* data constructors from our DTalCs. We can't do that yet, so we'll
need to set out on our own.

We want a function `outj :: Summed fs a -> Maybe (f a)` which acts as a prism
into our a la carte sum types. If our `Summed fs a` is constructed by a `f a`,
we should get back a `Just` -- otherwise `Nothing`. We define the following type
class:

```haskell
class Outjectable (f :: * -> *) (fs :: [* -> *]) where
    outj :: Summed fs a -> Maybe (f a)
```

with instances that again strongly resemble DTalC:

```haskell
instance Outjectable f (f ': fs) where
    outj (Here fa)     = Just fa
    outj (Elsewhere _) = Nothing

instance {-# OVERLAPPABLE #-} Outjectable f fs => Outjectable f (g ': fs) where
    outj (Here _ )      = Nothing
    outj (Elsewhere fa) = outj fa
```

The first instance says, "if what I'm looking for is the head of the list, return
that." The other says, "otherwise, recurse on an `Elsewhere`, or stop on a
`Here`."

And all that's left is to package all of these typeclasses into something more
easily pushed around:

```haskell
class ( Summable fs
      , Injectable f fs
      , Outjectable f fs
      , Functor (Summed fs)
      ) => (f :: * -> *) :<: (fs :: [* -> *])
instance ( Summable fs
         , Injectable f fs
         , Outjectable f fs
         , Functor (Summed fs)
         ) => (f :<: fs)
```

This is a trick I learned from [Edward Kmett's great talk on Monad
Homomorphisms][homos], in which you build a class that has all of the right
constraints, and then list the same constraints for an instance of it. Adding
the new class as a constraint automatically brings all of its dependent
constraints into scope; `f :<: fs` thus implies `Summable fs`, `Injectable f
fs`, `Outjectable f fs`, and `Functor (Summed fs)` in a much more terse manner.

As a good measure, I wrote a test that `outj` is a left-inverse of `inj`:

```haskell
injOutj_prop :: forall fs f a. (f :<: fs) => Proxy fs -> f a -> Bool
injOutj_prop _ fa = isJust $ (outj (inj fa :: Summed fs a) :: Maybe (f a))

{-# LANGUAGE TypeApplications #-}
main = quickCheck (injOutj_prop (Proxy @'[ []
                                         , Proxy
                                         , Maybe
                                         , (,) Int
                                         ]) :: Maybe Int -> Bool)
```

where we use the `Proxy fs` to drive type checking for the otherwise hidden `fs`
from the type signature in our property.

And there you have it! Data types a la carte which are guaranteed
correct-by-construction, which we can automatically get into and out of. In the
next post we'll look at how rewriting our command functor in terms of DTalC
solves all of our `Interrupt`-related headaches.

A working version of all this code together can be found [on my GitHub
repository][code].

[stories]: http://reasonablypolymorphic.com/tags/rpg.html
[dtalc]: http://www.cs.ru.nl/~W.Swierstra/Publications/DataTypesALaCarte.pdf
[homos]: https://www.youtube.com/watch?v=YTaNkWjd-ac
[code]: https://github.com/isovector/dependent-types/blob/b30a0620539733580e194a0edf582fcf8431d3fd/src/Stories.hs#L72-L112

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

If you're going to memorize any two *particular* examples of monoids, it had
better be these two:

```haskell
instance Monoid [a] where
  mempty = []
  a <> b = a ++ b

instance (Monoid a, Monoid b) => Monoid (a, b) where
  mempty = (mempty, mempty)
  (a1, b1) <> (a2, b2) = (a1 <> a2, b1 <> b2)
```

The first says that lists form a monoid under the empty list and concatenation.
The second says that products preserve monoids.

The list monoid instance is responsible for the semantics of the ordered,
"sequency" data structures. That is, if I have some sequential flavor of data
structure, its monoid instance should probably satisfy the equation `toList a <>
toList b = toList (a <> b)`. Sequency data structures are things like lists,
vectors, queues, deques, that sort of thing. Data structures where, when you
combine them, you assume there is no overlap.

The second monoid instance here, over products, is responsible for pretty much
all the other data structures. The first thing we can do with it is remember
that functions are just really, really big product types, with one "slot" for
every value in the domain. We can show an isomorphism between pairs and
functions out of booleans, for example:

```haskell
from :: (Bool -> a) -> (a, a)
from f = (f False, f True)

to :: (a, a) -> (Bool -> a)
to (a, _) False = a
to (_, a) True  = a
```

and under this isomorphism, we should thereby expect the `Monoid a => Monoid
(Bool -> a)` instance to agree with `Monoid a => Monoid (a, a)`. If you
generalize this out, you get the following instance:

```haskell
instance Monoid a => Monoid (x -> a) where
  mempty = \_ -> mempty
  f <> g = \x -> f x <> g x
```

which combines values in the codomain monoidally. We can show the equivalence
between this monoid instance and our original product preservation:

```haskell
  from f <> from g
= (f False,  f True) <> (g False, g True)
= (f False <> g False, f True <> g True)
= ((f <> g) False, (f <> g) True)
= from (f <> g)
```

and

```haskell
  to (a11, a12) <> to (a21, a22)
= \x -> to (a11, a12) x <> to (a21, a22) x
= \x -> case x of
    False -> to (a11, a12) False <> to (a21, a22) False
    True  -> to (a11, a12) True  <> to (a21, a22) True
= \x -> case x of
    False -> a11 <> a21
    True  -> a12 <> a22
= \x -> to (a11 <> a21, a12 <> a22) x
= to (a11 <> a21, a12 <> a22)
```

which is a little proof that our function monoid agrees with the
preservation-of-products monoid. The same argument works for any type `x` in the
domain of the function, but showing it generically is challenging.

Anyway, I digresss.

The reason to memorize *this* `Monoid` instance is that it's the monoid instance
that every data structure is trying to be. Recall that *almost all* data
structures are merely different encodings of functions, designed to make some
operations more efficient than they would otherwise be.

Don't believe me? A `Map k v` is an encoding of the function `k -> Maybe v`
optimized to efficiently query which `k` values map to `Just` something. That is
to say, it's a sparse representation of a function.


## From Theory to Practice

What does all of this look like in practice? Stuff like worrying about `foldr`
is surely programming-in-the-small, which is worth knowing, but isn't the sort
of thing that turns the tides of a successful application.

The reason I've been harping on about the function and product monoids is that
they are compositional. The uninformed programmer will be surprised by just far
one can get by composing these things.

At work, we need to reduce a tree (+ nonlocal references) into an
honest-to-goodness graph. While we're doing it, we need to collect certain
nodes. And the tree has a few constructors which semantically change the scope
of their subtrees, so we need to preserve that information as well.

It's actually quite the exercise to sketch out an algorithm that will accomplish
all of these goals when you're thinking about explicit mutation. Our initial
attempts at implementing this were clumsy. We'd fold the tree into a graph,
adding fake nodes for the `Scope` construcotrs. Then we'd filter all the nodes
in the graph, trying to find the ones we needed to collect. Then we'd do a graph
traversal from the root, trying to find these `Scope` nodes, and propagating
their information downstream.

Rather amazingly, this implementation kinda sorta worked! But it was slow, and
took $O(10k)$ SLOC to implement.

The insight here is that everything we needed to collect was monoidal:

```haskell
data Solution = Solution
  { graph :: Graph
  , collectedNodes :: Set Node
  , metadata :: Map Node Metadata
  }
  deriving stock (Generic)
  deriving (Semigroup, Monoidally) via Generically Solution
```

where the `deriving (Semigroup, Monoidally) via Generically Solution` stanza
gives us the semigroup and monoid instances that we'd expect from `Solution`
being the product of a bunch of other monoids.

And now for the *coup de grace*: we hook everything up with the `Writer` monad.
`Writer` is a chronically slept-on type, because most people seem to think it's
useful only for logging, and, underwhelming at doing logging compared to a real
logger type. But the charm is in the details:

```haskell
instance Monoid w => Monad (Writer w)
```

`Writer w` is a *monad* whenever `w` is a *monoid*, which makes it the perfect
monad for solving data-structure-creation problems like the one we've got in
mind. Such a thing gives rise to a few helper functions:

```haskell
collectNode :: MonadWriter Solution m => Node -> m ()
collectNode n = tell $ mempty { collectedNodes = Set.singleton n }

addMetadata :: MonadWriter Solution m => Node -> Metadata -> m ()
addMetadata n m = tell $ mempty { metadata = Map.singleton n m }

emitGraphFragment :: MonadWriter Solution m => Graph -> m ()
emitGraphFragment g = tell $ mempty { graph = g }
```

each of which is responsible for adding a little piece to the final solution.
Our algorithm is thus a function of the type:

```haskell
algorithm
  :: Metadata
  -- ^ the current scope
  -> Tree
  -- ^ the tree we're reducing
  -> Writer Solution Node
  -- ^ our partial solution, and the node corresponding to the root of the tree
```

which traverses the `Tree`, recursing with a different `Metadata` whenever it
comes across a `Scope` constructor, and calling our helper functions as it goes.
At each step of the way, the only thing it needs to return is the root `Node` of
the section of the graph it just built, which recursing calls can use to break
up the problem into inductive pieces.

This new implementation is roughly 20x smaller, coming in at @O(500)@ SLOC, and
was free of all the bugs we'd been dilligently trying to squash under the
previous implementation.

Chalk it down to another win for induction!


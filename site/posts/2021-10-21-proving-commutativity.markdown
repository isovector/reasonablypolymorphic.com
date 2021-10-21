---
layout: post
title: Proving Commutativity of Polysemy Interpreters
date: 2021-10-21 00:53
comments: true
tags: polysemy, testing, quickcheck
---

To conclude this [series of posts][series] on [polysemy-check][check], today
we're going to talk about how to ensure your effects are sane. That is, we want
to prove that correct interpreters compose into correct programs. If you've
followed along with the series, you won't be surprised to note that
`polysemy-check` can test this right out of the box.

[series]: /tags/polysemy.html
[check]: https://github.com/polysemy-research/polysemy-check

But first, what does it mean to talk about the correctness of composed
interpreters? This idea comes from Yang and Wu's [Reasoning about effect
interaction by fusion][fusion]. The idea is that for a given program, changing
the order of two subsequent actions from different effects should not change the
program. Too abstract? Well, suppose I have two effects:

[fusion]: https://dl.acm.org/doi/10.1145/3473578

```haskell
foo :: Member Foo r => Sem r ()
bar :: Member Bar r => Sem r ()
```

Then, the composition of interpreters for `Foo` and `Bar` is correct if and only
if[^not-quite] the following two programs are equivalent:

[^not-quite]: Well, there is a second condition regarding distributivity that is
  required for correctness. The paper goes into it, but `polysemy-check` doesn't
  yet implement it.

```haskell
forall m1 m2.
  m1 >> foo >> bar >> m2
=
  m1 >> bar >> foo >> m2
```

That is, since `foo` and `bar` are actions from different effects, they should
have *no influence on one another.* This sounds like an obvious property;
effects correspond to individual units of functionality, and so they should be
completely independent of one another. At least --- that's how we humans think
about things. Nothing actually forces this to be the case, and extremely
hard-to-find bugs will occur if this property doesn't hold, because it breaks a
mental abstraction barrier.

It's hard to come up with good examples of this property being broken in the
wild, so instead we can simulate it with a different broken abstraction. Let's
imagine we're porting a legacy codebase to `polysemy`, and the old code hauled
around a giant stateful god object:

```haskell
data TheWorld = TheWorld
  { counter :: Int
  , lots    :: Int
  , more'   :: Bool
  , stuff   :: [String]
  }
```

To quickly [get everything ported][porting], we replaced the original `StateT
TheWorld IO` application monad with a `Member (State TheWorld) r` constraint.
But we know better than to do that for the long haul, and instead are starting
to carve out effects. We introduce `Counter`:

[porting]: /blog/porting-to-polysemy/

```haskell
data Counter m a where
  Increment :: Counter m ()
  GetCount :: Counter m Int

makeSem ''Counter
```

with an interpretation into our god object:

```haskell
runCounterBuggy
    :: Member (State TheWorld) r
    => Sem (Counter ': r) a
    -> Sem r a
runCounterBuggy = interpret $ \case
  Increment ->
    modify $ \world -> world
                         { counter = counter world + 1
                         }
  GetCount ->
    gets counter
```

On its own, this interpretation is fine. The problem occurs when we use
`runCounterBuggy` to handle `Counter` effects that coexist in application code
that uses the `State TheWorld` effect. Indeed, `polysemy-check` tells us what
goes wrong:

```haskell
quickCheck $
  prepropCommutative @'[State TheWorld] @'[Counter] $
    pure . runState defaultTheWorld . runCounterBuggy
```

we see:

```
Failed.

Effects are not commutative!

k1  = Get
e1 = Put (TheWorld 0 0 False [])
e2 = Increment
k2  = Pure ()

(k1 >> e1 >> e2 >> k2) /= (k1 >> e2 >> e1 >> k2)
(TheWorld 1 0 False [],()) /= (TheWorld 0 0 False [],())
```

Of course, these effects are not commutative under the given interpreter,
because changing `State TheWorld` will overwrite the `Counter` state! That's not
to say that this sequence of actions *actually exists* anywhere in your
codebase, but it's a trap waiting to happen. Better to take defensive action
and make sure nobody can ever even *accidentally* trip this bug!

The bug is fixed by using a different data store for `Counter` than `TheWorld`.
Maybe like this:

```haskell
runCounter
    :: Sem (Counter ': r) a
    -> Sem r a
runCounter = (evalState 0) . reinterpret @_ @(State Int) $ \case
  Increment -> modify (+ 1)
  GetCount -> get
```

Contrary to the old handler, `runCounter` now introduces its own anonymous
`State Int` effect (via `reinterpret`), and then immediately eliminates it. This
ensures the state is invisible to all other effects, with absolutely no
opportunity to modify it. In general, this `evalState . reintrpret` pattern is a
very good one for implementing pure effects.

Of course, a really complete solution here would also remove the `counter` field
from `TheWorld`.

Behind the scenes, `prepropCommutative` is doing exactly what you'd expect ---
synthesizing monadic preludes and postludes, and then randomly pulling effects
from each set of rows and ensuring everything commutes.

At first blush, using `prepropCommutative` to test all of your effects feels
like an $O(n^2)$ sort of deal. But take heart, it really isn't! Let's say our
application code requires `Members (e1 : e2 : e3 : es) r`, and our eventual composed
interpreter is `runEverything :: Sem ([e] ++ es ++ [e3, e2, e1] ++ impl) a -> IO
(f a)`. Here, we only need $O(es)$ calls to `prepropCommutative`:

* `prepropCommutative @'[e2] @'[e1] runEverything`
* `prepropCommutative @'[e3] @'[e2, e1] runEverything`
* ...
* `prepropCommutative @'[e] @'(es ++ [e2, e1]) runEverything`

The trick here is that we can think of the composition of interpreters as an
interpreter of composed effects. Once you've proven an effect commutes with a
particular row, you can then add that effect into the row and prove a different
effect commutes with the whole thing. Induction is pretty cool!

As of today there is no machinery in `polysemy-check` to automatically generate
this linear number of checks, but it seems like a good thing to include in the
library, and you can expect it in the next release.

To sum up these last few posts, `polysemy-check` is an extremely useful and
versatile tool for proving correctness about your `polysemy` programs. It can be
used to show the semantics of your effects (and adherence of such for their
interpreters.) It can show the equivalence of interpreters --- such as the ones
you use for testing, and those you use in production. And now we've seen how to
use it to ensure that the composition of our interpreters maintains its
correctness.

Happy testing!


---
layout: post
title: Proving Equivalence of Polysemy Interpreters
date: 2021-10-16 12:06
comments: true
tags: polysemy, testing, quickcheck
---

Let's talk [more][last-blog] about [`polysemy-check`][polysemy-check]. Last week
we looked at how to do property-testing for a `polysemy` effects' laws. Today,
we'll investigate how to show that two interpretations are equivalent.

[last-blog]: https://reasonablypolymorphic.com/blog/polysemy-check/
[polysemy-check]: https://github.com/polysemy-research/polysemy-check

To continue with last week's example, let's say we have an effect that
corresponds to having a `Stack` that we can push and pop:

```haskell
data Stack s m a where
  Push      :: s -> Stack s m ()
  Pop       :: Stack s m (Maybe s)
  RemoveAll :: Stack s m ()
  Size      :: Stack s m Int

deriving instance Show s => Show (Stack s m a)
deriveGenericK ''Stack

makeSem ''Stack
```

Since we'd like to prove the equivalence of two interpretations, we'll need to
first write two interpretations. But, to illustrate, we're going simulate
multiple interpreters via a single interpretation, parameterized by which bugs
should be present in it.

purposes of brevity, we'll write a single interpretation of `Stack s` in terms
of `State [s]`, and then interpret _that_ in two different ways. In essence,
what we're really testing here is the equivalence of two `State`
interpretations, but it's good enough for an example.

We'll start with the bugs:

```haskell
data Bug
  = PushTwice
  | DontRemove
  deriving stock (Eq, Ord, Show, Enum, Bounded)

instance Arbitrary Bug where
  arbitrary = elements [minBound..maxBound]

hasBug :: [Bug] -> Bug -> Bool
hasBug = flip elem
```

The `PushTwice` bug, as you might expect, dispatched a `Push` command so that it
pushes twice onto the stack. The `DontRemove` bug causes `RemoveAll` to be a
no-op. Armed with our bugs, we can write a little interpreter for `Stack` that
translates `Stack s` commands into `State [s]` commands, and then immediately
runs the `State` effect:

```haskell
runStack
    :: [Bug]
    -> Sem (Stack s ': r) a
    -> Sem r ([s], a)
runStack bugs =
  (runState [] .) $ reinterpret $ \case
    Push s -> do
      modify (s :)
      when (hasBug bugs PushTwice) $
        modify (s :)

    Pop -> do
      r <- gets listToMaybe
      modify (drop 1)
      pure r

    RemoveAll ->
      unless (hasBug bugs DontRemove) $
        put []

    Size ->
      gets length
```

For our efforts we are rewarded: `runState` gives rise to four interpreters for
the price of one. We can now ask whether or not these interpreters are
equivalent. Enter `propEquivalent`:

With these interpreters out of the way, it's time to answer our original
question: are `pureStack` and `ioStack` equivalent? Which is to say, do they get
the same answer for every possible program? Enter `propEquivalent`:

```haskell
prepropEquivalent
    :: forall effs r1 r2 f
     . ( forall a. Show a => Show (f a)
       , forall a. Eq a => Eq (f a)
       )
    => ( Inject effs r1
       , Inject effs r2
       , Arbitrary (Sem effs Int)
       )
    => (forall a. Sem r1 a -> IO (f a))
    -> (forall a. Sem r2 a -> IO (f a))
    -> Property
```

All of the functions in `polysemy-check` have fun type signatures like this one.
But despite the preponderance of `forall`s, it's not as terrible as you might
think. The first ten lines here are just constraints. There are only two
arguments to `prepropEquivalent`, and they are the two interpreters you'd like
to test.

This type is crazy, and it will be beneficial to understand it. There are four
type variables, three of which are effect rows. We can distinguish between them:

- `effs`: The effect(s) you're interested in testing. In our case, our
  interpreter handles `Stack s`, so we let `effs ~ Stack s`.
- `r1`: The effects handled by interpreter 1. Imagine we had an interpreter for
  `Stack s` that ran it via `IO` instead. In that case, `r1 ~ '[State s, Embed
  IO]`.
- `r2` The effects handled by interpreter 2.

The relationships that must between `effs`, `r1` and `r2` are $effs \subset r1$
and $effs \subset r2$. When running `prepropEquivalent`, you *must* type-apply
`effs`, because Haskell isn't smart enough to figure it out for itself.

The other type variable to `prepropEquivalent` is `f`, which allows us to
capture the "resulting state" of an interpreter. In `runStack :: [Bug] -> Sem
(Stack s ': r) a -> Sem r ([s], a)`, you'll notice we transform a program
returning `a` into one returning `([s], a)`, and thus `f ~ (,) [s]`. If your
interpreter doesn't produce any resulting state, feel free to let `f ~
Identity`.

We're finally ready to test our interpreters! For any equivalence relationship,
we should expect something to be equivalent to itself. And this is true
regardless of which bugs we enable:

```haskell
prop_reflexive :: Property
prop_reflexive = do
  bugs <- arbitrary
  pure $
    prepropEquivalent @'[Stack Int]
      (pure . run . runStack bugs)  -- pure is getting us into IO
      (pure . run . runStack bugs)
```

So what's happening here? Internally, `prepropEquivalent` is generating random
programs of type `Sem '[Stack Int] Int`, and lifting that into `Sem r1 Int` and
`Sem r2 Int`, and then running both interpreters and ensuring the result is the
same for every program. Note that this means any fundamental non-determinism in
your interpretation will break the test! Make sure to use appropriate
interpreters for things like clocks and random values!

To strengthen our belief in `prepropEquivalent`, we can also check that
`runStack` is *not* equivalent to itself if different bugs are enabled:

```haskell
prop_bugsNotEquivalent :: Property
prop_bugsNotEquivalent =
  expectFailure $
    prepropEquivalent @'[Stack Int]
      (pure . run . runStack [PushTwice])
      (pure . run . runStack [])
```

Running this test will give us output like:

```
+++ OK, failed as expected. Falsified (after 3 tests):
([0,0],1) /= ([0],1)
```

The counterexample here isn't particularly helpful (I haven't yet figured out
how to `show` the generated program that fails,) but you can get a hint here by
noticing that the stack (the `[0,0]`) is twice as big in the first result as in
the second.

Importantly, by specifying `@'[Stack Int]` when calling `prepropEquivalent`, we
are guaranteed that the generated program will *only* use actions from `Stack
Int`, so it's not too hard to track down. This is another win for `polysemy` in
my book --- that we can isolate bugs with this level of granularity, even if we
can't yet perfectly point to them.

All of today's code (and more!) is [available][test] as a test in `polysemy-check`, if
you'd like to play around with it. But that's all for now. Next week we'll
investigate how to use `polysemy-check` to ensure that the composition of your
effects *themselves* is meaningful. Until then!

[test]: https://github.com/polysemy-research/polysemy-check/blob/master/test/ExampleSpec.hs


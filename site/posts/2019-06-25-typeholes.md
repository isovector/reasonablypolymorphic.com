---
layout: post
title: "Implement With Types, Not Your Brain!"
date: 2019-06-25 14:56
comments: true
tags: haskell, beginner
---

When asked about the virtues of Haskell's strong type system, most people will
say the best part is that it lets you refactor with a zen-like tranquility, or
that it stops your program from crashing at runtime. I mean, those are both
great. But my favorite part is that having a strong type system means I don't
need to use my brain to do programming.

It sounds snide, but it's true. Here's a function from [my library
polysemy][polysemy]:

[polysemy]: https://github.com/polysemy-research/polysemy

```haskell
hoistStateIntoStateT
    :: Sem (State s ': r) a
    -> S.StateT s (Sem r) a
hoistStateIntoStateT (Sem m) = m $ \u ->
  case decomp u of
    Left x -> S.StateT $ \s ->
      liftSem . fmap swap
              . weave (s, ())
                      (\(s', m') -> fmap swap
                                  $ S.runStateT m' s')
                      (Just . snd)
              $ hoist hoistStateIntoStateT x
    Right (Yo Get z _ y _)     -> fmap (y . (<$ z)) $ S.get
    Right (Yo (Put s) z _ y _) -> fmap (y . (<$ z)) $ S.put s
```

Gee, that's complicated! I must be really smart to have written such a function,
right?

Wrong! I just have a trick!

The technique is called "just use type holes," and for my money, it's the most
important skill in a Haskeller's tool-belt. The idea is to implement the tiny
part of a function that you know how to do, and then ask the compiler for help
on the rest of it. It's an iterative process. It's a discussion with the
compiler. Each step of the way, you get a little closer to the right answer, and
after enough iterations your function has written itself --- even if you're not
entirely sure *how.*

Let's go through an example together. Consider the random type signature that I
just made up:

```haskell
jonk :: (a -> b) -> ((a -> Int) -> Int) -> ((b -> Int) -> Int)
```

If you want a challenge, take a few minutes to try to implement this function.
It's tricky, and most people get lost along the way. When you're convinced that
it's sufficiently hard, continue reading.

The first step of writing a function is to bind all of the variables we have.
That's the `a -> b` and `(a -> Int) -> Int` bits here. I usually give them names
that help me remember their types --- such as `ab` and `aii`, respectively.

Then, bang out a `_` on the right hand side. This thing is a placeholder, and is
called a type hole.

```haskell
jonk ab aii = _
```

Try to compile this (consider using something like [ghcid][ghcid] so you don't
need to call `ghc` by hand.) The compiler will yell at you:

[ghcid]: https://github.com/ndmitchell/ghcid

```
    • Found hole: _ :: (b -> Int) -> Int
      Where: ‘b’ is a rigid type variable bound by
               the type signature for:
                 jonk :: forall a b.
                         (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
               at /home/sandy/Test.hs:3:1-62
    • In the expression: _
      In an equation for ‘jonk’: jonk ab aii = _
    • Relevant bindings include
        aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
        ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
        jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
          (bound at /home/sandy/Test.hs:4:1)
  |
4 | jonk ab aii = _
  |
```

A common complaint from beginners is that GHC's error messages are noisy. This
is true. To a first approximation, the useful bit of this error message is this:

```
• Found hole: _ :: (b -> Int) -> Int
• Relevant bindings include
    aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
    ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
    jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
      (bound at /home/sandy/Test.hs:4:1)
```

There's no way of getting GHC to shut up about that other stuff, so you just
need to train yourself to focus on this core piece of information. That's not to
say the other stuff *isn't* helpful, just that this stuff is almost always
enough.

So what is the compiler telling us? Two things:

1. The expression we want to replace `_` with must have type `(b -> Int) -> Int`.
2. We have some local binds (`aii`, `ab`, `jonk`, and their types) that we can
   use to help with the implementation.

Using this information, our goal is to write the correct expression in place of
the type hole. In most cases doing that in one step is unfeasible, but we can
often write a little more of expression, and use a type hole in *that*.

In this case, we notice that our hole has type `(b -> Int) -> Int`, which is to
say, that it's a function that takes a `(b -> Int)` and returns an `Int`. As
such, it means we should bind the `(b -> Int)` in a lambda:

```haskell
jonk ab aii = \bi -> _
```

The resulting error message in full is this:

```
    • Found hole: _ :: Int
    • In the expression: _
      In the expression: \ bi -> _
      In an equation for ‘jonk’: jonk ab aii = \ bi -> _
    • Relevant bindings include
        bi :: b -> Int (bound at /home/sandy/Test.hs:4:16)
        aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
        ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
        jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
          (bound at /home/sandy/Test.hs:4:1)
      Valid hole fits include
        maxBound :: forall a. Bounded a => a
          with maxBound @Int
          (imported from ‘Prelude’ at /home/sandy/Test.hs:1:1
           (and originally defined in ‘GHC.Enum’))
        minBound :: forall a. Bounded a => a
          with minBound @Int
          (imported from ‘Prelude’ at /home/sandy/Test.hs:1:1
           (and originally defined in ‘GHC.Enum’))
  |
4 | jonk ab aii = \bi -> _
  |
```

GHC now mentions "Valid hole fits". In my experience, these are almost always
useless, so I just exclude them. In GHCi, the following incantation will make
them disappear.

```
:set -fmax-valid-hole-fits=0
```

(or you can just squint and ignore them manually!)

Again, ignoring the irrelevant pieces of the error message, we can pare GHC's
response down to this:

```
• Found hole: _ :: Int
• Relevant bindings include
    bi :: b -> Int (bound at /home/sandy/Test.hs:4:16)
    aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
    ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
    jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
      (bound at /home/sandy/Test.hs:4:1)
```

OK, great! Now we just need to produce an `Int`. While we could just put `0`
here, that is a *clearly wrong* solution, since we wouldn't be using any of
`ab`, `aii` or `bi`. Don't just return `0`.

But we notice that both `aii` and `bi` will return an `Int`. Since that's what
we want to return, the odds are good that we want to call one of these functions
in this hole. Let's choose `aii` as a guess. Feel free to write in your notebook
that you are guessing about `aii`, but also `bi` could have been chosen --- we
have no guarantees that `aii` is the right call!

```haskell
jonk ab aii = \bi -> aii $ _
```

```
• Found hole: _ :: a -> Int
• Relevant bindings include
    bi :: b -> Int (bound at /home/sandy/Test.hs:4:16)
    aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
    ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
    jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
      (bound at /home/sandy/Test.hs:4:1)
```

Our hole has a function type, so let's introduce a lambda:

```haskell
jonk ab aii = \bi -> aii $ \a -> _
```

```
• Found hole: _ :: Int
• Relevant bindings include
    a :: a (bound at /home/sandy/Test.hs:4:29)
    bi :: b -> Int (bound at /home/sandy/Test.hs:4:16)
    aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
    ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
    jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
      (bound at /home/sandy/Test.hs:4:1)
```

We need to produce an `Int` again. Since we don't have one in scope, our only
options are again `aii` and `bi`. But we've already used `aii`, so let's try
`bi` this time.

```haskell
jonk ab aii = \bi -> aii $ \a -> bi $ _
```

```
• Found hole: _ :: b
• Relevant bindings include
    a :: a (bound at /home/sandy/Test.hs:4:29)
    bi :: b -> Int (bound at /home/sandy/Test.hs:4:16)
    aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
    ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
    jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
      (bound at /home/sandy/Test.hs:4:1)
```

Great! Now we need to produce a `b`. We have a function that can do that, `ab ::
a -> b`. So let's call *that*:

```haskell
jonk ab aii = \bi -> aii $ \a -> bi $ ab $ _
```

```
• Found hole: _ :: a
• Relevant bindings include
    a :: a (bound at /home/sandy/Test.hs:4:29)
    bi :: b -> Int (bound at /home/sandy/Test.hs:4:16)
    aii :: (a -> Int) -> Int (bound at /home/sandy/Test.hs:4:9)
    ab :: a -> b (bound at /home/sandy/Test.hs:4:6)
    jonk :: (a -> b) -> ((a -> Int) -> Int) -> (b -> Int) -> Int
      (bound at /home/sandy/Test.hs:4:1)
```

Finally, we have a hole whose type is `a`. And we *have* an `a`! Let's just use
that thing!

```haskell
jonk ab aii = \bi -> aii $ \a -> bi $ ab $ a
```

```
[1 of 1] Compiling Main             ( /home/sandy/Test.hs, interpreted )
Ok, one module loaded.
```

Cool! It worked! We just wrote a non-trivial function without doing any
thinking, really. Not bad! But can we be confident that our implementation is
any good?

The first line of defense against this is to enable `-Wall`. In GHCi, you can do
this via:

```
:set -Wall
```

You'll notice there are no warnings generated by our definition. This is usually
enough of a sanity check that our implementation is fine. For example, let's see
what happens when we try the *obviously stupid* implementation:

```haskell
jonk ab aii = \bi -> 0
```

```
/home/sandy/Test.hs:4:6: warning: [-Wunused-matches]
    Defined but not used: ‘ab’
  |
4 | jonk ab aii = \bi -> 0
  |      ^^

/home/sandy/Test.hs:4:9: warning: [-Wunused-matches]
    Defined but not used: ‘aii’
  |
4 | jonk ab aii = \bi -> 0
  |         ^^^

/home/sandy/Test.hs:4:16: warning: [-Wunused-matches]
    Defined but not used: ‘bi’
  |
4 | jonk ab aii = \bi -> 0
  |
```

Those warnings are pointing out that we haven't used everything available to us.
If we assume that the _type of `jonk` is correct_, then any implementation of
`jonk` which doesn't use all of its variables is *extremely suspect.*

The other common way to go wrong here is that you'll notice that `jonk` comes up
in the relevant bindings *while trying to write `jonk`.* For example, this thing
will happily typecheck:

```haskell
jonk = jonk
```

But this too is clearly wrong, since we haven't done any work. The situation
becomes more insidious when you call yourself recursively _after doing some
work_, which can be correct. Let's look at an example of that.

Let's try this type on for size:

```haskell
zoop :: (a -> b -> b) -> b -> [a] -> b
```

The first thing to do is to bind all of our variables:

```haskell
zoop abb b as = _
```

But we notice that `as` has type `[a]`. Since `[a]` has two constructors, let's
pattern match on those before going any further.

```haskell
zoop abb b []       = _
zoop abb b (a : as) = _
```

```
• Found hole: _ :: b
• Relevant bindings include
    b :: b (bound at /home/sandy/Test.hs:4:10)
    abb :: a -> b -> b (bound at /home/sandy/Test.hs:4:6)
    zoop :: (a -> b -> b) -> b -> [a] -> b
      (bound at /home/sandy/Test.hs:4:1)

• Found hole: _ :: b
• Relevant bindings include
    as :: [a] (bound at /home/sandy/Test.hs:5:17)
    a :: a (bound at /home/sandy/Test.hs:5:13)
    b :: b (bound at /home/sandy/Test.hs:5:10)
    abb :: a -> b -> b (bound at /home/sandy/Test.hs:5:6)
    zoop :: (a -> b -> b) -> b -> [a] -> b
      (bound at /home/sandy/Test.hs:4:1)
```

Oh god! Too many holes at once. My brain is already exploding. You honestly
expect me to keep this much information in my head at once?? Instead, we can
replace one of the holes with `undefined` in order to get GHC to shut up and let
us focus.

```haskell
zoop abb b []        = _
zoop abb b (a : as) = undefined
```

```
• Found hole: _ :: b
• Relevant bindings include
    b :: b (bound at /home/sandy/Test.hs:4:10)
    abb :: a -> b -> b (bound at /home/sandy/Test.hs:4:6)
    zoop :: (a -> b -> b) -> b -> [a] -> b
      (bound at /home/sandy/Test.hs:4:1)
```

Much easier. We see that we need to produce a `b`, and hey, look at that. We
already have one. Furthermore, *we don't* have an `a`, and so we have *no
chance* of calling `abb`. So we assume `b` is correct. Let's fill it in, and
then replace our `undefined` with a hole again:

```haskell
zoop abb b []       = b
zoop abb b (a : as) = _
```

```
• Found hole: _ :: b
• Relevant bindings include
    as :: [a] (bound at /home/sandy/Test.hs:5:17)
    a :: a (bound at /home/sandy/Test.hs:5:13)
    b :: b (bound at /home/sandy/Test.hs:5:10)
    abb :: a -> b -> b (bound at /home/sandy/Test.hs:5:6)
    zoop :: (a -> b -> b) -> b -> [a] -> b
      (bound at /home/sandy/Test.hs:4:1)
```

Again we want to produce a `b`. We *could* use the `b` we have, but that would
mean `abb` is completely unused in our function. So let's assume we want to call
`abb` instead. Since it takes two arguments, let's give the first one a hole,
and the second `undefined`. One step at a time.

```haskell
zoop abb b []       = b
zoop abb b (a : as) = abb _ undefined
```

```
• Found hole: _ :: a
• Relevant bindings include
    as :: [a] (bound at /home/sandy/Test.hs:5:17)
    a :: a (bound at /home/sandy/Test.hs:5:13)
    b :: b (bound at /home/sandy/Test.hs:5:10)
    abb :: a -> b -> b (bound at /home/sandy/Test.hs:5:6)
    zoop :: (a -> b -> b) -> b -> [a] -> b
      (bound at /home/sandy/Test.hs:4:1)
```

We want an `a`. And we have an `a`. Since we have no guarantees that `as` isn't
`[]`, this `a` is our only choice. So it's pretty safe to assume our hole should
be filled with `a`.

```haskell
zoop :: (a -> b -> b) -> b -> [a] -> b
zoop abb b []       = b
zoop abb b (a : as) = abb a _
```

```
• Found hole: _ :: b
• Relevant bindings include
    as :: [a] (bound at /home/sandy/Test.hs:5:17)
    a :: a (bound at /home/sandy/Test.hs:5:13)
    b :: b (bound at /home/sandy/Test.hs:5:10)
    abb :: a -> b -> b (bound at /home/sandy/Test.hs:5:6)
    zoop :: (a -> b -> b) -> b -> [a] -> b
      (bound at /home/sandy/Test.hs:4:1)
```

So we need to produce a `b`, and we still have the unused `as :: [a]` to work
with, so it's unlikely to just be our binding `b`. Instead, our only option
which takes a `[a]` is `zoop` itself! This is a recursive call, but we've
already popped the head off our list, so it's not going to be an infinite loop.

Lets fill in our hole with `zoop _ _ as`. Or, `zoop _ undefined as` if you
prefer.

```haskell
zoop abb b []       = b
zoop abb b (a : as) = abb a $ zoop _ undefined as
```

```
• Found hole: _ :: a -> b -> b
• Relevant bindings include
    as :: [a] (bound at /home/sandy/Test.hs:5:17)
    a :: a (bound at /home/sandy/Test.hs:5:13)
    b :: b (bound at /home/sandy/Test.hs:5:10)
    abb :: a -> b -> b (bound at /home/sandy/Test.hs:5:6)
    zoop :: (a -> b -> b) -> b -> [a] -> b
      (bound at /home/sandy/Test.hs:4:1)
```

Probably `abb`, because we're recursing, and have no real reason to want to
change this function. Fill it in, and, for the same argument, replace our
`undefined` with `b`. Our final function in all its glory is this:

```haskell
zoop :: (a -> b -> b) -> b -> [a] -> b
zoop abb b []       = b
zoop abb b (a : as) = abb a $ zoop abb b as
```

And it works! Except that `-Wall` yells at us:

```
/home/sandy/Test.hs:4:6: warning: [-Wunused-matches]
    Defined but not used: ‘abb’
  |
4 | zoop abb b []       = b
  |
```

This is a little alarming, until we realize that `abb` isn't *not* used in
`zoop`, it's just not used in this branch. We can put a wildcard to match `abb`
here to get rid of this warning:

```haskell
zoop :: (a -> b -> b) -> b -> [a] -> b
zoop _   b []       = b
zoop abb b (a : as) = abb a $ zoop abb b as
```

(note that this `_` on the left-hand side of the equals sign is *not* a type
hole, it's a wildcard pattern match!)

Finally we're finished! A little experimentation will convince you that this
`zoop` thing we just wrote is in fact just `foldr`! Pretty impressive for just
blindly filling in holes, no?

I'm not going to say that blindly filling in type holes *always* works, but I'd
say maybe 95% of the time? It's truly amazing just how far you can get by
writing down the right type and making sure you use every variable.

The reason why this works is known as [theorems for free][theorems], which
roughly states that we can infer lots of facts about a type signature (assuming
it's correct.) One of those facts we can infer is often the *the only
possible implementation.* It's cool as fuck, but you don't need to understand
the paper to use this idea in practice.

[theorems]: /blog/theorems-for-free/

One question you might have is "what the heck does it mean for a type to be
correct?" Good question! It means your type should be *as polymorphic as
possible*. For example, if you want a function that creates a list with length
$n$, where all elements are the same value, then that thing should have type
`Int -> a -> [a]`, not `Int -> Bool -> [Bool]`. Because we can do this operation
for any type, we don't need to give it a monomorphic type. Here we would say
`Int -> a -> [a]` is the correct type for this operation, while `Int -> Bool ->
[Bool]` is not.

You know when people say "types are not an alternative to documentation?" I
think this is a pretty knock-down argument to that claim. Once you really
understand the typesystem, most of the time, types *really are* the best
documentation --- they often tell you *exactly* what the function does, in a way
that English comments never will.

In conclusion, a strong type system is fucking awesome because it's smart enough
to know the necessary type of any given expression. Which means you can slowly
use type holes to chip away at a difficult implementation, without ever really
knowing what you're doing. It's *marvelous.* Get into the habit of using this
technique, and you'll quickly be amazed at just how good you get at Haskell.


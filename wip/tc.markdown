---
layout: post
title: tc
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

[Last time][passes] we chatted about using a GHC plugin to run custom
Core-to-Core transformations on the programs that GHC is compiling. Doing so
allows us to add custom optimization passes, and even other, more *exotic*
things like [rewriting lambda expression as categorical operations][concat].

[passes]:
[concat]:

Today I want to talk about another sort of GHC plugin: *type-checker plugins!*
TC plugins let you hook into GHC's constraint machinery and help it solve
domain-specific problems that it wouldn't be able to otherwise. One of the more
interesting examples of a TC plugin is [nomeata's][nomeata] [ghc-justdoit][jdi]
--- which will automatically generate a value of the correct type, essentially
letting you leave implementations as "exercises for the compiler."

[nomeata]:
[jdi]:

[Polysemy][polysemy] uses a TC plugin in order to improve type-inference. The
result is that it can provide type-inference that is as good as `mtl`'s, without
succumbing to the pitfalls that accompany `mtl`'s approach.

[polysemy]:


## The Problem

Consider the following program:

```haskell
foo :: MonadState Int m => m ()
foo = modify (+ 1)
```

Such a thing compilers and runs no problem. There are no surprises here for any
Haskell programmers who have ever run into `mtl`. But the reason it works is
actually quite subtle. If we look at the type of `modify` we see:

```haskell
modify :: MonadState s m => (s -> s) -> m ()
```

which suggests that the `s -> s` function we pass to it should determine the `s`
parameter. But our function `(+ 1)` has type `Num a => a -> a`, therefore the
type of `modify (+1)` should be this:

```haskell
modify (+ 1) :: (MonadState s m, Num s) => m ()
```

So the question is, why the heck is GHC willing to use a `MonadState Int m`
constraint to solve the wanted `(MonadState s m, Num s)` constraint arising from
a use of `modify (+1)`? The problem feels analogous to this one, which *doesn't
work:*

```haskell
bar :: Show Bool => a -> String
bar b = show b  -- doesn't work
```

Just because we have a `Show Bool` constraint in scope _doesn't mean that `a` is
a `Bool`!_ So how come we're allowed to use our `MonadState Int m` constraint,
to solve a `(MonadState s m, Num s)`? Completely analogously, _we don't know
that `s` is an `Int`!_

The solution to this puzzler is in the definition of `MondState`:

```haskell
class Monad m => MonadState s (m :: * -> *) | m -> s where
```

Notice this `| m -> s` bit, which is known as a *functional dependency*  or a
*fundep* for short. The fundep says "if you know `m`, you also know `s`," or
equivalently, "`s` is completely determined by `m`." And so, when typechecking
`foo`, GHC is asked to solve both `MonadState Int m` and `(Num s, MonadState s
m)`. But since there can only be a *single instance* of `MonadState` for m, this
means that `MonadState Int m` and `MonadState s m` _must be the same_.
Therefore `s ~ Int`.

This is an elegant solution, but it comes at a cost --- namely that we're only
allowed to use a single `MonadState` at a time! If you're a longtime Haskell
programmer, this probably doesn't feel like a limitation to you; just stick all
the pieces of state you want into a single type, and then use some classy fields
to access them, right? [Matt Parsons][parsonsmatt] has [a blog post][trouble] on
the pain points, and some bandages, for doing this with typed errors. At the end
of the day, the real problem is that we're only allowed a single `MonadError`
constraint.

[parsonsmatt]:
[trouble]: https://www.parsonsmatt.org/2018/11/03/trouble_with_typed_errors.html

Polysemy "fixes the glitch" by just not using fundeps. This means you're
completely free to use as many state, error, and whatever effects you want all
at the same time. The downside? Type-inference sucks again. Indeed, the
equivalent program to `foo` in `polysemy` doesn't compile by default:

```haskell
foo' :: Member (State Int) r => Sem r ()
foo' = modify (+ 1)
```

```
• Ambiguous use of effect 'State'
  Possible fix:
    add (Member (State s0) r) to the context of
      the type signature
  If you already have the constraint you want, instead
    add a type application to specify
      's0' directly, or activate polysemy-plugin which
        can usually infer the type correctly.
• In the expression: modify (+ 1)
  In an equation for ‘foo'’: foo' = modify (+ 1)
```

This situation blows chunks. It's obvious what this program should do, so let's
just fix it.


## The Solution

Let's forget about the compiler for a second and ask ourselves how the Human
Brain Typechecker(TM) would type-check this problem. Given the program:

```haskell
foo' :: Member (State Int) r => Sem r ()
foo' = modify (+ 1)
```

A human would look at the `modify` here, and probably run an algorithm similar
to this:

* Okay, what `State` is `modify` running over here?
* Well, it's some sort of `Num`.
* Oh, look, there's a `Member (State Int) r` constraint in scope.
* That thing wouldn't be there if it wasn't necessary.
* I guess `modify` is running over `State Int`.

Pretty great algorithm! Instead, here's what GHC does:

* Okay, what `State` is `modify` running over here?
* Well, it's some sort of `Num`.
* But that thing is polymorphic.
* Guess I'll emit a `(Num n, Member (State n) r)` constraint.
* Why did the stupid human put an unnecessary `Member (State Int) r` constraint
    here?
* What an idiot!

And then worse, it won't compile because the generated `n` type is now ambiguous
and not mentioned anywhere in the type signature!

Instead, let's use a TC plugin to make GHC reason more like a human when it
comes to `Member` constraints.


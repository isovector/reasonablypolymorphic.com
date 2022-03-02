---
layout: post
title: "Polysemy Internals: Freer Interpretations of Higher-Order Effects"
date: 2019-05-31 01:11
comments: true
tags: polysemy, internals, haskell, technical
---

> aka "what the hell is that `Yo` type?"

This is the first post in a series of implementation details in
[`polysemy`][polysemy] --- a fast, powerful and low-boilerplate effect-system
library.

[polysemy]: https://github.com/isovector/polysemy

Even if you're not particularly interested in `polysemy`, there are some
functional pearls here --- and a crash course on the history on the
implementations of free monads in Haskell.

---


Critics of free monads often make the claim that higher-order effects aren't
possible. This has historically been true, but Wu, Schrijvers and Hinze's
paper [Effect Handlers in Scope][effects] gives a technique for lifting the
restriction. Today I want to illustrate the problem, discuss Wu et al.'s
solution, and then show what changes `polysemy` makes to remove the boilerplate.
In the process, we'll look at finding free constructions for tricky typeclasses.

[effects]: https://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf


## The Problem

Let's consider the `Error e` effect, in which we'd like to be able to `throw`
errors of type `e`, and `catch` any errors thrown within a specific block of
code. You're already familiar with this concept, in `transformers` it's called
`ExceptT e`, and in `mtl`, `MonadError e`. A typical usage of this effect might
be:

```haskell
foo =
  catch
    do             -- computation to run
      when (not someBool) $ throw SomeError
      pure True
    \SomeError ->  -- error handler
      pure False
```

We would expect `foo` to be `pure False` whenever `someBool` is `False`; and
vice versa. The idea is that a `throw` should short-circuit the rest of the
computation, until it reaches the end of a `catch` statement. This is the basis
of every exception system of all time, so we won't belabor the example any
further.

Given some appropriate `m`, we'd like to model this problem with the following
interface:

```haskell
throw :: e -> m a
catch :: m a -> (e -> m a) -> m a
```

In first-order effect systems such as [`freer-simple`][freer-simple], our
effects have kind `* -> *`. With such a kind, we can easily model `throw`, but
it's less clear how to model `catch`:

[freer-simple]: http://hackage.haskell.org/package/freer-simple

```haskell
data Error e a where
  Throw :: e -> Error e a
  Catch :: ??
```

We simply don't have an `m` available to us in order to write something
equivalent to `m a -> (e -> m a) -> m a`. There are a few unsatisfactory
solutions here --- you can either choose a concrete `m` and bake it in (which
defeats the _entire purpose_ of effect systems), or you can attempt to encode
`m` somewhere inside of the `Error e` part. Neither is fruitful.

`freer-simple` actually takes a pretty clever approach to this problem. Instead
of modeling `catch` in the `Error e` effect, it just provides `catch` as a
function:

```haskell
catch
    :: Member (Error e) r
    => Eff r a
    -> (e -> Eff r a)
    -> Eff r a
catch ma f = -- replace every call to `throw e` in `ma` with `f e`
```

And what do you know, this solution actually works pretty well. It accurately
captures the semantics of `catch` for `ExceptT`. Success! For most people, most
of the time, this implementation of `catch` is perfectly fine.

But let's consider an interpretation of `Error e` which *isn't* completely
analogous to `ExceptT`. After all, the whole point of effect-systems is to be
able to arbitrarily reinterpret the meaning of your programs. So let's pretend
that we're writing an interpretation of the system which wants to audit the
happy code path. As a result, we'd like to log whether or not we successfully
got to the end of a `catch` block.

In essence, we'd like to replace every call to `catch ma f` with:

```haskell
catch' ma f = catch (ma <* logSuccessfulExit) f
```

meaning `logSuccessfulExit` will be called *if and only if* `ma` didn't contain
a `throw` statement.

Unfortunately, the clever encoding of `catch` as a separate function *outside*
of `Effect e` means that this interpretation of `catch` is impossible. The
problem is fundamentally that by virtue of being outside the effect, `catch`
must choose its own interpretation of catching effects, and you're out of luck
if its choice isn't what you want.

This is a bit of a contrived example, but it shows up every time you want to
embed a computation; such as doing callbacks, coroutines, asynchronous work, or
resource bracketing. It's a *big* class of problems that quickly become
untenable in the first-order world.


## Effect Handlers in Scope

[Wu et al. give us a real solution][effects] for the problem above. Instead of
modeling our effects with kind `* -> *`, we give them a kind `(* -> *) -> * ->
*`. This extra `(* -> *)` is enough to hold a monad in. As such, `Error e` is
now modeled as:

```haskell
data Error e m a where
  Throw :: e -> Error e m a
  Catch :: m a -> (e -> m a) -> Error e m a
```

This extra `m` parameter lets us write `Catch` as a constructor, meaning it is
now part of the effect algebra. By writing clever constructors, we can force `m`
to be the effect stack we're running in:

```haskell
catch
    :: Member (Error e) r
    => Eff r a -> (e -> Eff r a) -> Eff r a
```

which nicely ties the recursive knot.

This change is pretty straightforward, and has probably occurred to most people
who've spent any time playing around with the internals of first-order free
monads. However, here is where the first problem sets in.

Effect systems model interpretations of effects as functions. For example, lets'
assume we have a `State s` effect to play with. We can give an interpretation of
it with the type:

```haskell
runState :: s -> Eff (State s ': r) a -> Eff r (s, a)
```

In the first-order world, you can just have `runState` walk through every
action in `Eff`, and handle the `State s` ones. In the higher-order world,
however, we *also* need to run `runState` on all of the *embedded* computations
(like `Catch`) as well --- and then somehow merge the resulting side states back
into the main thread.

Recall above that we tied the recursive knot on `catch`, so that the `m` in
`Error e m` was always equal to the actual `Eff` monad its being run in. By
calling `runState`, we're promising that that `m` is of the form `Eff (State s
': r)`. But now we're eliminating the `State s` effect, *and we want to maintain
the invariant that `m` is the same monad.* Which means, we need to somehow use
`runState` to eliminate the `State s` *inside of* `Catch`.

It makes my head spin, too. English is not particularly good at describing these
kinds of things, so pay attention to the types here:

1. We called `catch :: Eff r a -> (e -> Eff r0 a) -> Eff r0 a` somewhere in our application code
2. We then interpret the application via `runState :: s -> Eff (State s ': r1) a -> Eff r1 (s, a)`
3. As such, we learn that `r0 ~ (State s ': r1)`
4. After calling `runState`, we are left only with `r1` in our effect stack.
5. But `catch` still contains `r0`. We need to transform it into `r1` to maintain
    our invariant that the computations embedded *inside* `catch` are in same
    monad as the call *to* `catch`.

Doing such a thing is going to require a function:

```haskell
call'runState'InsideError
    :: s
    -> Error (Eff (State s ': r)) a
    -> Error (Eff r) (s, a)
```

which for reasons that will become clearer later, we will uncurry into:

```haskell
call'runState'InsideError
    :: (s, Error (Eff (State s ': r)) a)
    -> Error (Eff r) (s, a)
```

The implementation of this function is guided by the types, and looks like this:

```haskell
call'runState'InsideError
    :: (s, Error (Eff (State s ': r)) a)
    -> Error (Eff r) (s, a)
call'runState'InsideError (_, Throw e) = Throw e
call'runState'InsideError (s, Catch ma f) =
  Catch (runState s ma)
        (\e -> runState s $ f e)
```

Such an example is helpful for building intuition, but is completely infeasible
in the real world. Not only do we need one of these functions for every effect
inside of our stack, but we also need one for every interpretation of every
effect in our stack! This is `O(m*n)` functions in the number of effects and
interpretations we have.

The insight of Wu et al. is that we can get this down to `O(n)` --- one function
analogous to `call'runState'InsideError` for each effect. Let's go through the
derivation together.

The first thing to notice is that we don't need to hard-code `runState` in
`call'runState'InsideError'`. It's fine to just pass it in as a parameter:


```haskell
elimStateInsideError
    :: (forall x. (s, Eff (State s ': r) x) -> Eff r (s, x))
    -> (s, Error (Eff (State s ': r)) a)
    -> Error (Eff r) (s, a)
elimStateInsideError _ (_, Throw e) = Throw e
elimStateInsideError elimState (s, Catch ma f) =
  Catch (elimState (s, ma))
        (\e -> elimState (s, f e))
```

Note that the `elimState` function must be rank-2 so that we can use it on every
instance of `Catch` --- there's no guarantee that they'll all be called to
produce the same type.

The next step is to notice that there's a homomorphism here; we transforming a
`(s, m a)` into `m' (s, a)`, by somehow pushing the `(,) s` bit through the
monad. We can make that a little more clear by explicitly factoring it out:

```haskell
elimStateInsideError
    :: (f ~ ((,) s))
    => (forall x. f (Eff (State s ': r) x) -> Eff r (f x))
    -> f (Error (Eff (State s ': r)) a)
    -> Error (Eff r) (f a)
```

This type is identical to before, we've just renamed `(,) s` to `f`. Let's do
the same renaming trick on `Eff (State s ': r)`:

```haskell
elimStateInsideError
    :: ( f ~ ((,) s)
       , m ~ Eff (State s ': r)
       )
    => (forall x. f (m x) -> Eff r (f x))
    -> f (Error m a)
    -> Error (Eff r) (f a)
```

and then *again* on `Eff r`:

```haskell
elimStateInsideError
    :: ( f ~ ((,) s)
       , m ~ Eff (State s ': r)
       , n ~ Eff r
       )
    => (forall x. f (m x) -> n (f x))
    -> f (Error m a)
    -> Error n (f a)
```

As it stands, our current implementation of `elimStateInsideError` will actually
work for any `m` and `n`; so we can just get rid of those renames:

```haskell
elimEffectInsideError
    :: (f ~ ((,) s))
    => (forall x. f (m x) -> n (f x))
    -> f (Error m a)
    -> Error n (f a)
elimEffectInsideError _ (_, Throw e) = Throw e
elimEffectInsideError elim (s, Catch ma f) =
  Catch (elim (s, ma))
        (\e -> elim (s, f e))
```

Let's now *undo* our uncurrying of our `s -> Error m a -> ...`  as `(s, Error m
a) -> ...`. But since we've renamed `s` away, we're not allowed to reference it
anymore. Instead, we can use `f ()`, aka `(s, ())`, which you'll notice is
isomorphic to `s`.

```haskell
elimEffectInsideError
    :: (f ~ ((,) s))
    => (forall x. f (m x) -> n (f x))
    -> f ()
    -> Error m a
    -> Error n (f a)
elimEffectInsideError _ _ Throw e = Throw e
elimEffectInsideError elim (s, ()) (Catch ma f) =
  Catch (elim (s, ma))
        (\e -> elim (s, f e))
```

As one last step, we can rewrite the explicit destructuring of the `f ()`
parameter using its functor instance. Given the ice-cream cone function `(<$) ::
Functor f => a -> f b -> f a`, which replaces the contents of a functor, we can
rewrite `elimEffectInsideError` as follows:

```haskell
elimEffectInsideError
    :: (f ~ ((,) s))
    => (forall x. f (m x) -> n (f x))
    -> f ()
    -> Error m a
    -> Error n (f a)
elimEffectInsideError _ _ Throw e = Throw e
elimEffectInsideError elim s (Catch ma f) =
  Catch (elim $ ma <$ s)
        (\e -> elim $ f e <$ s)
```

and in doing so, are now fully functor-agnostic, so we can get rid of the
`f`-renaming now:

```haskell
elimEffectInsideError
    :: Functor f
    => (forall x. f (m x) -> n (f x))
    -> f ()
    -> Error m a
    -> Error n (f a)
```

That was a lot of work! But we've bought ourselves a huge amount with this. Now
`elimEffectInsideError` is general enough that it supports eliminating *any*
effect inside of `Error`. The last step is to wrap this thing up into a
typeclass, which Wu et al. call `weave`:

```haskell
class (∀ m. Functor m => Functor (e m)) => Effect e where
  weave
      :: (Functor f, Functor m, Functor n)
      => f ()
      -> (∀ x. f (m x) -> n (f x))
      -> e m a
      -> e n (f a)
```

Don't worry about the extra mentions  of `Functor` in this definition; they're
there for reasons we don't care about today.

By giving an instance of `Effect` for `e`, we can now thread any other
effects *through* `e`. If we give an instance of `Effect` for every effect, we
get higher-order effects that can be run through one another in any order. Happy
days!

This `weave` transformation is the major contribution of Effect Handlers in
Scope. And while it does indeed solve the problem of higher-order effects, such
a thing brings with it a lot of boilerplate; we need to write an instance of
`Effect` for each of our effects, which is non-trivial and can't be automated
via today's support for generics.


## Free Effects

Back in the bad old days of [`free`][free], we would have had to model the
first-order version of `Error e` above (the one that just has `Throw`) as
follows:

[free]: http://hackage.haskell.org/package/free

```haskell
data Error e a = forall x. Throw (x -> a)
```

while `State s` would look like this:

```haskell
data State s a
  = Get (s -> a)
  | Put s (() -> a)
```

It's gross, *and* you'd need to give `Functor` instances for both. *AND* you
can't even derive `Functor` for `Error e` due to the existential.

The specifics here aren't very important, but the point is that this was a bunch
of boilerplate that got in the way of doing any work. The main contribution of
Kiselyov and Ishii's paper [Freer Monads, More Extensible Effects][freer] is
that we can use a *free functor* to automate away this boilerplate. The result
is what puts the "simple" in `freer-simple`[^1].

[freer]: https://okmij.org/ftp/Haskell/extensible/more.pdf
[^1]: Plus, it provides better combinators and more helpful error messages.

The free functor is called [`Coyoneda`][coyoneda][^2], and it looks like this:

[thinking]: https://thinkingwithtypes.com/
[coyoneda]: https://www.stackage.org/haddock/lts-13.23/kan-extensions-5.2/Data-Functor-Coyoneda.html
[^2]: For further discussion of `Coyoneda` and how it can help performance, perhaps you might be interested in [my book][thinking].

```haskell
data Coyoneda f b where
  Coyoneda :: f a -> (a -> b) -> Coyoneda f b

instance Functor (Coyoneda f) where
  fmap f' (Coyoneda fa f) = Coyoneda fa (f' . f)
```

As you can see, `Coyoneda f` is a `Functor`, *even when `f` itself isn't.*
`Coyoneda` just accumulates all of the `fmap`s you wanted to do, and you can
choose later what to do with the resulting function.

This got me to thinking. Maybe there's a free `Effect` that can likewise
accumulate all of the `weave`ing we'd like to do, so that library users don't
need to write those instances themselves.

The "trick" to making a free construction is to just make a datatype that stores
each parameter to the characteristic function. In the `Functor` example, you'll
notice a similarity between the types of (flipped) `fmap` and `Coyoneda`:

```haskell
flip fmap :: f a -> (a -> b) -> f b
Coyoneda  :: f a -> (a -> b) -> Coyoneda f b
```

So let's do the same thing, for `weave`, and construct an equivalent datatype.
Recall the type of `weave`:

```haskell
weave
    :: (Functor f, Functor m, Functor n)
    => f ()
    -> (∀ x. f (m x) -> n (f x))
    -> e m a
    -> e n (f a)
```

As a first attempt, let's just turn this thing into a GADT and see what happens.
I called it `Yo` a little because it's sorta like `Coyoneda`, but mostly because
naming things is hard.

```haskell
data Yo e m a where
  Yo :: Functor f
     => e m a
     -> f ()
     -> (forall x. f (m x) -> n (f x))
     -> Yo e n (f a)
```

While this looks right, it turns out to be a no-go. We can't actually give an
instance of `Effect` for `Yo e`. We can get close, by realizing that the
composition of any two functors is also a functor (given via the `Compose`
newtype). With that in mind, it's just a little work to make all of the types
line up:

```haskell
instance Effect (Yo e) where
  weave s' elim' (Yo e s elim) =
    Yo e (Compose $ s <$ s')
         (fmap Compose . elim' . fmap elim . getCompose)
```

Unfortunately, this definition doesn't quite work. The problem is that `weave s
elim` is supposed to result in a `e m a -> e n (f a)`, but ours has type `e m (g
a) -> e n (Compose f g a)`! By hard-coding that `f` into the result of our GADT,
we've painted ourselves into a corner. Similar problems would crop up if we
wanted to give a `Functor` instance to `Yo e m`.

As is so often the case in this line of work, the solution is to make `f`
existential, and to take another function which is responsible for producing the
desired type. We add a `(f a -> b)` parameter to `Yo`, and make it return `Yo e
n b`:

```haskell
data Yo e m a where
  Yo :: Functor f
     => e m a
     -> f ()
     -> (forall x. f (m x) -> n (f x))
     -> (f a -> b)
     -> Yo e n b
```

We can now call `getCompose` in this last function --- in order to undo our
trick of packing the two pieces of state together.

```haskell
instance Effect (Yo e) where
  weave s' elim' (Yo e s elim f) =
    Yo e (Compose $ s <$ s')
         (fmap Compose . elim' . fmap elim . getCompose)
         (fmap f . getCompose)
```

Giving an instance of `Functor (Yo e m)` can also riff on this final parameter,
exactly in the same way that `Coyoneda` did:

```haskell
instance Functor (Yo e m) where
  fmap f' (Yo e s elim f) = Yo e s elim (f' . f)
```

(The real implementation also needs `hoist :: (forall x. m x -> n x) -> e m a ->
e n a`, which turns out to be a special case of `weave`. This is left as an
exercise for the ambitious reader.)

All that's left is be able to lift `e m a`s into `Yo e m a`s. In every free
construction I've ever seen, this operation is to just fill all of your
parameters with identity --- and this case is no different!

```haskell
liftYo :: Functor m => e m a -> Yo e m a
liftYo e = Yo e (Identity ()) (fmap Identity . runIdentity) runIdentity
```

We're done! This funny `Yo` construction is powerful enough to coalesce entire
chains of effect interpreters into a single call. We haven't done anything
magical here --- someone still needs to figure out what these functions actually
mean for their interpretation. By collecting it all into a single place, we can
cut down on boilerplate and find easier ways to express these concepts to the
end-user.

But that's a tale for another time, when we talk about `polysemy`'s `Tactics`
machinery.


---
layout: post
title: "Freer, yet Too Costly Higher-order Effects"
date: 2019-03-12 00:16
comments: true
tags: freer-monads, extensible-effects, technical
---

I'm throwing in the towel. For now at least.

As of today I have free, higher-order effects working. Unfortunately, *they are
not fast.* I don't think this is a fundamental limitation, merely that whatever
code I've written isn't amenable to GHC's optimization process.

I've been hammering on this for about 50 hours now. It's been driving me slowly
crazy, and promised myself I'd stop if I hadn't solved it by now. That being
said, before putting this project to rest, I wanted to do a quick write-up
detailing what I've learned, how everything fits together, and where I'm hoping
someone will pick up the ball. [Here's the repository.][github]


## Higher Order Effects

In the [`freer-simple`][freer] model, effects are first-order---meaning they are
unable to embed `Eff` computations inside of them. This is occasionally
annoying, primarily when trying to write `bracket`-like effects.

[freer]: https://github.com/lexi-lambda/freer-simple

You can sort of work around the problem by encoding your scoped computation as
an interpretation of an effect, but this often comes at the cost of fixing the
interpretations of the other effects you're dealing with.

This fundamental limitation comes from the fact that `freer-simple` effects have
kind `* -> *`. There's nowhere in here to stick the `Eff` stack you're working
in. You can kind of hack it in, but it never plays nicely.

The solution is given in the paper [Effect Handlers in Scope][scope], and
implemented in the [`fused-effects`][fused] package. The idea is to parameterize
each of your effects with a monad---ie. they have kind `(* -> *) -> * -> *`.
This parameter gets instantiated at the entire `Eff` stack, as seen by the type
of `send :: Member e r => e (Eff r) a -> Eff r a`

[scope]: http://www.cs.ox.ac.uk/people/nicolas.wu/papers/Scope.pdf
[fused]: https://github.com/fused-effects/fused-effects

While it's an obvious insight, actually getting everything to play nicely is
tricky. The primary issue is how do you push interpretations through these
additional monadic contexts? For example, let's consider a bracket-esque effect:

```haskell
data Bracket m x where
  Bracket :: m a          -- ^ allocate
          -> (a -> m ())  -- ^ deallocate
          -> (a -> m x)   -- ^ use
          -> Bracket m x
```

Assume we want to push a `State` effect through these `m`s. What are the correct
semantics for how the state is accumulated? Should any state changed in the
`deallocate` block count outside of the bracket? What should happen in the `use`
case if an exception is thrown and the rest of the block is short-circuited?

Not only are we concerned with the semantics, but also the actual mechanism of
propagating this state throughout the computation.

Effect Handlers in Scope introduces `weave` in a typeclass, which is responsible
for this state-propagation behavior. Statefulness for an effect is encoded as
some arbitrarily chosen functor `f`, and `weave` describes how the effect should
move that state through the effect. Behold:

```haskell
class Effect e where
  weave
      :: Functor f
      => f ()
      -> (forall x. f (m x) -> n (f x))
      -> e m a
      -> e n (n (f a))
```

The `f ()` parameter is the current "state of the world", and the rank-2 thing
is this distribution law. You can intuit the `m` parameter being an effect stack
with all of the effects present, and the `n` parameter as being the same effect
stack---but with the top of it taken off. To clarify, we could monomorphize it
thusly:

```haskell
weave
    :: Functor f
    => f ()
    -> (forall x. f (Eff (g ': r) x) -> Eff r (f x))
    -> e (Eff (g ': r)) a
    -> e (Eff r) (Eff r (f a))
```

This janky return type: `e (Eff r) (Eff r (f a))` comes from the fact that
Effect Handlers in Scope describes a traditional "free" (as opposed to freer)
approach to a free monad. The last parameter of an effect is actually a
continuation for the next piece of the computation. By mangling it, we're
ensuring the caller (which will be library code) respects the evaluation
semantics.

`weave` implicitly defines the evaluation semantics of an effect---it pins how
state propagates through them, which in turn defines which pieces of the effect
are observable to the outside.


## Freeing the Higher Orders

> Warning: This next section describes a janky-ass solution to the problem. It's
> clearly a hack and clearly not the right answer. But maybe by writing out what
> I did, someone with a keen eye can point out where I went wrong.

So this is all well and good. It works, but requires a lot of boilerplate. As
presented in the paper, a new effect requires:

* A `Functor` instance
* An `MFunctor` instance (providing `hoist :: forall x. (f x -> g x) -> e f a -> e g a`)
* An `Effect` instance as above, and an additional method not described here

If you're following in the `fused-effects` tradition, for each interpretation
you *additionally* need a new `Carrier` type, with its own `Functor`,
`Applicative` and `Monad` instances, and then another typeclass tying the effect
to its carrier.

`fused-effects` improves the $O(n^2)$ MTL instance problem to $O(n)$---albeit
with a big constant factor :(

This is a huge amount of work! I've said it before and I'll say it again: *ain't
nobody got time for that.* If it feels like too much work, people aren't going
to do it. A solution that depends on humans not being lazy isn't one that's
going to take off.

So wouldn't it be nice if we could just all of this effect stuff for free?

Here's where I admittedly went a little off the rails. The first step towards
getting a freer `Functor`-less `Monad` instance for `Eff` is to define it in
terms of its final encoding. I made the obvious changes to [last time][toofast]
without thinking too much about it:

[toofast]: https://reasonablypolymorphic.com/blog/too-fast-too-free/

```haskell
newtype Freer f a = Freer
  { runFreer
        :: forall m
         . Monad m
        => (forall x. f (Freer f) x -> m x)
        -> m a
  }
```

I have no idea if this is *right*, but at least it gives a `Monad` instance for
free. One limitation you'll notice is that the continuation in `runFreer` is a
natural transformation, and thus it's *unable to change its return type.*

That means interpretations like `runError :: Eff (Error e ': r) a -> Eff r
(Either e a)` are surprisingly difficult to implement. More on this later---I
just wanted to point out this flaw.

From here I followed [Oleg][oleg] and implemented `Eff` as a type synonym,
making sure to tie the knot and instantiate the `m` parameter correctly:

[oleg]: http://okmij.org/ftp/Haskell/extensible/more.pdf

```haskell
type Eff r = Freer (Union r (Eff r))
```

But how can we get a free implementation for `weave`?

It's this mental thing I came up with, which is sort of like `Coyoneda` but for
`weave`:

```haskell
data Yo e m a where
  Yo :: (Monad n, Functor f)
     => e m a
     -> f ()
     -> (forall x. f (m x) ~> n (f x))
     -> (f a -> b)
     -> Yo e n b
```

> In retrospect, I would not spend any more time on this approach---I'd just
> make people give an instance of `weave` for higher-order effects, and
> machinery to derive it automatically for first-order ones.
>
> But then how can we get an `MFunctor` instance for free? You can't just derive
> it generically---lots of higher-order effects want existentials, and thus
> can't have `Generic` instances.

This `Yo` thing mirrors the definition of `weave` pretty closely. The idea is
that it can accumulate arbitrarily many `weave`s into a single `Yo`, and then
dispatch them all simultaneously.

Some interesting points to note are that the state functor `f` is
existentialized, and that there is this final `f a -> b` parameter to make it
play nicely with the `Union` (more on this in a second.) We can implement
`weave` now by replacing the existing state functor with a `Compose` of the new
one and the old one.

```haskell
weave
    :: (Monad m, Monad n, Functor f)
    => f ()
    -> (forall x. f (m x) -> n (f x))
    -> Union r m a
    -> Union r n (f a)
weave s' distrib (Union w (Yo e s nt f)) =
  Union w $
    Yo e (Compose $ s <$ s')
         (fmap Compose . distrib . fmap nt . getCompose)
         (fmap f . getCompose)
```

We can also use `Yo` to get a free `MFunctor` instance:

```haskell
instance MFunctor (Yo e) where
  hoist f (Yo e s nt z) = Yo e s (f . nt) z
```

OK, all of this works I guess. But what's with this weird `f a -> b` thing in
`Yo` that I mentioned earlier? Well recall the type of `runFreer`, when
instantiated at `Union`:

```haskell
runFreer
    :: forall m
     . Monad m
    => (forall x. Union r (Eff r) x -> m x)
    -> m a
```

The only way we can produce an `m a` is via this rank-2 thing, which is a
natural transformation from `Union r (Eff r)` to `m`. In other words, it's not
allowed to change the type. We can't just stuff the `f` into the result and
return an `m (f a)` instead---this thing doesn't form a `Monad`! Fuck!

All of this comes to a head when we ask ourselves how to actually get the state
out of such a contraption. For example, when we call `runState` we want the
resulting state at the end of the day!

The trick is the same one I used in the last post---we're able to instantiate
the `m` inside `runFreer` at whatever we like, so we just choose `StateT s (Eff
r)` and then run that thing afterwards. Again, *this is very clearly a hack.*

Because `weave` is given freely, interpretations must eventually actually decide
what that thing should look like. Some combinators can help; for example, this
is the interface I came up with for implementing `runBracket`:

```haskell
runBracket
    :: Member (Lift IO) r
    => (Eff r ~> IO)
    -> Eff (Bracket ': r) a
    -> Eff r a
runBracket finish = deep $ \start continue -> \case
  Bracket alloc dealloc use -> sendM $
    X.bracket
      (finish $ start alloc)
      (finish . continue dealloc)
      (finish . continue use)
```

The `deep` combinator gives you `start` and `continue` (which are the cleverly
disguised results of `weave`), and asks you to give a natural transformation
from your effect into `Eff r`.

The actual implementation of `deep` isn't going to win any awards in
understandability, or in inline-ability:

```haskell
deep
    :: (∀ m f y
           . Functor f
          => (forall x. m x -> (Eff r (f x)))
          -> (∀ i o. (i -> m o) -> f i -> Eff r (f o))
          -> e m y
          -> Eff r (f y)
       )
    -> Eff (e ': r) a
    -> Eff r a
deep transform (Freer m) = m $ \u ->
  case decomp u of
    Left x -> liftEff $ hoist (deep transform) x
    Right (Yo eff state nt f) -> fmap f $
      transform
        (deep transform . nt . (<$ state))
        (\ff -> deep transform . nt . fmap ff)
        eff
```

> Notice that whoever implements `transform` needs to give an equivalent of an
> implementation of `weave` anyway. Except that instead of only writing it once
> per effect, they need to write it per interpretation.

We can also give an implementation for `runState` in terms of a `StateT s`:

```haskell
runState :: forall s r a. s -> Eff (State s ': r) a -> Eff r (s, a)
runState s = flip runStateT s . go
  where
    go :: forall x. Eff (State s ': r) x -> StateT s (Eff r) x
    go (Freer m) = m $ \u ->
      case decomp u of
        -- W T F
        Left x -> StateT $ \s' ->
          liftEff . weave (s', ())
                          (uncurry (flip runStateT))
                  $ hoist go x
        Right (Yo Get state nt f) -> fmap f $ do
          s' <- get
          go $ nt $ pure s' <$ state
        Right (Yo (Put s') state nt f) -> fmap f $ do
          put s'
          go $ nt $ pure () <$ state
```

This is *also completely insane.* Notice the aptly-named section `W T F`, where
for no reason I can discern other than satisfying the typechecker, we convert
from a `StateT s` to a `(s, ())` and back again. But why?? Because this is what
`weave` wants---and we need to satisfy `weave` because it's the only way to
change the type of a `Union`---and we need to do *that* in order to reinterpret
everything as a `StateT s`.

There is a similarly WTF implementation for `runError`. But worse is the
combinator I wrote that generalizes this pattern for running an effect in terms
of an underlying monad transformer:

```haskell
shundle
   :: ∀ a f t e r
    . ( MonadTrans t
      , ∀ m. Monad m => Monad (t m)
      , Functor f
      )
   => (∀ x. Eff r (f x) -> t (Eff r) x)
   -> (∀ x. t (Eff r) x -> Eff r (f x))
   -> (∀ x. f (t (Eff r) x) -> Eff r (f x))
   -> f ()
   -> (∀ m tk y
          . Functor tk
         => (∀ x. f () -> tk (m x) -> Eff r (f (tk x)))
         -> tk ()
         -> e m y
         -> t (Eff r) (tk y)
      )
   -> Eff (e ': r) a
   -> Eff r (f a)
shundle intro finish dist tk zonk = finish . go
  where
    go :: ∀ x. Eff (e ': r) x -> t (Eff r) x
    go (Freer m) = m $ \u ->
      case decomp u of
        Left x -> intro . liftEff . weave tk dist $ hoist go x
        Right (Yo e sf nt f) -> fmap f $
          zonk (\r -> shundle intro finish dist r zonk . nt) sf e
```

Don't ask why it's called `shundle` or why it has a variable called `zonk`. It
was funny to me at the time and I needed whatever smiles I could get to continue
making progress. Believe it or not, this abomination does indeed generalize
`runState`:

```haskell
statefully
    :: (∀ m. e m ~> StateT s (Eff r))
    -> s
    -> Eff (e ': r) a
    -> Eff r (s, a)
statefully f s =
  shundle
    (StateT . const)
    (flip runStateT s)
    (uncurry $ flip runStateT)
    (s, ()) $ \_ tk -> fmap (<$ tk) . f

runState :: s -> Eff (State s ': r) a -> Eff r (s, a)
runState = statefully $ \case
  Get    -> get
  Put s' -> put s'
```

`runState` is actually quite reasonable! At this point I was willing to concede
"worse is better"---that most of the time people only really care about
`StateT`-esque state in their effects. And really the only thing they've been
missing is `bracket`. And we now have `bracket`, and an easy way of doing
`StateT`-esque state.

So I was going to hand it in to one library or another---if not for full marks,
then at least for the participation trophy.

But then I ran my benchmark, and saw that it performs 10x *slower* than
`freer-simple`. Even for effect stacks *that don't need to weave.*

**SHAME.**

**SORROW.**

And I guess this is where I leave it. The machinery is clearly **wrong**, but
amazingly it actually does what it says on the tin. Unfortunately it does it so
slowly that I think the people who complain about the performance of free monads
might actually have a point this time.

I've got my heart crossed that someone will swoop in here and say "here's what
you've done wrong" and it will be a minor change and then everything will
optimize away and we will make merry and the freer monad revolution will be
complete.

I'm very tired.

[Here's the repository again][github].

[github]: https://github.com/isovector/too-fast-too-free/tree/higher-rank


## What a Real Solution Would Look Like

I think I have enough familiarity with the problem at this point to know what a
solution would look like---even if I can't find it myself:

* `runFreer` could produce a `f a` if you asked for it
* `Weave` would be a typeclass that effects authors would need to implement. But
    they could derive it for free if the `m` parameter was unused. This would be
    the only instance necessary to implement by hand.
* The library would provide a [`handleRelayS`][relay]-esque interface for defining
    interpreters.
* By the time the user's code ran for the interpretation, every monadic value in
    their effect would be bindable without any further effort---ala `cata`.

[relay]: https://github.com/lexi-lambda/freer-simple/blob/ec84ae4e23ccba1ae05368100da750c196bbbcbb/src/Control/Monad/Freer/Internal.hs#L291-L308

I'd also be happy if an existing solution (probably `fused-effects`) were given
the tools to satisfy the above list. In particular, the `handleRelayS` thing.


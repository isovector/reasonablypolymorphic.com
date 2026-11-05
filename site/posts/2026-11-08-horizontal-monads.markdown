---
layout: post
title: Musically Horizontal Monads
date: 2026-11-08 10:55
comments: true
tags: music, haskell, yoneda
---

Sorry for the delay! My household has had a couple of chaotic days of
everyone-being-very-very-sick and house guests and 4:30am airport drop-offs. But
we're back! This blog post got written in several parts over several days, so it
might be a little disjointed. Apologies.

Anyway...

In the [last post][spans] we discussed a way of attaching durations to
instantaneous musical events: just wrap them with a duration, stupid! Then we
wrote a function

[spans]: /blog/musical-spans/

```haskell
spanning :: SF (Event (), Event a) (Event (Span a))
```

which takes an event stream of stopping points, as well as an event stream of
starting points[^oops]. It then spans each starting event until the next stop or
start. The stops are there so that we can add silence if necessary.

[^oops]: Writing that sentence out makes it clear that I got the arguments
         backwards. Oops!

Having a function like `spanning` around is cool because it means we can just
emit starting and stopping events from whatever upstream process we might like,
and it will automatically turn them into "rhythm." And of course, that upstream
process is welcome to derive the stop stream from the start stream (or vice
versa), if you don't want to have to think about it.

Anyway, that's all and good. But musicians have a lot of intellectual moment
behind *not* thinking about music that way. Instead they usually just think of
having durations intrinsically attached to notes --- that is to say, they
conceive of the note and the duration at the same time. Since we have an
explicit desideratum here of making it easy to get good results, we ought to
provide some more conventional ways of thinking about writing lines.

Writing lines is usually done as "pick a note and a duration, then after that
duration, pick another note and another duration. Rinse and repeat." Of course,
there's some wiggle room where you can instead choose to *not* select a note and
leave silence in its place. Depending on how functional-programming-pilled you
are, this either sounds like a monoid or a monad. Let's explore both ideas,
starting with the monoid.

A horizontal monoid seems like it ought to sequence one piece of music before
another, in a temporal-sense. That is, `a <> b` should play `a`, and then once
`a` is done, it should play `b`.

Recall that `Signal` already has `Semigroup/Monoid` instances, but looking at
the type, they necessarily can't be the right thing:

```haskell
data Signal a = Signal (Time -> a) [(Time, Segment a)]
  deriving stock Functor
  deriving (Semigroup, Monoid) via Ap Signal a
```

If you're unfamiliar with the [`Ap`][ap] newtype, it lifts the `Semigroup` and
`Monoid` instances over the `Applicative` structure. That is, we've effectively
derived the following instances:

[ap]: https://hackage-content.haskell.org/package/base-4.22.0.0/docs/Data-Monoid.html#t:Ap

```haskell
instance Semigroup a => Semigroup (Signal a) where
  (<>) = liftA2 (<>)

instance Monoid a => Monoid (Signal a) where
  mempty = pure mempty
```

The clue that this is doing the wrong thing for our purposes is the
`Semigroup a =>` constraint. If we were putting one `Signal a` after another *in
time*, we'd never need to combine `a`s, and thus we would have no need for a
`Semigroup a` instance. Thus, this instance *must* be doing a point-wise zip of
times. Which is all to say that this is no good to us.

What we instead must do is build a wrapper type which provides the correct
temporal-sequencing monoid. Let's take a moment to pour over our primitives and
see if any of them are feasible for actually making that happen.

The relevant primitive happens to be `switchS`:

```haskell
switchS :: Signal (a, Event b) -> (b -> Signal a) -> Signal a
```

which long-time readers might recall has [seen some action on this
blog][switching] in the past. The idea is that we will run the first `Signal` until
the first occurrence of the `Event c`, then use that in order to switch to the
given continuation.

[switching]: /blog/yampa-switching/

So `switchS` gives us the "do one thing after another" semantics we want (notice
its lack of a `Semigroup a` constraint!) This happens to be most of the work
done, now it's just a matter of accumulating the rest of the bits we need: the
actual notes we're playing, the start points, and the stop points. Let's package
all of that up into a little datatype:

```haskell
data HState a = HState
  { hs_out :: a
  , hs_starts :: Event ()
  , hs_stops :: Event ()
  }
  deriving stock (Functor, Generic)
  deriving (Semigroup, Monoid) via Generically (HState a)
```

A horizontal structure then is some sort of newtype over `Signal (HState a)`. As
it happens, writing the monadic horizontal structure is going to be a little
more informative at this point, since we can lift the monoidal version out
directly. But we can immediately put `HState` to work!

In the exact style of [Yampa Switching][switching], we will use the
[`Cont`inuation monad][cont], which allows us to bind over the `a` in some
function `(a -> b) -> b` --- in our case, this will be the `(a -> Signal b) ->
Signal b` that curries out of `switchS`. This is already well-treaded territory
on this blog, so you can go read the Yampa Switching post if you're curious
about the exact details here.

[cont]: https://hackage-content.haskell.org/package/mtl-2.3.2/docs/Control-Monad-Cont.html#t:Cont

As a first approximation, wrapping this up gives us the type:

```haskell
newtype Horizontal o a = Horizontal
  { unHorizontal :: Cont (Signal (HState o)) a
  }
```

However, this is somewhat unsatisfactory. `Signal`s are covariant in their
output (here `HState o`), but `Cont` is *invariant* in that parameter. Blinding
moving forward with `Horizontal` as written would mean we wouldn't have an
operation `mapOut :: (o -> o') -> Horizontal o a -> Horizontal o' a` which in
practice turns out to be quite a limitation indeed!

Instead we can do a little bit of a [Yoneda][yoneda]-style encoding, where we
hold onto a function that maps from `o` into the eventual result of the
invariant `r` parameter. Check this thing out:

[yoneda]: https://hackage-content.haskell.org/package/kan-extensions-5.2.8/docs/Data-Functor-Yoneda.html#t:Yoneda

```haskell
newtype Yo f o a = Yo
  { unYo :: forall b. (o -> b) -> Cont (f b) a
}
deriving stock Functor
deriving (Semigroup, Monoid) via Ap (Yo f o) a
```

The idea is that we delay building up our `Cont` until you hand us a way of
mapping from `o` into whatever type `b` you eventually end up wanting. We
usually use a trick like this to get a free *functor*, but here we're using it
to get a free *bifunctor*:

```haskell
instance Bifunctor (Yo f) where
  bimap f g (Yo y) = Yo $ \k -> fmap g $ y $ k . f
```

The `Applicative` and `Monad` instances also come already-paid-for, but we must
write them out ourselves:

```haskell
instance Applicative (Yo r o) where
  pure a = Yo $ const $ pure a
  liftA2 f (Yo a) (Yo b) = Yo $ \k -> liftA2 f (a k) (b k)

instance Monad (Yo r o) where
  Yo m >>= f = Yo $ \k -> m k >>= \a -> unYo (f a) k
```

This concludes our diversion into writing `Yo`. Popping the stack: recall we're
still trying to write a monadic horizontal structure. Which we can now write
out as `Horizontal r o a` (with `r` being left intentionally unmotivated for the
time being), getting all our relevant instances for free:

```haskell
newtype Horizontal r o a = Horizontal
  { unHorizontal :: forall b. (o -> b) -> Cont (Signal (HState b)) a
  }
  deriving (Bifunctor)
    via Yo (Compose Signal HState)
  deriving (Functor, Applicative, Monad)
    via Yo (Compose Signal HState) o
  deriving (Semigroup, Monoid)
    via Yo (Compose Signal HState) o a
```

Take a moment to appreciate how *amazing* GHC is here; each of those deriving
vias is lifting an unrelated type through a polytype `forall b` *and* through a
`Compose`, the latter of which doesn't have most instances we're actually
intersted in![^via]

[^via]: As a little aside, if you're not `deriving` 90%+ of your instances,
    you should start. Good places to look for opportunities involve the wrappers
    in `Data.Monoid` and `GHC.Generics`.

Our primary introduction form for `Horizontal` is `mkHorizontal`, which acts as
one `Signal o` for some amount of time, before rendering a continuation of type
`a`:

```haskell
{-# LANGUAGE ApplicativeDo #-}

mkHorizontal :: Signal o -> Time -> a -> Horizontal r o a
mkHorizontal so t a = Horizontal $ \k -> cont $ switchS $ do
  o <- so
  start <- atS 0 ()
  stop <- atS t ()
  ea <- atS t a
  pure (HState (k o) start stop, ea)
```

Note that we issue a start event at time 0, and both a stop event and switch
event at time `t`. From this we can derive `fill` and `hit`, both of which use a
constant value across their `Signal o`, differing only in what they return as a
monadic continuation:

```haskell
fill :: Time -> a -> Horizontal r a a
fill t a = mkHorizontal (pure a) t a

hit :: Time -> a -> Horizontal r a ()
hit t = void . fill t
```

And of course, the `mapOut` function we had to invent the `Yo` machinery in
order to provide:

```haskell
mapOut :: (o -> o') -> Horizontal r o a -> Horizontal r o' a
mapOut = flip bimap id
```


## A Musical Aside

It's probably worth taking a moment to discuss *what exactly the hell*  is going
on with all of this crazy yoneda continuation monad stuff. What does it *buy*
us?

Lets write a little motif:

```haskell
motif :: Note -> Horizontal r Note Note
motif n = do
  hit (1/4) n
  hit (1/4) $ n + 4
  hit (1/4) $ n + 3
  pure $ n + 2
```

notice that this emits notes relative to its input. In somewhat-standard
notation, `motif F` looks like this[^svg]:

[^svg]: In glorious SVG. Sorry for the shitty image quality in previous posts!

![Motif](/images/music4/out1.cropped.svg)

using this triangle symbol to indicate the continuation. But now check this out.
We can bind the result in order to build a musical sequence; `motif F >>= motif`
looks like this:

![Sequencing Motif](/images/music4/out2.cropped.svg)

This happens to be the underlying machinery in Tymoczko's work on sequences
(chapter 4 of [Tonality][tonality]), though it is not presented as such (and I
suspect he didn't have monads in mind when writing it.)

[tonality]: https://dmitri.mycpanel.princeton.edu/tonality-an-owners-manual.html


## Back to Haskell

Revitalized with a real connection to real musical ideas, we press on through
the mires of abstract nonsense. The most pressing problem remaining is how do we
eliminate `Horizontal`? By means of `unsafeRunHorizontal`:

```haskell
unsafeRunHorizontal
  :: Horizontal r o a
  -> (a -> Signal o)
  -> Signal (HState o)
unsafeRunHorizontal (Horizontal f) k
  = runCont (f id)
  $ fmap (\o -> HState o NoEvent NoEvent) . k
```

which isn't actually unsafe, but *will be* due to a few additions to our API in
a second. But a nicer eliminator is `horizontal`, which as originally promised,
calls `spanning` on our behalf:

```haskell
horizontal :: Horizontal r o a -> Signal (Event (Span o))
horizontal h
  = flip runSF
      ( unsafeRunHorizontal h
      $ const
      $ pure
      $ error "impossible: horizontal sampled too late"
      )
  $ proc (HState o starts stops) -> spanning -< (stops, o <$ starts)
```

Here we use `unsafeRunHorizontal` and pass it a dummy continuation, since we
know we're never going to actually sample it past the duration of our
`Horizontal`. Then we take the output `HState`, sample `o` *only at the start
points*, and pass the stop points through unmolested.

It can also be useful to turn a `Horizontal` directly into an event stream,
ignoring its spans:

```haskell
getHorizontal :: Horizontal r o a -> Signal (Event o)
getHorizontal = fmap (fmap getSpan) . horizontal
```


## Putting Everything to Rest

The final two mysteries remaining are the unmotivated `r` parameter in
`Horizontal r o a`, and why `unsafeRunHorizontal` is unsafe.

Recall that musicians often think about periods of silence, or *rests.* While we
could model rests as a `Nothing` value in a `Maybe`-typed `Horizontal`, this
would get rather in the way of our nice combinators! In particular, nothing says
we must interpret a `Horizontal` as a discrete function; if it's continuous,
then the `Nothing` value would make sense. But if we're exporting discrete
function, then the `Nothing`s never actually show up and the `Just`s are
unnecessary.

So here's the trick; this phantom `r` type in `Horizontal r o a` corresponds to
"are there any rests in this value?" We can use a `DataKinds` to get ourselves a
type-level value to play with:

```
data Restful = HasRests

type Horizontal :: Restful -> Type -> Type -> Type

type role Horizontal nominal representational representational
```

Our new `rest` combinator is the only thing that uses the `r`
parameter:

```haskell
rest :: Time -> Horizontal HasRests a ()
rest t = Horizontal $ const $ cont $ switchS $ do
  stop <- atS 0 ()
  ea <- atS t ()
  pure ( HState (error "impossible: rest can't be sampled") NoEvent stop
       , ea
       )
```

Notice that `rest` sets a stop point at t=0, and doesn't create any new start
points. Furthermore, the actual value of type `a` here is an `error` value. It
claims to be "impossible," which we will enforce momentarily.

Something peculiar here is that we only have a single type of kind `Restful`,
namely `HasRests`. How can we differentiate `Horizontal`s that use `rest` from
those that don't? Our old friend [the ST trick][trick] comes knocking, requiring
that `r` remain fully polymorphic:

[trick]: https://wiki.haskell.org/Monad/ST#An_explanation_in_Haskell-Cafe

```haskell
switchHorizontal
    :: (forall r. Horizontal r o a)
    -> (a -> Signal o)
    -> Signal (HState o)
switchHorizontal h = unsafeRunHorizontal h
```

Now `switchHorizontal` can give us a continuous function *only when the
`Horizontal` doesn't contain any `rest`s!* Usage of `unsafeRunHorizontal` makes
no such guarantees, and thus will crash with the impossible error when used on a
`rest`.

Note that `horizontal` has no such compunctions; it samples its function only at
the designated start points, which `rest` doesn't provide. And since our
semigroup/applicative instances are all temporally end-to-end, nothing can
introduce a start point inside of a `rest`.


## Our Temporal Monoid

We began all of this looking for a temporal monoid whose multiplication would
glue horizontal structures end-to-end. We then switched over to making a monad
that did the same thing, but we don't need to give up on our dreams of monoids!

In fact, `Horizontal` is already the monoid we want, with a minor niggle in that
it wants a semigroup/monoid over the continuation value. If we tie that to be
`()` everything falls out for free:

```haskell
newtype HM r o = HM { unHM :: Horizontal r o () }
  deriving newtype (Semigroup, Monoid)
  -- Get a functor instance via our Bifunctor
  deriving Functor via Data.Bifunnctor.Flip.Flip (Horizontal r) ()
```

I don't actually think this type is worth using, since it means our introduction
forms need to be lifted into this newtype. But it's nice to know that we could
do such a thing if we wanted to!


## Next Time

That's all I have to say about rhythm for now. I don't consider this to be the
last word, but it's as far as I've figured anything out. I've been reading a ton
of textbooks on the topic, and the author who seems to be the *least* confused
about it is [Peter Westergaard][westergaard]. His formulation is in terms of "if
you want a listener to mentally parse a hierarchical structure out of your
notes, what properties would make that parsing easy?"

[westergaard]: https://en.wikipedia.org/wiki/Peter_Westergaard's_tonal_theory#Operations_on_rhythm

That's a thing I'd like to explore further, but I'm on a [publishing
deadline][nanowrimo] here, so I can't take too much time to do research in
between blog posts. Next time we'll discuss [Tymoczko's theory of
harmony][tonality], which will dramatically power up our ability to make
something that sounds like *music.* Until then!

[nanowrimo]: https://nano2.org/


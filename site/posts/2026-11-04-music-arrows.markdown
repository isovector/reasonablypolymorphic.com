---
layout: post
title: Musical Signal Functions
date: 2026-11-04 12:42
comments: true
tags: music, arrows, haskell
---

We've been chatting for a few days about my vision for a constructive model of
music. So far it's been rather loosey-goosey; lots of vibes, some semantics, but
nothing in the way of implementation. Today let's get our boots muddy and do
enough implementation that we have something concrete to talk about.

## Events and Signals

In particular, in [Musical Signals][signals] we discussed a `Signal` type that
is a continuous function of time, equipped with a set of interesting times that
we actually care about. In addition, we proposed an `Event` type that we will
use in conjunction with `Signal`s to signify sparse, discrete functions over
time.

[signals]: /blog/music-signals/

Let's begin with `Event`. It's just a little newtype wrapper around `Maybe`:

```haskell
newtype Event a = MkEvent
  { eventToMaybe :: Maybe a
  }
  deriving stock (Foldable, Traversable, Generic)
  deriving newtype
    (Functor, Applicative, Monad, Eq, Ord, Show, Alternative, Semigroup, Monoid)

{-# COMPLETE Event, NoEvent #-}
pattern Event :: a -> Event a
pattern Event a = MkEvent (Just a)

pattern NoEvent :: Event a
pattern NoEvent = MkEvent Nothing

event :: b -> (a -> b) -> Event a -> b
event b f = maybe b f . eventToMaybe
```

As discussed in the [footnote][footnote] on that page, perhaps we want to not
export the `Event` pattern, the `MkEvent` constructor, or the
`Applicative`/`Monad` instances. That seems likely like the way to go, but I
haven't yet put much thought into whether it solves all the problems. So let's
export them for now (because they are genuinely useful!) and circle back at some
point in the future.

[footnote]: /blog/music-signals/#fn1

My idea for implementing `Signal` is to keep around a bunch of continuous
segments of function, each of which might have a time-of-interest at the exact
instant that the segment starts. A `Segment` is defined thusly:

```haskell
data Segment a = Segment
  { segVal :: Maybe a
  , segment :: Time -> a
    -- ^ Must be meaningfully defined for the *entirety* of time!
  }
  deriving stock Functor
```

The obvious `Applicative Segment` instance has the wrong semantics here, so we
don't provide it. The problem being that `segVal` corresponds to a value of the
function at a time of interest. Which is to say, that if `segVal` is ever
`Just`, it must *remain* `Just` as we `ap` our way through it! But `Applicative`
isn't powerful enough to do that, because filling in the missing data would
require us to know what `Time` we should be sampling the function at.

We address the problem with a new `combine` function:


```haskell
-- | Like 'liftA2' for 'Segment', when we have a concrete time to sample at.
combine :: Time -> (a -> b -> c) -> Segment a -> Segment b -> Segment c
combine t f (Segment a fa) (Segment b fb) =
  Segment
    ( asum
       [ liftA2 f a b
       , fmap (f (fa t)) b
       , fmap (flip f (fb t)) a
       ])
    (liftA2 f fa fb)
```

The `asum` here attempts to fill in the interesting value by combining the
`Maybe`s. If that fails, it then tries to fill it in by fmapping over either
individual interesting value.

Collecting our `Segment`s into a `Signal` requires a few helper functions:
`merge` takes two sorted lists of pairs, and computes a sorted list of
[`These`][these]. The idea being that if both lists have a key at the same
index, we keep both of them around. If only one has a value, we tag it with
which list it came from:

[these]: https://hackage.haskell.org/package/strict-0.5.1/docs/Data-Strict-These.html#t:These

```haskell
-- | Specialized 'Data.Align.align' for sorted pairs.
merge :: Ord a => [(a, b)] -> [(a, c)] -> [(a, These b c)]
merge [] ys       = fmap (fmap That) ys
merge (x : xs) [] = fmap (fmap This) (x : xs)
merge xx@((tx, x) : xs) yy@((ty, y) : ys) =
  case compare tx ty of
    LT -> (tx, This x) : merge xs yy
    GT -> (ty, That y) : merge xx ys
    EQ -> (tx, These x y) : merge xs ys
```

We use `merge` to define `joining`, which does a `scanl` of two sorted lists of
`Segment`s. The idea here is that the two lists are effectively interval trees,
and the intervals are not guaranteed to line up. So we use a `scanl` hold onto
the old value of each until it gets replaced with a new value.

```haskell
joining
    :: Ord a
    => Segment b
    -> Segment c
    -> [(a, Segment b)]
    -> [(a, Segment c)]
    -> [(a, (Segment b, Segment c))]
joining a0 b0 as bs
  = drop 1
  $ scanl
    (\(_, (a, b)) (t, th) ->
      case th of
        This a'     -> (t, (a', open b))
        That b'     -> (t, (open a, b'))
        These a' b' -> (t, (a', b'))
    )
    ( error "unused initial time argument"
    , (a0, b0)
    )
  $ merge as bs

open :: Segment a -> Segment a
open s = s { segVal = Nothing }
```

With all that ceremony out of the way, we're ready to define `Signal`s, which
contain an original `Time -> a` function with no interesting timepoints, and
then a sorted list of new `Segment`s.

```haskell
-- | A piecewise function, built out of 'Segment' intervals.
data Signal a
  = Signal
      (Time -> a)
      -- ^ The function before we have switched to any 'Segment'.
      [(Time, Segment a)]
      -- ^ Sorted by time.
  deriving stock Functor
```

Of course, this is not the only possible implementation of `Signal`, nor am I
claiming it's the best one. It's just one that I came up with that satisfied all
the laws and wasn't slower than molasses. I've also got a relatively-fresh new
baby, so a lot of this got written on very little sleep. Anyway...

Despite `Segment` not admitting an `Applicative` instance, `Signal` does,
because it keeps track of where each `Segment` begins.

```haskell
instance Applicative Signal where
  pure a = Signal (pure a) mempty
  liftA2 f (Signal a as) (Signal b bs)
    = Signal (liftA2 f a b)
    $ fmap (uncurry $ \t -> (t,) . uncurry (combine t f))
    $ joining (Segment Nothing a) (Segment Nothing b) as bs
```

We can show that `Signal` preserves the [semantics we gave][signals] by giving
projections out of it into the semantic domain:

```haskell
sample :: Signal a -> (Time -> a)
sample (Signal fa []) t = fa t
sample (Signal fa ((t0, sa) : as)) t =
  case compare t t0 of
    LT -> fa t
    EQ ->
      case sa of
        Segment Nothing f -> f t
        Segment (Just a) _ -> a
    GT -> sample (Signal (segment sa) as) t
```

This function is the continuous-`μ` given by our semantics. The discrete-`μ` is
called `values`:

```haskell
values :: Signal a -> [(Time, a)]
values (Signal _ as) = mapMaybe (traverse segVal) as
```

which returns a sorted list of interesting times (and their associated values.)
In the `Signal (Event a)` case, we have a more useful function, which gets only
those values which *actually contain a discrete value*:

```haskell
events :: Signal (Event a) -> [(Time, a)]
events = mapMaybe (traverse eventToMaybe) . values
```


## Arrows

`Signal`s are nice representations of interesting-things-over-time. But the
mental model of [abstract modular synthesizers][vibes] is not about
interesting-things-over-time. It's about ways of *transforming and combining*
interesting-things-over-time.

[vibes]: /blog/musical-vision/

Haskell has some deep-cut notation for this, namely the `-XArrows` extension and
its related `proc` notation. Long-time readers of the blog will know that we're
[no][arrows1] [strangers][arrows2] to [arrows][arrows3] here!

[arrows1]: /blog/arrowized-frp/
[arrows2]: /blog/arrows-to-arrows/
[arrows3]: /blog/reviewing-again/

But as a *very* quick recap, given instances of `Category` and `Arrow`:

```haskell
class Category a where
  id  :: a x x
  (.) :: a y z -> a x y -> a x z

class Category a => Arrow a where
  arr   :: (b -> c) -> a b c
  (***) :: a b c -> a b' c' -> a (b, b') (c, c')
```

we gain access to `proc` notation, which is very convenient for composing arrow
values:

```haskell
proc input ->
 a <- foo -< input
 b <- bar -< (input, a)
 let output = qux a b
 returnA -< output
```

This notation is syntactic sugar for the egregious:

```haskell
  arr qux
. id *** bar
. arr (\i -> (snd i, i))
. id *** foo
. arr (\i -> (i, i))
```

which I think we can all agree is *slightly* less readable than the `proc`
notation.

The rough vibes here is that `Category a` abstracts the notion of what a function
is. Rather than using Haskell `->` arrows, we can instead use `a`-arrows. The
`Category` methods `(.)` and `id` do exactly what you'd expect --- composition
and identity of `a`-arrows.

The `Arrow a` class extends this with some way of turning arbitrary Haskell
arrows into `a`-arrows, as well as a way to run two different `a`-arrows on the
`fst` and `snd` of a (Haskell) product type. The exact semantics of what that
looks like depends on your `a`-arrow type (much like the exact semantics of `do`
notation depend on your choice of a monad!)

Anyway, to pull back to musical transformations. If we were to find some sort of
music-aware `Arrow` instance, `proc`-notation is exactly what we'd want in order
to "run patches" in our abstract modular synthesizer. That is to say, it
provides the plumbing for moving music in and out of transformations. As a
teaser for what's to come, here's a little example from my sandbox:

```haskell
-- A horizontal pattern describing an unfolding dyadic voice-leading that
-- descends by fifth, before swapping the voices by moving away from one
-- another.
divergence = replicateH 12 $ foldMap dnote
  [ voiceLead 0 3
  , expand 0 1
  ]

song = horizontal $ resize 0.25 $ proc i -> do
  -- Compute an abstract voice leading over time
  vl <- liftH msumE <<< divergence -< i

  -- Apply that voice leading to the first two notes of a triad
  ns <- replicateH 12 $ with id -< applyVoiceLeading vl $ chord triad
  returnA -< ns
```

which describes this this nice little dyad expansion:

![Dyad Expansion](/images/music2/out1.cropped.png)

If we replace the last line with:

```haskell
  -- Convert the "polyphony" into "counterpoint"
  let (lo :> hi :> Nil) = toV ns

  -- Clamp the lo voice so it stays within its register
  lo' <- liftH $ clampOctave (-9, 0) 0.5 -< lo

  -- Convert the "counterpoint" back into "polyphony"
  returnA -< fromV $ lo' :> hi :> Nil
```

we get this:

![Clamped Dyad Expansion](/images/music2/out2.cropped.png)

and of course we can also clamp the upper voice:

```haskell
  -- Clamp the voices so they stay within their registers
  lo' <- liftH $ clampOctave (-9, 0) 0.5 -< lo
  hi' <- liftH $ clampOctave (0, 7) 0.5 -< hi

  -- Convert the "counterpoint" back into "polyphony"
  returnA -< fromV $ lo' :> hi' :> Nil
```

and we get this:

![Doubly-Clamped Dyad Expansion](/images/music2/out3.cropped.png)

Now I'll be the first to admit that this is a completely unusable DSL. But it
does actually work! And if you squint, you can sort of see the modular
synthesizer idea at play. Inside the proc notation, we are sampling all of our
`Signal`s simultaneously, but routing the output of (eg) the voice leading into
the input of `replicateH $ with id`, which is what builds out the rhythmic
pattern. Then we take the output of that, separate it into `Signal`s of its
constituent voices, and feed those into `clampOctave`, which moves a `Signal`'s
notes into the given range of scale degrees.

Something cool but not pictured here, `clampOctave` takes a second argument (the
`0.5`) which tells it to look *into the future* and not perform any displacement
if it would need to move again within that 0.5 of a measure. This is some sort
of "retro-hysteresis" where signals can depend on their future values! Which
sounds crazy when you're thinking about wiring up synthesizers, but much less
crazy when you're sitting down writing out a score. Of course the notes in your
score can depend on notes that happen later on in the song! One of the many
benefits of *explicitly modeling time* in `Signal`s.


## Signal Functions

Hopefully you're excited to see how we go about doing any of this acausal
wizardry stuff. But it all starts from getting `proc` notation working. Which,
recall, means we need a type to give an `Arrow` instance to.

Behold, the signal function (`SF`):

```haskell
newtype SF a b = SF
  { runSF :: Signal a -> Signal b
  }
  deriving (Functor, Applicative) via WrappedArrow SF a
  deriving (Semigroup, Monoid) via Ap (SF a) b
```

which you will note is *literally a function between `Signal`s.* Its `Category`
instance comes immediately from Haskell functions' instance:

```haskell
instance Category SF where
  id = SF id
  SF g . SF f = SF (g . f)
```

The `Arrow` instance is similarly straightforward --- separate out the product,
run the functions on each half, then use the applicative instance to combine
them back into a single `Signal`:

```haskell
instance Arrow SF where
  arr = SF . fmap
  SF f *** SF g = SF $ \sg ->
    liftA2 (,) (f $ fmap fst sg) (g $ fmap snd sg)
```

That's really all there is to it! We can give some means of introducing `SF`s:

```haskell
constS :: Signal a -> SF x a
constS = SF . const
```

as well as a few primitives whose definition we don't have time to get into:

```haskell
-- | Create a single occurrence of an Event at the given time.
at :: Time -> a -> SF x (Event a)

-- | Convert a discrete stream into a continuous one, by holding the value of
-- the last event seen.
hold :: a -> SF (Event a) a

-- | Like 'hold', but backwards in time. Hold the value of the /next/ event that
-- will occur.
fhold :: a -> SF (Event a) a

-- | Stateful folds over Events
scanE :: (s -> a -> (s, b)) -> s -> SF (Event a) (Event b)

-- | Full-scale rewrites of Event streams
ev2ev :: ([(Time, a)] -> [(Time, b)]) -> SF (Event a) (Event b)

-- | Run the first SF until the 'Event' occurs, then switch into the
-- continuation.
switch :: SF a (b, Event c) -> (c -> SF a b) -> SF a b
```

(for completeness' sake, there ought to be time-reverse versions of `scanE` and
`switch` too!)

This seems like a good place to leave it for now. In the next post we'll discuss
how to turn all of this abstract machinery into something that actually
resembles music.


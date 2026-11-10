---
layout: post
title: Musical Notes and Scales
date: 2026-11-15 11:39
comments: true
tags: music, haskell, types
---

Sorry for the delay. Everyone in my household came down with egregious
sicknesses. And I had a bunch of unsatisfying things in my music theory that
needed to get worked out. But we're mostly better and the theoretical issues are
resolved, so we're BACK baby.

---

Over the last two posts we discussed [abstract musical pitches][pitches] and
(some) [efficient voice leadings][vls] which help move us smoothly between
different configurations in musical space.

[pitches]: /blog/pitches-1/
[vls]: /blog/voice-leadings/

It's been all very interesting *musically*, but you must admit there hasn't been
much in the way of functional programming going on. Today we're going to get
back to brass tacks and see about making all of these notions precise,
compositional, and fun to work with.

Where we left things is with a `Fin n` type:

```haskell
type Fin :: Nat -> Type
data Fin n

instance  KnownNat n          => Enum    (Fin n)
instance (KnownNat n, 1 <= n) => Bounded (Fin n)
```

which has exactly `n` distinct values. We then made a `Deg n` type, whose
semantics are "exactly one of `n` distinct values, with an octave component." We
represent this implicitly by way of an `Int`:

```haskell
type Deg :: Nat -> Type
newtype Deg n = Deg
  { getDeg :: Int
  }
  deriving stock (Generic)
  deriving newtype (Eq, Ord, Show, Num, Enum, Real, Integral)
```

and give its semantics by way of a function:

```haskell
degToPC :: KnownNat n => Deg n -> (Int, Fin n)
degToPC (Deg d) =
  let (oct, pc) = divMod d n
   in (oct, toEnum pc)
```

where the output `Int` is which octave the degree ended up in.

We have then been discussing "scales" as mappings of the form `Fin m -> Fin n`.
These have always been in scare quotes because this is not really how musicians
traditionally think about scales! Whatever this mapping concept *is,* it doesn't
really have a standard name in musical vocabulary. But scales are the closest
thing semantically, so we're going to just shadow that name and go about our
business.

It's a bit of a tricky line to balance. So whenever we're talking about the
loose musical idea, we'll use the word "scale." And whenever we mean this
mapping, we'll go with `Scale`.


## Some Failed Attempts at Pinnning Down Scales

However, it's been a bit of a simplification to say a `Scale` is a mapping `Fin
n -> Fin m`. We'd like our `Scale`s to be *monotone mappings,* which is to say
that if `i :: Deg m <= j :: Deg m`, then `(applyScale sc i) :: Deg n <=
(applyScale sc j) :: Deg n`. Enforcing monotonicity on `Fin`-to-`Fin` mappings
is possible, but it requires us to preserve the ordering of pitch classes
*within a single octave.* That is to say, it means we can't do any sort of
permutation.

Thus, perhaps we should think about `Scale`s as mappings `Fin m -> Deg n`. This
is much closer to what we want (although it has some shortcomings that we will
see shortly.) But let's move forward with this attempt in order to motivate some
of the later decisions:

```haskell
type Scale :: Nat -> Nat -> Type
newtype Scale m n = Scale (Fin m -> Deg n)
```

We can introduce a new scale by way of `mkScale`:

```haskell
mkScale :: (KnownNat m, 1 <= m) => (Fin m -> Deg n) -> Scale m n
mkScale f =
  let image = sort $ do
        m <- [0 .. maxBound @(Fin m)]
        pure $ f m
   in Scale $ \m -> image !! fromEnum m
```

which enumerates all values in `f`, sorts them (in order to ensure
monotonicity), and then builds a `Scale` that uses the `Fin m` to select from
the sorted values.

We can apply a scale to a `Deg` by way of `applyScale`:

```haskell
applyScale
    :: forall m n
     . Scale m n
    -> Deg m
    -> Deg n
applyScale (Scale f) (Deg dm) =
  let (oct, pc) = divMod dm $ scaleSize @m
      Deg dn = f $ toEnum pc
   in Deg (dn + oct * scaleSize @n)
```

which ensures we preserve the necessary semantics of `degToPC` given earlier.

All is so far well and good. But not for long.

In some cases we might want to reverse a `Scale`'s mapping, eg going from `Deg
7` to `Deg 3`. This makes a lot of sense musically. For example, we might want
to include a [neighbor note][neighbor], or a [passing tone][passing] when
writing out otherwise-triadic music. More directly, projecting down to a smaller
abstract pitch class is the exact mechanism of [tintinnabuli][tintin].

[neighbor]: https://en.wikipedia.org/wiki/Nonchord_tone#Neighbor_tone
[passing]: https://en.wikipedia.org/wiki/Nonchord_tone#Passing_tone
[tintin]: https://en.wikipedia.org/wiki/Tintinnabuli

Unfortunately however, reversing a mapping `Fin m -> Deg n` is obvious hogwash
from the perspective of our functional programming ivory tower. In the usual
case that `m <= n`, this is a very non-injective function, so we have no chance
of turning it around.

And yet, it's musically meaningful. So, regardless of whether we *can* do it in
Haskell, we somehow **must.** Otherwise whatever it is we've built is modeling
the wrong thing.

Our mental pattern matchers that say "you can't reverse a non-bijective
function" are absolutely correct. But it's worth taking a moment to think about
*why exactly* we can't in this case. Consider the musically-common case of
working in a `Scale 3 7 = Fin 3 -> Deg 7`. Here, some of the `Deg 7`s are
targeted by the `Fin 3`. In particular, `0, 2, 4 :: Deg 7` get targeted by the
`triad` scale introduced in a previous post.

So reversing `0, 2, 4 :: Fin 7` is easy enough --- we just send them to `0, 1, 2
:: Deg 3`. The hard part is deciding where ought we send `1, 3, 5, 6 :: Fin 7`.
Well, why don't we just send them to *themselves*?

Sounds a little crazy, I know, but check this out. If we could attach *other
scalar degree offsets* to each note, we could invert a scale by mapping the
image directly to the domain whenever possible. And when it's not possible, we
could represent it as an offset from the nearest thing in the domain.

A little example might help. Say we have `0..7 :: Fin 7` and we'd like to
reverse them across a `Scale 3 7`. If we represent exact points in `Deg 3` as
white note heads, and "offsets" as black note heads, one possible reverse
mapping looks like this:

![Offsets Above](/images/music7/out1.cropped.png)

<!-- \header { tagline = "" } -->
<!-- \absolute -->
<!--   \new Staff = "up" -->
<!--   << -->
<!--     \accidentalStyle piano-cautionary -->
<!--     \new Voice -->
<!--     { \omit Staff.TimeSignature -->
<!--       \cadenzaOn -->
<!--       \fixed c { <c'>2 -->
<!--                  <c' \tweak duration-log #2 d'> -->
<!--                  <e'> -->
<!--                  <e' \tweak duration-log #2 f'> -->
<!--                  <g'> -->
<!--                  <g' \tweak duration-log #2 a'> -->
<!--                  <g' \tweak duration-log #2 b'> -->
<!--                  <c''> -->
<!--                  } } -->
<!--   >> -->
<!-- \paper { -->
<!-- ragged-last = ##t -->
<!-- } -->


If we assume we have some operation `(/+) :: Fin 3 -> Deg 7 -> Note 3`, this
diagram corresponds to:

```haskell
[0, 0 /+ 1, 1, 1 /+ 1, 2, 2 /+ 1, 2 /+ 2, 3]
```

Of course, such a mapping is not unique. For example, we can also do a "round
up, offset down" approach:

![Offsets Below](/images/music7/out2.cropped.png)

which is similarly:

```haskell
[0, 1 /- 1, 1, 2 /- 1, 2, 3 /- 2, 3 /- 1, 3]
```

All of this is to say that `Deg`s aren't quite what we're looking for!


## Enter Notes

As we've seen, `Deg`s aren't quite powerful enough to represent these offsets.
So we'll first need to make a type to hold the offsets. The closest
standard-musical terminology here is "ornamentation," so that's what we'll go
with.

An `Ornaments` is a mapping from scalar sizes to offsets. Rather than keeping
the scalar sizes around in the type system (as we have done for `Fin` and `Deg`
and `Scale`), here we're going to simplify things down to an `IntMap`:

```haskell
newtype Ornaments a = Ornaments
  { getOrnaments :: IntMap a
  }
  deriving stock (Generic, Functor)
  deriving newtype (Show)
  deriving (Semigroup, Monoid) via MonoidalIntMap (Sum a)
```

Two `Ornaments` are equal when they have the same non-zero elements:

```haskell
normalizeOrnaments :: (Num a, Eq a) => Ornaments a -> Ornaments a
normalizeOrnaments = Ornaments . IM.filter (/= 0) . getOrnaments

instance (Eq a, Num a) => Eq (Ornaments a) where
  (==) = on (==) (getOrnaments . normalizeOrnaments)

instance (Ord a, Num a) => Ord (Ornaments a) where
  compare = on compare (getOrnaments . normalizeOrnaments)
```

We can also introduce `Ornaments`:

```haskell
ornament :: forall n a. KnownNat n => a -> Ornaments a
ornament = Ornaments . IM.singleton (scaleSize @n)
```

and eliminate them:

```haskell
decompOrnament
    :: forall n
     . KnownNat n
    => Ornaments Int
    -> (Ornaments Int, Deg n)
decompOrnament o
  = maybe
      (o, 0)
      ( (coerce (IM.filterWithKey @Int (\k _ -> k /= scaleSize @n)) o, )
      . Deg
      )
  $ IM.lookup (scaleSize @n)
  $ getOrnaments o

getOrnament :: forall n. KnownNat n => Ornaments Int -> Deg n
getOrnament = snd . decompOrnament
```

Here `decompOrnament @n` returns the `Deg n` ornament, and returns a new
`Ornaments` with that scale degree removed. If you don't care about the removal,
you're welcome to call `getOrnament` directly.

Armed with `Ornaments`, we can now make `Note`, which wraps a degree with
ornaments:

```haskell
type Note :: Nat -> Type
data Note n = Note (Deg n) (Ornaments Int)
  deriving stock (Generic, Eq, Ord)
```

`Note`s admit a `Num` instance, which combines ornaments pointwise:

```haskell
instance Num (Note n) where
  fromInteger n = Note (fromInteger n) mempty
  Note a as + Note b bs = Note (a + b) $ as <> bs
  Note a as - Note b bs = Note (a - b) $ as <> fmap negate bs
  Note a (Ornaments as) * Note b (Ornaments bs) =
    Note (a * b) $ Ornaments $ IM.intersectionWith (*) as bs
  abs    (Note a as) = Note (abs a)    $ fmap abs    as
  signum (Note a as) = Note (signum a) $ fmap signum as
```

and we can add an ornamental offset to a `Note` by way of `stepIn @c`:

```haskell
stepIn :: forall c n. (KnownNat c, KnownNat n) => Int -> Note n -> Note n
stepIn k (Note a as) =
  case scaleSize @c == scaleSize @n of
    True -> Note (a + Deg k) as
    False -> Note a $ as <> ornament @c k
```

An invariant enforced by `stepIn` is that you never have an ornament of size `n`
attached to a note also of size `n`. If you attempt to, we just change the `Deg
n` instead.


## Scales Revisited

Now that we have `Note`s, we can define `Scale`s in terms of them, and we are
rewarded with a convenient place to stick offsets when we invert scales. `Scale`
and `mkScale` change only in that we reference `Note` instead of `Deg`:


```haskell
type Scale :: Nat -> Nat -> Type
newtype Scale m n = Scale (Fin m -> Note n)
```

```haskell
mkScale :: (KnownNat m, 1 <= m) => (Fin m -> Note n) -> Scale m n
mkScale f =
  let image = sort $ do
        m <- [0 .. maxBound @(Fin m)]
        pure $ f m
   in Scale $ \m -> image !! fromEnum m
```

However, `applyScale` needs to do slightly more work: it must respect incoming
and outgoing ornamentation. The `Note m` might have a `n`-sized ornament, in
which case we must add it immediately. And then we must combine the remaining
ornaments with any which might arise from the `Scale`'s mapping:

```haskell
applyScale
    :: forall m n
     . Scale m n
    -> Note m
    -> Note n
applyScale (Scale f) (Note (Deg dm) os) =
  let (oct, pc) = divMod dm $ scaleSize @m
      (Note (Deg dn) os') = f $ toEnum pc
      (os'', od) = decompOrnament @n os
   in Note (od + Deg (dn + oct * scaleSize @n)) $ os' <> os''
```

With all of this work, we're now ready to tackle inverting scales. The thrust of
the idea here is a relatively simple algorithm:

1. Compute the image of the scale. Take the resulting pitch class, and associate
   it with the corresponding input pitch class. Negate the octave and ornaments
   when doing this.
2. Check if the inverse pitch class exist directly in your image map. If so,
   return it directly.
3. If not, select the best candidate of the image with respect to the inverse
   pitch class. Compute how far the best candidate is away from the input, and
   add that distance as an extra ornament.

Of course, the devil is in the details. Getting the "best candidate" might
require looking in a different octave. We wrap the candidate logic into a
chooser:

```haskell
(forall x. Ord x => Fin b -> [(Fin b, x)] -> (Int, x))
```

which receives the desired pitch class, the image, and must return one element
of the image along with an octave displacement. Since the entire thing is stuck
in a `forall x`, the chooser is allowed only to look at the `Fin b`s to
determine what is the best candidate. As a little illustration here, we might
want to round up to the nearest pitch class in the image. So we'd want to filter
the image by anything `>= pc`. But if `pc` is already the largest thing in the
image, we'd instead want to return the smallest thing in the image with a +1
octave offset.

If you're curious, the logic in its full glory is thus:

```haskell
invertScale
    :: forall a b
     . (1 <= a)
    => (forall x. Ord x => Fin b -> [(Fin b, x)] -> (Int, x))
    -> Scale a b
    -> Scale b a
invertScale choose (Scale f) = do
  let img :: [(Fin b, Note a)]
      img = do
        a <- [0 .. maxBound @(Fin a)]
        let (Note (Deg db) os) = f a
        let (o, pc) = divMod db $ scaleSize @b
        let b = toEnum @(Fin b) pc
        pure ( b
             , Note (fromIntegral a - Deg (scaleSize @a * o))
                 $ fmap negate os
             )
  Scale $ \b ->
    case lookup b img of
      Just a -> a
      Nothing -> do
        let (ox, chosen) = choose b img
            (b', Note da os) =
              case find ((== chosen) . snd) img of
                Just c -> c
                Nothing -> error "impossible"
            diff = fromIntegral b - (fromIntegral b' + ox * scaleSize @b)
        Note (da + Deg (ox * scaleSize @a)) $ os <> ornament @b diff
```

which we specialize with a few different choices of chooser:

```haskell
invertScaleAbove   :: (1 <= a) => Scale a b -> Scale b a
invertScaleBelow   :: (1 <= a) => Scale a b -> Scale b a
invertScaleNearest :: (1 <= a) => Scale a b -> Scale b a
```

As a little aside, I haven't found a great way of naming the first two
functions. Here "above" means "round down and offset up", and below is the
opposite. Any suggestions for more obvious names here would be greatly
appreciated.

That's all for today. In the next post we'll investigate the types behind voice
leadings, with a similar attention to precision.


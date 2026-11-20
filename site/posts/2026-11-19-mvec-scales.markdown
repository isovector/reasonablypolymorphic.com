---
layout: post
title: The Third Scale Encoding is Hopepfully the Charm
date: 2026-11-19 21:55
comments: true
tags: haskell, music, scales
---

Well, unfortunately time has run out, and I am not going to make the NaNoWriMo
writing goal! I'm off to Japan on Monday and promised my wife that I'd do at
least a little thinking about the trip before we head off. So that means I'm
putting a (temporary) close on the music stuff for a few weeks. But don't worry;
I can't get this stuff off my brain, so some time off is likely only going to
stoke the flames.

With that being said...

My plan today was to write about vertical configurations and voice leadings. But
I realized my notion of voice leadings didn't agree with [Tymoczko][tymoczko]'s.
And while there are a lot of music theorists whose opinions I don't put much
stock into, Tymoczko is one whose thoughts I value very much.

[tymoczko]: https://dmitri.mycpanel.princeton.edu/index.html

While trying to answer those questions, I looked at my implementation of
[Neo-Riemannian transformations][neo] and realized it was convoluted as all hell
(which I knew). Furthermore I noticed that our work on scales the [other
day][scales] did almost everything I was doing by hand in the Neo-Riemannian
case. So I swapped out the bespoke stuff for everyday scale things, and the
tests stayed green.

[neo]: https://en.wikipedia.org/wiki/Neo-Riemannian_theory
[scales]: /blog/notes-scales/

Happy days. But then I changed my test generators (so that notes would include
[generalized accidentals][accidentals]) and the tests went red! For reasons
unrelated to Neo-Riemannian transformations, but for darker, scarier reasons.
*Scales* were doing the wrong thing.

[accidentals]: /blog/accidentals/

Oh man. Not so good. The problem is that under our previous encoding, *not all
scales are [retractable][retraction].* Check it out:

[retraction]: https://en.wikipedia.org/wiki/Section_(category_theory)

We previously left `Scale`s defined thusly:

```haskell
type Scale :: Nat -> Nat -> Type
newtype Scale m n = Scale (Fin m -> Note n)
```

The codomain being `Note n` was so that we had a place to stick a scale degree
and an accidental. We really only wanted to store a pitch class and an
accidental, but you could rotate the pitch classes in a scale and then the lower
pitch classes might only be reachable an octave up. Thus the degrees.

OK fine. But look at this mapping:

```haskell
weird :: Scale 2 7
weird = Scale $ \case
  0 -> 0
  1 -> stepIn @12 1 0
```

Here we've defined a scale that maps both pitch classes in `Fin 2` to `0 :: Deg
7`, but the second pitch class also carries a (chromatic) sharp. All is well and
good, until we go to invert this thing. Inverting the image of the first pitch
class is fine:

```haskell
let weirder = invertScaleAbove weird

applyScale weirder (0 :: Note 7)
    == (0 :: Deg 2)
```

but inverting the image of the second, well...

```haskell
applyScale weirder (stepIn @12 1 0 :: Note 7)
    == stepIn @12 1 0 :: Deg 2
```

Because application of scales dispatches only on pitch classes, it can't branch
on the accidental here. So what was once in the image of `weird` is now somehow
getting smuggled along when we apply the inverse of `weird`. Weird!

This is a fundamental problem with our scales as written. They simply do not
always admit left inverses!

To be clear, the problem here is that `weird` isn't injective in its mappings
from `Fin 2` to `Fin 7` (both `0, 1 :: Fin 2` end up at `0 :: Fin 7`.) So if we
could force the scale to be injective, then the error conditions wouldn't apply,
and we *always would* be able to find a left inverse.

So then, *how do we ensure we have an injective mapping between finite numbers?*


## A Quick Musical Note

As an aside to the main thrust of this blog post, I found it quite elucidating
to think about what this "injective mapping of pitch classes" constraint
*actually means* in terms of music.

And I THINK that this is the underlying constraint that [enharmonic
spelling][spelling] is attempting to solve.

[spelling]: https://en.wikipedia.org/wiki/Enharmonic_equivalence

<style type="text/css">
.music-digraph {
  display: inline-block;
  letter-spacing: -0.15em;
  transform: scaleX(0.85);
  font-weight: 600;
}
</style>

[Recall][accidentals] that the standard musical staff notates the diatonic scale
(`Fin 7`), which corresponds (roughly) to the white keys on the piano. For time
immemorial we have been working in `Fin 7`, and this is why the black keys *don't
have their own names* -- because the black keys are the five notes that you need
to add in to get to `Fin 12`. We happily talk about the white notes as A, B, C,
D, E, F, G, but the black notes are relegated to mere modifiers --- sometimes as
D#, other times as Eb. But never as <span class="music-digraph">DE</span>.

Anyway, since we can't call it the note between D and E as <span
class="music-digraph">DE</span>, what can we do? Well we need to project this
note down to `Fin 7`. Which of course can't be done in general, but we cheat by
adding an accidental. Is it either D# or Eb? It depends! What does it depend on?

Conventional spelling rules say that it ought to be offset from "the scale note
it is acting in place of." Which is to say that it must be *temporarily
replacing* some note in the scale, and it steals that note's pitch class!

If we pull this back to injective mapping of finite numbers, the weird
historical rule makes sense. *In order to preserve this injective mapping* you
**must** remove any other notes which would otherwise map to the same pitch
class!

I feel like I am not articulating this very well. Maybe some diagrams would
help. But I'd actually like to go to bed sometime tonight and there is still too
much to write down before I need to put the book ends on my music project for a
few weeks. Alas.

Let me know in the comments if any of this section makes a lick of sense. Or if
it doesn't. That's what we call <tt>e n g a g e m e n t</tt>, baby.


## Dependently-Typed Programming to the Rescue

OK so anyway, back to trying to enforce injectivity of finite maps.

Thankfully I wrote a [book on Agda][cbc] which happens to be pretty helpful for
working out solutions to stuff like this.

[cbc]: https://leanpub.com/certainty-by-construction

Recall that functions `Fin n -> a` are isomorphic to vectors `Vec n a` (which is
to say, a product of `n` copies of `a`.) This fact will come up again when I
eventually get around to writing about voice leadings. But you will notice that
functions `Fin n -> a` are not injective functions between `Fin`s!

To be concrete, let's say we're looking for mappings of the form `Fin m -> (Fin
n, a)`. Which solves our scale problem (because we can put our accidentals in
`a`.) So as a first step, we could consider encoding this mapping as:

```haskell
Vec m (Maybe a)
```

with the invariant that there be exactly `n` elements that contain `a`s. For
example, `triad :: Scale 3 7` would look like this:

```haskell
triad' :: Vec 7 (Maybe (Accidentals Int))
triad' = let a = mempty
  in Just a
  :> Nothing
  :> Just a
  :> Nothing
  :> Just a
  :> Nothing
  :> Nothing
  :> Nil
```

Here we have filled exactly 3 of the 7 total slots. We can then recover the
mapping by traversing over the `Just`s and pairing each with the next `Fin 3`:

```haskell
triad'' :: Vec 7 (Maybe (Fin 3, Accidentals Int))
triad'' = let a = mempty
  in Just (0, a)
  :> Nothing
  :> Just (1, a)
  :> Nothing
  :> Just (2, a)
  :> Nothing
  :> Nothing
  :> Nil
```

Now if we zip this vector with its own indices, we get this:

```haskell
triad''' :: Vec 7 (Fin 7, Maybe (Fin 3, Accidentals Int))
triad''' = let a = mempty
  in (0, Just (0, a))
  :> (1, Nothing)
  :> (2, Just (1, a))
  :> (3, Nothing)
  :> (4, Just (2, a))
  :> (5, Nothing)
  :> (6, Nothing)
  :> Nil
```

Finally, filter out the `Nothing`s, and you're left with (he said, gesticulating
wildly) exactly three values, and their corresponding indices in both `Fin 3`
and `Fin 7`:

```haskell
triad'''' :: [(Fin 7, (Fin 3, Accidentals Int))]
triad'''' = let a = mempty
  in [ (0, (0, a))
     , (2, (1, a))
     , (4, (2, a))
     ]
```

Since you and I both "know" that there are three elements in this list, we can
give a "total" function:

```haskell
triad :: Fin 3 -> (Fin 7, Accidentals Int)
triad n = triad'''' !! fromIntegral n
```

Sure enough this does work! But it only works because of our invariant that
there are exactly[^well] 3 `Just`s in our original vector. That's cool and all,
but it seems like the sort of thing that would be easy to get wrong. And then
you'd be crashing at runtime, and that's not the Haskell Ethos.

[^well]: Well technically it works because there are at least 3 elements...

So what can we do instead? Let's make a type that is like a `Vec`, but which
counts slots separately from filled slots. I needed a name so I called it an
`MVec`, but the `M` doesn't actually stand for anything. Behold:

```haskell
type MVec :: Nat -> Nat -> Type -> Type
data MVec slots filled a where
  MNil ::                              MVec  0           0           a
  MCons :: a -> MVec slots filled a -> MVec (slots + 1) (filled + 1) a
  MSkip ::      MVec slots filled a -> MVec (slots + 1)  filled      a
```

Here, `MCons` acts exactly like `:>` did in our vector example --- it sticks an
element in front of another `MVec`. But in doing so, it increases the slots and
the fill count both by one. However, there's also `MSkip` which only increases
the slots (and correspondingly doesn't have a place to put an `a`.)

This structure thus perfectly encodes our `m` slots of which exactly `n` are
filled semantics. Very cool. As a little proof, we can project a `MVec m n a`
down to either a `Vec n a` or a `Vec m (Maybe a)`:

```haskell
embedMVec :: MVec m n a -> Vec n a
embedMVec MNil = Nil
embedMVec (MCons a as) = a :> embedMVec as
embedMVec (MSkip as) = embedMVec as

projectMVec :: MVec m n a -> Vec m (Maybe a)
projectMVec MNil = Nil
projectMVec (MCons a as) = Just a :> projectMVec as
projectMVec (MSkip as) = Nothing :> projectMVec as
```

So that's all well and good. But we can also *actually find things* in this data
structure, as given by `mlookup`:

```haskell
mlookup :: MVec m n a -> Fin n -> (Fin m, a)
mlookup (MCons a _) FZ = (FZ, a)
mlookup (MCons _ mn) (FS n) =
  case mlookup mn n of
    (m, a) -> (FS m, a)
mlookup (MSkip mn) n =
  case mlookup mn n of
    (m, a) -> (FS m, a)
```

which you will happily note follows the same logic we worked through for
`triad`, and is exactly the function we want to use for making `Scale`s.

We can also go the other way, and search on the `Fin m` indices:

```haskell
msearch :: MVec m n a -> Fin m -> Maybe (Fin n, a)
msearch MNil a = case a of
msearch (MCons a _) FZ = Just (FZ, a)
msearch (MCons _ as) (FS n) = fmap (first FS) $ msearch as n
msearch (MSkip _) FZ = Nothing
msearch (MSkip as) (FS n) = msearch as n
```

which I'm not super sure is important, but it was fun to write.

The real reason for calling this thing `MVec` was so that I could put `m`s in
front of all its functions' names. Which finally pays off when we get to the
`MVec` composition function:

```haskell
malign
  :: (x -> y -> z)
  -> MVec c b x
  -> MVec b a y
  -> MVec c a z
malign _ MNil MNil = MNil
malign f (MSkip bc) ab = MSkip $ malign f bc ab
malign f (MCons x bc) (MCons y ab) = MCons (f x y) $ malign f bc ab
malign f (MCons _ bc) (MSkip ab) = MSkip $ malign f bc ab
```

This function does end-wise composition of `MVec`s. If you have one `MVec` that
has `c` slots and `b` items, and another which has `b` slots and `a` items
(sorry for the type variable shuffling!), then we ought to be able to make an
`MVec` with `c` slots and only `a` items. This corresponds to composition of
scales, so it's really quite important!

The trick is we traverse over the b-in-c collection. Whenever we find an item
there, we consider it to be a potential slot of the a-in-b collection. If a-in-b
says to skip, then we skip it. But if they're both cons cells, we can use the
given function to combine their values into a `z`.

Quite nice if you ask me.


## Back To Scales

Now that we have `MVec`s, it's pretty trivial to implement the small-to-big
scale mapping that we've been thinking about. Really we just need to keep an
`MVec m n` around, convert it into the old representation via `mlookup`, and
then all of the last post's machinery around scales works just fine.

Except, how do you invert them? Remember that we did all of this work to invert
them. If an `MVec m n` has `m` slots of which `n` are full, it necessarily means
that `n <= m`. Which is to say that it's slightly more complicated than just
keeping a `MVec m n` around.

The trick of course is that if you invert a scale, *it's still the same `MVec`
you need!* Thus a `Scale a b` is either an embedding from `a` to `b`, or a
projection from `b` back to `a`:

```haskell
type Scale :: Nat -> Nat -> Type
data Scale a b where
  Embed   ::                 MVec b a (Accidentals Int) -> Scale a b
  Project :: Quantization -> MVec b a (Accidentals Int) -> Scale b a
```

Notice that it's the same `MVec` in both constructors, the only difference is
which direction the scale goes. This `Quantization` thing is a little enum:

```haskell
data Quantization = Below | Above | Nearest
```

which corresponds exactly to the three `invertScale*` functions from last time.
Really it means "if you're looking at a scale degree which doesn't fit, which
note should we add offsets to?" I don't think I like having this field, and when
I'm back from Japan I'll explore just sticking the chooser in there.

Once we've added `Project`, however, I don't think scales compose anymore. Not
to fear, we'll just *make* them compose by adding a new constructor:

```haskell
data Scale a b where
  Embed   ::                 MVec b a (Accidentals Int) -> Scale a b
  Project :: Quantization -> MVec b a (Accidentals Int) -> Scale b a
  Compose :: Scale x b -> Scale a x                     -> Scale a b
```

Composition of scales tries to `malign` when possible:

```haskell
compScale :: Scale b c -> Scale a b -> Scale a c
compScale (Embed bc) (Embed ab) = Embed $ malign (<>) bc ab
compScale bc ab = Compose bc ab
```

and inversion is now a little swap-er-oo of our constructors:

```haskell
invertScale :: Quantization -> Scale a b -> Scale b a
invertScale q (Embed slots) = Project q slots
invertScale _ (Project _ slots) = Embed slots
invertScale q (Compose f g) = Compose (invertScale q g) (invertScale q f)
```

So that's the thrust of today's work. Having sorted out all of these details has
dramatically simplified up the codebase (and found a bunch of bugs), which I
always consider to be a harbinger of being on the right track. Making any of
this stuff usable is its own exercise in existential types and type reflection
shenanigans, but maybe we'll cover that another day if there's sufficient
interest.


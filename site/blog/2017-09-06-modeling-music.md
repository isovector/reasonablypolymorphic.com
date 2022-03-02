---
layout: post
title: "Modeling Music"
date: 2017-09-06 19:03
comments: true
tags: music, haskell
---

One of my long-term goals since forever has been to get good at music. I can
sightread music, and I can play music by ear -- arguably I can play music well.
But this isn't to say that I am good at music; I'm lacking any theory which
might take me from "following the path" of music to "navigating" music.

Recently I took another stab at learning this stuff. Every two years or so I
make an honest-to-goodness attempt at learning music theory, but inevitably run
into the same problems over and over again. The problem is that I have yet to
find any music education resources that communicate on my wavelength.

Music education usually comes in the form of "here are a bunch of facts about
music; memorize them and you will now know music." As someone who got good at
math because it was the only subject he could find that didn't require a lot of
memorization, this is a frustrating situation to be in for me. Music education,
in other words, presents too many theorems and too few axioms.

My learning style prefers to know the governing fundamentals, and derive results
when they're needed. It goes without saying that this is not the way most music
theory is taught.

Inspired by my recent forays into learning more mathematics, I've had an
(obvious) insight into how to learn things, and that's to model them in systems
I already understand. I'm pretty good at functional programming, so it seemed
like a pretty reasonable approach.

I've still got a *long* way to go, but this post describes my first attempt at
modeling music, and, vindicating my intuitions, shows how we can derive value
out of this model.


## Music from First Principles

I wanted to model music, but it wasn't immediately obviously how to actually go
about doing that. I decided to write down the few facts about music theory I
*did* know: there are notes.

```haskell
data Note = C | C' | D | D' | E | F | F' | G | G'| A | A' | B
  deriving (Eq, Ord, Show, Enum, Bounded, Read)
```

Because Haskell doesn't let you use `#` willy-nilly, I decided to mark sharps
with apostrophes.

I knew another fact, which is that the sharp keys can also be described as flat
keys -- they are [enharmonic](https://en.wikipedia.org/wiki/Enharmonic). I
decided to describe these as pattern synonyms, which may or may not have been a
good idea. Sometimes the name of the note matters, but sometimes it doesn't, and
I don't have a great sense of when that is. I resolved to reconsider this
decision if it caused issues down the road.

```haskell
{-# LANGUAGE PatternSynonyms #-}

pattern Ab = G'
pattern Bb = A'
pattern Db = C'
pattern Eb = D'
pattern Gb = F'
```

The next thing I knew was that notes have some notion of *distance* between
them. This distance is measured in **semitones**, which correspond to the pitch
difference you can play on a piano. This distance is called an **interval**, and
the literature has standard names for intervals of different sizes:

```haskell
data Interval
  = Uni    -- 0 semitones
  | Min2   -- 1 semitone
  | Maj2   -- 2 semitones
  | Min3   -- etc.
  | Maj3
  | Perf4
  | Tri
  | Perf5
  | Min6
  | Maj6
  | Min7
  | Maj7
  deriving (Eq, Ord, Show, Enum, Bounded, Read)
```

It's pretty obvious that intervals add in the usual way, since they're really
just names for different numbers of semitones. We can define addition over them,
with the caveat that if we run out of interval names, we'll loop back to the
beginning. For example, this will mean we'll call an octave a `Uni`son, and a
13th a `Perf4`. Since this is "correct" if you shift down an octave every time
you wrap around, we decide not to worry about it:

```haskell
iAdd :: Interval -> Interval -> Interval
iAdd a b = toEnum $ (fromEnum a + fromEnum b) `mod` 12
```

We can similarly define subtraction.

This "wrapping around" structure while adding should remind us of our group
theory classes; in fact intervals are exactly the group
$\mathbb{Z}/12\mathbb{Z}$ -- a property shared by the hours on a clock where $11
+ 3 = 2$. That's certainly interesting, no?

If intervals represent distances between notes, we should be able to subtract
two notes to get an interval, and add an interval to a note to get another note.

```haskell
iBetween :: Note -> Note -> Interval
iBetween a b = toEnum $ (fromEnum a - fromEnum b) `mod` 12

iAbove :: Note -> Interval -> Note
iAbove a b = toEnum $ (fromEnum a + fromEnum b) `mod` 12
```

Let's give this all a try, shall we?

```haskell
> iAdd Maj3 Min3
Perf5

> iBetween E C
Maj3

> iAbove D Maj3
F'
```

Looks good so far! Encouraged by our success, we can move on to trying to
model a scale.


## Scales

This was my first stumbling block -- what exactly is a scale? I can think of a
few: C major, E major, Bb harmonic minor, A melodic minor, and plenty others! My
first attempt was to model a scale as a *list of notes*.

Unfortunately, this doesn't play nicely with our mantra of "axioms over
theorems". Represented as a list of notes, it's hard to find the common
structure between C major and D major.

Instead, we can model a scale as a list of *intervals*. Under this lens, all
major scales will be represented identically, which is a promising sign. I
didn't know what those intervals happened to be, but I did know what C major
looked like:

```haskell
cMajor :: [Note]
cMajor = [C, D, E, F, G, A, B]
```

We can now write a simple helper function to extract the intervals from this:

```haskell
intsFromNotes :: [Note] -> [Interval]
intsFromNotes notes = fmap (\x -> x `iBetween` head notes) notes

major :: [Interval]
major = intsFromNotes cMajor
```

To convince ourselves it works:

```haskell
> major
[Uni,Maj2,Maj3,Perf4,Perf5,Maj6,Maj7]
```

Seems reasonable; the presence of all those major intervals is probably why they
call it a major scale. But while memorizing the intervals in a scale is likely a
fruitful exercise, it's no good to me if I want to actually *play* a scale. We
can write a function to add the intervals in a scale to a tonic in order to get
the actual *notes* of a scale:

```haskell
transpose :: Note -> [Interval] -> [Note]
transpose n = fmap (iAbove n)
```

```haskell
> transpose A major
[A,B,C',D,E,F',G']
```

Looking good!


## Modes

The music theory I'm actually trying to learn with all of this is
jazz theory, and my jazz theory book talks a lot about modes. A mode of a scale,
apparently, is playing the same notes, but starting on a different one. For
example, G mixolydian is actually just the notes in C major, but starting on G
(meaning it has an F&#9838;, rather than F#).

By rote, we can scribe down the names of the modes:

```haskell
data Mode
  = Ionian
  | Dorian
  | Phrygian
  | Lydian
  | Mixolydian
  | Aeolian
  | Locrian
  deriving (Eq, Ord, Show, Enum, Bounded, Read)
```

If you think about it, playing the same notes as a different scale but starting
on a different note sounds a lot like rotating the order of the notes you're
playing. I got [an algorithm for rotating a list off stack
overflow](https://stackoverflow.com/a/16379034/5617054):

```haskell
rotate :: Int -> [a] -> [a]
rotate _ [] = []
rotate n xs = zipWith const (drop n (cycle xs)) xs
```

which we can then use in our dastardly efforts:

```haskell
modeOf :: Mode -> [a] -> [a]
modeOf mode = rotate (fromEnum mode)
```

```haskell
> modeOf Mixolydian $ transpose C major
[G,A,B,C,D,E,F]
```

That has a F&#9838;, all right. Everything seems to be proceeding according to
our plan!

Something that annoys me about modes is that "G mixolydian" has the notes of C,
not of G. This means the algorithm I need to carry out in my head to jam with my
buddies goes something as follows:

* G mixolydian?
* Ok, mixolydian is the fifth mode.
* So what's a major fifth below G?
* It's C!
* What's the C major scale?
* OK, got it.
* So I want to play the C major scale but starting on a different note.
* What was I doing again?

That's a huge amount of thinking to do on a key change. Instead, what I'd prefer
is to think of "mixolydian" as a transformation on G, rather than having to
backtrack to C. I bet there's an easier mapping from modes to the notes they
play. Let's see if we can't tease it out!

So to figure out what are the "mode rules", I want to compare the intervals of C
major (ionian) to C whatever, and report back any which are different. As a
sanity check, we know from thinking about G mixolydian that the mixolydian rules
should be `Maj7 => Min7` in order to lower the F# to an F&#9838;.


```haskell
modeRules :: Mode -> [(Interval, Interval)]
modeRules m = filter (uncurry (/=))
            . zip (intsFromNotes $ transpose C major)
            . intsFromNotes
            . transpose C
            $ modeOf m major
```

What this does is construct the notes in C ionian, and then in C whatever, turns
both sets into intervals, and then removes any groups which are the same. What
we're left with is pairs of intervals that have changed while moving modes.

```haskell
> modeRules Mixolydian
[(Maj7,Min7)]

> modeRules Dorian
[(Maj3,Min3), (Maj7,Min7)]
```

Very cool. Now I've got something actionable to memorize, and it's saved me a
bunch of mental effort to compute on my own. My new strategy for determining D
dorian is "it's D major but with a minor 3rd and 7th".


## Practicing

My jazz book suggests that practicing every exercise along the circle of fifths
would be formative. The circle of fifths is a sequence of notes you get by
successively going up or down a perfect 5th starting from C. In jazz allegedly
it is more valuable to go down, so we will build that:

```haskell
circleOfFifths :: [Note]
circleOfFifths = iterate (`iMinus` Perf5) C
```

This is an infinite list, so we'd better be careful when we look at it:

```haskell
> take 5 circleOfFifths
[C,F,A',D',G']
```

Side note, we get to every note via the circle of fifths because there are 12
distinct notes (one for each semitone on C). A major fifth, being 7 semitones,
is semi-prime with 12, meaning, meaning it will never get into a smaller cycle.
Math!

Ok, great! So now I know which notes to start my scales on. An unfortunate
property of the jazz circle of fifths is that going down by fifths means you
quickly get into the freaky scales they don't teach 7 year olds. You get into
the weeds where the scales start on black notes and don't adhere to your puny
human intuitions about fingerings.

A quick google search suggested that there is no comprehensive reference for
"what's the fingering for scale X". However, that same search did provide me
with a heuristic -- "don't use your thumb on a black note."

That's enough for me to go on! Let's see if we can't write a program to solve
this problem for us. It wasn't immediately obvious to me how to generate
potential fingerings, but it seems like we'll need to know which notes are
black:

```haskell
isBlack :: Note -> Bool
isBlack A' = True
isBlack C' = True
isBlack D' = True
isBlack F' = True
isBlack G' = True
isBlack _ = False
```

For the next step, I thought I'd play it safe and hard code the list of
fingering patterns for the right hand that I already know.

```haskell
fingerings :: [[Int]]
fingerings = [ [1, 2, 3, 1, 2, 3, 4, 5]  -- C major
             , [1, 2, 3, 4, 1, 2, 3, 4]  -- F major
             ]
```

That's it. That's all the fingerings I know. Don't judge me. It's obvious that
none of my patterns as written will avoid putting a thumb on a black key in the
case of, for example, Bb major, so we'll make a concession and say that you can
start anywhere in the finger pattern you want.

```haskell
allFingerings :: [[Int]]
allFingerings = do
  amountToRotate <- [0..7]
  fingering      <- fingerings
  pure $ rotate amountToRotate fingering
```

With this list of mighty potential fingerings, we're ready to find one that fits
a given scale!

```haskell
fingeringOf :: [Note] -> [Int]
fingeringOf notes = head $ do
  fingers <- allFingerings
  guard . not
        . or
        . fmap (\(n, f) -> isBlack n && f == 1)
        . zip notes
        $ fingers
  pure fingers
```

We can test it:

```haskell
> fingeringOf $ transpose C major
[1,2,3,1,2,3,4,5]

> fingeringOf $ transpose F major
[1,2,3,4,1,2,3,4]

> fingeringOf $ transpose A' major
[2,3,1,2,3,4,5,1]
```

So it doesn't work *amazingly*, but it does in fact find fingerings that avoid
putting a thumb on a black key. We could tweak how successful this function is
by putting more desirable fingerings earlier in `allFingerings`, but as a proof
of concept this is good enough.

That's about as far as I've taken this work so far, but it's already taught me
more about music theory than I'd learned in 10 years of lessons (in which,
admittedly, I skipped the theory sections). More to come on this topic,
probably.

As usual, [you can find the associated code on
Github](https://github.com/isovector/jazz/).


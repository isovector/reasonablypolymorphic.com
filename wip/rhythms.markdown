---
layout: post
title: rhythms
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

We've been thinking a lot about musical structures over these last few posts.
Today we're going to look into some rhythmic concerns, and in particular, figure
out how to turn a discrete signal of instantaneous events into something that
*actually looks like music.*

Recall that we've been working with a `Signal a` type, which is a continuous
function of `Time -> a`, packaged along with a set of "interesting times" that
we might be interested in looking at. We smuggle *discrete* events into these
interesting times. But what makes a time interesting?

One immediate answer, musically, is "when something happens." That something
could be a point in the meter, a chord change, the beginning of a note, the end
of a note, a modulation, the return of a motif, every time an A is played, etc.
Essentially, whenever you might think a time is interesting :)

Of these, we're primarily going to focus on the beginning and end of notes
today. Since once we've sorted that bit out, we have the better part of a
musical MVP. It's not going to be anywhere close to the [vision][vision], but
it's a necessary step along the path.

[vision]: /blog/music-overview/

So what we've built so far is an `Event` type, which demarks instantaneous and
momentary things. We have a `Signal` type which models things-over-time. It
seems likely that in order to play notes we're going to want a `Signal` of
`Event`s of something. Let's say [MIDI notes][midi] for now, since it's an
obvious sort of "computer music" interface.

[midi]: https://en.wikipedia.org/wiki/MIDI

The problem of course is that `Event`s are instantaneous, but audible things are
not; they necessarily have a duration. I played around with data structures in
the style of [interval trees][itrees] for a [long time][bad] before coming to
the conclusion that that way lies folly.

[bad]: /blog/more-algebraic-music/
[itrees]: https://en.wikipedia.org/wiki/Interval_tree

Instead what seems to be the play is to explicitly model `Span`s:

```haskell
data Span a = Span
  { duration :: Time
  , getSpan :: a
  }
  deriving stock (Eq, Ord, Show, Functor, Foldable, Traversable, Generic)
```

and then just generate them in our `Signal`. So rather than talk about `Event
MIDINote`, we instead use `Event (Span MIDINote)`. This is very much in the
style of "regular old music scores" where there is *explicit syntax* for
encoding the span of a note:

![Rhythmic symbols](/images/music3/out1.cropped.png)

If you're not familiar with music notation, the top line  contains (after the
funny "c" thing) the symbols for sounded notes. The first symbol takes up one
unit of time, the next takes half that, and so on and so forth. The bottom line,
in corresponding columns, are the same durations, except for silences rather
than for sounded notes.

Anyway, the point here is namely that musicians are very much in the habit of
thinking about "how long does this note sound for?" So attaching the `Span` to
the note we want to play isn't a very far-fetched idea at all.

That being said...

It turns out to be a *drag* to have to always be sticking durations on things.
I suspect the pain is already internalized in some sort of Stockholm Syndrome,
because every written notation and every computer program for music requires you
to write down the damn durations.

As it happens, writing down the durations in advance is not very compositional.
For example, if we stretch the time domain of our `Signal` (which is very
reasonable and possible, since it's just a function `Time -> a`), we'd expect
the note durations to stretch too! But they can't, since we'd have the type:

```haskell
stretch :: Rational -> Signal a -> Signal a
```

which you'll notice is polymorphic in `a`. Of course, we could do some ad-hoc
bullshit where we stick in a typeclass constraint for "stretchable things" but
this is the way of madness.

What if, instead, we were to *derive* the durations? After all, we already know
*when* everything *is*, temporally-speaking. The first type that comes to mind
for something like this would be:

```haskell
SF (Event a)  (Event (Span a))
```

that is, a function over `Signal`s, which takes an input stream of events and
outputs a stream of events with a duration attached to them. What duration?
Presumably until the next event! While this is a perfectly fine type (and isn't
very hard to implement), it has the obvious downside that it can't represent
silence. If a sound spans until the next sound, then there's nowhere to stick
any silence!

What I ended up with was to take *two* input event streams:

```haskell
spanning :: SF (Event (), Event a) (Event (Span a))
```

where the `Event ()` stream indicates *changes* and the `Event a` stream
indicates *beginnings of notes.* Thus a note spans until the next `Event a` or
`Event ()` --- whichever comes first.

The implementation is not very tricky. We use our primitive

```haskell
ev2ev :: ([(Time, a)] -> [(Time, b)]) -> SF (Event a) (Event b)
```

and zip together the events with the tail of the events, taking the difference
in their times. All that's left is to combine the event streams, which is
exactly what the `Alternative` instance on `Event` does:

```haskell
spanning :: SF (Event (), Event a) (Event (Span a))
spanning = proc (end, a) -> do
  let merged = Just <$> a <|> Nothing <$ end
  ev2ev
    (\es -> catMaybes
      $ zipWith
          (\(t1, ema) (t2, _) -> case ema of
            Just a -> Just (t1, Span (t2 - t1) a)
            Nothing -> Nothing
          )
          es
      $ drop 1 es
    ) -< merged
```

I don't know about you, but I think this is [pretty cool][republicans]. For two
different reasons. The first is that we've accidentally just derived the notion
of a [musical voice][part], which is to say a logical grouping of musical events
into something that could be sung by a person, or played on an instrument.
Voices and (most) instruments only make one note at a time, which is exactly
the postcondition of `spanning`.

[republicans]: https://www.youtube.com/watch?v=S1gHv6jdE3E
[part]: https://en.wikipedia.org/wiki/Part_(music)

The other cool thing here is that now we can change note lengths in the same way
we can change chords and modulations --- namely by doing transformations in
`SF`. You can imagine a `Signal Tension` which describes how much tension the
composer wants you to feel through the journey of the song. By deriving an event
stream out of the modulating `Tension`, where events happen frequently in high
tension situations, and less often under low tension, we can automatically
*drive note durations* from our `Tension` parameter! I haven't used a lot of
DAWs, but my understanding is (and the clankers agree) that almost(?) no DAWs
support duration as an automation. So we might be in terra nova over here!

Perhaps you're starting to get a taste that maybe all of this ["solving
music"][vision] isn't such a pipe dream after all. There's clearly still a huge
distance to travel before we're anywhere close to anything useful, but the
primitives do seem to be pulling their weight.

Of course, nobody wants to call `spanning` by hand, so next time we'll see about
finding nicer ways of generating horizontal structures.


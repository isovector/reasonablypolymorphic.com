---
layout: post
title: Some Useful FRP Combinators
date: TO_BE_DETERMINED
comments: true
tags: frp, game
---

As some of you might know, I'm working on building a procedurally-generated RPG
game right now. My key insight was that Haskell would be an exceptionally good
fit to this problem, given that the most-cited difficulty in making
procedurally-generated things is ensuring all of the subsystems compose together
well.

I had some experience building things in [Elm][elm], and its Haskell cousin
[Helm][helm], but, as I had unwittingly realized [a year before starting this
project][nomonads], neither of them is powerful enough to build
 a procedurally-generated game. Let me elucidate:

*elm (and most of the existent FRP libraries) only provide an `Applicative`
interface on top of their `Signal`s. Elm takes this stance in the triangle of
unpleasantness that is no monads, space leaks, or the loss of referential
transparency. Helm follows in Elm's footsteps, and nobody else seems to have
documented why they don't have a monadic interface -- though I would assume it's
for the same reason. Without a `Monad` instance for `Signal`, encapsulating
reusable functionality into self-contained modules is nigh-impossible.

TODO(sandy): THIS ISNT VERY GOOD v

Suppose my game is launched, and as DLC I want to add a magic mirror in the
desert which requires being spoken to. For fun, I decide to let you use your
computer's microphone to speak to the mirror. Since the microphone is a separate
component that is only going to be used by the magic mirror, it would be silly
if the transitive closure of things that might generate this mirror module
all needed to know about the microphone, but this is indeed the case.

We can't initialize the microphone separately and pull it into our mirror
*a la carte*, due to the lack of `join`. We *can* wrap the entire application in
a `Reader` to [abstract away passing this parameter around][stopworrying]

TODO(sandy): THIS ISNT VERY GOOD ^

So we need `Monad`s if we want any chance of being productive in this domain of
procedural-generation.

[elm]:
[helm]:
[nomonads]:
[stopworrying]:

My first approach in this domain was to simply model `Signal`s as being
denotationally equal to `Time -> a` -- an `a` that changes over time. The idea
was that this was continuous, but I sort of cheated because I'm bad at
denotations. In fact it was actually `Int -> IO a`, where the `IO` was to do
side effects, like `getRealTime` which gave the *illusion of being continuous.*
I'm ashamed to admit that I actually thought this was a good idea.

Perhaps more disgusting than that was that I wanted my `Signal`s to be
*rewindable*, so they had to track all of their previous values for all time.
This resulted in what you might call a "small space leak." I put in some
`unsafePerformIO` hacks to get reasonable performance for folds that occurred
recently in time, which worked for recent time, but turned out to be $O(n!)$ if
you ever needed to fast-forward a non-recently-evaluated `Signal` to the
present.

Programming is hard, as it turns out.

Many hours of uneasiness later, I found another issue in my poorly-thought-out
`Signal` library. After I realized that my `unsafePerformIO`-created "mailboxes"
weren't quite unsafe enough (because Haskell would give me the same pointer for
two things with identical declarations, even if that declaration had
`unsafePerformIO` in it and a `NOINLINE` clause), I "fixed" the issue.

The result is a strong contender for my most terrifying commit message of all
time:

> i solemnly swear on all that is holy that if these mailboxes give me any more
> issues I will write something with real semantics

They did. I held up my end of the bargain, and tracked down the remarkably
gorgeous [FRPNow][frpnow]: "forget the past, change the future!". I was in love
at first sight. It came with a [denotational design][denotation], had a `Monad`
instance, and promised to solve my space leaks.

[denotation]:

Unfortunately for me, FRPNow had *very* different semantics from my `Signal`
library, so I couldn't just drop it in place. Fortunately for me, FRPNow is
actually well-designed and unlikely to cause me any grief going forwards.

While my library only had `Signal`s -- "continuous" transformations of a value
over time, FRPNow also has discrete `Event`s. It also has continuous (note the
lack of scare quotes) transformations, but it calls them `Behavior`s.

But the genius of FRPNow is, appropriately, the `Now` monad. `Now` is kind of
`IO` but with time semantics: it describes things you can do at a particular
moment in time, like sample a `Behavior`, send an `Event`, or kick off some
`IO`.

In short, `Now` is what I didn't come up with because I went with
`unsafePerformIO` instead. Because apparently I'm just *begging* for trouble.

It took more time than I'm proud of figuring out how to use the dang thing.
Here's a combinator that should exist in the core library: run an action as
often as possible:

```haskell
poll :: Now a -> Now (Behavior a)
poll now = loop
  where
    loop = do
        e  <- async (return ())
        a  <- now
        e' <- planNow $ loop <$ e
        return $ step a e'
```

FRPNow's behaviors can only change instantaneously, which happens via an `Event`
telling them to:

```haskell
step :: a -> Event (Behavior a) -> Behavior a
```

`step` starts with value `a`, and changes to the signaled `Behavior a` when the
event fires. It's elegant, but it took some time to grok. And it's a lot of
boilerplate. `poll` does all of this lifting for us -- writing a clock is now
dead easy:

```haskell
clock :: Now (Behavior Time)
clock = poll . sync $ (getTime :: IO Time)
```

Cool! While we're on the topic, let's talk about combinators for a while longer.
Most FRP libraries I've found offer a function of the form:

```haskell
foldp :: (a -> b -> b) -> b -> Behavior a -> Behavior b
```

As you might expect, the first parameter is a folding function, the second is an
initial value, and the third is the state of the world you're sampling from.

Elm trumpets this function as the solution to "how do I write games?" And
they're not wrong: it's possible, if unpleasant. For example, we might define a
player character as a `foldp move` over the arrow keys.

There are two annoyances I've run into while attempting to "folding my p", if
you will:

* the folding function is pure, so it *must* be aware of *everything* that can
    cause your character to change state, and
* there is only a single input, even though most complex behaviors will depend
    on many.

Let's look at an example of code *that I actually wrote* for my player
character:

```haskell
-- A list of actions to perform at any given moment in time.
interactions :: Behavior [Prop -> IO ()]

-- `true` iff `Key` has just been pressed.
keyPress :: Key -> Behavior Signal

player :: Behavior Prop
player = foldp update playerProp $ (,,,,,)
             <$> fmap (filter isWall)  scene
             <*> fmap (filter isFloor) scene
             <*> interactions
             <*> elapsed
             <*> arrows
             <*> keyPress SpaceKey
  where
    update (walls, floors, ints, dt, dir, active) p =
        if active && (not $ null ints)
           then seq (unsafePerformIO $ mapM_ ($ p) ints) p
           else
                let dpos = scaleRel (dt * playerSpeed) dir
                 in tryMove walls floors p dpos
```

There are so many terrible things going on here, and I'm not proud of it, but it
worked. The most salient is the six lines of constructing that single input
behavior to `foldp`. Adding a new input behavior was *painful*: I had to add a
new comma to my tuple constructor, a new `(<*>)` invocation, and then
destructure it in `update`. That is a lot of repeating myself in a language
where we pride ourselves on being [DRY][dry].

But wait, it gets worse. The seasoned veteran will spot it quickly: `seq .
unsafePerformIO`. Here, `interactions` is a behavior describing changes we want
to perform on the outside world -- but pure code isn't allowed to do that!

Don't run away in terror yet. Consider the following combinator:

[dry]:

```haskell
{-# LANGUAGE TupleSections #-}
foldmp :: a
       -> (a -> Now a)
       -> Now ( Behavior a
              , (a -> a) -> IO ())
foldmp start f = do
    -- Construct the underlying mailbox.
    (evStream, mailbox) <- callbackStream
    let events = nextAll evStream
    nextEvent <- sample events

    -- Like `poll`, but aware of the event stream.
    b <- loop start events nextEvent
    return (b, mailbox)
  where
    loop a events nextEvent = do
        -- See if our event has fired yet...
        evVal <- sample $ tryGetEv nextEvent
        (a'mb, nextEvent') <-
            case evVal of
              -- And if it has, fold over all its transformations.
              Just updates ->
                  sample events >>= return . (foldr ($) a updates,)
              Nothing -> return (a, nextEvent)
        a' <- f a'mb

        -- Just `poll`.
        e  <- async (return ())
        e' <- planNow $ loop a' events nextEvent' <$ e
        return $ step a' e'
```

`foldmp` turns out to be the function we wished we had when we were writing
`player` up there: it returns a behavior that folds itself over time (with a
monadic fold, however, so it can sample other behaviors!), and a "mailbox" that
we can use to introduce changes in the fold from an external source.

Unfortunately, if two transformations are given to the mailbox at the same time,
it's non-deterministic which will win. This is a problem I haven't solved yet,
but by which have yet to be bitten. Any solutions would be highly appreciated.

Anyway -- rewriting `player` in terms of `foldmp` is already a much nicer
experience:

```haskell
player :: Now (Behavior Prop)
player = fmap fst . foldmp playerProp $ \p -> do
    ints   <- sample interactions
    dt     <- sample elapsed
    dir    <- sample arrows
    active <- sample $ keyPress SpaceKey
    props  <- sample scene
    let walls  = filter isWall props
        floors = filter isFloor props

    if active
        then do
            liftIO $ mapM_ id ints
            return p
        else
            let dpos = scaleRel (dt * playerSpeed) dir
             in tryMove walls floors p dpos
```

Better, but notice how this is pretty much a direct port -- we're throwing away
the mailbox that `foldmp` gives back. We can instead use it to separate out the
interaction logic:

```haskell
player :: Now ( Behavior Prop
              , (Prop -> Prop) -> IO ())
player = do
    r@(_, addr) <- foldmp playerProp $ \p -> do
        dt    <- sample elapsed
        dir   <- sample arrows
        props <- sample scene
        let walls  = filter isWall props
            floors = filter isFloor props
            dpos   = scaleRel (dt * playerSpeed) dir
        return $ tryMove walls floors p dpos

    poll $ do
        ints   <- sample interactions
        active <- sample $ keyPress SpaceKey
        when active . liftIO $ forM_ ints (addr $)

    return r
```

It's nice that `player` can now fold in a natural way: interactions are no
longer shoe-horned in just for the sake of making it compile, but now run in
their own context.

However, we can do better yet. Recall that `poll` runs as quickly as it can; but
`keyPress SpaceKey` by happens only very rarely. We'll change `keyPress` to
instead be `keyPress :: Key -> Behavior (Event ())`, which conceptually, is, at
any moment, an `Event` referring to the *next* time that `Key` is pressed.

This suggests another combinator, like `poll`, but only running when events come
in:

```haskell
onEvent :: Behavior (Event a)
        -> (a -> Now ())
        -> Now ()
onEvent events f = loop
  where
    loop = do
        e <- sample events -- ^ The next time this event happens.
        planNow $ ((>> loop) . f) <$> e
        return ()
```

And now pulling it all together:

```haskell
newPlayer :: Now ( Behavior Prop
                 , (Prop -> Prop) -> IO ())
newPlayer = return $ do
    r@(sig, addr) <- foldmp playerProp $ \p -> do
        dt    <- sample elapsed
        dir   <- sample arrows
        props <- sample scene
        let walls  = filter isWall props
            floors = filter isFloor props
            dpos   = scaleRel (dt * playerSpeed) dir
        return $ tryMove walls floors p dpos

    onEvent (keyPress SpaceKey) . const $ do
        ints <- sample interactions
        liftIO $ forM_ ints (addr $)

   return r
```

Wow! It's everything we ever wanted! We've eliminated our space leaks,
eliminated a bunch of boilerplate, modularized our logic, made the whole thing
performant, and managed to come up with a typesafe messaging protocol over time
in the process.


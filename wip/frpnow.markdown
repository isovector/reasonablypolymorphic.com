---
layout: post
title: frpnow
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
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

here is a useful combinator to continuously run a `Now` action

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

Let's talk about combinators for a while. Most FRP libraries I've found offer a
function of the form:

```haskell
foldp :: (a -> b -> b) -> b -> Behavior a -> Behavior b
```

As you might expect, the first parameter is a folding function, the second is an
initial value, and the third is the state of the world you're sampling from.

Elm trumpets this function as the solution to "how do I write games?" And
they're not wrong, it's possible, if unpleasant. For example, we might define a
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
           then seq (unsafePerformIO $ mapM_ id ints) p
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
    (evStream, mailbox) <- callbackStream
    let events = nextAll evStream
    nextEvent <- sample events
    b <- loop start events nextEvent
    return (b, mailbox)
  where
    loop a events nextEvent = do
        e     <- async (return ())
        evVal <- sample $ tryGetEv nextEvent
        (a'mb, nextEvent') <-
            case evVal of
              Just updates ->
                  sample events >>= return . (foldr ($) a updates,)
              Nothing -> return (a, nextEvent)
        a' <- f a'mb
        e' <- planNow $ loop a' events nextEvent' <$ e
        return $ step a' e'
```

TODO: this is nondeterministic :(

`foldmp` turns out to be the function we wished we had when we were writing
`player` up there: it returns a behavior that folds itself over time (with a
monadic fold, however, so it can sample other behaviors!), and a "mailbox" that
we can use to introduce changes in the fold from an external source.

Rewriting `player` in terms of `foldmp` is already a much nicer experience:

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

Much better, but notice how this is pretty much a direct port -- we're throwing
away the mailbox that `foldmp` gives back. We can instead use it to separate out
the interaction logic:

```haskell
player :: Now ( Behavior Prop
              , (Prop -> Prop) -> IO ())
player = foldmp playerProp $ \p -> do
    dt    <- sample elapsed
    dir   <- sample arrows
    props <- sample scene
    let walls  = filter isWall props
        floors = filter isFloor props
        dpos = scaleRel (dt * playerSpeed) dir
    return $ tryMove walls floors p dpos

interactionHandler :: ((Prop -> Prop) -> IO ())
                   -> Now ()
interactionHandler addr = poll $ do
    ints   <- sample interactions
    active <- sample $ keyPress SpaceKey
    when active . liftIO $ forM_ ints (addr $)
```

It's nice that `player` can now fold in a natural way, and that interactions are
no longer shoe-horned in just for the sake of making it compile. Unfortunately,
there's a bit of plumbing necessary on the caller to connect the `player`
mailbox with the `interactionHandler`.

```haskell
keyPress :: Key -> Behavior Bool
```

which is true if the key wasn't pressed last frame but is now. we're wasting all
of these cpu cycles by polling even though we don't need to anymore.

change to:

```haskell
keyPress :: Key -> Behavior (Event ())
```

now we get a discrete event when the key was pressed, and we can run some logic
on that. define the following combinator

note its similarity to `poll`

```haskell
onEvent :: Behavior (Event a)
        -> (a -> Now ())
        -> Now ()
onEvent events f = loop
  where
    loop = do
        e <- sample events
        planNow $ ((>> loop) . f) <$> e
        return ()
```

and now pulling it all together:

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
            dpos = scaleRel (dt * playerSpeed) dir
        dpos  <- fmap (scaleRel $ dt * playerSpeed) . sample $ arrows keys
        return $ tryMove walls floors p dpos

    onEvent (keyPress SpaceKey) . const $ do
        ints <- sample interactions
        liftIO $ forM_ ints (addr $)

   return r
```

---
layout: post
title: "Devlog: Action Menus, Timers and Hit Detection"
date: 2018-02-01 21:50
comments: true
tags: devlog, neptune
---

The other day, I found myself working on the interaction subsystem of my game
engine. I want the game to [play like Monkey Island 3][mi3], which means you can
click on the ground to walk there. You can also click and hold on an interactive
piece of scenery in order to have a context-sensitive menu pop-up, from which
you can choose how to interact with the object in question. If you're not
familiar with the genre, watching a few minutes of the video linked above should
give you some idea of what I'm trying to build.

[mi3]: https://youtu.be/v8eNzUtCVlY?t=863

An adventure game in which you're unable to interact with anything isn't much of
a game, and that's where we left the engine. So it seemed like a thing to focus
on next.

I knew that click/hold interaction that I wanted formed some sort of [DFA][dfa],
so I unwisely headed down that garden path for a bit. After implementing a bit,
I found a state machine with the denotation of `type DFA s e a = s -> e ->
Either s a`, where `s` is the state of the machine, `e` is the type of an edge
transition, and `a` is the eventual output of the machine. Upon the final
result, however, it became clear that I had fallen into an abstraction hole. I
spent a bunch of time figuring out the implementation of this thing, and then
afterwards realized it didn't actually solve my problem.  Whoops. Amateur
Haskell mistake :)

[dfa]: https://en.wikipedia.org/wiki/Deterministic_finite_automaton

The problem is that transitioning into some state might need to make a monadic
action in order to generate the next edge. For example, when you press down on
the mouse button, we need to start a timer which will open the action menu when
it expires. This could be alleviated by changing `Either` to `These` and letting
`a ~ (Monad m => m b)`, but that struck me as a pretty ugly hack, and getting
the implementation of the denotation to work again was yucky.

So I decided that instead maybe I should write a dumb version of what I wanted,
and find out how to abstract it later if I should need similar machinery again
in the future. I burned my `DFA` implementation in a fire.

This posed a problem, though, because if I wanted to write this for real I was
going to need things to actually interact with, and I didn't yet have those. I
decided to put the interaction sprint on hold, in order to focus more on having
things with which to interact.

One abstraction I think in terms of when working with adventure games is that of
the **hotspot**. A hotspot is a mask on the background image which indicates a
static piece of interesting geometry. For example, a window that never moves
would be baked into the background image of the room, and then a hotspot would
be masked on top of it to allow the character to interact with it.

For example, if our room looks like this (thanks to MI2 for the temporary art):

![room background][bg]

[bg]: /images/bg.png

Then our mask image would look like this:

![room mask][mask]

[mask]: /images/mask.png

We can add some logic to be able to read the mask:

```haskell
mkHotspot
    :: Image PixelRGBA8
    -> (Word8 -> Bool)
    -> Hotspot
    -> Pos
    -> Maybe Hotspot
mkHotspot img f h = bool Nothing (Just h)
                  . f
                  . getHotspotByte
                  . uncurry (pixelAt img)
                  . (\(V2 x y) -> (x, y))
                  . clampToWorld
                  . fmap round
  where
    clampToWorld = clamp (V2 0 0) $ imageSize img
    getHotspotByte (PixelRGBA8 _ g _ _) = g
```

and now bake the first three parameters of this function when we construct our
level definition.

In order to test these things, I gave added a field `_hsName :: Hotspot ->
String` in order to be able to test if my logic worked. The next step was to
bind the click event to be able to call the `Pos -> Maybe Hotspot` that I
curried out of `mkHotspot` and stuck into my `Room` datastructure (`_hotspots ::
Room -> Pos -> Maybe Hotspot`).

I clicked around a bunch, and found that `print . fmap _hsName $ _hotspots
currentRoom mousePos` lined up with the door when I clicked on it. It seemed to
be working, so I considered my first yak shave successful: I now had something
in the world that I could interact with.

The next step was to code up a little bit of the DFA I was originally working
on. I decided that I should make the avatar walk to the place you clicked if it
wasn't a hotspot.

```haskell
case event of
  MouseButton Down ->
    case _hotspots currentRoom mousePos of
      Just hs ->
        print $ _hsName hs

      Nothing ->
        when (isWalkable (_navmesh currentRoom) mousePos) $
          emap $ do
            with isAvatar
            pure defEntity'
              { pathing = Set $ NavTo mousePos
              }
```

So: when the mouse is pressed, see if it was over top of a hotspot. If so, print
out the name of it. Otherwise, check the navmesh of the room, and see if that's
a valid place to walk. If so, update any entity who has the `isAvatar` component
and set its `pathing` component to be the location we want.

The engine at this point already has navigation primitives, which is why this
works. We'll discuss how the navmesh is generated and used in another devlog
post.

I ran this code and played around with it for a while. Everything looked good --
after I remembered to set `isAvatar` on my player entity :)

The next step was to implement timers that would have a callback, and could be
started and stopped. I'd need support for these in order to wait a little bit
before opening up the action menu. Thankfully, timers are super easy: just have
an amount of time you decrement every frame until it hits zero, and then do the
necessary action. I came up with this model for timers:

```haskell
data Timer = Timer
  { _tTime     :: Time
  , _tCallback :: Game ()
  }

data TimerType
  = TimerCoin
  deriving (Eq, Ord)

data GlobalState = GlobalState
  { ... -- other stuff
  , _timers :: Map TimerType Timer
  }
```

A `Timer` is just an amount of remaining time and something to do afterwards.
It's stored in the `GlobalState` with a `TimerType` key. I originally thought
about using a bigger type (such as `Int`) as my timer key, but realized that
would make canceling specific timers harder as it would imply they're given a
non-deterministic key when started. The interface for starting and canceling
timers turned out to be trivial:

```haskell
startTimer :: TimerType -> Time -> Game () -> Game ()
startTimer tt t cb =
  setGlobals $ timers . at tt ?~ Timer t cb

cancelTimer :: TimerType -> Game ()
cancelTimer tt =
  setGlobals $ timers . at tt .~ Nothing
```

The only thing left is to update timers and run their callbacks when it's time.
I fucked around with this implementation too hard, trying to find a completely
lensy way of doing it, but eventually settled on this ugly `fromList . toList`
thing:

```haskell
updateTimers :: Time -> Game ()
updateTimers dt = do
  ts  <- getGlobals $ view timers
  ts' <- forOf traverse ts $ \t ->
           if _tTime t - dt <= 0
             then _tCallback t $> Nothing
             else pure . Just
                       $ t & tTime -~ dt

  setGlobals $
    timers .~ M.fromList (catMaybes . fmap sequence $ M.toList ts')
```

`ts'` is a traversal over the `Map` of timers, that decrements each of their
times, optionally runs their callbacks, then returns a `Mayber Timer` for each
one. The last line is where the interesting bit is -- `sequence` over a
`(TimerType, Maybe Timer)` is a `Maybe (TimerType, Timer)`, which we can then
insert back into our `Map` as we construct it -- essentially filtering out any
timers which have expired.

Finally we can get back to our DFA. Instead of printing out the name of the
hotspot you clicked on, we can now start a timer that will update our game
state. I added a field to `GlobalState`:

```haskell
data GlobalState = GlobalState
  { ... -- other stuff
  , _gInputDFA :: InputDFA
  }

data InputDFA
  = IStart
  | IBeforeCoin
  | ICoinOpen Pos HotSpot
  deriving (Eq, Ord)
```

The idea is that we start in state `IStart`, transition into `IBeforeCoin` when
we start the timer, and into `ICoinOpen` when the timer expires. Additionally,
if the user releases the mouse button, we want to cancel the timer. All of this
becomes:

```haskell
case (_gInputDFA globalState, event) of
  (IStart, MouseButton Down) ->
    case _hotspots currentRoom mousePos of
      Just hs -> do
        startTimer TimerCoin 0.5 $ do
          setGlobals $ gInputDFA .~ ICoinOpen mousePos hs
        setGlobals $ gInputDFA .~ IBeforeCoin

      Nothing ->
        -- as before

  (IBeforeCoin, MouseButton Up) -> do
    cancelTimer TimerCoin
    setGlobals $ gInputDFA .~ IStart

  (ICoinOpen p hs, MouseButton Up) -> do
    let verb = getBBSurface (coinSurface p) mousePos
    for_ verb $ doInteraction hs
    setGlobals $ gInputDFA .~ IStart
```

If you care, try to trace through these cases and convince yourself that this
logic is correct. The reason we have a position stored inside the `ICoinOpen` is
so that we know where the mouse was when the user started holding their mouse
down. This corresponds to where we should draw the action menu.

This is done in the drawing routine by checking the current state of
`_gInputDFA` -- if it's `ICoinOpen` it means the menu is up and we need to draw
it.

The only last thing is how can we map where you release your mouse button on the
menu to what interaction we should do. Our action menu looks like this:

![the action menu][actions]

[actions]: /images/actionbar.png

From left to right, these squares represent talking/eating, examining, and
manipulating. We need some way of mapping a location on this image to a desired
outcome.

Doing rectangle collision is easy enough -- we define a bounding box and a test
to see if a point is inside of it (as well as some auxiliary functions for
constructing and moving `BB`s, elided here):

```haskell
data BB = BB
  { leftX   :: Float
  , rightX  :: Float
  , topY    :: Float
  , bottomY :: Float
  } deriving (Eq, Ord, Show)


inBB :: BB -> Pos -> Bool
inBB BB{..} (V2 x y) = and
  [ x >= leftX
  , x <  rightX
  , y >= topY
  , y <  bottomY
  ]

rectBB :: Float -> Float -> BB
moveBB :: Pos -> BB -> BB
```

The final step is to somehow map these bounding boxes to things we want to
return. This seems like it'll be a recurring theme, so we build some machinery
for it:

```haskell

data BBSurface a = BBSurface [(BB, a)]
  deriving (Eq, Ord, Show)

getBBSurface :: BBSurface a -> Pos -> Maybe a
getBBSurface (BBSurface bs) p =
  getFirst . flip foldMap bs $ \(b, a) ->
    if inBB b p
       then First $ Just a
       else First $ Nothing
```

The abstraction is my amazingly-named `BBSurface`, which is a mapping of `BB`s
to values of some type `a`. We can find a `Maybe a` on the `BBSurface` by just
checking if the point is in any of the bounding boxes. If it is, we return the
first value we find.

All that's left is to construct one of these `BBSurface`s for the coin, and then
to move it to the position indicated inside the `ICoinOpen`. Easy as pie.
Pulling everything together, and our interactive menu works as expected. Great
success!

Next time we'll talk about navigation. Thanks for reading!


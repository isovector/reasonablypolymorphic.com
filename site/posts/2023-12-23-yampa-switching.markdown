---
layout: post
title: "FRP in Yampa: Part 3: Switching"
date: 2023-12-24 00:12
comments: true
tags: FRP, yampa, haskell, technical, programming, gamedev
---

[Yesterday](https://reasonablypolymorphic.com/blog/arrowized-frp) we
looked at arrowized FRP in Yampa, and saw how it the `proc` notation is to
arrows as `do` is for monads. While these syntaxes don't give you any new power,
notation nevertheless matters and helps us better structure our programs.

So far all of our programs have consisted of a single signal function. We've
sketched out how to build a lobotomized version of the Snake game, but real
games have things like title screens and option menus as well as the actual
gameplay component. If you were determined, you could probably figure out how to
build these missing components with what we've seen so far, but it wouldn't be
fun.

Instead, we turn our attention to switches.


## Switching

Yampa's `SF` type isn't monadic, but the `switch` combinator gets you
surprisingly close:

```haskell
switch :: SF i (o, Event e) -> (e -> SF i o) -> SF i o
```

The idea is that you run the first `SF` until the outputted `Event` produces an
event, at which point you take its value and use it to generate a new `SF`,
which you subsequently run.

As an example, let's build a little coproduct type for the choices we might make
on the menu screen:

```haskell
data MenuOption = Start | Options
```

Our menu screen is now an `SF` that outputs the things we'd like to draw on the
screen (a `Render`), as well as an `Event MenuOption` corresponding to an event
for when we actually make a selection:

```haskell
menuScreen :: SF () (Render, Event MenuOption)
menuScreen = ...
```

As before, we have our main Snake game, and now a new screen for the options:

```haskell
mainGame :: SF () Render
mainGame = ...

optionsScreen :: SF () Render
optionsScreen = ...
```

We can tie it all together by `switch`ing from `menuScreen` to the appropriate
next `SF`:

```haskell
program :: SF () Render
program = switch menuScreen $ \case
  Start   -> mainGame
  Options -> optionsScreen
```

Again, you can kind of squint to get the picture, but things get a little
gnarlier when you actually get into the gritty details here. For example, in a
real game, you might go back to the menu screen after the game ends, and you'd
*certainly* go back after setting up the appropriate options. If we wanted to
encode those rules, we'd need to fiddle with some types.

Let's add `Event ()`s to `mainGame` and `optionScreen`, corresponding to when
the player has died and when the options have been set, respectively:

```haskell
mainGame :: SF () (Render, Event ())
optionsScreen :: SF () (Render, Event ())
```

With a creative amount of `switch`ing, it's possible to encode everything we'd
like:

```haskell
program :: SF () Render
program = switch menuScreen $ \case
  Start   -> switch mainGame      $ const program
  Options -> switch optionsScreen $ const program
```

Of course, we can use `switch` for much more than just modeling state
machines---the following example uses it as a combinator to do something for a
while:

```haskell
timed :: Time -> SF i o -> SF i o
timed dur s1 s2 =
  switch
    (proc i -> do
      o  <- s1 -< i
      ev <- after dur () -< ()
      returnA -< (o, ev)
    ) $ const s2
```

or, more interestingly, a combinator which interpolates a function:

```haskell
interpolate :: Time -> (Time -> a) -> SF (i, a) o -> SF i o -> SF i o
interpolate dur f interp final =
  switch
    (proc i -> do
      t  <- time -< ()
      o  <- s1 -< (i, t / dur)
      ev <- after dur () -< ()
      returnA -< (o, ev)
    ) $ const final
```

The parameter `f` here will be called with values of time from `0` to `1`,
linearly increasing until `dur`. This is the sort of combinator that is
extremely useful for animating objects, where you'd like to tween from a known
starting point to a know ending point.


## Making a Real Monad

Most of what I know about Yampa I learned by reverse-engineering [Alex
Stuart](https://das.li/index.html)'s excellent game
[Peoplemon](https://linearity.itch.io/peoplemon) ([source
here](https://hub.darcs.net/linearity/pplmonad)). As you might expect, it's a
fun parody on Pokemon.

One night while desperately trying to work out how he programmed up the
menu-based battle system in Peoplemon, I came across the mysteriously named
[Lightarrow.hs](https://hub.darcs.net/linearity/pplmonad/browse/src/Lightarrow.hs),
which makes the following improvement over the `switch`ing technique above.

He sticks the whole thing into the `Cont` monad:

```haskell
newtype Cont r a = Cont { runCont :: (a -> r) -> r }
```

I think this is the first and only time I've seen a use for `Cont` in the wild,
that doesn't stem *directly* from trying to CPS everything in order to make your
program go faster from fusion. It's so COOL to see a real world opportunity to
throw `Cont` at a problem!

Anyway. This type is known as `Swont`, which I've always assumed was something
like "signal continuation" but your guess is as good as mine:

```haskell
newtype Swont i o a = Swont { unSwont :: Cont (SF i o) a }
  deriving newtype (Functor, Applicative, Monad)
```

We can lift any `SF i (b, Event c)` into a `Swont` via `swont`:

```haskell
swont :: SF i (o, Event e) -> Swont i o e
swont = Swont . cont . switch
```

and we can lower the whole thing again by way of `switchSwont`:

```haskell
switchSwont :: Swont i o e -> (e -> SF i o) -> SF i o
switchSwont sw end = runCont (unSwont sw) end
```

What's really nice about `Swont` is that it is a genuine, bona-fide monad. This
gives us a really lovely notation for programming sequential things like state
machines or battle animations---stuff that consists of needing to switch between
disparate things with discrete reasons to change.

We can use `Swont` to encode our above state machine in a much more familiar
way:

```haskell
foreverSwont :: Swont i o e -> SF i o
foreverSwont sw = switchSwont (forever sw) $ error "impossible"

program :: SF () Render
program = foreverSwont $ do
  menuScreen >>= \case
    Start   -> mainGame
    Options -> optionsScreen
```

Not bad at all!


## Wrapping Up

Today we looked at Yampa's `switch` combinator, seen how it can be used to
string disparate signals together, and seen how wrapping the whole thing in
a continuation monad can make the whole thing tolerable to work with.

In tomorrow's post, we'll look at writing object routers in Yampa---essentially,
the main data structure for tracking lots of game objects, and allowing them to
communicate with one another. Until then, I hope you're having a very special
Christmas weekend.



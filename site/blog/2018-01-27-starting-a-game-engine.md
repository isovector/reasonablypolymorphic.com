---
layout: post
title: "Devlog: Starting a Game Engine"
date: 2018-01-27 13:39
comments: true
tags: devlog, neptune
---

I'm ravenously working my way through Austin Kleon's excellent book [Show Your
Work][work]. One of the points that most resounded with me was to, as you might
anticipate, show your work. But more importantly, to share it every day. I've
decided to take up that challenge in documenting the development of some of my
bigger projects. The goal has a few facets: to show how I work and the struggles
that I face while writing Haskell on a day-to-day basis; to lend my voice
towards the art of game programming in Haskell; and to bolster [my 2018
publishing goals][2018].

[work]: https://www.goodreads.com/book/show/18290401-show-your-work
[2018]: http://sandymaguire.me/blog/perpetual-motion/

I want to make an old school point-and-click adventure game in the style of
[Monkey Island][mi] or [Full Throttle][ft]. I've wanted to make one for as long
as I can remember, and I finally have a concept and some amount of script that I
think would be fitting for the medium. I spent roughly two days searching for
engines to run this baby on, and I didn't have any luck whatsoever.

[mi]: https://en.wikipedia.org/wiki/The_Curse_of_Monkey_Island
[ft]: https://en.wikipedia.org/wiki/Full_Throttle_(1995_video_game)

* [adventure][adventure] - an old adventure game engine I wrote back in '12 or so. It
    requires writing a *lot* of lua, and appears to have bitrotten since then. I
    couldn't get it to compile.
* [Adventure Game Studio][ags] - the latest version of the IDE immediately segfaults
    when run through WINE.
* [WinterMute][wm] - has a "garbage" rating on WINE HQ.
* [Godot/Escoria][escoria] - Escoria doesn't appear to run on recent versions of Godot.
* [Visionaire][visionaire] - I successfully got the editor running on WINE, but it couldn't
    draw anything, so I could edit everything but had no visual feedback on
    anything.
* [Bladecoder Adventure Engine][bae] - I fought to compile this for a while, and
    eventually succeeded, but got scared of it. It's written by a single guy in
    a language I never want to touch, and decided the risk factor was too high.
* [Unity Adventure Creator][uac] - looks promising, but required forking out 70 euros
    before you could try it. As someone who [is unemployed][retired] knows
    nothing about Unity, this is a pretty steep price to determine whether or
    not the project will work for my purposes.

[retired]: http://sandymaguire.me/blog/reaching-climbing/
[adventure]: https://github.com/isovector/adventure
[ags]: https://github.com/isovector/adventure
[wm]: http://dead-code.org/home/
[escoria]: https://github.com/godotengine/escoria
[visionaire]: https://www.visionaire-studio.net/?lang=en
[bae]: https://github.com/bladecoder/bladecoder-adventure-engine
[uac]: https://github.com/bladecoder/bladecoder-adventure-engine

So it looks like we're SOL. The existing engines don't seem like they're going
to cut it. Which means we're going to need to roll our own.

Fortunately I've rolled a few of my own already. This wasn't my first rodeo.
There's the previously mentioned [adventure][adventure], an unnamed XNA/C# one I
wrote before knowing about source control which is unfortunately lost to the
sands of time, and one I most recently put together as a technical demo for a
project a friend and I were going to work on. The friend pulled out,
unfortunately, so the project died, but that means I have a starting point.

The engine as it existed had basic functionality for pathing around a bitmap,
moving between rooms, and basic support for interacting with the environment.
Unwisely, it was also a testbed for lots of type-trickery involving
existentially pushing around types to manage the internal state of things in the
game. It was intended that we'd do all of our game scripting directly in
Haskell, and this seemed like the only approach to have that work.

So my first order of business was to tear out all of the existential stuff. I've
learned since that you should always avoid existentializing things unless you
are really really sure you know what you're doing. It's a soft and slow rule,
but more often than not I regret existentializing things. The new plan was to
script the game with a dedicating scripting language, and so Haskell never needs
to know about any of the internal state.

Since writing the first draft of this game engine, I've published a library
called [`ecstasy`][ecs]. It's an entity-component system that allows you to
describe behaviors over components of things, and then compose all of those
behaviors together. The magic here is that you can write a function that only
manipulates the components you need, and the library will lift it over all
entities such a behavior would be relevant to. This means you can
pick-and-choose different behaviors for game objects without needing to do a lot
of heavy plumbing to get everything to play nicely with one another.

[ecs]: https://github.com/isovector/ecstasy

And so the next step was to hook up `ecstasy` to my existing engine. I didn't
want to alter any of the game's behavior yet, so entities managed by `ecstasy`
would have to exist completely parallel to the ones managed by the existing
engine.

I defined my `ecstasy` component type with the most minimal support for drawing
things on the screen.

```haskell
data EntWorld f = Entity
  { pos      :: Component f 'Field Pos
  , gfx      :: Component f 'Field Picture
} deriving (Generic)
```

and then updated my drawing routine to find any `Entity` who had both a `pos`
and a `gfx` and then hook it into the existing drawing stuff:

```haskell
drawGame :: MyState -> IO Picture
drawGame ms@(s, _) = evalGame' ms $ do
  gfxs <- efor . const $
    (,) <$> get pos <*> get gfx

  pure . scaleToView s
       . uncurry translate (-camera)
       . pictures
       $ roomPic
       : [ drawActors actors
         , drawGfxs gfxs
         ]
```

There was some silly plumbing necessary to connect my old, convoluted `Game`
monad with the `System` monad provided by `ecstasy`. That's what this `ms@(s,
_)` and `Game'` silliness is here; little shims that can run the two monads
simultaneously and reconcile the results. It was pretty gnarly, but thankfully
only a hack until I could convert enough of the game logic over to being
exclusively managed by `ecstasy`.

I think that's where we'll leave the dev blog for today. I want to get us
roughly caught up to the present in terms of getting from there-to-here in order
to provide a better overall view of what game development in Haskell looks like.
But I'm also pretty anxious to actually get some work done, rather than just
describing work I have done. I expect the posts to get more technical as we get
closer to being caught up, when I don't need to depend on my memory for what
changes were made.

Next time we'll discuss ripping out most of the silly global variables that used
to be in play, and talk about how an ECS better models things like "what should
the camera be focused on?" and "how should characters navigate the space?"

Until then.


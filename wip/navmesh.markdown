---
layout: post
title: "Devlog: Navigation"
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

One of the tropes of the golden era of point-n-click adventure games is, would
you believe it, the pointing and clicking. In particular, pointing where you'd
like the avatar to go, and clicking to make it happen. This post will explore
how I made that happen in my [neptune][neptune] game engine.

[neptune]:

The first thing we need to do is indicate to the game which parts of the
background should be walkable. Like we did for [marking hotspots][hotspots],
we'll use an image mask. Since we have way more density in an image than we'll
need for this, we'll overlay it on the hotspot mask.

[hotspots]:

Again, if the room looks like this:

![room background][bg]

[bg]: /images/bg.png

Our mask image would look like this:

![room mask][mask]

[mask]: /images/mask.png

Here, the walkable section of the image is colored in blue. You'll notice
there's a hole in the walk mask corresponding to the table in the room; we
wouldn't want our avatar to find a path that causes him to walk through the
table.

However there is something important to pay attention to here; namely that we're
making an adventure game. Which is to say that our navigation system doesn't
need to be all that good; progress in the game is blocked more by storytelling
and puzzles than it is by the physical location of the player (unlike, for
example, in a platformer game.) If the avatar does some unnatural movement as he
navigates, it might be *immersion-breaking*, but it's not going to be
*game-breaking*.

Which means we can half ass it, if we need to. But I'm getting ahead of myself.

The first thing we're going to need is a function which samples our image mask
and determines if a given position is walkable.

```haskell
canWalkOn :: Image PixelRGBA8 -> V2 Int -> Bool
canWalkOn img (V2 x y)
    = flip testBit walkableBit
    . getWalkableByte
    $ pixelAt img x y
  where
    getWalkableByte (PixelRGBA8 _ _ b _) = b
    walkableBit = 7
```

Currying this function against our image mask gives us a plain ol' function
which we can use to query walk-space.

In a 3D game, you'd use an actual mesh to mark the walkable regions, rather than
using this mask thing. For that purpose, from here on out we'll call this thing
a navmesh, even though it isn't strictly an appropriate name in our case.

Because pathfinding algorithms are defined in terms of graphs, the next step is
to convert our navmesh into a graph. There are lots of clever ways to do this,
but remember, we're half-assing it. So instead we're going to do something
stupid and construct a square graph by sampling every $n$ pixels, and connecting
it to its orthogonal neighbors if both the sample point and its neighbor are
walkable.

It looks like this:

![graph building][graph]

[graph]: /images/graph.gif

Given the navmesh, we sample every $n$ points, and determine whether or not to
put a graph vertex there (white squares are vertices, the black squares are just
places we sampled.) Then, we put an edge between every neighboring vertex (the
white lines.)

We're going to want to run [A*][astar] over this graph eventually, which is
implemented in Haskell via [`Data.Graph.AStar.aStar`][astarimpl]. This package
uses an implicit representation of this graph rather than taking in a graph data
structure, so we'll construct our graph in a manner suitable for `aStar`.

[astar]:
[astarimpl]: https://hackage.haskell.org/package/astar-0.3.0.0/docs/Data-Graph-AStar.html#v:aStar

But first, let's write some helper functions to ensure we don't get confused
about whether we're in world space or navigation space.

```haskell
-- | Sample every n pixels in on the navmesh.
sampleRate :: Float
sampleRate = 4

-- | Newtype to differentiate nav node coordinates from world coordinates.
newtype Nav = Nav { unNav :: Int }
  deriving (Eq, Ord, Num, Integral, Real)

toNav :: V2 Float -> V2 Nav
toNav = fmap round
      . fmap (/ sampleRate)

fromNav :: V2 Nav -> V2 Float
fromNav = fmap (* sampleRate)
        . fmap fromIntegral
```

`toNav` and `fromNav` are roughly inverses of one another -- good enough for
half-assing it at least. We'll do all of our graph traversal stuff in nav-space,
and use world-space only at the boundaries.

We start with some helper functions:

```haskell
navBounds :: Image a -> V2 Nav
navBounds = subtract 1
          . toNav
          . fmap fromIntegral
          . imageSize
```

`navBound` gives us the largest valid navigation point from an image -- this
will be useful later when we want to build a graph and *don't* want to sample
points that are not on it.

The next step is our `neighbors` function, which should compute the edges for a
given node on the navigation step.

```haskell
neighbors :: V2 Nav -> HashSet (V2 Nav)
neighbors v2 = HS.fromList $ do
  let canWalkOn' = canWalkOn
                 . fmap floor
                 . fmap fromNav

  V2 x y <- fmap (v2 &)
            [ _x -~ 1
            , _x +~ 1
            , _y -~ 1
            , _y +~ 1
            ]
  guard $ canWalkOn' img v2
  guard $ x >= 0
  guard $ x <= w
  guard $ y >= 0
  guard $ y <= h
  guard . canWalkOn' img $ V2 x y
  return $ V2 x y
```

We use the list monad here to construct all of the possible neighbors -- those
which are left, right, above and below our current location, respectively. We
then guard on each, ensure our current nav point is walkable, that our candidate
neighbor is within nav bounds, and finally that the candidate itself is
walkable. We need to do this walkable check last, since everything will explode
if we try to sample a pixel that is not in the image.

Finally we need a distance function, which we will use both for our astar
heuristic as well as our actual distance. The actual distance metric we use
doesn't matter, so long as it corresponds monotonically with the actual distance

```haskell
pathfind :: Image PixelRGBA8 -> V2 Double -> Pos -> Maybe [Pos]
pathfind img = \src dst -> astar neighbors dist (flip dist navDst) navSrc
  where
    navSrc = toNav src
    navDst = toNav dst




---
layout: post
title: Performance and Feature Case Studies in Ecstasy
date: 2018-05-18 13:37
comments: true
tags: haskell, type trickery, technical, performance
---

In my ([copious][retirement]) spare time, I've been working on an [RTS
game][typecraft] written in Haskell. It's using my entity-component system
library [ecstasy][ecstasy] in anger, for what is likely the library's first
time. As a result, I'm learning a lot about doing performance haggling with the
compiler, as well as getting opportunities for [even more][trickery]
type-trickery. I thought both might make for interesting topics of discussion.

[retirement]: http://sandymaguire.me/blog/reaching-climbing/
[typecraft]: https://github.com/isovector/typecraft
[ecstasy]: https://github.com/isovector/ecstasy
[trickery]: /tags/haskell.html


## Overview of ecstasy's internals

Before diving into what I've been changing recently, it's probably a good idea
to quickly talk inside baseball about how ecstasy works. The basic idea is this,
you define a "world" [higher-kinded data][hkd] (HKD) corresponding to the
components you care about. The library instantiates your HKD world in different
ways to form a [*structure-of-arrays*][soa] corresponding to the high-efficiency
storage of the ECS, and to form *just a structure* corresponding to an actual
entity.

[hkd]: /blog/higher-kinded-data/
[soa]: https://en.wikipedia.org/wiki/AOS_and_SOA

This machinery is built via the `Component` type family:

```haskell
type family Component (s :: StorageType)
                      (c :: ComponentType)
                      (a :: *) :: *
```

Using [`DataKinds`][datakinds], `Component` is parameterized by three types. `s
:: StorageType` describes how the library wants to use this component --
possibly in the "structure-of-arrays" format consumed by the library, or as an
entity structure, to be used by the application programmer. `s` is left
polymorphic when defining the HKD.

The `c :: ComponentType` parameter is used to indicate the *semantics* of the
field; some options include "each entity may or may not have this field" or "at
most one entity may have this field." The former might be used for something
like `position`, while the latter could be `focusedOnByTheCamera`.

Finally, `a :: *` is the actual type you want the field to have.

Having data is a great first step, but it's currently just an opaque blob to the
library. This is where [GHC.Generics][generics] comes in -- given an
(auto-derivable) `Generic` instance for our world, we can use `GHC.Generics`
to automatically further derive more specialized machinery for ourselves.

As an example, assume our world looked like this (absent the `Component`
trickery):

```haskell
data World f = World
  { position :: f (V2 Double)
  , graphics :: f Graphics
  }
```

we can use `GHC.Generics` to automatically generate the equivalent to a
function:

```haskell
getEntity :: Int -> World Data.IntMap.IntMap -> World Maybe
getEntity ent storage =
  World (Data.IntMap.lookup ent $ position storage)
        (Data.IntMap.lookup ent $ graphics storage)
```

which converts from a structure-of-arrays representation to a
structure-of-maybes. The actual technique behind implementing these generic
functions is out of scope for today's topic, but I've [written on it
previously][lenses].

[datakinds]: https://downloads.haskell.org/~ghc/7.8.4/docs/html/users_guide/promotion.html
[generics]: https://www.stackage.org/haddock/lts-11.0/base-4.10.1.0/GHC-Generics.html
[lenses]: /blog/free-lenses/

For its part, `ecstasy` exposes the `SystemT` monad, which at its heart is just
a glorified `Control.Monad.Trans.State.StateT (Int, World 'Storage)`. The `Int`
keeps track of the next ID to give out for a newly created entity.

To a rough approximation, this is all of the interesting stuff inside of
`ecstasy`. So armed with this knowledge, we're ready to tackle some of the
problems that have been unearthed recently.


## Stupid space leaks

My original test for `ecstasy` was a [small platformer][iwmag] -- a genre not
known for the sheer number of entities all interacting at once. As a result,
`ecstasy` performed terribly, but I didn't notice because I hadn't benchmarked
it or actually stress-tested it whatsoever. But that's OK, I wrote it to scratch
an itch while hanging out in a Thai airport; I've never claimed to write
titanium-grade software :)

[iwmag]: https://github.com/isovector/iwmag

But in my RTS, the library was obvious struggling after allocating only 100
dudes. The thing was leaking memory like crazy, which was because I used lazy
state and containers. Oopsie daisies! Replacing `Control.Monad.Trans.State` and
`Data.IntMap` with their strict versions cleared it up.

Honestly I'm not sure why the lazy versions are the default, but I guess that's
the world we live in. **SANDY'S HOT PRO TIPS**: don't use lazy maps or state
unless you've really thought about it.


## Virtual components

While working on my RTS, I realized that I was going to need fast spacial
queries to answer questions like "is there anyone around that I should attack?"
The result was [some sort of Frankenstein bastard child][myquad] of a
[quadtree][quadtree] and a reverse index to answer both "where am I?" and "who's
nearby?"

[myquad]: /blog/free-lenses/
[quadtree]: https://en.wikipedia.org/wiki/Quadtree

This worked well to answer the queries I asked of it, but posed a problem; in
order to maintain its indices, my datastructure needed to be the source of truth
on who was where. Having a `position` component wasn't going to cut it anymore,
since the ECS was no longer responsible for this data. I briefly considered
trying to write a shim to keep the two datasources in sync, but it felt
simultaneously like an ad-hoc hack and a maintenance nightmare, so I gave up and
removed the component.

Unfortunately, all was not well. I added some monadic getters and setters to
help shuffle the position information around, but oh god this became a garbage
fire. Things that were before atomic updates now had extra calls to get and set
the bastard, and everything was miserable.

I realized what I really wanted was the capability for `ecstasy` to be *aware*
of components without necessarily being the *owner* of them. Which is to say,
components whose reads and writes invisibly dispatched out to some other monadic
system.

OK, great, I knew what I wanted. Unfortunately, the implementation was not so
straightforward. The problem was the functions I wanted:

```haskell
vget :: Ent -> m (Maybe a)
vset :: Ent -> Update a -> m ()
```

had this troublesome `m` parameter, and there was no clear place to put it. The
monad to dispatch virtual calls to is a property of the interpretation of the
data (actually running the sucker), not the data itself.

As a result, it wasn't clear where to actually keep the `m` type parameter. For
example, assuming we want `position` to be virtual in our world:

```haskell
data World s = World
  { position :: Component s 'Virtual (V2 Double)
  }
```

Somehow, after unifying `s ~ 'Storage`, we want this to come out as:

```haskell
data World 'Storage = World
  { position :: ( Ent -> m (Maybe (V2 Double)        -- vget
                , Ent -> Update (V2 Double) -> m ()  -- vset
                )
  }
```

But where do we get the `m` from? There's no obvious place.

We could add it as a mandatory parameter on `World`, but that forces an
implementation detail on people who don't need any virtual fields.

We *could* existentialize it, and then `unsafeCoerce` it back, but... well, I
stopped following that line of thought pretty quickly.

My first solution to this problem was to add a `Symbol` to the `Virtual`
component-type token, indicating the "name" of this component, and then using a
typeclass instance to actually connect the two:

```haskell
data World s = World
  { position :: Component s ('Virtual "position") (V2 Double)
  }

-- we put the monad here: `m`
instance VirtualAccess "position" m (V2 Double) where
  vget = ...
  vset = ...
```

While it *worked*, this was obviously a hack and my [inner muse of library
design][deno] was so offended that I spent another few days looking for a better
solution. Thankfully, I came up with one.

[deno]: /blog/follow-the-denotation/

The solution is one I had already skirted around, but failed to notice. This
monad is a property only of the interpretation of the data, which is to say it
really only matters when we're building the world *storage*. Which means we can
do some janky dependency-injection stuff and hide it inside of the storage-type
token.

Which is to say, that given a world of the form:

```haskell
data World s = World
  { position :: Component s 'Virtual (V2 Double)
  }
```

we could just pass in the appropriate monad when instantiating the world for its
storage. Pseudocode:

```haskell
data World (Storage m) = World
  { position :: Component (Storage m) 'Virtual (V2 Double)
  }
```

All of a sudden, the `Component` type family now has access to `m`, and so it
can expand into the `vget`/`vset` pair in a type-safe way. And the best part is
that this is completely invisible to the user who never needs to care about our
clever implementation details.

Spectacular! I updated all of the code generated via `GHC.Generics` to run in
`m` so it could take advantage of this virtual dispatch, and shipped a new
version of `ecstasy`.


## Polymorphic performance woes

While all of this virtual stuff worked, it didn't work particularly quickly. I
noticed some significant regressions in performance in my RTS upon upgrading to
the new version. What was up? I dug in with the profiler and saw that my
`GHC.Generics`-derived code was no longer being inlined. [HKD was performing
more terribly than I thought!][terrible]

[terrible]: /blog/hkd-not-terrible/

All of my `INLINE` pragmas were still intact, so I wasn't super sure what was
going on. I canvassed #ghc on freenode, and the ever-helpful [glguy][glguy] had
this to say:

[glguy]: https://github.com/glguy

> <glguy> generics can't optimize away when that optimization relies on GHC
> applying Monad laws to do it

Oh. Lame. That's why my performance had gone to shit!

I'm not sure if this is true, but my understanding is that the problem is that
my monad was polymorphic, and thus the inliner wasn't getting a chance to fire.
glguy pointed me towards the aptly-named [confusing][confusing] lens combinator,
whose documentation reads:

[confusing]: https://www.stackage.org/haddock/lts-11.9/lens-4.16.1/src/Control.Lens.Traversal.html#confusing

> Fuse a `Traversal` by reassociating all of the `<*>` operations to the left
> and fusing all of the `fmap` calls into one. This is particularly useful when
> constructing a `Traversal` using operations from `GHC.Generics`...
>
> `confusing` exploits the [Yoneda][yoneda] lemma to merge their separate uses
> of `fmap` into a single `fmap` and it further exploits an interesting property
> of the right Kan lift (or [Curried][curried]) to left associate all of the
> uses of `<*>` to make it possible to fuse together more `fmap`s.
>
> This is particularly effective when the choice of functor `f` is unknown at
> compile time or when the `Traversal` in the above description is recursive or
> complex enough to prevent inlining.

[yoneda]: https://www.stackage.org/haddock/lts-11.7/kan-extensions-5.1/Data-Functor-Yoneda.html
[curried]: https://www.stackage.org/haddock/lts-11.7/kan-extensions-5.1/Data-Functor-Day-Curried.html

That sounds *exactly* like the problem I was having, doesn't it? The actual
`confusing` combinator itself was no help in this situation, so I dug in and
looked at its implementation. It essentially lifts your `m`-specific actions
into `Curried (Yoneda m) (Yoneda m)` (don't ask me!), and then lowers it at the
very end. My (shaky) understanding is this:

`Yoneda f` is a functor even when `f` itself is not, which means we have a free
functor instance, which itself means that `fmap` on `Yoneda f` can't just lift
`fmap` from `f`. This is cool if `fmap`ing over `f` is expensive -- `Yoneda`
just fuses all `fmap`s into a single one that gets performed when you lower
yourself out of it. Essentially it's an encoding that reduces an $O(n)$ cost of
doing $n$ `fmap`s down to $O(1)$.

`Curried f f` similarly has a free `Applicative` instance, which, he says
waving his hands furiously, is where the `<*>` improvements come from.

So I did a small amount of work to run all of my `GHC.Generics` code in `Curried
(Yoneda m) (Yoneda m)` rather than in `m` directly, and looked at my perf
graphs. While I was successful in optimizing away my `GHC.Generics` code, I was
also successful in merely pushing all of the time and allocations out of it and
into `Yoneda.fmap`. Curiously, this function isn't marked as `INLINE` which I
suspect is why the inliner is giving up (the isomorphic `Functor` instance for
`Codensity` *is* marked as `INLINE`, so I am *very hesitantly* rallying the
hubris to suggest this is a bug in an Ed Kmett library.)

Despite the fact that I've been saying "we want to run virtual monadic actions,"
throughout this post, I've really meant "we want to run virtual applicative
actions." Which is why I thought I could get away with using `Curried (Yoneda m)
(Yoneda m)` to solve my optimization problems for me.

So instead I turned to [`Codensity`][codensity], which legend tells can
significantly improve the performance of free *monads* by way of the same
mystical category-theoretical encodings. Lo and behold, moving all of my monadic
actions into `Codensity m` was in fact enough to get the inliner running again,
and as a result, getting our HKD once more to be less terrible.

[codensity]: https://www.stackage.org/haddock/lts-11.7/kan-extensions-5.1/Control-Monad-Codensity.html#t:Codensity

If you're curious in how `Codensity` and friends work their magic, glguy pointed
me to a tutorial he wrote [explaining the technique][boggle]. Go give it a read
if you're feeling plucky and adventurous.

[boggle]: https://github.com/glguy/generic-traverse/blob/master/src/Boggle.hs


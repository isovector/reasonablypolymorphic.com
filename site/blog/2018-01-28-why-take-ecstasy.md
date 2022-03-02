---
layout: post
title: Why Take Ecstasy
date: 2018-01-28 11:11
comments: true
tags: haskell, dsl, design, type trickery
---

 [/u/Ahri][ahri] asked on reddit about [yesterday's post][starting],

[ahri]: https://www.reddit.com/user/Ahri
[starting]: http://reasonablypolymorphic.com/blog/starting-a-game-engine

> Perhaps you could explain a little bit about your choice to write [ecstasy][ecstasy]
> rather than to use apecs? I've not used apecs, I'm just interested as I had
> done some limited research into writing games in Haskell and apecs seemed to
> have traction.

[ecstasy]: https://github.com/isovector/ecstasy

That seems like a really good idea, and combined with the fact that I really
haven't published anything about [`ecstasy`][ecstasy] suggested I actually write
about it!


## What is an ECS?

So before diving in, let's take a look at the problem an entity-component-system
(ECS) solves. Let's say we're writing a simple 2D platformer, we'll have dudes
who can run around and jump on platforms.

The way I'd go about writing this before knowing about ECS would be to implement
one feature at a time, generally using the player character to test it as I
went. I write functions that look something like this:

```haskell
moveActor :: Controller -> Actor -> Actor
moveActor ctrl actor =
  actor & actorPos +~ movingDirection ctrl
```

and then provide some types to hold all of the world together:

```haskell
data Universe = Universe
  { _uPlayer       :: Actor
  , _uPlayerCtrl   :: Controller
  , _uCurrentLevel :: Level
  }

data Level = Level
  { _lActors :: [Actor]
  }
```

and finally write some glue code to lift `moveActor` over the universe.

```haskell
updateUniverse :: Universe -> Universe
updateUniverse u@Universe{..} =
  u & uPlayer %~ moveActor _uPlayerCtrl
    & uCurrentLevel . lActors . traverse %~ moveActor someCtrl
```

On the surface this feels good. We've reused the code for `moveActor` for both
the player and any other dudes on the level who might want to walk around. It
feels like we can build up from here, and compose pieces as we go.

Which is true if you're really patient, good at refactoring, or have spent a lot
of time building things like this and know where you're going to run afoul.
Because you're always going to run afoul in software.

The problem with our first attempt at this code is that it codifies a lot of
implicit assumptions about our game. For example, did you notice that it implies
we'll always have an `Actor` for the player? It seems like a reasonable
assumption, but what if you want to play a cut-scene? Or how about if you don't
want to always have control over the player? Maybe you've just been hit by
something big that should exert some acceleration on you, and you don't want to
be able to just press the opposite direction on the control stick to negate it.

All of a sudden, as you try to code for these things, your simple `moveActor`
function takes more and more parameters about the context of the circumstances
in which it's running. And what's worse is that often the rules of how these
behaviors should play out will change depending on whether its the player or
some enemy in the level. We're left with a conundrum -- should we build
ad-hoc infrastructure around the callers of `moveActor` or should we put all of
the logic inside of it?

As you can imagine, it pretty quickly becomes a mess.

In one of the few times I'll praise object-oriented programming, I have to say
that its inheritance-based polymorphism lends itself well to this problem. You
can build more complicated and specific behaviors out of your ancestors'
behaviors. Unfortunately, this approach bucks the OOP best-practice of
"composition over inheritance."

ECS takes what I consider to be the functional-programming-equivalent of this
OOP strategy. It's fundamental stake in the ground is that rather than
representing your universe of game objects as an array-of-structs, you instead
represent it as a struct-of-arrays. Conceptually, this is a cognitive shift that
means instead of looking like this:

```haskell
data GameObject = GameObject
  { position :: V2
  , velocity :: V2
  , graphics :: Picture
  , buffs    :: [Buff]
  , notAffectedByGravity :: Bool
  }

type Universe = [GameObject]
```

you instead model the domain like this:

```haskell
data Universe = Universe
  { position :: Array V2
  , velocity :: Array V2
  , graphics :: Array Picture
  , buffs    :: Array [Buff]
  , notAffectedByGravity :: Array Bool
  }
```

This has some profound repercussions. First of all, notice that we have no
guarantee that our `Array`s are the same length, which implies that not every
`GameObject` need have all of its possible components.

All of a sudden, we can pick and choose which components an entity has.
Entities, now instead of being explicitly modeled by a `GameObject` are
implicitly defined by an `Int` corresponding to their index in all of the
arrays.

From here, we can now write specific, *global* behaviors that should manipulate
the components of an entity. We can avoid a lot of our previous ad-hoc machinery
by essentially running a `map` that performs pattern matching on only the
components we want to care about. For example, we can say that we only want to
draw entities who have both a `position` and a `graphics`. We want to apply
gravity to all entities that have a `velocity`, but *don't* have the
`notAffectedByGravity` flag.


## apecs

*EDIT 2018-01-30*: [The author of apecs has replied to this post][reply]. It's
worth reading through, as it gives a useful perspective from the other side.

[reply]: https://www.reddit.com/r/haskell/comments/7tlwtl/why_and_how_i_wrote_my_own_entity_component_system/dtgzrab/

With an understanding of what ECS brings to the table, we're now ready to take a
look at different ways of implementing such a system. We first turn our
attention to [apecs][apecs].

[apecs]: https://github.com/jonascarpay/apecs

If we wanted to model our above `GameObject` via `apecs`, it might look
something like this:

```haskell
newtype Position = Position (V2 Double)
instance Component Position where
  type Storage Position = Map Position

newtype Velocity = Velocity (V2 Double)
instance Component Velocity where
  type Storage Velocity = Map Velocity

newtype Graphics = Graphics Picture
instance Component Graphics where
  type Storage Graphics = Map Graphics

newtype Buffs = Buffs [Buff]
instance Component Buffs where
  type Storage Buffs = Map Buffs

newtype NotAffectedByGravity = NotAffectedByGravity
instance Flag NotAffectedByGravity where
  flag = NotAffectedByGravity
instance Component NotAffectedByGravity where
  type Storage NotAffectedByGravity = Set NotAffectedByGravity

makeWorld "World"
  [ ''Position
  , ''Velocity
  , ''Graphics
  , ''Buffs
  , ''NotAffectedByGravity
  ]
```

You'll have to admit it's a lot of boilerplate, which in turn would use Template
Haskell to generate something similar to our conceptual `Universe` above:

```haskell
data World = World
  { position :: Array (Maybe Position)
  , velocity :: Array (Maybe Velocity)
  , graphics :: Array (Maybe Graphics)
  , buffs    :: Array (Maybe Buffs)
  , notAffectedByGravity :: Set Int
  }
```

I haven't dug too much into the internals of `apecs`, so this representation
might not be perfect, but it's good enough for us to get an understanding of
what's going on here.

We can now use some of `apecs`' primitives to, for example, transfer our
velocity over to our position:

```haskell
rmap $ \(Position p, Velocity v) -> Position $ p + v
```

This `rmap` function is something I'd describe as "fucking magic." You pass it a
lambda, it inspects the type of the lambda, uses the tuple of its input to
determine which components an entity must have, and then will update the
components of the corresponding output tuple.

At first, this seems like a fine abstraction, but it breaks down pretty quickly
when used in anger. For example, what if you want to run a function over
`Position` that only works if you *don't* have a `Velocity`? Or if you want to
remove a component from an entity? `apecs` can do it, but [good luck finding the
right function][docs]. Do you want `cmap`, `cmapM`, `cmapM_`, `cimapM`,
`cimapM_`, `rmap'`, `rmap`, `wmap`, `wmap'` or `cmap'`? After a week of working
with the library, I still couldn't come up with heads or tails for which
function I needed in any circumstance. I'm sure there's a mnemonic here
somewhere, but I'm not bright enough to figure it out.

[docs]: https://hackage.haskell.org/package/apecs-0.2.4.7/docs/Apecs.html#v:cmap

When you do eventually find the right function, doing anything other than a pure
map from one component to another becomes an exercise in futility and magic
pattern matching. There's this thing called `Safe` you sometimes need to pattern
match over, or produce, and it roughly corresponds to when you're not guaranteed
to have all of the components you asked for.

There are several other gotchas, too. For example, you can construct an entity
by providing a tuple of the components you want to set. Unfortunately, due to
`apecs`' design, this thing *must be type-safe.* Which means you can't construct
one based on runtime data if you're loading the particular components from e.g.
a level editor. Well, you can, if you're willing to play "existentialize the
dictionary" and learn enough of the underlying library (and quirks of Haskell's
type inference algorithm) in order to convince the compiler what you're doing is
sound.

One final gotcha I'll mention is that this magic tuple stuff is provided through
typeclasses which are generated for the library by template haskell. Out of the
box, you only get support for 5-tuples, which means you can't easily construct
entities with more components than that. Furthermore, changing the TH to
generate more results in exponential growth of your compile times.

None of this is to say that `apecs` is bad software. It's actually pretty
brilliant in terms of its technology; I just feel as though its execution is
lacking. It depends on a lot of tricks that I wouldn't consider to be idiomatic
Haskell, and its usability suffers as a consequence.


## Ecstasy

So with all of the above frustrations in mind, and a lot of time to kill in a
Thai airport, I felt like I could make a better ECS. Better is obviously
subjective for things like this, but I wanted to optimize it for being used by
humans.

My explicit desiderata were:

1) Keep boilerplate to a minimum.
2) The user shouldn't ever bump into any magic.

I think [`ecstasy`][ecstasy] knocks it out of the park on both of these fronts.
Before diving into how it all works, let's take a peek at how it's used. We can
define our components like so:

```haskell
data EntWorld f = Entity
  { position :: Component f 'Field V2
  , velocity :: Component f 'Field V2
  , graphics :: Component f 'Field Picture
  , buffs    :: Component f 'Field [Buff]
  , notAffectedByGravity :: Component f 'Field ()
  } deriving (Generic)

type Entity = EntWorld 'FieldOf
```

That's it! No template haskell, no typeclasses, no nothing. You get everything
for free just out of this one `deriving Generic` statement. We'll talk about how
it works in just a second.

We can implement the velocity/position behavior as follows:

```haskell
emap $ do
  p <- get position
  v <- get velocity
  pure defEnt'
    { position = Set $ p + v
    }
```

Ecstasy clearly wins on minimizing the definition-side of boilerplate, but it
seems like we've gained some when we actually go to use these things. This is
true, but what we buy for that price is flexibility. In fact, `emap` is powerful
enough to set, unset and keep components, as well as branch on whether or not a
component is actually there. Compare this to the ten functions with different
signatures and semantics that you need to keep in mind when working with
`apecs`, and it feels like more of a win than the syntax feels like a loss.

So the question I'm sure you're wondering is "how does any of this work?" And
it's a good question. Part of the reason I wrote this library was to get a feel
for the approach and for working with [GHC.Generics][generics].

[generics]:

The idea comes from my colleague [Travis Athougies][travis] and his
mind-meltingly cool library [`beam`][beam]. The trick is to get the library user
to define one semantic type that makes sense in their domain, and then to use
tricky type system extensions in order to corral it into everything you need.
`beam` uses this approach to model database tables; `ecstasy` uses it to provide
both a struct-of-arrays for your components, as well as just a struct
corresponding to a single entity.

[travis]: http://travis.athougies.net/
[beam]: https://github.com/tathougies/beam

As you'd expect, the sorcery is inside of the `Component` type family. We can
look at its definition:

```haskell
type family Component (s :: StorageType)
                      (c :: ComponentType)
                      (a :: *) :: * where
  Component 'FieldOf  c      a = Maybe a
  Component 'SetterOf c      a = Update a

  Component 'WorldOf 'Field  a = IntMap a
  Component 'WorldOf 'Unique a = Maybe (Int, a)
```

This `Component` thing spits out different types depending on if you want a
record for the entity (`'FieldOf`), an updater to change which components an
entity has (`'SetterOf`), or the actual universe container to hold all of this
stuff (`'WorldOf`). If we're building an entity record, every component is a
`Maybe`. If we're describing a change to an entity, we use `data Update a = Set
a | Unset | Keep`. If we want a place to store all of our entities, we generate
an `IntMap` for every `'Field`. There's also support for adding components that
are uniquely owned by a single entity, but we won't get into that today.

The trick here is that we get the user to fill in the `c :: ComponentType` when
they define the components, and ask them to keep the `s :: StorageType`
polymorphic. The library then can instantiate your `EntWorld f` with different
`StorageType`s in order to pull out the necessary types for actually plumbing
everything together.

We use the `Generic` derivation on `EntWorld` in order to allow ourselves to
construct the underlying machinery. For example, when you're defining an entity,
you don't want to be able to `Keep` the old value of its components, since it
didn't have any to begin with. We can use our `Generic` constraint in order to
generate a function `toSetter :: EntWorld 'FieldOf -> EntWorld 'SetterOf` which
takes an entity record and turns it into an entity update request, so that we
don't actually need special logic to construct things. The `Generic` constraint
also helps generate default values of the `EntWorld 'WorldOf` and other things,
so that you don't need to write out any boilerplate at the value level in order
to use these things.

The actual how-to-do of the `GHC.Generics` is outside of the scope of today's
post, but you can [read through the source code][src] if you're curious.

[src]: https://github.com/isovector/ecstasy/blob/c59109ec38c9b440a6aacfa0d6540adb9ed8df00/src/Data/Ecstasy/Deriving.hs


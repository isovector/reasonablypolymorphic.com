---
layout: post
title: "FRP in Yampa: Part 4: Routing"
date: 2023-12-26 16:03
comments: true
tags: FRP, yampa, haskell, technical, programming, gamedev
---

In the [last post](/blog/yampa-switching/), we investigated the `switch`
combinator, and saw how it can give us the ability to work with "state
machine"-sorts of things in our functionally reactive programs.

Today we turn our attention towards game objects---that is, independently
operating entities inside of the game, capable of behaving on their own and
communicating with one another. I originally learned of this technique from the
paper [The Yampa Arcade](https://www.antonycourtney.com/pubs/hw03.pdf), but
haven't looked at it in a few years, so any shortcomings here are my own.

Nevertheless, the material presented here does in fact work---I've actually
[shipped a game](https://github.com/isovector/ld52/releases/tag/publish) using
this exact technique!


## Game Objects

Before we dive into the Yampa, it's worth taking some time to think about what
it is we're actually trying to accomplish. There are a series of constraints
necessary to get everything working, and we'll learn a lot about the problem
domain by solving those constraints simultaneously.

The problem: we'd like several `Object`s running around, which we'd like to
program independently, but which behave compositionally. There are going to be a
lot of moving pieces here---not only in our game, but also in our solution---so
let's take a moment to define a type synonym for ourselves:

```haskell
type Object = SF ObjectInput ObjectOutput
```

Of course, we haven't yet defined `ObjectInput` or `ObjectOutput`, but that's
OK! They will be subject to a boatload of constraints, so we'll sort them out as
we go. At the very least, we will need the ability for an `Object` to render
itself, so we can add a `Render` field:

```haskell
data ObjectOutput = ObjectOutput
  { oo_render :: Render
  , ...
  }
```

We would like `Object`s to be able to interact with one another. The usual
functional approach to this problem is to use message passing---that is,
`Object`s can send values of some message type to one another. Those messages
could be things like "I shot you!" or "teleport to me," or any sort of crazy
game-specific behavior you'd like.

In order to do this, we'll need some sort of `Name` for each `Object`. The exact
structure of this type depends on your game. For the purposes of this post we'll
leave the thing abstract:

```haskell
data Name = ...
```

We'll also need a `Message` type, which again we leave abstract:

```haskell
data Message = ...
```

Sending messages is clearly an *output* of the `Object`, so we will add them to
`ObjectOutput`:

```haskell
data ObjectOutput = ObjectOutput
  { oo_render :: Render
  , oo_outbox :: [(Name, Message)]
  , ...
  }
```

There are actions we'd like to perform in the world which are not messages we
want to send to anyone; particularly things like "kill my `Object`" or "start
a new `Object`." These two are particularly important, but you could imagine
updating global game state or something else here.

```haskel
data Command
  = Die
  | Spawn Name ObjectState Object
  | ...
```

Commands are also outputs:

```haskell
data ObjectOutput = ObjectOutput
  { oo_render   :: Render
  , oo_outbox   :: [(Name, Message)]
  , oo_commands :: [Command]
  , ...
  }
```

Finally, it's often helpful to have some common pieces of state that belong to
all `Object`s---things like their current position, and hot boxes, and anything
else that might make sense to track in your game. We'll leave this abstract:

```haskell
data ObjecState = ...

data ObjectOutput = ObjectOutput
  { oo_render   :: Render
  , oo_outbox   :: [(Name, Message)]
  , oo_commands :: [Command]
  , oo_state    :: ObjectState
  }
```

Let's turn our attention now to the input side. It's pretty clear we're going to
want incoming messages, and our current state:

```haskell
data ObjectInput = ObjectInput
  { oi_inbox :: [(Name, Message)]
  , oi_state :: ObjectState
  }
```

What's more interesting, however, than knowing our own state is knowing
everyone's state. Once we have that, we can re-derive `oi_state` if we know our
own `Name`. Thus, instead:

```haskell
data ObjectInput = ObjectInput
  { oi_inbox    :: [(Name, Message)]
  , oi_me       :: Name
  , oi_everyone :: Map Name ObjectState
  }

oi_state :: ObjectInput -> ObjectState
oi_state oi
    = fromMaybe (error "impossible!")
    $ Data.Map.lookup (oi_me oi)
    $ oi_everyone oi
```


## Parallel Switching

Armed with our input and output types, we need now figure out how to implement
any of this. The relevant combinator is Yampa's `pSwitch`, with the ridiculous
type:

```haskell
pSwitch
  :: Functor col
  => (forall sf. gi -> col sf -> col (li, sf))
  -> col (SF li o)
  -> SF (gi, col o) (Event e)
  -> (col (SF li o) -> e -> SF gi (col o))
  -> SF gi (col o)
```

Yes, there are five type variables here (six, if you include the rank-2 type.)
In order, they are:

1. `col`: the data structure we'd like to store everything in
2. `gi`: the *global* input, fed to the eventual signal
3. `li`: the *local* input, fed to each object
4. `o`: the output of each object signal
5. `e`: the type we will use to articulate desired changes to the world

Big scary types like these are an excellent opportunity to turn on
`-XTypeApplications`, and explicitly fill out the type parameters. From our work
earlier, we know the types of `li` and `o`---they ought to be `ObjectInput` and
`ObjectOutput`:

```haskell
pSwitch @_
        @_
        @ObjectInput
        @ObjectOutput
        @_
  :: Functor col
  => (forall sf. gi -> col sf -> col (ObjectInput, sf))
  -> col (SF ObjectInput ObjectOutput)
  -> SF (gi, col ObjectOutput) (Event e)
  -> (col (SF ObjectInput ObjectOutput) -> e -> SF gi (col ObjectOutput))
  -> SF gi (col ObjectOutput)
```

It's a little clearer what's going on here. We can split it up by its four
parameters:

1. The first (value) parameter is this rank-2 function which is responsible for
   splitting the global input into a local input for each object.
2. The second parameter is the collection of starting objects.
3. The third parameter extracts the desired changes from the collection of outputs
4. The final parameter applies the desired changes, resulting in a new signal of
   collections.

We are left with a few decisions, the big ones are: what should `col` be, and
what should `e` be? My answer for the first is:

```haskell
data ObjectMap a = ObjectMap
  { om_objects  :: Map Name (ObjectState, a)
  , om_messages :: MonoidalMap Name [(Name, Message)]
  }
  deriving stock Functor
```

which not only conveniently associates names with their corresponding objects
and states, but also keeps track of the messages which haven't yet been
delivered. We'll investigate this further momentarily.

For maximum switching power, we can therefore make our event type be `ObjectMap
Object -> ObjectMap Object`. Filling all the types in, we get:

```haskell
pSwitch @ObjectMap
        @_
        @ObjectInput
        @ObjectOutput
        @(ObjectMap Object -> ObjectMap Object)
  :: (forall sf. gi -> ObjectMap sf -> ObjectMap (ObjectInput, sf))
  -> ObjectMap Object
  -> SF (gi, ObjectMap ObjectOutput)
        (Event (ObjectMap Object -> ObjectMap Object))
  -> ( ObjectMap Object
    -> (ObjectMap Object -> ObjectMap Object)
    -> SF gi (ObjectMap ObjectOutput)
     )
  -> SF gi (ObjectMap ObjectOutput)
```

which is something that feels almost reasonable. Let's write a function that
calls `pSwitch` at these types. Thankfully, we can immediately fill in two of
these parameters:

```haskell
router
    :: ObjectMap Object
    -> SF gi (ObjectMap ObjectOutput)
router objs =
  pSwitch @ObjectMap
          @_
          @ObjectInput
          @ObjectOutput
          @(ObjectMap Object -> ObjectMap Object)
    _
    objs
    _
    (\om f -> router' $ (f om) { om_messages = mempty })
```

We are left with two holes: one which constructs `ObjectInput`s, the other which
destructs `ObjectOutput`s. The first is simple enough:

```haskell
routeInput :: gi -> ObjectMap sf -> ObjectMap (ObjectInput, sf)
routeInput gi om@(ObjectMap objs msgs) = om
  { om_objects = flip Data.Map.mapWithKey objs $ \name (_, sf) ->
      (, sf) $ ObjectInput
        { oi_inbox    = fromMaybe mempty $ Data.MonoidalMap.lookup name msgs
        , oi_me       = name
        , oi_everyone = fmap fst objs
        }
  }
```

Writing `decodeOutput` is a little more work---we need to accumulate every
change that `ObjectOutput` might want to enact:

```haskell
decodeOutput :: Name -> ObjectOutput -> Endo (ObjectMap Object)
decodeOutput from (ObjectOutput _ msgs cmds _) = mconcat
  [ flip foldMap msgs $ uncurry $ send from
  , flip foldMap cmds $ decodeCommand from
  ]

send :: Name -> Name -> Message -> Endo (ObjectMap Object)
send from to msg
  = Endo $ #om_messages <>~ Data.MonoidalMap.singleton to [(from, msg)]

decodeCommand :: Name -> Command -> Endo (ObjectMap Object)
decodeCommand _ (Spawn name st obj)
  = Endo $ #om_objects . at name ?~ (st, obj)
decodeCommand who Die
  = Endo $ #om_objects %~ Data.Map.delete who
```

There's quite a lot going on here. Rather than dealing with `ObjectMap Object ->
ObjectMap Object` directly, we instead work with `Endo (ObjectMap Object)` which
gives us a nice monoid for combining endomorphisms. Then by exploiting `mconcat`
and `foldMap`, we can split up all of the work of building the total
transformation into pieces. Then `send` handles sending a message from one
object to another, while also `decodeCommand` transforms each `Command` into an
endomap.

We can tie everything together:

```haskell
router
    :: ObjectMap Object
    -> SF gi (ObjectMap ObjectOutput)
router objs =
  pSwitch @ObjectMap
          @_
          @ObjectInput
          @ObjectOutput
          @(ObjectMap Object -> ObjectMap Object)
    routeInput
    objs
    (arr $ Event
         . appEndo
         . foldMap (uncurry decodeOutput)
         . Data.Map.assocs
         . om_objects
         . snd
         )
    (\om f -> router' $ (f om) { om_messages = mempty })
```

Notice that we've again done the monoid trick to run `decodeOutput` on every
output in the `ObjectMap`. If you're not already on the monoid bandwagon,
hopefully this point will help to change your mind about that!

So our router is finally done! Except not quite. For some reason I don't
understand, `pSwitch` is capable of *immediately* switching if the `Event` you
generate for `decodeOutput` immediately fires. This makes sense, but means Yampa
will happily get itself into an infinite loop. The solution is to delay the
event by an infinitesimal amount:

```haskell
router
    :: ObjectMap Object
    -> SF gi (ObjectMap ObjectOutput)
router objs =
  pSwitch @ObjectMap
          @_
          @ObjectInput
          @ObjectOutput
          @(ObjectMap Object -> ObjectMap Object)
    routeInput
    objs
    ((arr $ Event
         . appEndo
         . foldMap (uncurry decodeOutput)
         . Data.Map.assocs
         . om_objects
         . snd
         ) >>> notYet)
    (\om f -> router' $ (f om) { om_messages = mempty })
```

There's probably a more elegant solution to this problem, and if you know it,
please do get in touch!


## Wrapping Up

Today we saw how to use the `pSwitch` combinator in order to build a router
capable of managing independent objects, implementing message passing between
them in the process.

You should now have enough knowledge of Yampa to get real tasks done, although
if I'm feeling inspired, I might write one more post on integrating a Yampa
stream into your `main` function, and doing all the annoying boilerplate like
setting up a game window. Maybe! Watch this space for updates!


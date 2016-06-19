---
layout: post
title: Towards Procedurally Generated Stories via Free Monads
date: 2016-06-02 01:34
comments: true
tags: haskell, dsl, rpg
---

> Strongly inspired by Dave Laing's fantastic series [Cofun with cofree
comonads][cofun]. This post and the next are mostly rehashes of (superior) blog
posts of his, but there is novel material to be covered soon.

I am eternally torn between a dichotomy I like to call "finish shit vs. solve
cool problems." Finishing shit requires a lot of polish around the boring
corners of a project, after all the cool stuff has been solved -- and there's
always another cool problem waiting to be solved.

In particular, this dichotomy has recently manifested itself as "I should make
an RPG vs. I already know how to make RPGs, it'd be fun creatively but gee that
sounds like a lot of tedium and wouldn't teach me much in the end, except for
maybe the value of hard work."

![](/images/rpg.jpg "I should make an RPG")

Then I realized making an RPG doesn't need to be tedious and boring. I'll just
teach a computer how to generate an RPG. Goldmine genius idea. I don't know how
to make a procedurally generated RPG, but really, how hard could it be?

This post is the first of many on just how hard it can be.


## The Motivation

People have been making [roguelikes][roguelikes] for decades. While roguelikes
are spectacularly cool, they're not really RPGs in the more common sense of the
word. There's no narrative to a roguelike, you just adventure around and kill
shit.

The RPG that inspired me to make an RPG was [Earthbound][earthbound], which is
known for its quirky atmosphere and for managing to pull of some sort of
weird-humorous-plot-mixed-with-lovecraftian-horror juxtaposition. Earthbound
*feels* like it might have been made on drugs, but somehow manages to still be a
fantastic experience.

*This* is the kind of thing I want to generate. Lots of games have tried to
generate interesting worlds and plots, but, at least when I was in the games
industry, the state of the art was prefabricating modules and stitching them
together. Sure, it's hard to generate solid plots, but I don't think its
intractable.

I think the problem might have been this: this problem is fundamentally
functional; any imperative approach is going to be a Bad time.

Maybe. Lots of this is vaporware still, but it *feels* right, and I have a
plausible path to actually executing on it.


## The Idea

Enough run-around. Are you ready to hear my revolutionary idea to generate
procedural RPGs with coherent and interesting stories?

1) Build a datastructure representing a story.
2) Turn this datastructure into a game.

Amazing, right?

Okay, not that amazing, but here's the rub. Instead of building this
datastructure by hand, we'll write a domain specific language (DSL) which will
generate the datastructure for us. And then if we then embed this language into
Haskell, we'll lift all of the expressiveness of Haskell into our DSL. If we
limit the DSL to a few number of primitive operations, and implement all of the
interesting pieces as combinators on top, it will be easy to abstract over, and
more importantly, to interpret.

This interpretation step is, unsurprisingly, where the "magic" happens.

Separating the *structure* of what we want to do (which is what the DSL provides
us) from *how* we do it means we can do different things with the same data. For
example, given a basic plot skeleton, we can run over it, and with the help of a
random number generator, determine a theme. Then, given the theme and the plot
skeleton, build necessary locations to help advance the plot from one scene to
the next. Then, with all of this, we can build intermediate landscapes to stitch
the locations together. And so on and so forth.

There are lots of potential failure modes here, but the approach seems feasible.


## The Pieces

So I went through a bunch of games whose stories I adore, and I attempted to
deconstruct them into their primitive operations. A simplified datastructure of
what I came up with is provided here:

```haskell
type Story = [StoryPrim]

data StoryPrim = Change Character ChangeType
               | Interrupt Story Story

data ChangeType = Introduce
                | Die
                | Leave
                | Arrive Location
                | Kill Character
                | Learn ChangeResult

data ChangeResult = ChangeResult Character ChangeType
```

which is to say, a `Story` is a list of `StoryPrim`s, which is either a change
in character state, or one `Story` being interrupted by another (eg. if
someone's murder attempt is foiled by an unexpected arrival.)

This isn't comprehensive enough to generate entire stories, but it's definitely
good enough to motivate the remainder of this post.


## Free Monads

Let's take a little break and talk some math.

Free monads are one of the neatest things I've learned about recently. The
definition (in Haskell) of a free monad over a functor `f` is this:

```haskell
data Free f a = Pure a
              | Bind (f (Free f a))
```

Which can be thought of a recursive datastructure which bottoms out with a
`Pure` or recurses with an `Bind`. The definition was hard for me to work my
head around, so let's give it a concrete functor and see what pops out:

```haskell
data Free [] a = Pure a
               | Bind [Free [] a]
```

If we squint, this is actually just a tree where `Bind` is a $n$-ary branch,
and `Pure` is a value at a leaf. So a tree is just a special case of the free
monad. That's kinda hot, if you're as into this stuff as much as I am.

But what's more hot is that given any `instance Functor f`, `Free f` forms a
monad:

```haskell
instance Functor f => Monad (Free f) where
  return a = Pure a
  Pure a >>= f = f a
  Bind m >>= f = Bind (fmap (>>= f) m)
```

It's probably the dumbest `Monad` instance imaginable, but hey, it adheres to
the monad laws, and that's really all we ask for. The laws are satisfied only in
a very trivial sense, in that all we've done here is encode the rules of
`return` and `(>>=)` into our datastructure which is to say, we haven't done any
processing yet. We'll return to this in a moment.

It's called "free" for exactly this reason of trivially satisfying the laws --
given any functor `f` we can get an (admittedly stupid) monad over `f` for free.

Because our free monad is just a datastructure in the exact shape of a
computation we *would* want to carry out over its contents, it's easy to write
an interpreter for it. Or several.

See where I'm going with this?

Here's the kicker: **Free monads turn out to be the abstraction behind DSLs
because they encode the *structure* of a computation, without imposing an
*interpretation* over it.**

But remember, getting a free monad requires having a functor. If we can find a
means of encoding our `Story` grammar above as a functor, we can lift it into a
DSL via `Free`.


## The Command Functor

So we need a means of getting a `Functor` instance for our `Story` type
described above. But how?

Let's start playing madlibs with what we know.

```haskell
type Story a = Free StoryF a

data StoryF a = -- ???
```

Looking at the definition of `Free` specialized over our functor `StoryF` once
again hints us in the right direction:

```haskell
data Story a = Pure a
             | Bind (StoryF (Story a))
```

The polymorphic variable of our `StoryF` functor is only ever going to be a
`Story a`, which is to say a pure `a` or a bind computing more of the
final value.

So our polymorphic type variable is the type of the continuing computation.
Because `Pure` from `Free` takes care of how computations terminate, our functor
should always have a continuing computation. Voila:

```haskell
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | Interrupt (Story ()) (Story ()) a
```

contrasting this against our old `StoryPrim`, we've just added a new product
involving `a` to all each of our sum terms. Again, `a` should be considered to
be the type of the continuing computation.

But what's this funny `ChangeResult -> a` thing? Well, recall that we wanted a
`Change` to return a `ChangeResult` indicating what changed, which is to say
this result should be a *parameter* to the rest of the computation -- thus our
function type[^1].

[^1]: If this isn't immediately evident to you, [make sure you
understand][do-sugar] how `do` desugaring works.

`StoryF` is what's known as our command functor, because as we will see, its
constructors will eventually act as commands in our DSL.

But wait! Not so fast. We haven't yet provided a `Functor` instance for
`StoryF`. It's trivial, but we present it here for completeness:

```haskell
instance Functor StoryF where
    fmap f (Change c ct k)    = Change c ct (f . k)
    fmap f (Interrupt s s' k) = Interrupt s s' (f k)
```

And so `StoryF` is now a `Functor`, which means that `Free StoryF` is a `Monad`,
which means that we can use `do` notation inside of it! We're most of the way
to our DSL!

All that's left is to lift our `StoryF` data constructors into `Story`
constructors. The details of this are a little messy, but luckily `liftF` from
the `free` package does most of the manual labor for us.

```haskell
change :: Character -> ChangeType -> Story ChangeResult
change c ct = liftF $ Change c ct id

interrupt :: Story () -> Story () -> Story ()
interrupt s s' = liftF $ Interrupt s s' ()
```

and that's it! Short of some helpful combinators, we're done! We can now write
basic stories in Haskell using `do` notation!

```haskell
myStory :: Story Int
myStory = do
    let mandalf = Character "Mandalf the Wizard"
        orcLord = Character "Orclord Lord of the Orcs"
        orcBaby = Character "Orclord's Child"

    sadness <- kill mandalf orcLord
    change orcBaby $ Learn sadness

    return 5

die :: Character -> Story ChangeResult
die who = change who Die

kill :: Character -> Character -> Story ChangeResult
kill who whom = change who (Kill whom) <* die whom
```

As far as stories go, one about a child learning of its father's death is
probably not going to win any feel-good-novella-of-the-year, but the example
serves to showcase several things:

* We can build abstractions with standard Haskell combinators (eg. killing
    someone implies that they die.)
* The fact that this typechecks shows that our language is expressive enough for
    characters to learn of the arbitrary actions of one another (including
    learning that they've learned something.) Furthermore, knowledge is
    first-class and can be passed around the story however we see fit.
* Like all monads, our DSL can describe things that happen *while* returning
    potentially unrelated data. The $5$ above is meaningless, but allows us to
    interleave story descriptions with arbitrary computations.

This seems like a good place to stop for today -- we've covered a lot of ground.
Next time we'll discuss how we can use cofree comonads (I am *not* kidding here)
to build an interpreter for our DSL.

[cofun]: http://dlaing.org/cofun/
[roguelikes]: https://en.wikipedia.org/wiki/Roguelike
[earthbound]: https://en.wikipedia.org/wiki/EarthBound
[do-sugar]: https://en.wikibooks.org/wiki/Haskell/do_notation#Translating_the_bind_operator


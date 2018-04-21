---
layout: post
title: An Existential Crisis
date: 2016-07-15 22:51
comments: true
tags: haskell, existentials, rpg, dsl, semantics
---

We're slowly making progress towards being able to procedurally generate
stories. [Last time][coiter] around we built our first comonad, and could thus
provide our first interpretation of a `Story`. Success!

[coiter]: http://reasonablypolymorphic.com/blog/coiter


## Weeds in the Abstraction Garden

Unfortunately, not all is blissful in this glorious garden of abstraction we've
cultivated for ourselves. Something rotten is afoot. Brace yourself for the
horror: our semantics are bad.

Recall the definition of our command functor:

```haskell
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | Interrupt (Story ()) (Story ()) a
```

So what's the problem? Well, if you think about how we'll use `Interrupt`, we've
broken an important principle: everything is an expression. The semantics we had
for `Interrupt` was that the first `Story ()` was interrupted at some point with
the second `Story ()`, and once that was finished, the `a` would continue.

Given these semantics, the second `Story ()` runs in the same "line of reality"
as `a`. However, the fact that our interrupting story returns `()` means it can
never pass any information along to the continued computation. We've
accidentally implemented a black hole of knowledge in our story system.

How? Let's see:

```haskell
story :: Story ()
story = do
    interrupt (leave charlie) $ do
        deathOfCharlie <- die charlie
        return () -- mandated by our `Story ()` type
```

This is a sad story, about how while attempting to leave, Charlie dies. However,
nobody can ever learn about this, and it can never affect the rest of the story,
since the value `deathOfCharlie` can never escape the scope of the `interrupt`
block.

While it's certainly *different* storytelling, it's not very *good*
storytelling. A story about random things happening which don't affect the rest
of the plot is kind of what we'd expect a procedurally generated story to look
like, but I think we can do better. [Sometimes this kind of storytelling can be
successful][room], but it's usually not.

[room]: https://en.wikipedia.org/wiki/The_Room_(film)


## That Which Exists Without My Knowledge

So what's the solution? Well, in the same way that the `Change` constructor
creates a `ChangeResult` and passes it to the remainder of the computation, our
`Interrupt` should create a `y` (the result of the interrupting story), and pass
*it* on to the remainder of the computation.

But `x` can vary! And `StoryF` is recursive! But `x` can vary between layers of
`StoryF`s. Clearly[^1] `x` is unreasonably polymorphic for us to be able to pin
down as a type parameter to `StoryF`. So what ever can we do?

[^1]: To be honest, I'm not certain of this, but I've spent some time thinking
about it and haven't yet come up with a way of doing it.

Existential quantification to the rescue! If you're unfamiliar with this, it's
essentially having an instance of an interface in more traditional OOP
languages. We have some type `x`, but we don't know anything about it, and the
only thing we can do with it is shuffle it around, desperately hoping someone
down the line has a function that works over *any* type.

Let's make it happen:

```haskell
{-# LANGUAGE ExistentialQuantification #-}
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | forall x y. Interrupt (Story x) (Story y) (y -> a)
```

The `forall x y` syntax introduces two type variables `x` and `y` which are
existential -- they're in scope but we can never know what they are. Our two
stories can now vary over any types, and the continuation of our program takes
the result of the latter story.

This gives us our desired semantics; all that's left is to make it typecheck.
There's a fair amount of plumbing to do, but slow and steady wins the race.


## Mechanical Exist-fixing

We update our `CoStoryF` to also handle existentials:

```haskell
data CoStoryF b = CoStoryF
                { changeH    :: Character -> ChangeType -> (ChangeResult, b)
                , interruptH :: forall x y. Story x -> Story y -> (y, b)
                }
```

And we need to pin an additional `fmap` into our iniquitous mess of `CoStoryF`'s
`Functor` instance:

```haskell
instance Functor CoStoryF where
    fmap f (CoStoryF c i) = CoStoryF
        ((fmap . fmap . fmap) f c)
        ((fmap . fmap . fmap) f i)
```

along with the `Zap` instance to `zap` the our resulting `y` into our `StoryF`'s
`y -> a`:

```haskell
instance Zap StoryF CoStoryF where
    zap f (Change    c ct k) (CoStoryF h _) = zap f k (h c ct)
    zap f (Interrupt x y  k) (CoStoryF _ h) = zap f k (h x y)
```

Success! Everything compiles! So it must work, right? This suspicious rhetorical
question turns out to actually be misleading -- everything actually *does* work.
This is Haskell, after all.


## A Good Story Is Always Ranked(N)

However, it's now significantly harder to construct `CoStory b`s. Before, our
interrupted stories couldn't actually ever change anything, so we didn't need to
interpret them. That approach no longer holds water, so we need to find a way of
letting a `CoStory` be implemented in terms of itself.

Recall that we previously constructed our `CoStory b` out of a few values:

* `start :: b`
* `handleChange :: b -> Character -> ChangeType -> (ChangeResult, b)`
* `handleInterrupt :: b -> Story () -> Story () -> b`

That `handleInterrupt` is no longer going to fly. Let's update it to our new
semantics and try again:

```haskell
handleInterrupt :: b -> Story x -> Story y -> (y, b)
```

Good! But we have no means of interpreting `Story y` in order to get the `y` of
our resulting pair. Fortunately, we do have a means of interpreting `Story`s:
`interpret :: Story a -> CoStory b -> (a, b)`. We'll want to fix the `CoStory b`
to be the one we're currently defining, so that you can't accidentally change
your interpretation strategy half way through.

```haskell
{-# LANGUAGE RankNTypes #-}
handleInterrupt :: (forall a. Story a -> (a, b))
                -> b
                -> Story x
                -> Story y
                -> (y, b)
```

What's this `forall a.` stuff? Well, without it, our type variable `a` will get
bound the first time we interpreted a story, which would be to either `x` or to
`y`. Once this is the case, we'd be unable to interpret the *other* story.
Annotating our interpretation function parameter here forces Haskell to hold off
binding that type variable: instead of working *on some* type `a`, it must work
`forall a`. Get it?

With all the pieces in place, we're ready to write our helper function. Prepare
yourself for the most horrifying type signature I've ever written:

```haskell
mkCoStory :: b
          -> (b -> Character -> ChangeType -> (ChangeResult, b))
          -> (forall x y . (forall a. Story a -> (a, b))
                        -> b
                        -> Story x
                        -> Story y
                        -> (y, b))
          -> CoStory b
```

Don't panic! In a second, you'll recognize this is just the combination of
`start`, `handleChange` and `handleInterrupt` mashed into a single function.
You'll notice we also had to mark our `x` and `y` type variables as being
`forall`, since our `handleInterrupt` function mustn't be bound to the first `x`
and `y`s it finds.

The implementation is worth working your way through to see how it works:

```haskell
mkCoStory start changeH interruptH =
    fix $ \self -> coiter (next (flip interpret self)) start
  where
    next run b =
        CoStoryF
            (changeH b)
            (interruptH (unsafeCoerce run) b)
```

It's not as lovely as I'd like. In particular, there's that `unsafeCoerce` in
there which tricks the compiler into forgetting that our "never can be known"
type `y` is exiting the `forall y` scope that defines it. This is safe because
we're only forgetting that it's existential for a second -- immediately after we
feed it back into an existential of the same type (we've just moved between the
`Story y` and the `y -> a` in `forall x y. Interrupt (Story x) (Story y) (y ->
a)`). That's all true, but it still makes me nervous.

I'd love to know if you can come up with a better solution, but in the meantime,
this works well enough.


## Roll Call!

With the help of `mkCoStory`, we're now able to write a `CoStory` which computes
all of the characters referenced in a `Story` -- even if they're only
hypothetical:

```haskell
getCharacters :: CoStory (Set Character)
getCharacters = mkCoStory S.empty changeH interruptH
  where
    changeH b c ct = (ChangeResult c ct, S.insert c b)
    interruptH
        (run :: forall a. Story a -> (a, Set Character))
        b x y = ( fst (run y)
                , mconcat [b, snd (run x), snd (run y)]
                )
```

`getCharacters` collects referenced characters by keeping track of who
changes, and recursing into interrupted branches.

The explicit type signature of `run` is unfortunate but necessary --
`RankNTypes` breaks Hindley-Milner type inference, so we need to tell Haskell
what we're doing.

So we've successfully cleaned up our semantics, and enforced that our
interpretation of a `Story` is internally consistent. However, there's still
room for error -- we haven't enforced that all interpretations of a `Story`
produce the same `ChangeResult` tokens. Since subsequent code can branch on
their contents, this is a problem just waiting to happen, and we'll fix it next
time.


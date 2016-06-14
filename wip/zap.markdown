---
layout: post
title: zap
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

Last time around, we discussed [duality and cofree comonads][cofree] towards our
quest in generating rich stories. I promised that comonads were the abstraction
and machinery behind interpreters, but I have yet to prove that. Let's do it
today.

## The Mmand Functor

[Two posts ago][free], we created a "command functor" whose job it was to
specify the specific commands possible in our DSL:

```haskell
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | Interrupt (Story ()) (Story ()) a

type Story a = Free StoryF a
```

Recall, this should be understood as "a story is built out of primitives where
characters can change, or of one story interrupted by another." The polymorphic
`a` is "the type of the next piece of the computation," and so the conspicuous
`(ChangeResult -> a)` argument to the `Change` data constructor is "the
remainder of the computation will be given a `ChangeResult`" or perhaps more
naturally, "the `Change` command returns a `ChangeResult`."

If you've been following along with my talk on duality, you'll probably suspect
that we'll need a co-command functor to go with our cofree comonad. But since
duality is a symmetric operation, two 'co-'s cancel out, and we're just left
with a "mmand functor." I'm sorry, I couldn't resist. It's not even going to
turn out to be a dual, but the pun was just too good. Whatever.

Let's look at why. Naively swapping our sums and products decidedly leads us in
the path of madness:

```haskell
-- 100% confirmed for crazy
data CoChange a = ChangeCharacter Character
                | ChangeChangeType ChangeType
                | ChangeChangeResult (ChangeResult -> a)
data CoInterrupt a = InterruptInterruptedStory (Story ())
                   | InterruptInterruptingStory (Story ())
                   | InterruptResult a
data CoStoryF a = CoStoryF (CoChange a) (CoInterrupt a)
```

TODO(sandy): WHY is this crazy

No no no no no. Burn it with fire. This is obviously not what we want. How do we
know? Because it's crazy. Remember, `a` is the continuation of our computation,
but ... umm.

## OKWTF

Ok, so what are we *actually* trying to do?

What we really want to do is define a function:

```haskell
interpret :: CoStory b -> Story a -> (a, b)
```

which is to say, a function that runs `Story a` programs through a `CoStory b`
interpreter, and get back both the resulting computation (from the monad), and
the resulting world (from the comonad).

We can view this as the special case of a more general function:

```haskell
zap :: (Functor f, Functor g) => (a -> b -> c) -> f a -> g b -> c
```

which is a function where somehow the functors `f` and `g` "annihilate" one
another, and allow us to run pure functions over top of them. Obviously this
depends on our choice of `f` and `g`, so we will make a typeclass:

```haskell
class (Functor f, Functor g) => Zap f g | f -> g, g -> f where
    zap :: (a -> b -> c) -> f a -> g b -> c
```

It's reasonable to assume (this is usually the case with typeclasses) that we
can define `Zap f g` inductively. By that I mean, we can probably derive `Zap
(Cofree CoStoryF) (Free StoryF)` given `Zap CoStoryF StoryF`. This might give us
clues as to what `CoStoryF` would look like.

But where do we start? Well, let's start by trying to build a `Zap` for the
functors inside of `StoryF`. It's definition, again:

```haskell
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | Interrupt (Story ()) (Story ()) a
```

The functors out of which `StoryF` is built are kind of hidden, but if you
squint, you'll see we have a sum (between `Change` and `Interrupt`), a product
(the parameters in each branch), and a function.

In functor form, we know these as `(,) a`, `(->) a` and `Either a`. This
suggests we should start looking for instances of `Zap` between these functors.
Since pairs make up most of `StoryF`, let's start there. Our naive approach in
dualizing the products into sums earlier gave us crazy results, so let's look at
building a `Zap ((,) a) ((->) a)` instead.

This means we're looking for a function. Given the type signature, it's pretty
easy to work out:

```haskell
zap :: (a -> b -> c) -> (x, a) -> (x -> b) -> c
zap f (x, a) xtob = f a (xtob x)
```

Note that we don't need to derive `Zap ((->) a) ((,) b)` as well, since we can
just `flip` our incoming pure function and then use that in our other instance.
Slick!

This suggests we might be able to construct a `Zap`able `CoStoryF` by changing
all of the pairs with functions (and vice versa) in `StoryF`. For reasons I
don't entirely understand (but would probably make sense if I were smart enough
to draw the diagrams), we'll turn our sums into products.

Makes total sense, right? Yeah, me neither. But maybe looking at some actual
code will help. Here's the transformation I just suggested:


```haskell
data CoStoryF a = CoStoryF
                { changeH :: Character -> ChangeType -> (ChangeResult, a)
                , interruptH :: Story () -> Story () -> a
                }
```

This actually makes a great deal of sense if you look at it for a minute or two.
If a `StoryF` is actually one of any possible commands, each with arguments, a
`CoStoryF` should be capable of computing all possible commands by running those
arguments as function parameters.

Again, the `Zap CoStoryF StoryF` instance is informative:

```haskell
instance Zap CoStoryF StoryF where
    zap f (CoStoryF h _) (Change c ct k) = let (cr, a) = h c ct
                                               b       = k cr
                                            in f a b
    zap f (CoStoryF _ h) (Interrupt x x' b) = f (h x x') b

    -- or more tersely, using our zap for products and functions:
    zap f (CoStoryF h _) (Change c ct k)    = zap f (h c ct) k
    zap f (CoStoryF _ h) (Interrupt x x' k) =     f (h x x') k
```

I claim that this does what we want. But why does this work? Well we're using
the sum arguments from our `StoryF` type as an *index* into the product handler
of our `CoStoryF`. In the case of `Change`, we feed the *resulting*
`ChangeResult` of interpreting the `Change` back into the continuation `k` in
order to obtain our `b`.

Maybe you're starting to see now why this `Zap` machinery is useful for running
our program: it automatically interleaves the results from our interpretation
into the bound values in our DSL.

TODO: this is actually largely the same
But first we need to implement `Zap (Cofree f) (Free g)`. It's a little more
involved, but once you get it, should help solidify how `Cofree` and `Free` are
related.

```haskell
instance Zap f g => Zap (Cofree f) (Free g) where
    zap f (Cofree a _)  (Pure b)  = f a b
    zap f (Cofree _ as) (Bind bs) = zap (zap f) as bs
```

Notice how we're doing the same trick here: using the sum value of our `Free`
type to pick a particular piece out of the product of our `Cofree` type.


## Adjunctions

Looks like we don't yet (I know, I know) have enough theory to figure out what
we need to build.

```haskell
class (Functor f, Functor g) => Adjunction f g | f -> g, g -> f where
    unit   :: a -> g (f a)
    counit :: f (g a) -> a
```


```haskell
instance (Cofree cf) (Free f) where
    unit   :: a -> Free f (Cofree cf a)
    unit = Pure

    counit :: Cofree cf (Free f a) -> a
    counit cffa =
```


[cofree]:
[free]:


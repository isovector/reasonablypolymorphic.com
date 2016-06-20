---
layout: post
title: comonad-instance
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

As an example, let's write a simple interpreter which counts how many times
characters change states in the main flow of the program (we ignore interrupted
story-lines for now because they pose an extra challenge we'll get into next
time).

```haskell
-- Every change increases our number of changes by one.
coChange :: Int -> Character -> ChangeType -> (ChangeResult, Int)
coChange w c ct = (ChangeResult c ct, w + 1)

-- We ignore changes that happen in interrupted branches, so return the incoming
-- number of changes.
coInterrupt :: Int -> Story () -> Story () -> Int
coInterrupt w x x' = w
```

These are the individual handlers for our `CoStoryF`, and now to put it all
together:

```haskell
changeCounter :: CoStory Int
changeCounter = coiter next start
  where
    next w = CoStoryF (coChange w) (coInterrupt w)
    start  = 0
```

But what is this wild `coiter` thing? It's pronounced less like "coitus" and
more like "co-iterate". Its type:

```haskell
coiter :: Functor f => (a -> f a) -> a -> Cofree f a
```

`coiter` builds an infinite `Cofree` comonad by taking a starting value, and a
means of doing induction on how the comonad changes the deeper you get into the
cofree. It's defined like this:

```haskell
coiter :: Functor f => (a -> f a) -> a -> Cofree f a
coiter next start = Cofree start (coiter next <$> next start)
```

For us, the `w` variable in `coChange` and `coInterrupt` is tracking our
comonadic value, so it's the value that changes as our characters do. In the
case of a `Change`, we increase our resulting `w` by one. For `Interrupt`, we
just return the one we were given, since we're not yet sure how to deconstruct
our constituent `Story ()`s. We'll sort that out in the next post.

And we're done! Let's prove that it works. Given our old `Story`:

```haskell
myStory :: Story String
myStory = do
    let mandalf = Character "Mandalf the Wizard"
        orcLord = Character "Orclord Lord of the Orcs"
        orcBaby = Character "Orclord's Child"

    sadness <- kill mandalf orcLord -- 2 changes (orcLord dies & mandalf did it)
    change orcBaby $ Learn sadness  -- a third change

    return "Feel good story of the year"
```

we can run it:

```haskell
interpret :: CoStory b -> Story a -> (a, b)
interpret costory story = zap (,) story costory

interpret changeCounter myStory -- result: ("Feel good story of the year", 3)
```

So what have we accomplished here? We've built general purpose machinery

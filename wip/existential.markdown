---
layout: post
title: existential
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

Recall:

```haskell
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | Interrupt (Story ()) (Story ()) a
```

```haskell
{-# LANGUAGE ExistentialQuantification #-}
data StoryF a = Change Character ChangeType (ChangeResult -> a)
              | forall x y. Interrupt (Story x) (Story y) (y -> a)
```

```haskell
data CoStoryF b = CoStoryF
                { changeH    :: Character -> ChangeType -> (ChangeResult, b)
                , interruptH :: forall x y. Story x -> Story y -> (y, b)
                }
```

```haskell
instance Functor CoStoryF where
    fmap f (CoStoryF c i) = CoStoryF
        ((fmap . fmap . fmap) f c)
        ((fmap . fmap . fmap) f i)
```

```haskell
instance Zap StoryF CoStoryF where
    zap f (Change    c ct k) (CoStoryF h _) = zap f k (h c ct)
    zap f (Interrupt x y  k) (CoStoryF _ h) = zap f k (h x y)
```

```haskell
{-# LANGUAGE RankNTypes #-}
liftCoStory :: b
            -> (b -> Character -> ChangeType -> (ChangeResult, b))
            -> (forall x y . (forall a. Story a -> (a, b))
                          -> b
                          -> Story x
                          -> Story y
                          -> (y, b))
            -> CoStory b
liftCoStory start changeH interruptH =
    fix $ \self -> coiter (next (flip runStory self)) start
  where
    next run b =
        CoStoryF
            (changeH b)
            (interruptH (unsafeCoerce run) b)
```

```haskell
characters :: CoStory (Set Character)
characters = liftCoStory S.empty changeH interruptH
  where
    changeH b c ct = (ChangeResult c ct, S.insert c b)
    interruptH
        (run :: forall a. Story a -> (a, Set Character))
        b x y = ( fst (run y)
                , mconcat [b, snd (run x), snd (run y)]
                )
```

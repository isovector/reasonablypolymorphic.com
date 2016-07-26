---
layout: post
title: type-families
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

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

```haskell
data StoryF a
    = Change Character ChangeType (ChangeResult -> a)
    | forall x y. Interrupt (Free StoryF x)
                            (Free StoryF y)
                            (y -> a)
    | Macguffin (Desirable -> a)

instance Eq Desirable
```

```haskell
data BakedStoryF a
    = Change Character ChangeType a
    | forall x y. Interrupt (Free StoryF x)
                            (Free StoryF y)
                            a
    | Macguffin a
```

```haskell
data StoryF' g a
    = Change Character ChangeType (g ChangeResult a)
    | forall x y. Interrupt (Free (StoryF g) x)
                            (Free (StoryF g) y)
                            (g y a)
    | Macguffin (g Desirable a)

type StoryF = StoryF' (->)
type BakedStoryF = StoryF' Snd

data Snd f g = Snd g deriving Functor
```

```haskell
type family Cx g a b :: * where
    Cx (->) a b = a -> b
    Cx Snd  a b = b

data StoryF g a
    = Change Character ChangeType (Cx g ChangeResult a)
    | forall x y. Interrupt (Free (StoryF g) x)
                            (Free (StoryF g) y)
                            (Cx g y a)
    | Macguffin (Cx g Desirable a)
```

```haskell
{-# LANGUAGE DataKinds #-}
data BakedState = Constructed | Baked

type family Cx (s :: ReduceState)
               (a :: *)
               (f :: * -> * -> *)
               (b :: *) :: * where
    Cx 'Constructed a f b = f a b
    Cx 'Baked       a f b = b

data StoryF s a
    = Change Character ChangeType (Cx s ChangeResult (->) a)
    | forall x y. Interrupt (Free (StoryF s) x)
                            (Free (StoryF s) y)
                            (Cx s y (->) a)
    | Macguffin (Cx s Desirable (->) a)
```

```haskell
data CoStoryF s k
    = CoStoryF
    { changeH    :: Character -> ChangeType -> Cx s ChangeResult (,) k
    , interruptH :: forall x y. Free (StoryF s) x
                             -> Free (StoryF s) y
                             -> Cx s y (,) k
    , macguffinH :: Cx s Desirable (,) k
    }
```

```haskell
{-# LANGUAGE DataKinds #-}
data BakedState = Constructed | Baked | Reified

type family Cx (s :: ReduceState)
               (a :: *)
               (f :: * -> * -> *)
               (b :: *) :: * where
    Cx 'Constructed a f b = f a b
    Cx 'Baked       a f b = b
    Cx 'Reified     a f b = b

type family ReifyAs s a b :: * where
    ReifyAs 'Constructed a b = a
    ReifyAs 'Baked       a b = a
    ReifyAs 'Reified     a b = b

data StoryF s a = Change Character ChangeType (Cx s ChangeResult (->) a)
                | forall x y. Interrupt (ReifyAs s (Free (StoryF s) x) a)
                                        (ReifyAs s (Free (StoryF s) y) a)
                                        (Cx s y (->) a)
                | Macguffin (Cx s Desirable (->) a)
```


```haskell
type Story      = Free (StoryF 'Constructed)
type BakedStory = Free (StoryF 'Baked)

apply :: Story a -> BakedStory a
apply = (\(_,_,a) -> a) . go 0
  where
    go :: Int -> Story a -> (Int, a, BakedStory a)
    go i (Free (Change c ct k)) =
        let (i', a, k') = go i . k $ ChangeResult c ct
        in (i', a, Free $ Change c ct k')
    go i (Free (Interrupt x y k)) =
        let (i',   _, x') = go i  x
            (i'',  r, y') = go i' y
            (i''', a, k') = go i'' $ k r
        in (i''', a, Free $ Interrupt x' y' k')
    go i (Free (Macguffin k)) = go (i + 1) . k . Desirable $ show i
    go i (Pure a) = (i, a, Pure a)
```

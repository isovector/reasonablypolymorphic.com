---
layout: post
title: frpnow
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

here is a useful combinator to continuously run a `Now` action

```haskell
poll :: Now a -> Now (Behavior a)
poll now = loop
  where
    loop = do
        e  <- async (return ())
        a  <- now
        e' <- planNow $ loop <$ e
        return $ step a e'
```

all of these frp libraries seem to think this is a useful function

```haskell
foldp :: Eq b => (a -> b-> b) -> b -> Signal a -> Signal b
```

it's not really:

```haskell
player :: Behavior Prop
player = foldp update playerProp $ (,,,,,)
             <$> fmap (filter isWall)  scene
             <*> fmap (filter isFloor) scene
             <*> interactions
             <*> elapsed
             <*> arrows
             <*> keyPress SpaceKey
  where
    update (walls, floors, ints, dt, dir, active) p =
        if active && (not $ null ints)
           then let interaction = head ints
                 in unsafePerformIO $ mapM_ id interaction
           else
                let dpos = scaleRel (dt * playerSpeed) dir
                 in tryMove walls floors p dpos
```

egregious unsafeperformio

we can do better by introducing `foldmp`:

```haskell
{-# LANGUAGE TupleSections #-}
foldmp :: a
       -> (a -> Now a)
       -> Now ( Behavior a
              , (a -> a) -> IO ())
foldmp start f = do
    (evStream, mailbox) <- callbackStream
    let events = nextAll evStream
    nextEvent <- sample events
    b  <- loop start events nextEvent
    return (b, mailbox)
  where
    loop a events nextEvent = do
        e     <- async (return ())
        evVal <- sample $ tryGetEv nextEvent
        (a'mb, nextEvent') <-
            case evVal of
              Just updates ->
                  sample events >>= return . (foldr ($) a updates,)
              Nothing -> return (a, nextEvent)
        a' <- f a'mb
        e' <- planNow $ loop a' events nextEvent' <$ e
        return $ step a' e'
```

rewriting `player` in terms of this is better, we avoid gnarly tuples fmapping

```haskell
player :: Now (Behavior Prop)
player = fmap fst . foldmp playerProp $ \p -> do
    ints   <- sample interactions
    dt     <- sample elapsed
    dir    <- sample arrows
    active <- sample $ keyPress SpaceKey
    props  <- sample scene
    let walls  = filter isWall props
        floors = filter isFloor props

    if active
        then do
            liftIO $ mapM_ id interactions
            return p
        else
            let dpos = scaleRel (dt * playerSpeed) dir
             in tryMove walls floors p dpos
```

but notice how this is a direct port. since we now have a mailbox, we can
separate out the interaction logic

```haskell
player :: Now ( Behavior Prop
              , (Prop -> Prop) -> IO ())
player = foldmp playerProp $ \p -> do
    dt    <- sample elapsed
    dir   <- sample arrows
    props <- sample scene
    let walls  = filter isWall props
        floors = filter isFloor props

    let dpos = scaleRel (dt * playerSpeed) dir
    return $ tryMove walls floors p dpos

interactionHandler :: ((Prop -> Prop) -> IO ())
                   -> Now ()
interactionHandler addr = poll $ do
    ints   <- sample interactions
    active <- sample $ keyPress SpaceKey
    when active . forM_ interactions (addr $)
```

so much better!

but currently we have

```haskell
keyPress :: Key -> Behavior Bool
```

which is true if the key wasn't pressed last frame but is now. we're wasting all
of these cpu cycles by polling even though we don't need to anymore.

change to:

```haskell
keyPress :: Key -> Behavior (Event ())
```

now we get a discrete event when the key was pressed, and we can run some logic
on that. define the following combinator

note its similarity to `poll`

```haskell
onEvent :: Behavior (Event a)
        -> (a -> Now ())
        -> Now ()
onEvent events f = loop
  where
    loop = do
        e <- sample events
        planNow $ ((>> loop) . f) <$> e
        return ()
```

and now pulling it all together:

```haskell
newPlayer :: Now ( Behavior Prop
                 , (Prop -> Prop) -> IO ())
newPlayer = return $ do
   r@(sig, addr) <- foldmp playerProp $ \p -> do
       dt    <- sample elapsed
       dpos  <- fmap (scaleRel $ dt * playerSpeed) . sample $ arrows keys
       props <- sample scene
       let walls  = filter isWall props
           floors = filter isFloor props
       return $ tryMove walls floors p dpos

   onEvent (keyPress SpaceKey) . const $ do
       ints <- sample interactions
       forM_ ints (addr $)

   return r
```

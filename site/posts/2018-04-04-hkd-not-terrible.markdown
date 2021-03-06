---
layout: post
title: "HKD: Less Terrible than You Might Expect"
date: 2018-04-04 14:15
comments: true
tags: haskell, technical, programming, hkd
---

I thought I'd take some time to respond to some of the concerns raised about my
recent [Higher-Kinded Data][hkd] and [Free Lenses for Higher-Kinded
Data][lenses] posts.

[hkd]: /blog/higher-kinded-data
[lenses]: /blog/free-lenses


## Deriving Instances for HKD

One of the biggest concerns over the HKD technique was that it breaks automated
deriving of instances. This is not entirely true, it just requires turning on
`{-# LANGUAGE StandaloneDeriving #-}` and then using one of two approaches.

The simplest method is that we can simply derive all of our instances only for
the types we expect to use:

```haskell
deriving instance Eq (Person' Identity)
deriving instance Eq (Person' Maybe)
deriving instance Ord (Person' Identity)
deriving instance Ord (Person' Maybe)
```

Admittedly it's kind of a shit solution, but technically it does work.

An alternative approach is to automatically lift these instances from `f a` over
the `HKD f a` type family. The construction is a [little more involved][constr]
than I want to get into today, but thankfully it's available as [library
code][lib] from the spiffy [`one-liner`][oneliners] package.

[constr]: https://stackoverflow.com/a/49620701/4793220
[lib]: https://hackage.haskell.org/package/one-liner-1.0/docs/Generics-OneLiner.html#t:Constraints
[oneliners]: https://hackage.haskell.org/package/one-liner/

After adding `one-liner` as a dependency, we can lift our instances over a
polymorphic `f` using the `Constraints` type-synonym:

```haskell
deriving instance (Constraints (Person' f) Eq) => Eq (Person' f)
```

Easy!


## Runtime Performance

The other big concern was over whether we pay performance costs for getting so
many cool things for free.

For the most part, if you mark all of your generic type-class methods as
`INLINE` and turn on `-O2`, most of the time you're not going to pay any runtime
cost for using the HKD technique.

Don't believe me? I can prove it, at least for our free lenses.

Let's fire up the [`inspection-testing`][testing] package, which allows us to
write core-level equalities that we'd like the compiler to prove for us. The
equality we want to show is that the core generated for using our free lenses is
exactly what would be generated by using hand-written lenses.

[testing]: https://github.com/nomeata/inspection-testing

We can do this by adding some front-matter to our module:

```haskell
{-# LANGUAGE TemplateHaskell #-}
{-# OPTIONS_GHC -O -fplugin Test.Inspection.Plugin #-}

import Test.Inspection
```

This installs the `inspection-testing` compiler plugin, which is responsible for
doing the work for us. Next, we'll define our lenses:

```haskell
freeName :: Lens' (Person' Identity) String
Person (LensFor freeName) _ = getLenses

handName :: Lens' (Person' Identity) String
handName a2fb s = a2fb (pName s) <&> \b -> s { pName = b }
```

and finally, we can write the equalities we'd like GHC to prove for us. This is
done in two steps -- writing top-level left- and right- handed sides of the
equality, and then writing a TemplateHaskell splice to generate the proof.

```haskell
viewLhs, viewRhs :: Person' Identity -> String
viewLhs = view freeName
viewRhs = view handName

inspect $ 'viewLhs === 'viewRhs
```

Compiling this dumps some new information into our terminal:

```
src/Main.hs:34:1: viewLhs === viewRhs passed.
inspection testing successful
      expected successes: 1
```

We can write an analogy equality to ensure that the generated setter code is
equivalent:

```haskell
setLhs, setRhs :: String -> Person' Identity -> Person' Identity
setLhs y = freeName .~ y
setRhs y = handName .~ y

inspect $ 'setLhs === 'setRhs
```

And upon compiling this:

```
src/Main.hs:34:1: viewLhs === viewRhs passed.
src/Main.hs:35:1: setLhs === setRhs passed.
inspection testing successful
      expected successes: 2
```

Cool! Just to satisfy your curiosity, the actual lenses themselves aren't
equivalent:

```haskell
inspect $ 'freeName === 'handName
```

results in a big core dump showing that `freeName` is a gross disgusting chain
of `fmap`s and that `handName` is pretty and elegant. And the module fails to
compile, which is neat -- it means we can write these proofs inline and the
compiler will keep us honest if we ever break them.

But what's cool here is that even though our lenses do *not* result in
equivalent code, actually using them does -- which means that under most
circumstances, we won't be paying to use them.


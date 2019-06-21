---
layout: post
title: Polysemy Research's Latest Results
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

Polysemy turns out to be a surprisingly hard engineering problem. As the number
of regular contributors continues to grow, we've created a new organization on
Github to track all of the related pieces of infrastructure that are coming down
the pipeline. Today I want to talk about three exciting developments that
have come out of this research.

## Loopbreaker

As described in [Writing Custom Optimization
Passes][writing-custom-optimizations], The `polysemy-plugin` has had support for
creating explicit loopbreakers for self-recursive functions. The result is
pretty dramatic code improvements in a lot of cases when `-O2` is turned on.

[writing-custom-optimizations]:

Rather embarrassingly, after publishing that post, it turned out that my
implementation didn't in fact improve optimizations. Sure, it spit out the
correct code, but it was being done too late, and some special analysis passes
had already run. The result: we'd generate loopbreakers, but they wouldn't be
used.

The excellent [TheMatten][TheMatten] took it upon himself to fix this. There's
no trick --- just do the same transformations after renaming, rather than after
typechecking. We realized this plugin is useful outside of polysemy, so it's
been released as a [standalone package][loopbreaker].

[TheMatten]:
[loopbreaker]:


## MTL Absorption

As of `polysemy-zoo-0.1.2.0`, due to the incredible work of
[adamConnerSax][adamConnerSax], polysemy now has a `mtl`-interop story.

[adamConnerSax]: https://github.com/adamConnerSax

Though it seems like it would be straightforward to give eg. an instance of
`MonadState` for `Sem`:

```haskell
instance Member (State s) r => MonadState s (Sem r) where
  get = Polysemy.State.get
  put = Polysemy.State.put
```

Unfortunately, this doesn't compile. It violates `MonadState`'s functional
dependency that `| m -> s`. This is important for mtl's story around
type-inference, but it's not particularly relevant to us!

Today there is a [function][absorbState]:

[absorbState]: https://hackage.haskell.org/package/polysemy-zoo-0.3.0.0/docs/Polysemy-ConstraintAbsorber-MonadState.html

```haskell
absorbState
    :: Member (State s) r
    => (MonadState s (Sem r) => Sem r a)
    -> Sem r a
```

which does some tricky [reflection][reflection] to generate a `MonadState s`
dictionary *out of thin air* for `Sem r`. To be quite honest, the implementation
is beyond my comprehension, but the tests pass and that's good enough for me.

[reflection]:

As a result, we're now able to run `mtl`-style code directly in `polysemy`. That
means code of the form:

```haskell
foo :: (MonadState s m, MonadError e m, MonadIO m) => m ()
```

can be run via `absorbError $ absorbError foo` with type `Members '[State s,
Error e, Lift IO] r => Sem r ()`. Very cool!

Afraid that we haven't covered your favorite bespoke `mtl`-style effect? No
problem --- the tools for building your own `absorb` functions are exported and
easy to use. Please send a PR if you make one!


## RPC Effects

While working on [`hskit`][hskit] --- a hackable web-browser written in Haskell
--- an upstream dependency forced process-separation on me. That means the
effects I want to use need to run on a *separate process!* Yikes!

[hskit]:

This was a big problem for a while, before realizing that this sort of thing is
exactly why I like effect systems! There's nothing preventing me from giving an
interpretation of my effects that shuffles them over the network and runs them
there. Which is to say, there's nothing to prevent me from running my effects as
RPCs!

For example, given the effect:

```haskell
data Labeler m a where
  GetLinkRects :: Labeler m [AABB Float]
  SetLabels    :: [(String, AABB Float)] -> Labeler m ()
```

I can interpret it by sending it over the network:

```haskell
runLabelerOverRPC :: Member RPC r => Sem (Labeler ': r) a -> Sem r a
runLabelerOverRPC = interpret \case
  GetLinkRects -> do
    sendMessage "Labeler"
    sendMessage "GetLinkRects"
    recvSomething

  SetLabels labels -> do
    sendMessage "Labeler"
    sendMessage "SetLabels"
    sendSomething labels
```

and then, as part of my RPC server, I can interpret it there:

```haskell
dispatchLabeler :: Members '[RPC, Labeler, Error RPCError] r => Sem r ()
dispatchLabeler = do
  recvMessage >>= \case
    "GetLinkRects" -> getLinkRects >>= sendSomething
    "SetLabels"    -> do
      labels <- recvSomething
      setLabels labels
    _ -> throw RPCError
```

The function `runLabelerOverRPC` runs on the client by "handling" the `Labeler`
effect, and communicates with the server, which itself has a copy of the
`Labeler` effect.

These functions are both entirely boilerplate. Unfortunately, generics aren't
powerful enough to solve this problem for us, so we need to turn to Template
Haskell. I have a PR in the works that will automatically generate the
`runAsRPC` and `dispatch` function pairs de/serializing effects. It's not yet
industry-grade, but it's an exciting development in the space!


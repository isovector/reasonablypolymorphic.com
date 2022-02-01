---
layout: post
title: Testing Polysemy With polysemy-check
date: 2021-10-09 14:23
comments: true
tags: polysemy, testing, quickcheck
---

[Last week][porting] we covered how to port an existing codebase to
[`polysemy`][polysemy]. The "why you might want to do this" was left implicit,
but to be more explicit about things, it's because littering your codebase with
`IO` makes things highly-coupled and hard to test. By forcing yourself to think
about effects, you are forced to pull concerns apart, and use the type-system to
document what's going on. But more importantly for today, it gives us a layer of
indirection inside of which we can insert testing machinery.

[porting]: /blog/porting-to-polysemy/
[polysemy]: https://hackage.haskell.org/package/polysemy

To take an extreme example from the codebase I'm currently working on, compare a
function with its original (non-polysemized) type:

```haskell
api :: Opts -> ServerT API App
```

which looks very simple, and gives the false impression that `api` is fairly
uninteresting. However, there is an amazing amount of `IO` hiding inside of
`App`, which becomes *significantly more evident* when we give this type
explicit dependency constraints:

```haskell
api ::
  Members
    '[ AReqIDStore,
       AssIDStore,
       BindCookieStore,
       BrigAccess,
       DefaultSsoCode,
       Error SparError,
       GalleyAccess,
       IdP,
       Input Opts,
       Logger (Msg -> Msg)
       Logger String,
       Now,
       Random,
       Reporter,
       SAML2,
       SAMLUserStore,
       SamlProtocolSettings,
       ScimExternalIdStore,
       ScimTokenStore,
       ScimUserTimesStore,
     ]
    r =>
  Opts ->
  ServerT API (Sem r)
```

Wow! Not so innocent-looking now, is it? Each `Member` constraint here is a unit
of functionality that was previously smuggled in via `IO`. Not only have we made
them more visible, but we've now exposed a big chunk of testable surface-area.
You see, each one of these members provides an abstract interface, which we can
implement in any way we'd like.

Because `IO` is so hard to test, the idea of `polysemy` is that we can give
several interpretaions for our program --- one that is pure, lovely, functional,
and, importantly, very easy to test. Another interpretation is one that 
runs fast in `IO`. The trick then is to decompose the problem of testing into
two steps:

1. show that the program is correct under the model interpreter
2. show that the model interpreter is equivalent to the real interpreter

This sounds great in principle, but as far as I know, it's never been actually
done in practice. My suspicion is that people using `polysemy` in the wild don't
get further than step 1 (which is OK --- a good chunk of the value in effect
systems is in the decomposition itself.) Doing all of the work to show
equivalence of your interpreters is a significant amount of work, and until now,
there have been no tools to help.

**Introducing [`polysemy-check`][polysemy-check]:** a new library for proving
all the things you'd want to prove about a `polysemy` codebase. `polysemy-check`
comes with a few tools for synthesizing [`QuickCheck`][quickcheck] properties,
plus machinery for getting `Arbitrary` instances for effects for free.

[polysemy-check]: https://hackage.haskell.org/package/polysemy-check
[quickcheck]: https://hackage.haskell.org/package/QuickCheck


## Using polysemy-check

To get started, you're going to need to give two instances for every effect in
your system-under-test. Let's assume we have a stack effect:

```haskell
data Stack s m a where
  Push :: s -> Stack s m ()
  Pop :: Stack s m (Maybe s)
  RemoveAll :: Stack s m ()
  Size :: Stack s m Int

makeSem ''Stack
```

The instances we need are given by:

```haskell
deriving instance (Show s, Show a) => Show (Stack s m a)
deriveGenericK ''Stack
```

where `deriveGenericK` is TemplateHaskell that from
[`kind-generics`][kind-generics] (but is re-exported by `polysemy-check`.)
`kind-generics` is `GHC.Generics` on steroids: it's capable of deriving generic
code for GADTs.

[kind-generics]: https://hackage.haskell.org/package/kind-generics

The first thing that probably comes to mind when you consider `QuickCheck` is
"checking for laws." For example, we should expect that `push s` followed by
`pop` should be equal to `pure (Just s)`. Laws of this sort *give meaning to
effects,* and act as *sanity checks on their interpreters.*

Properties for laws can be created via `prepropLaw`:

```haskell
prepropLaw
    :: forall effs r a f
     . ( (forall z. Eq z => Eq (f z))
       , (forall z. Show z => Show (f z))
       )
    => ( Eq a
       , Show a
       , ArbitraryEff effs r
       )
    => Gen (Sem r a, Sem r a)
    -> (forall z. Sem r (a, z) -> IO (f (a, z)))
    -> Property
```

Sorry for the atrocious type. If you're looking for Boring Haskell, you'd best
look elsewhere.

The first argument here is a `QuickCheck` generator which produces two programs
that should be equivalent. The second argument is the interpreter for `Sem`
under which the programs must be equivalent, or will fail the resulting
`Property`. Thus, we can write the `push/pop` law above as:

```haskell
law_pushPop
    :: forall s r f effs res
     . (
         -- The type that our generator returns
         res ~ (Maybe s)

         -- The effects we want to be able to synthesize for contextualized
         -- testing
       , effs ~ '[Stack s]

         -- Misc constraints you don't need to care about
       , Arbitrary s
       , Eq s
       , Show s
       , ArbitraryEff effs r
       , Members effs r
       , (forall z. Eq z => Eq (f z))
       , (forall z. Show z => Show (f z))
       )
    => (forall a. Sem r (res, a) -> IO (f (res, a)))
    -> Property
law_pushPop = prepropLaw @effs $ do
  s <- arbitrary
  pure ( push s >> pop
       , pure (Just s)
       )
```

Sorry. Writing gnarly constraints is the cost not needing to write gnarly code.
If you know how to make this better, please open a PR!

There's something worth paying attention to in `law_pushPop` --- namely the type
of the interpreter `(forall a. Sem r (Maybe s, a) -> IO (f (Maybe s, a)))`. What
is this `forall a` thing doing, and where does it come from? As written, our
generator would merely checks the equivalence of the exact two given programs,
but this is an insufficient test. We'd instead like to prove the equivalence of
the `push/pop` law *under all circumstances.*

Behind the scenes, `prepropLaw` is synthesizing a monadic action to run *before*
our given law, as well as some actions to run *after* it. These actions are
randomly pulled from the effects inside the `effs ~ '[Stack s]` row (and so
here, they will only be random `Stack` actions.) The `a` here is actually the
result of these "contextual" actions. Complicated, but you really only need to
get it right once, and can copy-paste it forevermore.

Now we can specialize `law_pushPop` (plus any other laws we might have written)
for a would-be interpreter of `Stack s`. Any interpreter that passes all the
properties is therefore proven to respect the desired semantics of `Stack s`.


## Wrapping Up

`polysemy-check` can do lots more, but this post is overwhelming already. So
next week we'll discuss how to prove the equivalence of interpreters, and how to
ensure your effects are sane with respect to one another.


---
layout: post
title: Writing Custom Optimization Passes
date: 2019-05-22 13:39
comments: true
tags: polysemy, plugin, optimization
---

I've been paying a lot of attention to performance in [`polysemy`][polysemy].
Getting it to be fast [has been really hard][costly]. It's clearly possible, but
for the longest time I was afraid I'd need to fork the compiler. And that didn't
seem like a thing that would attract a large-user base.

[polysemy]: https://github.com/isovector/polysemy/
[costly]: /blog/freer-yet-too-costly/

For example, `polysemy` benefits greatly from a [late specialization
pass][specialization], and would benefit further from aggressive inlining
*after* the late specialization pass. Unfortunately, [GHC doesn't do any
inlining passes after `-flate-specialise`][passes], so it feels like we're stuck
on this front.

[specialization]: /blog/specialization/
[passes]: https://github.com/ghc/ghc/blob/master/compiler/simplCore/SimplCore.hs#L320-L345

Thankfully, the eternally helpful [mpickering][mpickering] pointed me at the
[GHC plugin interface][plugins], which has support for directing the optimizer
to do things it wouldn't usually.

[mpickering]: https://mpickering.github.io/
[plugins]: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/extending_ghc.html#writing-compiler-plugins

Today, I want to talk about how I made the [`polysemy-plugin`][polyplug] run two
optimizations that greatly benefit code written with `polysemy`.

[polyplug]: https://github.com/isovector/polysemy/tree/master/polysemy-plugin

The gist of writing a GHC plugin is to import `ghc:Plugins`, and to create an
exported top-level bind `plugin :: Plugin`. Other code can use this plugin by
specifying the `-fplugin=` option to point at this module.


## Installing Core ToDos

`Plugin`s have a field called `installCoreToDos` with type `[CommandLineOption]
-> [CoreToDo] -> CoreM [CoreToDo]`. A `CoreToDo` is GHC's oddly-named concept of
a compiler pass over Core. This function receives the list of `CoreToDo`s it was
planning to do, and you can change that list if you want.

By default there's a big flowchart of `CoreToDo`s that the compiler will run
through in order to compile a module. The optimization level (`-O`) effects
which passes get run, as do many of the [individual optimization
flags][optflags].

[optflags]: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/using-optimisation.html#f-platform-independent-flags

By attaching our extra optimization passes to the end of this list, we can make
GHC optimize harder than it usually would. But because most code *won't* benefit
from this extra work, we guard the new optimization passes behind two
conditions. The user must be compiling with optimizations turned on, and the
module being compiled must import `Polysemy`.

Checking for the optimization level is simple enough, we can pull it out of the
`DynFlags` (GHC's datatype that stores all of the crazy flags you might have
set):

```haskell
  dflags <- getDynFlags
  case optLevel dflags of
    0 -> -- corresponds to -O0
    1 -> -- corresponds to -O
    2 -> -- corresponds to -O2
```

Checking, however, for presence of the `Polysemy` module is less
straightforward. Honestly I'm not sure what the "correct" solution to this
problem is, but I'm pretty happy with the disgusting hack I came up with.

The `CoreM` monad (which is what you're running in when you install `CoreToDo`s)
doesn't exactly have [stellar documentation][corem]. It has access to the
`HscEnv`, which in turn has a `hsc_mod_graph :: ModuleGraph` --- which sounds
like the sort of thing that might contain the modules currently in scope.
Unfortunately this is not so; `hsc_mod_graph` contains the modules defined in
the *package* being defined.

[corem]: https://www.stackage.org/haddock/lts-13.21/ghc-8.6.5/CoreMonad.html#t:CoreM

If we could get our hands on the `ModGuts` (GHC's representation of a Haskell
module), we could inspect its `mg_deps :: Dependencies` field, which would
surely have what we need. Unfortunately, I couldn't find any easy way to get
access to the `ModGuts` in a `CoreM` without jumping through several hoops.

But one thing caught my eye! There is an operation `getVisibleOrphanMods ::
CoreM ModuleSet`, which after some investigation, turns out to contain any
module in scope (directly or otherwise) that defines an orphan instance.

It's disgusting, but I made an internal module in `polysemy` that contains the
following definitions:

```haskell
module Polysemy.Internal.PluginLookup where

class PluginLookup t
data Plugin
```

and the corresponding orphan instance in the module I wanted to track in my
plugin:

```haskell
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Polysemy.Internal.PluginLookup

instance PluginLookup Plugin
```

I know, I know. But because the module that defines these things is internal,
there's no way for anyone else to define instances of this thing. So at least
it's a safe use of orphans.

Sure enough, this little gem is enough to get my module noticed by
`getVisibleOrphanMods`, and so I can check for the presence of my module via:

```haskell
  mods <- moduleSetElts <$> getVisibleOrphanMods
  if any ((== mkModuleName "Polysemy.Internal") . moduleName) mods
     then ...
```

And voila, we're now ready to install our extra `CoreToDo`s. In this case, I
just cargo-culted a few from GHC's existing passes list. Namely I added a
`CoreDoSpecialising`, a `CoreDoStaticArgs`, yet another `CoreDoSpecialising`,
and a bevvy of simplification passes. The result might be overkill, but it's
sufficient to massage [this scary core][bad] into [this][good] --- and get
roughly a 1000x runtime performance improvement in the process.

[bad]: https://gist.github.com/isovector/e4832512ec9c73bff94432a7a58470f9#file-t16473-dump-simpl
[good]: https://gist.github.com/isovector/e4832512ec9c73bff94432a7a58470f9#gistcomment-2883147


## Inlining Recursive Calls

But this lack of optimization passes wasn't the only thing slowly `polysemy`
down. The library depends on several library- and user-written functions that
are complicated and necessarily self-recursive.

GHC is understandably hesitant to inline recursive functions --- the result
would diverge --- but as a side-effect, it seems to refuse to optimize big
recursive functions whatsoever. For my purposes, this meant that most of the
crucial machinery in the library was being completely ignored by GHC's best
optimization pass.

I accidentally stumbled upon a fix. To illustrate, let's pretend like the
`factorial` function is my complicated self-recursive function. The optimizer
would refuse to fire when the function was written like this:

```haskell
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial (n - 1)
{-# INLINE factorial #-}
```

But, a minor syntactic tweak was enough to trick the compiler into optimizing
it:

```haskell
factorial :: Int -> Int
factorial 0 = 1
factorial n = n * factorial' (n - 1)
{-# INLINE factorial #-}

factorial' :: Int -> Int
factorial' = factorial
{-# NOINLINE factorial' #-}
```

Now `factorial` is no longer self-recursive. It's mutually recursive, and for
some reason, the `NO/INLINE` pragmas are enough to keep GHC off our back. This
is an easy fix, but it's annoying boilerplate. And I *hate* annoying
boilerplate.

Early versions of `polysemy` shipped with a function `inlineRecursiveCalls :: Q
[Dec] -> Q [Dec]` which would use Template Haskell to transform our slow,
self-recursive `factorial` above into the fast, mutually-exclusive version
below. While this worked, it was unsatisfactory; TH splices don't play nicely
with haddock or with text editors.

But this isn't something that regular users should need to care about!
Optimization concerns should lie solely in the responsibility of library-writers
--- not in their users. It seemed like a good opportunity to write a custom
optimization pass, and like any curious boy, I took it.

We can use the `CoreDoPluginPass :: String -> (ModGuts -> CoreM ModGuts) ->
CoreToDo` constructor to inject our own `ModGuts` transformation as an
optimization pass. Recall that `ModGuts` is GHC's definition of a module. For
our purposes, we're interested in its `mg_binds` field, which contains all of
the value-level things in the module.

A `mg_binds` is a `[Bind CoreBndr]`, and a `Bind CoreBndr` is a pair of a name
and its corresponding expression definition. More specifically, the definition
for `Bind` is:

```haskell
data Bind b = NonRec b (Expr b)
            | Rec [(b, (Expr b))]
```

A non-recursive binding is something like `x = 5`, while a recursive binding is
anything that is self- or mutually-recursive.

So, if we want to transform self-recursive calls into mutually-recursive calls,
we first need to identify if a definition is self-recursive. Fortunately, the
incredible `syb` library comes in handy here, as it lets us write small queries
that get lifted over the entire datatype.

We can write `containsName` using [`everywhere`][everywhere], [`mkQ`][mkQ] and the [`Any`][Any] monoid to
determine if the `CoreBndr` name is used anywhere in the `CoreExpr`[^1].

[everywhere]: https://www.stackage.org/haddock/lts-13.22/syb-0.7/Data-Generics-Schemes.html#v:everywhere
[mkQ]: https://www.stackage.org/haddock/lts-13.22/syb-0.7/Data-Generics-Aliases.html#v:mkQ
[Any]: https://www.stackage.org/haddock/lts-13.22/base-4.12.0.0/Data-Monoid.html#t:Any
[^1]: GHC has a bad habit of using type synonyms. A `CoreExpr` is just a `Expr CoreBndr`.

```haskell
containsName :: CoreBndr -> CoreExpr -> Bool
containsName n =
    getAny .
      everything
        (<>)
        (mkQ (Any False) matches)
  where
    matches :: CoreExpr -> Any
    matches (Var n') | n == n' = Any True
    matches _ = Any False
```

If `containsName b e` is `True` for any `(b, e)` in the `mg_binds`, then that
function is self-recursive. As such, we'd like to generate a new `NOINLINE` bind
for it, and then replace the original self-call to be to this new bind.

Replacing a call is just as easy as finding the recursion:

```haskell
replace :: CoreBndr -> CoreBndr -> CoreExpr -> CoreExpr
replace n n' = everywhere $ mkT go
  where
    go :: CoreExpr -> CoreExpr
    go v@(Var nn)
      | nn == n   = Var n'
      | otherwise = v
    go x = x
```

But creating the new binding is rather more work; we need to construct a new
name for it, and then fiddle with its `IdInfo` in order to set the inlining
information we'd like.

```haskell
loopbreaker :: Uniq -> CoreBndr -> CoreExpr -> [(Var, CoreExpr)]
loopbreaker newUniq n e =
  let Just info = zapUsageInfo $ idInfo n
      info' = setInlinePragInfo info alwaysInlinePragma
      n' = mkLocalVar
             (idDetails n)
             (mkInternalName newUniq (occName n) noSrcSpan)
             (idType n)
         $ setInlinePragInfo vanillaIdInfo neverInlinePragma
   in [ (lazySetIdInfo n info', replace n n' e)
      , (n', Var n)
      ]
```

First we use `zapUsageInfo` to make GHC forget that this binding is
self-recursive[^2], and then use `setInlinePragInfo` to spiritually inject a
`{-# INLINE n #-}` pragma onto it. We then construct a new name (a nontrivial
affair; `loopbreaker` above is simplified in order to get the new `Uniq` to
ensure our variable is hygienic), and replace the self-recursive call with a
call to the new name. Finally, we need to spit out the two resulting binds.

[^2]: I'm not sure this part is necessary, but it doesn't seem to hurt.

There's a little machinery to call `loopbreaker` on the `mg_guts`, but it's
uninteresting and this post is already long enough. If you're interested, the
[full code is available on Github][inline]. In total, it's a little less than
100 lines long; pretty good for adding a completely new optimization pass!

[inline]: https://github.com/isovector/polysemy/blob/f84dc2577524e8ba25c35b9b7479c63edd220a6e/polysemy-plugin/src/Polysemy/Plugin/InlineRecursiveCalls.hs

That's enough about writing plugins for improving performance; in the next post
we'll discuss typechecker plugins, and how they can be used to extend GHC's
constraint-solving machinery. Stay tuned!


---
layout: post
title: Faking Fundeps with Typechecker Plugins
date: 2019-05-25 02:17
comments: true
tags: ghc, polysemy, plugin, typechecker
---

> The approach here, and my original implementation are both lifted almost
> entirely from [Luka Horvat][LukaHorvat]'s [plugin for `simple-effects`][simple-effects].
> All praise should be directed to him.

[LukaHorvat]: https://github.com/LukaHorvat
[simple-effects]: https://gitlab.com/LukaHorvat/simple-effects/commit/966ce80b8b5777a4bd8f87ffd443f5fa80cc8845#f51c1641c95dfaa4827f641013f8017e8cd02aab

---

[Last time][passes] we chatted about using a GHC plugin to run custom
Core-to-Core transformations on the programs that GHC is compiling. Doing so
allows us to add custom optimization passes, and even other, more *exotic*
things like [rewriting lambda expression as categorical operations][concat].

[passes]: /blog/writing-custom-optimizations/
[concat]: https://github.com/conal/concat

Today I want to talk about another sort of GHC plugin: *type-checker plugins!*
TC plugins let you hook into GHC's constraint machinery and help it solve
domain-specific problems that it wouldn't be able to otherwise. One of the more
interesting examples of a TC plugin is [nomeata's][nomeata] [ghc-justdoit][jdi]
--- which will automatically generate a value of the correct type, essentially
letting you leave implementations as "exercises for the compiler."

[nomeata]: https://www.joachim-breitner.de/blog
[jdi]: http://hackage.haskell.org/package/ghc-justdoit

[Polysemy][polysemy] uses a TC plugin in order to improve type-inference. The
result is that it can provide type-inference that is as good as `mtl`'s, without
succumbing to the pitfalls that accompany `mtl`'s approach.

[polysemy]: https://github.com/isovector/polysemy/


## The Problem

Consider the following program:

```haskell
foo :: MonadState Int m => m ()
foo = modify (+ 1)
```

Such a thing compiles and runs no problem. There are no surprises here for any
Haskell programmers who have ever run into `mtl`. But the reason it works is
actually quite subtle. If we look at the type of `modify` we see:

```haskell
modify :: MonadState s m => (s -> s) -> m ()
```

which suggests that the `s -> s` function we pass to it should determine the `s`
parameter. But our function `(+ 1)` has type `Num a => a -> a`, therefore the
type of `modify (+1)` should be this:

```haskell
modify (+ 1) :: (MonadState s m, Num s) => m ()
```

So the question is, why the heck is GHC willing to use a `MonadState Int m`
constraint to solve the wanted `(MonadState s m, Num s)` constraint arising from
a use of `modify (+1)`? The problem feels analogous to this one, which *doesn't
work:*

```haskell
bar :: Show Bool => a -> String
bar b = show b  -- doesn't work
```

Just because we have a `Show Bool` constraint in scope _doesn't mean that `a` is
a `Bool`!_ So how come we're allowed to use our `MonadState Int m` constraint,
to solve a `(MonadState s m, Num s)`? Completely analogously, _we don't know
that `s` is an `Int`!_

The solution to this puzzler is in the definition of `MondState`:

```haskell
class Monad m => MonadState s (m :: * -> *) | m -> s where
```

Notice this `| m -> s` bit, which is known as a *functional dependency*  or a
*fundep* for short. The fundep says "if you know `m`, you also know `s`," or
equivalently, "`s` is completely determined by `m`." And so, when typechecking
`foo`, GHC is asked to solve both `MonadState Int m` and `(Num s, MonadState s
m)`. But since there can only be a *single instance* of `MonadState` for m, this
means that `MonadState Int m` and `MonadState s m` _must be the same_.
Therefore `s ~ Int`.

This is an elegant solution, but it comes at a cost --- namely that we're only
allowed to use a single `MonadState` at a time! If you're a longtime Haskell
programmer, this probably doesn't feel like a limitation to you; just stick all
the pieces of state you want into a single type, and then use some classy fields
to access them, right? [Matt Parsons][parsonsmatt] has [a blog post][trouble] on
the pain points, and some bandages, for doing this with typed errors. At the end
of the day, the real problem is that we're only allowed a single `MonadError`
constraint.

[parsonsmatt]: https://www.parsonsmatt.org/
[trouble]: https://www.parsonsmatt.org/2018/11/03/trouble_with_typed_errors.html

Polysemy "fixes the glitch" by just not using fundeps. This means you're
completely free to use as many state, error, and whatever effects you want all
at the same time. The downside? Type-inference sucks again. Indeed, the
equivalent program to `foo` in `polysemy` doesn't compile by default:

```haskell
foo' :: Member (State Int) r => Sem r ()
foo' = modify (+ 1)
```

```
• Ambiguous use of effect 'State'
  Possible fix:
    add (Member (State s0) r) to the context of
      the type signature
  If you already have the constraint you want, instead
    add a type application to specify
      's0' directly, or activate polysemy-plugin which
        can usually infer the type correctly.
• In the expression: modify (+ 1)
  In an equation for ‘foo'’: foo' = modify (+ 1)
```

This situation blows chunks. It's obvious what this program should do, so let's
just fix it.


## The Solution

Let's forget about the compiler for a second and ask ourselves how the Human
Brain Typechecker(TM) would type-check this problem. Given the program:

```haskell
foo' :: Member (State Int) r => Sem r ()
foo' = modify (+ 1)
```

A human would look at the `modify` here, and probably run an algorithm similar
to this:

* Okay, what `State` is `modify` running over here?
* Well, it's some sort of `Num`.
* Oh, look, there's a `Member (State Int) r` constraint in scope.
* That thing wouldn't be there if it wasn't necessary.
* I guess `modify` is running over `State Int`.

Pretty great algorithm! Instead, here's what GHC does:

* Okay, what `State` is `modify` running over here?
* Well, it's some sort of `Num`.
* But that thing is polymorphic.
* Guess I'll emit a `(Num n, Member (State n) r)` constraint.
* Why did the stupid human put an unnecessary `Member (State Int) r` constraint
    here?
* What an idiot!

And then worse, it won't compile because the generated `n` type is now ambiguous
and not mentioned anywhere in the type signature!

Instead, let's use a TC plugin to make GHC reason more like a human when it
comes to `Member` constraints. In particular, we're going to mock the fundep
lookup algorithm:

* Whenever GHC is trying to solve a `Member (effect a) r` constraint
* And there is *exactly one* constraint in scope of the form `Member (effect b) r`
* Then emit a `a ~ b` constraint, allowing GHC to use the given `Member (effect b) r`
    constraint to solve the wanted `Member (effect a) r`


## TC Plugins

At its heart, a TC plugin is a value of type `TcPlugin`, a record of three
methods:

```haskell
data TcPlugin = forall s. TcPlugin
  { tcPluginInit  :: TcPluginM s
  , tcPluginSolve :: s -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
  , tcPluginStop  :: s -> TcPluginM ()
  }
```

The `tcPluginInit` field can be used to allocate a piece of state that is passed
to the other two records, and `tcPluginStop` finalizes that state. Most plugins
I've seen use the `s` parameter to lookup the GHC representation of classes that
they want to help solve.  However, the most interesting bit is the
`tcPluginSolve` function.

`tcPluginSolve` takes three lists of `Ct`s, which are different varieties of
constraints relevant to the problem.

1. The first list is the *given* constraints --- the ones a user has explicitly
   written out in a type signature.
2. The second list is the *derived* constraints --- things GHC has inferred from
   context.
3. The third list is the *wanted* constraints --- the ones that GHC can't solve
   on its own.

From these three lists, we are expected to provide a `TcPluginResult`, which for
our purposes is a pair of new `Ct`s we'd like GHC to solve; and a list of the
`Ct`s we solved, along with the corresponding dictionaries. Returning two empty
lists here signals to GHC "I can't do any more work!"

So let's get to work. The first thing we need to do is get our hands on the
`Member` class we want to solve. In `polysemy`, `Member` is actually just a type
synonym for a few other typeclasses; so the real typeclass we'd like to solve
for is called `Find`.

As a brief aside on the `Find` class, its definition is this:

```haskell
class Find (r :: [k]) (t :: k) where
```

and it means "lookup the index of `t` inside `r`". In Polysemy, `r` is usually
left polymorphic, for the same reasons that we leave the `m` polymorphic in
`MonadState s m`.

Anyway, we want to find the `Find` class. We can do this by writing a function
for our `tcPluginInit` function:

```haskell
findFindClass :: TcPlugin Class
findFindClass = do
  md <- lookupModule
          (mkModuleName "Polysemy.Internal.Union")
          (fsLit "polysemy")
  find_tc <- lookupName md $ mkTcOcc "Find"
  tcLookupClass find_tc
```

We first lookup the defining module, here `Polysemy.Internal.Union` in package
`polysemy`. We then lookup the `Find` name in that module, and then lookup the
class with that name. By setting `findFindClass` as our `tcPluginInit`, our
`tcPluginSolve` function will receive the `Find` class as a parameter.

Before diving into `tcPluginSolve`, we're going to need some helper functions.

```haskell
allFindCts :: Class -> [Ct] -> [(CtLoc, (Type, Type, Type))]
allFindCts cls cts = do
  ct <- cts
  CDictCan { cc_tyargs = [ _, r, eff ] } <- pure ct
  guard $ cls == cc_class cd
  let eff_name = getEffName eff
  pure (ctLoc ct, (eff_name, eff, r))

getEffName :: Type -> Type
getEffName t = fst $ splitAppTys t
```

The `allFindCts` function searches through the `Ct`s for `Find` constraints, and
unpacks the pieces we're going to need. We first pattern match on whether the
`Ct` is a `CDictCan`, which corresponds to everyday typeclass-y constraints. We
ensure it has exactly three type args (`Find` takes a kind, and then the two
parameters we care about), and ensure that this class is the `cls` we're looking
for.

We return four things for each matching `Ct`:

1. We need to keep track of its `CtLoc` --- corresponding to where the
   constraint came from. This is necessary to keep around so GHC can give good
   error messages if things go wrong.
2. The effect "name". This is just the head of the effect, in our ongoing
   example, it's `State`.
3. The actual effect we're looking for. This corresponds to the `t` parameter in
   a `Find` constraint. In the ongoing example, `State s`.
4. The effect stack we're searching in (`r` in the `Find` constraint).

So remember, our idea is "see if there is exactly one matching given `Find`
constraint for any wanted `Find` constraint --- and if so, unify the two."

```haskell
findMatchingEffect
    :: (Type, Type, Type)
    -> [(Type, Type, Type)]
    -> Maybe Type
findMatchingEffect (eff_name, _, r) ts =
  singleListToJust $ do
    (eff_name', eff', r') <- ts
    guard $ eqType eff_name eff_name'
    guard $ eqType r r'
    pure eff

singleListToJust :: [a] -> Maybe a
singleListToJust [a] = Just a
singleListToJust _ = Nothing
```

`findMatchingEffect` takes the output of `allFindCts` for a *single wanted
constraint*, and *all of the given* constraints, and sees if there's a single
match between the two. If so, it returns the matching effect.

We need one last helper before we're ready to put everything together. We wanted
to be able to generate new wanted constraints of the form `a ~ b`. Emitting such
a thing as a new wanted constraint will cause GHC to unify `a` and `b`; which is
exactly what we'd like in order to convince it to use one given constraint in
place of another.

```haskell
mkWanted :: CtLoc -> Type -> Type -> TcPluginM (Maybe Ct)
mkWanted loc eff eff' = do
  if eqType (getEffName eff) (getEffName eff')
     then do
       (ev, _) <- unsafeTcPluginTcM
                . runTcSDeriveds
                $ newWantedEq loc Nominal eff eff'
       pure . Just $ CNonCanonical ev
     else
       pure Nothing
```

What's going on here? Well we check if the two effects we want to unify have the
same effect name. Then if so, we use the wanted's `CtLoc` to generate a new,
derived wanted constraint of the form `eff ~ eff'`. In essence, we're promising
the compiler that it can solve the wanted if it can solve `eff ~ eff'`.

And finally we're ready to roll.

```haskell
solveFundep :: Class -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
solveFundep find_cls giv _ want = do
    let wanted_effs = allFindCts find_cls want
        given_effs  = fmap snd $ allFindCts find_cls giv

    eqs <- forM wanted_effs $ \(loc, e@(_, eff, r)) ->
      case findMatchingEffect e given_effs of
        Just eff' -> mkWanted loc eff eff'
        Nothing -> do
          case splitAppTys r of
            (_, [_, eff', _]) -> mkWanted loc eff eff'
            _                 -> pure Nothing

    pure . TcPluginOk [] $ catMaybes eqs
```

We get all of the `Find` constraints in the givens and the wanteds. Then, for
each wanted, we see if there is a singularly matching given, and if so, generate
a wanted constraint unifying the two.

However, if we *don't* find a singularly matching effect, we're not necessarily
in hot water. We attempt to decompose `r` into a type constructor and its
arguments. Since `r` has kind `[k]`, there are three possibilities here:

1. `r` is a polymorphic type variable, in which case we can do nothing.
2. `r` is `'[]`, so we have no effects to possibly unify, and so we can do
   nothing.
3. `r` has form `e ': es`, in which case we attempt to unify `e` with the
   wanted.

What's going on with this? Why is this bit necessary? Well, consider the case
where we want to *run* our effect stack. Let's say we have this program:

```haskell
foo' :: Member (State Int) r => Sem r ()
foo' = modify (+ 1)

main :: IO ()
main = do
  result <- runM . runState 5 $ foo'
  print result
```

The type of `runM . runState 5` is `Num a => Sem '[State a, Lift IO] x -> IO x`.
But `foo'` still wants a `State Int` constraint, however, `main` _doesn't have
any givens!_ Instead, the wanted we see is of the form `Find '[State a, Lift IO]
(State Int)`, and so we're justified in our logic above to unify `State Int`
with the head of the list.

Finally we can bundle everything up:

```haskell
plugin :: Plugin
plugin = defaultPlugin
    { tcPlugin = const $ Just fundepPlugin
    }

fundepPlugin :: TcPlugin
fundepPlugin = TcPlugin
    { tcPluginInit = findFindClass
    , tcPluginSolve = solveFundep
    , tcPluginStop = const $ pure ()
    }
```

and voila, upon loading our module via the `-fplugin` flag, GHC will
automatically start solving `Member` constraints as though they were fundeps!

This isn't the whole story; there are still a few kinks in the implementation
for when your given is more polymorphic than your wanted (in which case they
shouldn't unify), but this is enough to get a feeling for the idea. As always,
the [full source code is on Github][github].

[github]: https://github.com/isovector/polysemy/blob/master/polysemy-plugin/src/Polysemy/Plugin/Fundep.hs

As we've seen, TC plugins are extraordinarily powerful for helping GHC solve
domain-specific problems, and simultaneously quite easy to write. They're not
often the right solution, but they're a great thing to keep in your tool belt!


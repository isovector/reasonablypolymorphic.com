---
layout: post
title: "Algorithmically Scrapping Your Typeclasses"
date: 2018-04-16 13:47
comments: true
tags: compilers, haskell, programming, technical
---

I've been working on a simple Haskell98 compiler over the last few days, partly
as an excuse to learn how it works, and partly to have a test-bed for trying out
some potential language extensions. More on that in a future blog post.

As of yesterday, I have typeclass resolution working. The algorithm to desugar
constraints into dictionaries hasn't been discussed much. Since it's rather
involved, and quite interesting, I thought it might make a good topic for a blog
post.

Our journey begins having just implemented [Algorithm W][algw] aka
[Hindley-Milner][hm]. This is pretty well described in the literature, and there
exist several implementations of it in Haskell, so we will not dally here.
Algorithm W cashes out in a function of the type:

[algw]: http://web.cecs.pdx.edu/~mpj/thih/thih.pdf
[hm]: https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system

```haskell
infer :: SymTable VName Type -> Exp VName -> TI Type
```

where `SymTable VName` is a mapping from identifiers in scope to their types,
`Exp VName` is an expression we want to infer, and `TI` is our type-inference
monad. As a monad, `TI` gives us the ability to generate fresh type variables,
and to unify types as we go. `Type` represents an unqualified type, which is to
say it can be used to describe the types `a`, and `Int`, but not `Eq a => a`. We
will be implementing qualified types in this blog post.

`infer` is implemented as a [catamorphism][schemes], which generates a fresh
type variable for every node in the expression tree, looks up free variables in
the `SymTable` and attempts to unify as it goes.

[schemes]: /blog/recursion-schemes

The most obvious thing we need to do in order to introduce constraints to our
typechecker is to be able to represent them, so we two types:

```haskell
infixr 0 :=>
data Qual t = (:=>)
  { qualPreds  :: [Pred]
  , unqualType :: t
  } deriving (Eq, Ord, Functor, Traversable, Foldable)

data Pred = IsInst
  { predCName :: TName
  , predInst  :: Type
  } deriving (Eq, Ord)
```

Cool. A `Qual Type` is now a qualified type, and we can represent `Eq a => a`
via `[IsInst "Eq" "a"] :=> "a"` (assuming `OverloadedStrings` is turned on.)
With this out of the way, we'll update the type of `infer` so its symbol table
is over `Qual Types`, and make it return a list of `Pred`s:

```haskell
infer :: SymTable VName (Qual Type) -> Exp VName -> TI ([Pred], Type)
```

We update the algebra behind our `infer` catamorphism so that adds any `Pred`s
necessary when instantiating types:

```haskell
infer sym (V a) =
  case lookupSym a sym of
    Nothing -> throwE $ "unbound variable: '" <> show a <> "'"
    Just sigma -> do
      (ps :=> t) <- instantiate a sigma
      pure (ps, t)
```

and can patch any other cases which might generate `Pred`s. At the end of our
cata, we'll have a big list of constraints necessary for the expression to
typecheck.

As a first step, we'll just write the type-checking part necessary to implement
this feature. Which is to say, we'll need a system for discharging constraints
at the type-level, without necessarily doing any work towards code generation.

Without the discharging step, for example, our algorithm will typecheck `(==) (1
:: Int)` as `Eq Int => Int -> Bool`, rather than `Int -> Bool` (since it knows
`Eq Int`.)

Discharging is a pretty easy algorithm. For each `Pred`, see if it matches the
instance head of any instances you have in scope; if so, recursively discharge
all of the instance's context. If you are unable to find any matching instances,
just keep the `Pred`. For example, given the instances:

```haskell
instance Eq Int
instance (Eq a, Eq b) => Eq (a, b)
```

and a `IsInst "Eq" ("Int", "c")`, our discharge algorithm will look like this:

```
discharging: Eq (Int, c)
  try: Eq Int    --> does not match
  try: Eq (a, b) --> matches
    remove `Eq (Int, c)` pred
    match types:
      a ~ c
      b ~ Int
    discharge: Eq Int
    discharge: Eq c

discharging: Eq Int
  try: Eq Int  --> matches
  remove `Eq Int` pred

discharging: Eq c
  try: Eq Int    --> does not match
  try: Eq (a, b) --> does not match
  keep `Eq c` pred
```

We can implement this in Haskell as:

```haskell
match    :: Pred -> Pred -> TI (Maybe Subst)
getInsts :: ClassEnv -> [Qual Pred]

discharge :: ClassEnv -> Pred -> TI (Subst, [Pred])
discharge cenv p = do
  -- find matching instances and return their contexts
  matchingInstances <-
    for (getInsts cenv) $ \(qs :=> t) -> do
      -- the alternative here is to prevent emitting kind
      -- errors if we compare this 'Pred' against a
      -- differently-kinded instance.
      res <- (fmap (qs,) <$> match t p) <|> pure Nothing
      pure $ First res

  case getFirst $ mconcat matchingInstances of
    Just (qs, subst) ->
      -- match types in context
      let qs' = sub subst qs
      -- discharge context
      fmap mconcat $ traverse (discharge cenv) qs'

    Nothing ->
      -- unable to discharge
      pure (mempty, pure p)
```

Great! This works as expected, and if we want to only write a type-checker, this
is sufficient. However, we don't want to only write a type-checker, we also want
to generate code capable of using these instances too!

We can start by walking through the transformation in Haskell, and then
generalizing from there into an actual algorithm. Starting from a class
definition:

```haskell
class Functor f where
  fmap :: (a -> b) -> f a -> f b
```

we will generate a dictionary type for this class:

```haskell
data @Functor f = @Functor
  { @fmap :: (a -> b) -> f a -> f b
  }
-- =>
```

(I'm using the `@` signs here because these things are essentially type
applications. That being said, there will be no type applications in this post,
so the `@` should always be understood to be machinery generated by the
compiler for dictionary support.)

Such a definition will give us the following terms:

```haskell
@Functor :: ((a -> b) -> f a -> f b) -> @Functor f
@fmap    :: @Functor f -> (a -> b) -> f a -> f b
```

Notice that `@fmap` is just `fmap` but with an explicit dictionary (`@Functor
f`) being passed in place of the `Functor f` constraint.

From here, in order to actually construct one of these dictionaries, we can
simply inline an instances method:

```haskell
instance Functor Maybe where
  fmap = \f m -> case m of { Just x -> Just (f x); Nothing -> Nothing }

-- becomes

@Functor@Maybe :: @Functor Maybe
@Functor@Maybe =
  @Functor
  { @fmap = \f m -> case m of { Just x -> Just (f x); Nothing -> Nothing }
  }
```

Now we need to look at how these dictionaries actually get used. It's clear that
every `fmap` in our expression tree should be replaced with `@fmap d` for some
`d`. If the type of `d` is monomorphic, we can simply substitute the dictionary
we have:

```haskell
x :: Maybe Int
x = fmap (+5) (Just 10)

-- becomes

x :: Maybe Int
x = @fmap @Functor@Maybe (+5) (Just 10)
```

but what happens if the type `f` is polymorphic? There's no dictionary we can
reference statically, so we'll need to take it as a parameter:

```haskell
y :: Functor f => f Int -> f Int
y = \z -> fmap (+5) z

-- becomes

y :: @Functor f -> f Int -> f Int
y = \d -> \z -> @fmap d (+5) z
```

A reasonable question is when should we insert these lambdas to bind the
dictionaries? This stumped me for a while, but the answer is whenever you get to
a binding group; which is to say whenever your expression is bound by a
`let`, or whenever you finish processing a top-level definition.

One potential gotcha is what should happen in the case of instances with
their own contexts? For example, `instance (Eq a, Eq b) => Eq (a, b)`?  Well,
the same rules apply; since `a` and `b` are polymorphic constraints, we'll need
to parameterize our `@Eq@(,)` dictionary by the dictionaries witnessing `Eq a`
and `Eq b`:

```haskell
instance (Eq a, Eq b) => Eq (a, b) where
  (==) = \ab1 ab2 -> (==) (fst ab1) (fst ab2)
                  && (==) (snd ab1) (snd ab2)

-- becomes

@Eq@(,) :: @Eq a -> @Eq b -> @Eq (a, b)
@Eq@(,) = \d1 -> \d2 ->
  @Eq
  { (@==) = \ab1 ab2 -> (@==) d1 (fst ab1) (fst ab2)
                     && (@==) d2 (snd ab1) (snd ab2)
  }
```

Super-class constraints behave similarly.

So with all of the theory under our belts, how do we actually go about
implementing this? The path forward isn't as straight-forward as we might like;
while we're type-checking we need to desugar terms with constraints on them, but
the result of that desugaring depends on the eventual type these terms receive.

For example, if we see `(==)` in our expression tree, we want to replace it with
`(@==) d` where `d` might be `@Eq@Int`, or it might be `@Eq@(,) d1 d2`, or it
might just stay as `d`! And the only way we'll know what's what is *after* we've
performed the dischargement of our constraints.

As usual, the solution is to slap more monads into the mix:

```haskell
infer
    :: SymTable VName (Qual Type)
    -> Exp VName
    -> TI ( [Pred]
          , Type
          , Reader (Pred -> Exp VName)
                   (Exp VName)
          )
```

Our `infer` catamorphism now returns an additional `Reader (Pred -> Exp VName)
(Exp VName)`, which is to say an expression that has access to which expressions
it should substitute for each of its `Pred`s. We will use this mapping to assign
dictionaries to `Pred`s, allowing us to fill in the dictionary terms once we've
figured them out.

We're in the home stretch; now all we need to do is to have `discharge` build
that map from `Pred`s into their dictionaries and we're good to go.


```haskell
getDictTerm        :: Pred -> Exp VName
getDictTypeForPred :: Pred -> Type

-- DSL-level function application
(:@) :: Exp VName -> Exp VName -> Exp VName


discharge
    :: ClassEnv
    -> Pred
    -> TI ( Subst
          , [Pred]
          , Map Pred (Exp VName)
          , [Assump Type]
          , [Exp VName]
          )
discharge cenv p = do
  matchingInstances <-
    for (getInsts cenv) $ \(qs :=> t) -> do
      res <- (fmap (qs, t, ) <$> match t p) <|> pure Nothing
      pure $ First res

  case getFirst $ mconcat matchingInstances of
    Just (qs, t, subst) ->
      -- discharge all constraints on this instance
      (subst', qs', mapPreds, assumps, subDicts)
        <- fmap mconcat
         . traverse (discharge cenv)
         $ sub subst qs

      let dictTerm = getDictTerm t
          myDict = foldl (:@) dictTerm subDicts
      pure ( subst'
           , qs'
           , mapPreds <> M.singleton p myDict
           , assumps
           -- this is just in a list so we can use 'mconcat' to
           -- collapse our traversal
           , [myDict]
           )

    Nothing ->
      -- unable to discharge, so assume the existence of a new
      -- variable with the correct type
      param <- newVName "d"
      pure ( mempty
           , [p]
           , M.singleton p param
           , [MkAssump param $ getDictTypeForPred p]
           , [param]
           )
```

The logic of `discharge` is largely the same, except we have a little more logic
being driven by its new type. We now, in addition to our previous substitution
and new predicates, also return a map expanding dictionaries, a list of
`Assump`s (more on this in a second), and the resulting dictionary witnessing
this discharged `Pred`.

If we were successful in finding a matching instance, we discharge each of its
constraints, and fold the resulting dictionaries into ours. The more interesting
logic is what happens if we are unable to discharge a constraint. In that case,
we create a new variable of the necessary type, give that as our resulting
dictionary, and emit it as an `Assump`. `Assump`s are used to denote the
creation of a new variable in scope (they are also used for binding pattern
matches).

The result of our new `discharge` function is that we have a map from every
`Pred` we saw to the resulting dictionary for that instance, along with a list
of generated variables. We can build our final expression tree via running the
`Reader (Pred -> Exp VName)` by looking up the `Pred`s in our dictionary map.
Finally, for every assumption we were left with, we fold our resulting term in a
lambda which binds that assumption.

Very cool! If you're interested in more of the nitty-gritty details behind
compiling Haskell98, feel free to [SMASH THAT STAR BUTTON on Github.][cccc]

[cccc]: https://github.com/isovector/cccc


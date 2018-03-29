---
layout: post
title: Higher Kinded Data
date: TO_BE_DETERMINED
comments: true
tags: haskell, technical, programming
---

Today I want to demonstrate a "well-known" Haskell technique among library
authors, that I haven't ever seen written down. It allows you to do all sorts of
amazing things, such as: generate lenses for arbitrary data-types without
resorting to TemplateHaskell, `sequence` over data-types, and automatically
track dependencies for usages of record fields. We'll build the first two
examples here today, but the approach generalizes further.

For our examples, let's define the following (completely arbitrary) data-type:

```haskell
data Person = Person
  { pName :: String
  , pAge  :: Int
  } deriving (Generic)
```

That's cool and all. For purposes of discussion, let's say we want to let the
user fill in a `Person` via a web-form or something. Which is to say, it's
possible they'll screw up filling in some piece of information without
necessarily invalidating the rest of the datastructure. If they successfully
filled in the entire structure, we'd like to get a `Person` out.

One way of modeling this would be with a second datatype:

```haskell
data MaybePerson = MaybePerson
  { mpName :: Maybe String
  , mpAge  :: Maybe Int
  } deriving (Generic)
```

and a function:

```haskell
validate :: MaybePerson -> Maybe Person
validate (MaybePerson name age) =
  Person <$> name <*> age
```

This works, but it's annoying to write by hand, since it's completely
mechanical. Furthermore, having duplicated this effort means we'll need to use
our brains in the future to make sure all three definitions stay in sync.
Wouldn't it be cool if the compiler could help with this?

SURPRISE! IT CAN! And that's what I want to talk about today.

Notice that we can describe both `Person` and `MaybePerson` with the following
higher-kinded data (henceforth "**HKD**") definition:

```haskell
data Person' (f :: * -> *) = Person
  { pName :: f String
  , pAge  :: f Int
  } deriving (Generic)
```

Here we've parameterized `Person'` over something of kind `* -> *`, which allows
us to do the following in order to get our original types back:

```haskell
type Person      = Person' Identity
type MaybePerson = Person' Maybe
```

While this works, it's kind of annoying in the `Person` case, since now all of
our data is wrapped up inside of an `Identity`:

```
> :t pName @Identity
pName :: Person -> Identity String

> :t runIdentity . pName
runIdentity . pName :: Person -> String
```

We can fix this annoyance relatively trivially, after which we will look at why
defining `Person'` as such is actually useful. To get rid of the `Identity`s, we
can use a type-family that erases them:

```haskell
{-# LANGUAGE TypeFamilies #-}

-- "Higher-Kinded Data"
type family HKD f a where
  HKD Identity a = a
  HKD f        a = f a

data Person' (f :: * -> *) = Person
  { pName :: HKD f String
  , pAge  :: HKD f Int
  } deriving (Generic)
```

Using the `HKD` type family means that GHC will magically erase any `Identity`:

```
> :t pName @Identity
pName :: Person -> String

> :t pName @Maybe
pName :: Person -> Maybe String
```

and with that, the higher-kinded version of `Person` can be used as a drop-in
replacement for our original one. The obvious question is what have we bought
ourselves with all of this work. Let's look back at `validate` to help us answer
this question. We can rewrite it using our new `Person'` machinery:

```haskell
validate :: Person' Maybe -> Maybe Person
validate (Person name age) =
  Person <$> name <*> age
```

Interestingly enough, only our type and pattern match needed to change from our
original implementation. The neat thing is, now that we have consolidated
`Person` and `MaybePerson`, we can write a version of `validate` that will work
for any higher-kinded datatype.

We turn to [`GHC.Generics`][generics]. If you're unfamiliar with them, they
provide an isomorphism from a regular Haskell datatype to a generic
representation that can be manipulated by a clever programmer (ie: us.)

[generics]: https://www.stackage.org/haddock/lts-11.0/base-4.10.1.0/GHC-Generics.html

To start, we need to define a typeclass that will be the workhorse of our
transformation. In my experience, this is always the hardest part -- the types
of these generic-transforming functions are exceptionally abstract and in my
opinion, very hard to reason about. I came up with this:

```haskell
{-# LANGUAGE MultiParamTypeClasses #-}

class GFlay i o where
  gflay :: i p -> Maybe (o p)
```

It's called `flay` due to its similarity with the [flay][flay] package (although
this package uses a different method.)

[flay]: https://hackage.haskell.org/package/flay-0.2/docs/Flay.html

I only have "soft-and-slow" rules for reasoning about what your typeclass should
look like, but in general you're going to need both an `i`nput and an `o`utput
parameter. They both need to be of kind `* -> *` and then be passed this
existentialized `p`, for dark, unholy reasons known not by humankind. I then
have a little checklist I walk through to help me wrap my head around this
nightmarish hellscape:

* *Is my return type something other than just a differently-parameterized HKD?*
  If so, factor that return type into the typeclass method (seen here by the
  `Maybe` in my signature).
* *Is there recursion anywhere in my HKD?* If so, I need to add a type parameter
  `z :: * -> *` to the typeclass, such that `z` is the original higher-kinded
  datatype I'm working over.
* *Do I need to pull data out of my original `z`?* If so, I need to add a
  parameter to my method of type `z Identity -> i p`, which acts as a selector
  that I can build inductively.

Anyway, now it's just a matter of writing out instances of our typeclass for the
various GHC.Generic types. We can start with the base case, which is we should
be able to flay a `Maybe k`:

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}

instance GFlay (K1 a (Maybe k)) (K1 a k) where
  -- gflay :: K1 a (Maybe k) -> Maybe (K1 a k)
  gflay (K1 k) = K1 <$> k
  {-# INLINE gflay #-}
```

And most of the time, the rest is to just mechanically provide instances for the
other types. Unless you need to access metadata about the original type
anywhere, these instances will always be trivial homomorphisms.

We can start with products -- if we have `GFlay i o` and `Gflay i' o'`, we
should be able to run them in parallel:

```haskell
instance (GFlay i o, GFlay i' o')
    => GFlay (i :*: i') (o :*: o') where
  gflay (l :*: r) = (:*:) <$> gflay l <*> gflay r
  {-# INLINE gflay #-}
```

Likewise for coproducts:

```haskell
instance (GFlay i o, GFlay i' o')
    => GFlay (i :+: i') (o :+: o') where
  gflay (L1 l) = L1 <$> gflay l
  gflay (R1 r) = R1 <$> gflay r
  {-# INLINE gflay #-}
```

Furthermore, if we don't care about looking at metadata, we can simply lift a
`GFlay i o` over the metadata constructor:

```haskell
instance GFlay i o
    => GFlay (M1 _a _b i) (M1 _a' _b' o) where
  gflay (M1 x) = M1 <$> gflay x
  {-# INLINE gflay #-}
```

and then just for kicks, we can provide the following trivial instances, for
uninhabited types (`V1`) and for constructors without any parameters (`U1`):

```haskell
instance GFlay V1 V1 where
  gflay = undefined
  {-# INLINE gflay #-}

instance GFlay U1 U1 where
  gflay U1 = Just U1
  {-# INLINE gflay #-}
```

The use of `undefined` here is safe, since it can never be called anyway.

With all of this machinery out of the way, we can finally write a non-generic
version of `flay`:

```haskell
{-# LANGUAGE FlexibleContexts #-}

flay
    :: ( Generic (f Maybe)
       , Generic (f Identity)
       , GFlay (Rep (f Maybe))
               (Rep (f Identity))
       )
    => f Maybe
    -> Maybe (f Identity)
flay = fmap to . gflay . from
```

I always get a goofy smile when the signature for my function is longer than the
actual implementation; it means we've hired the compiler to write code for us.
What's neat about `flay` here is that it doesn't have any mention of `Person'`;
this function will work for *any* type defined as higher-kinded data. Spiffy.

---

Let's look at a more involved example of what we can do if our data is HKD --
generate lenses for it. The following example is heavily based on [Travis
Athougies][travis]' fantastic library [beam][beam], which is where I originally
learned all of this this HKD tomfoolery. Thanks, Travis -- you da man!

[travis]: http://travis.athougies.net/
[beam]: http://travis.athougies.net/projects/beam.html

So, we'd like to be able to generate lenses for all products in a HKD record.
We'll begin by thinking about what we'll need to instantiate our HKD parameter
as in order to make this happen. Recall, our `Person'` type:

```haskell
data Person' (f :: * -> *) = Person
  { pName :: f String
  , pAge  :: f Int
  } deriving (Generic)
```

By substituting `f ~ Lens' (Person' Identity)`, we'll have `pName :: Lens'
(Person' Identity) String`, which is exactly the type we want. Good start. Our
next step is to design the typeclass we'll use to generate this information.

We realize a few things here -- we should be able to generate these lenses *ex
nihilo*, which is to say, we won't need a `Person' Identity` to get the ball
rolling here. Therefore our typeclass method won't need an `i p` parameter.

But, we are going to be doing structural induction. Which means that we need
some way of "tracking" where we are in the type. Since we want to be generating
lenses at the end of the day, the most obvious way of doing this is to construct
a lens as we go, capable of getting us from `Person' Identity` to our current
point in the type induction. We'll add this lens as a parameter to our method.

At the end of the day, our `GLenses` typeclass looks like this:

```haskell
{-# LANGUAGE RankNTypes #-}

class GLenses z i o where
  glenses :: Lens' (z Identity) (i p) -> o p
```

which we can interpret as "if you give me a lens from `z Identity` to the point
in the induction I'm working over, I can give you the desired output type." Like
in our `flay` example, we'll keep `i` and `o` in tight lock-step.

We begin with a helper definition:

```haskell
data LensFor t x = LensFor (Lens' t x)
```

which hides the existentialized functor inside the definition of `Lens'`. This
is some necessary bookkeeping because GHC won't allow us to have rank-N
polymorphic instances. If you don't understand what that means, don't worry --
it's not important.

So, with this knowledge, we can write our base case. We want to transform a
constant type into a lens which will get back that constant type.

```haskell
instance GLenses z (K1 _x a)
                   (K1 _x (LensFor (z Identity) a)) where
  glenses l = K1 $ LensFor $ \f -> l $ fmap K1 . f . unK1
  {-# INLINE glenses #-}
```

Our transformation here will turn an `a` somewhere in our datatype into a
`LensFor (z Identity) a` -- aka a `Lens' (z Identity) a`. The actual
implementation isn't particularly interesting, I just played
[type-tetris][tetris] until it compiled.

[tetris]: /blog/love-types

And now for our induction. The general idea here is that we're going to need to
transform the lens we got into a new lens that focuses down through our generic
structure as we traverse it. We can look at the `M1` case because it's quite
trivial:

```haskell
instance (GLenses z i o)
    => GLenses z (M1 _a _b i) (M1 _a _b o) where
  glenses l = M1 $ glenses $ \f -> l $ fmap M1 . f . unM1
  {-# INLINE glenses #-}
```

All we do here is construct a lens that zooms in on the `M1` constructor, pass
it to `glenses`, and then wrap the result of that in our own `M1` constructor.
Wrapping it ourselves is what allows us to generate a value at the end of the
day.

The instance for products is similar, though a little messier since we don't
have helper functions to map over `(:*:)`:

```haskell
instance (GLenses z i o, GLenses z i' o')
    => GLenses z (i :*: i') (o :*: o') where
  glenses l = glenses (\f -> l (\(a :*: b) -> (:*: b) <$> f a))
          :*: glenses (\f -> l (\(a :*: b) -> (a :*:) <$> f b))
  {-# INLINE glenses #-}
```

Again, the implementation here was mostly type-tetris and a healthy amount of
copy-pasting code from `beam`.

It's worth noting that we are unable to provide an instance of `GLenses` for
`(:+:)`, since lenses are not defined over coproducts. This is no problem for us
and our `Person'` example, but it will in fact explode at compile time if you
try to generate lenses for a type that has coproducts.

With this out of the way, we need to write our function that will use all of the
generic machinery and provide a nice interface to all of this machinery. We're
going to need to call `glenses` (obviously), and pass in a `Lens' (z Identity)
(Rep (z Identity))` in order to get the whole thing running. Then, once
everything is build, we'll need to call `to` to turn our generic representation
back into the HKD representation.

But how can we get a `Lens'(z Identity) (Rep (z Identity))`? Well, we know that
`GHC.Generics` gives us an isomorphism between a type and its `Rep`, as
witnessed by `to` and `from`. We further know that every `Iso` is indeed a
`Lens`, and so the lens we want is just `iso from to`. Our function, then, is
"simply":

```haskell
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

getLenses
    :: forall z
     . ( Generic (z Identity)
       , Generic (z (LensFor (z Identity)))
       , GLenses z (Rep (z Identity))
                   (Rep (z (LensFor (z Identity))))
       )
    => z (LensFor (z Identity))
getLenses = to $ glenses @z $ iso from to
```

where I just wrote the `z (LensFor (z Identity))` part of the type signature,
and copy-pasted constraints until the compiler was happy.

OK, so let's take it for a spin, shall we? We can get our lenses thusly:

```haskell
Person (LensFor lName) (LensFor lAge) = getLenses
```

Yay! Finally we can ask GHCi for their types, which is a surprisingly satisfying
experience:

```
> :t lName
lName :: Lens' (Person' Identity) String
```

Pretty sweet, huh? Now that `getLenses` has been implemented generically, it can
become library code that will work for any product-type we can throw at it.
Which means free lenses without `TemplateHaskell` for any types we define in the
HKD form.

This pattern is useful enough that I've begun implement literally all of my
"data" (as opposed to "control") types as higher-kinded data. With an extra type
synonym `type X = X' Identity`, and `{-# LANGUAGE TypeSynonymInstances #-}`,
nobody will ever know the difference, except that it affords me the ability to
all of this stuff in the future if I want it.

As [Conal][deno] says, it might not necessarily be "for free" but at least it's
"already paid for."

[deno]: https://www.youtube.com/watch?v=bmKYiUOEo2A


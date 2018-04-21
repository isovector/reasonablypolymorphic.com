---
layout: post
title: "Higher-Kinded Data"
date: 2018-03-29 23:23
comments: true
tags: haskell, technical, programming, hkd
---

Today I want to demonstrate a "well-known" Haskell technique among library
authors, that I haven't ever seen written down. It allows you to do all sorts of
amazing things, such as: generate lenses for arbitrary data-types without
resorting to TemplateHaskell; `sequence` over data-types; and automatically
track dependencies for usages of record fields.

As for this post, we'll look at how to build type-level sequencing, and
investigate some other uses in subsequent ones. For our examples, let's define
the following (completely arbitrary) data-type:

```haskell
data Person = Person
  { pName :: String
  , pAge  :: Int
  } deriving (Generic)
```

That's cool and all, I guess. For purposes of discussion, let's imagine that we
want to let the user fill in a `Person` via a web-form or something. Which is to
say, it's possible they'll screw up filling in some piece of information without
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
data Person' f = Person
  { pName :: f String
  , pAge  :: f Int
  } deriving (Generic)
```

Here we've parameterized `Person'` over something `f` (of kind `* -> *`), which
allows us to do the following in order to get our original types back:

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

We can fix this annoyance trivially, after which we will look at why defining
`Person'` as such is actually useful. To get rid of the `Identity`s, we can use
a type family (a function at the type-level) that erases them:

```haskell
{-# LANGUAGE TypeFamilies #-}

-- "Higher-Kinded Data"
type family HKD f a where
  HKD Identity a = a
  HKD f        a = f a

data Person' f = Person
  { pName :: HKD f String
  , pAge  :: HKD f Int
  } deriving (Generic)
```

Using the `HKD` type family means that GHC will automatically erase any
`Identity` wrappers in our representations:

```
> :t pName @Identity
pName :: Person -> String

> :t pName @Maybe
pName :: Person -> Maybe String
```

and with that, the higher-kinded version of `Person` can be used as a drop-in
replacement for our original one. The obvious question is what have we bought
ourselves with all of this work. Let's look back at `validate` to help us answer
this question. Compare our old implementation:

```haskell
validate :: MaybePerson -> Maybe Person
validate (MaybePerson name age) =
  Person <$> name <*> age
```

with how we can now rewrite it with our new machinery:

```haskell
validate :: Person' Maybe -> Maybe Person
validate (Person name age) =
  Person <$> name <*> age
```

Not a very interesting change is it? But the intrigue lies in how little needed
to change. As you can see, only our type and pattern match needed to change from
our original implementation. What's neat here is that we have now consolidated
`Person` and `MaybePerson` into the same representation, and therefore they are
no longer related only in a nominal sense.

We can write a version of `validate` that will work for any higher-kinded
datatype.

The secret is to turn to [`GHC.Generics`][generics]. If you're unfamiliar with
them, they provide an isomorphism from a regular Haskell datatype to a generic
representation that can be structurally manipulated by a clever programmer (ie:
us.) By providing code for what to do for constant types, products and
coproducts, we can get GHC to write type-independent code for us. It's a really
neat technique that will tickle your toes if you haven't seen it before.

[generics]: https://www.stackage.org/haddock/lts-11.0/base-4.10.1.0/GHC-Generics.html

To start with, we need to define a typeclass that will be the workhorse of our
transformation. In my experience, this is always the hardest part -- the types
of these generic-transforming functions are exceptionally abstract and in my
opinion, very hard to reason about. I came up with this:

```haskell
{-# LANGUAGE MultiParamTypeClasses #-}

class GValidate i o where
  gvalidate :: i p -> Maybe (o p)
```

I only have "soft-and-slow" rules for reasoning about what your typeclass should
look like, but in general you're going to need both an `i`nput and an `o`utput
parameter. They both need to be of kind `* -> *` and then be passed this
existentialized `p`, for dark, unholy reasons known not by humankind. I then
have a little checklist I walk through to help me wrap my head around this
nightmarish hellscape that we'll walk through in a later installment of the
series.

Anyway, with our typeclass in hand, it's now just a matter of writing out
instances of our typeclass for the various GHC.Generic types. We can start with
the base case, which is we should be able to validate a `Maybe k`:

```haskell
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators     #-}

instance GValidate (K1 a (Maybe k)) (K1 a k) where
  -- gvalidate :: K1 a (Maybe k) -> Maybe (K1 a k)
  gvalidate (K1 k) = K1 <$> k
  {-# INLINE gvalidate #-}
```

`K1` represents a "constant type", which is to say that it's where our
structural recursion conks out. In our `Person'` example, it's the `pName :: HKD
f String` bit.

Most of the time, once you have the base case in place, the rest is to just
mechanically provide instances for the other types. Unless you need to access
metadata about the original type anywhere, these instances will almost always be
trivial homomorphisms.

We can start with products -- if we have `GValidate i o` and `GValidate i' o'`,
we should be able to run them in parallel:

```haskell
instance (GValidate i o, GValidate i' o')
    => GValidate (i :*: i') (o :*: o') where
  gvalidate (l :*: r) = (:*:)
                    <$> gvalidate l
                    <*> gvalidate r
  {-# INLINE gvalidate #-}
```

If `K1` referred directly to the selectors of our `Person'`, `(:*:)` corresponds
roughly to the `,` piece of syntax we separate our record fields with.

We can define a similar instance of `GValidate` for coproducts (corresponding to
a `|` in a data definition):

```haskell
instance (GValidate i o, GValidate i' o')
    => GValidate (i :+: i') (o :+: o') where
  gvalidate (L1 l) = L1 <$> gvalidate l
  gvalidate (R1 r) = R1 <$> gvalidate r
  {-# INLINE gvalidate #-}
```

Furthermore, if we don't care about looking at metadata, we can simply lift a
`GValidate i o` over the metadata constructor:

```haskell
instance GValidate i o
    => GValidate (M1 _a _b i) (M1 _a' _b' o) where
  gvalidate (M1 x) = M1 <$> gvalidate x
  {-# INLINE gvalidate #-}
```

Just for kicks, we can provide the following trivial instances, for uninhabited
types (`V1`) and for constructors without any parameters (`U1`):

```haskell
instance GValidate V1 V1 where
  gvalidate = undefined
  {-# INLINE gvalidate #-}

instance GValidate U1 U1 where
  gvalidate U1 = Just U1
  {-# INLINE gvalidate #-}
```

The use of `undefined` here is safe, since it can only be called with a value of
`V1`. Fortunately for us, `V1` is uninhabited, so this can never happen, and
thus we're morally correct in our usage of `undefined`.

Without further ado, now that we have all of this machinery out of the way, we
can finally write a non-generic version of `validate`:

```haskell
{-# LANGUAGE FlexibleContexts #-}

validate
    :: ( Generic (f Maybe)
       , Generic (f Identity)
       , GValidate (Rep (f Maybe))
                   (Rep (f Identity))
       )
    => f Maybe
    -> Maybe (f Identity)
validate = fmap to . gvalidate . from
```

I always get a goofy smile when the signature for my function is longer than the
actual implementation; it means we've hired the compiler to write code for us.
What's neat about `validate` here is that it doesn't have any mention of
`Person'`; this function will work for *any* type defined as higher-kinded data.
Spiffy.

That's all for today, folks. We've been introduced to the idea of higher-kinded
data, seen how it's completely equivalent with a datatype defined in a more
traditional fashion, and also caught a glimmer of what kind of things are
possible with this approach. This is where we stop for today, but in the next
post we'll look at how we can use the HKD approach to generate lenses without
resorting to TemplateHaskell.

Happy higher-kinding!

---

Big shoutouts to [Travis Athougies][travis] from whom I originally learned this
technique, and to [Ariel Weingarten][ariel] and [Fintan Halpenny][fintan] for
proofreading earlier versions of this post.

[travis]: http://travis.athougies.net/
[ariel]: https://github.com/asweingarten
[fintan]: https://github.com/FintanH


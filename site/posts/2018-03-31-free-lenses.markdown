---
layout: post
title: "Free Lenses for Higher-Kinded Data"
date: 2018-03-31 12:42
comments: true
tags: haskell, technical, programming, hkd
---

In the [previous blog post][hkd], we discussed *higher-kinded data* (HKD), the
technique of parameterizing your data types by something of kind `* -> *`, and
subsequently wrapping each of its fields by this parameter. The example we used
previously was transforming this type:

[hkd]: /blog/higher-kinded-data

```haskell
data Person = Person
  { pName :: String
  , pAge  :: Int
  } deriving (Generic)
```

into its HKD representation:

```haskell
data Person' f = Person
  { pName :: HKD f String
  , pAge  :: HKD f Int
  } deriving (Generic)
```

Recall that `HKD` is a type family given by

```haskell
type family HKD f a where
  HKD Identity a = a
  HKD f        a = f a
```

which is responsible for stripping out an `Identity` wrapper. This means we can
recreate our original `Person` type via `type Person = Person' Identity`, and
use it in all the same places we used to be able to.

Our previous exploration of the topic unearthed some rather trivial applications
of this approach; we generated a function `validate :: f Maybe -> Maybe (f
Identity)` which can roughly be described as a "type-level `sequence`." In fact,
in the comments, [Syrak][syrak] pointed out we can implement this function in a
less-round-about way via `gtraverse id`.

[syrak]: https://www.reddit.com/r/haskell/comments/884pe0/higherkinded_data_reasonably_polymorphic/dwi0a0f/

So, how about we do something a little more interesting today? Let's generate
lenses for arbitrary product types.

In my opinion, one of the biggest advantages of the HKD approach is it answers
the question "where can we put this stuff we've generated?" Generating lenses
generically is pretty trivial (once you have wrapped your head around the
mind-boggling types), but the harder part is where to put it. The [`lens`][lens]
package uses TemplateHaskell to generate new top-level bindings so it has
somewhere to put the lenses. But we have HKD.

[lens]: https://hackage.haskell.org/package/lens

Recall, our `Person'` type:

```haskell
data Person' f = Person
  { pName :: HKD f String
  , pAge  :: HKD f Int
  } deriving (Generic)
```

By substituting `f ~ Lens' (Person' Identity)`, we'll have `pName :: Lens'
(Person' Identity) String`, which is exactly the type we need. All of a sudden
it looks like we have an answer to "where should we put it": inside our original
structure itself. If we can generate a record of type `Person' (Lens' (Person'
Identity)`, destructuring such a thing will give us the lenses we want, allowing
us to name them when we do the destructuring. Cool!

Unfortunately, we're unable to partially apply type-synonyms, so we'll need to
introduce a new type constructor that we *can* partially apply. Enter
`LensesFor`:

```haskell
data LensFor s a = LensFor
  { getLensFor :: Lens' s a
  }
```

The next step is to *think really hard* about what our lens-providing type-class
should look like. At the risk of sounding like a scratched CD in a walkman, I
consider the design of the typeclass to be by far the hardest part of this
approach. So we'll work through the derivation together:

I always begin with my "template" generic-deriving class:

```haskell
class GLenses i o where
  glenses :: i p -> o p
```

where `p` is a mysterious existentialized type parameter "reserved for future
use" by the `GHC.Generics` interface. Recall that `i` is the incoming type for
the transformation (*not* the original `Person'` type), and `o` is
correspondingly the output type of the transformation.

Since lenses don't depend on a particular "input" record -- they should be able
to be generated *ex nihilo* -- we can drop the `i p` parameter from `glenses`.
Furthermore, since eventually our lenses are going to depend on our "original"
type (the `Person'` in our desired `LensesFor (Person' Identity)`), we'll need
another parameter in our typeclass to track that. Let's call it `z`.

```haskell
class GLenses z i o where
  glenses :: o p
```

As far as methods go, `glenses` is pretty unsatisfactory right now; it leaves
most of its type parameters ambiguous. No good. We can resolve this issue by
realizing that we're going to need to actually provide lenses at the end of the
day, and because `GHC.Generics` doesn't give us any such functionality, we'll
need to write it ourselves. Which implies we're going to need to do structural
induction as we traverse our generic `Rep`resentation.

The trick here is that in order to provide a lens, we're going to need to have a
lens to give. So we'll add a `Lens'` to our `glenses` signature -- but what type
should it have? At the end of the day, we want to provide a `Lens' (z Identity)
a` where `a` is the type of the field we're trying to get. Since we always want
a lens starting from `z Identity`, that pins down one side of our lens
parameter.

```haskell
class GLenses z i o where
  glenses :: Lens' (z Identity) _ -> o p
```

We still have the notion of an `i`nput to our `glenses`, which we want to
transform into our `o`utput. And that's what tears it; if we have a lens from
our original type where we currently are in our Generic traversal, we can
transform that into a Generic structure which contains the lenses we want.

```haskell
class GLenses z i o where
  glenses :: Lens' (z Identity) (i p) -> o p
```

Don't worry if you're not entirely sure about the reasoning here; I wasn't
either until I worked through the actual implementation. It took a few
iterations to get right. Like I said, figuring out what this method should look
like is by far the hardest part. Hopefully going through the rest of the
exercise will help convince us that we got our interface correct.

With our typeclass pinned down, we're ready to begin our implementation. We
start, as always, with the base case, which here is "what should happen if we
have a `K1` type?" Recall a `K1` corresponds to the end of our generic
structural induction, which is to say, this is a type that isn't ours. It's the
`HKD f String` in `pName :: HKD f String` from our example.

So, if we have an `a` wrapped in a `K1`, we want to instead produce a `LensFor
(z Identity) a` wrapped in the same.

```haskell
instance GLenses z (K1 _x a)
                   (K1 _x (LensFor (z Identity) a)) where
  glenses l = K1                            -- [3]
            $ LensFor                       -- [2]
            $ \f -> l $ fmap K1 . f . unK1  -- [1]
  {-# INLINE glenses #-}
```

Egads there's a lot going on here. Let's work through it together. In [1], we
transform the lens we were given (`l`) so that it will burrow through a `K1`
constructor -- essentially turning it from a `Lens' (z Identity) (K1 _x a)` into
a `Lens' (z Identity) a`. At [2], we wrap our generated lens in the `LensFor`
constructor, and then in [3] we wrap our generated lens back in the
`GHC.Generics` machinery so we can transform it back into our HKD representation
later.

And now for our induction. The general idea here is that we're going to need to
transform the lens we got into a new lens that focuses down through our generic
structure as we traverse it. We can look at the `M1` case because it's
babby's first instance when compared to `K1`:

```haskell
instance (GLenses z i o)
    => GLenses z (M1 _a _b i) (M1 _a _b o) where
  glenses l = M1 $ glenses $ \f -> l $ fmap M1 . f . unM1
  {-# INLINE glenses #-}
```

Here we're saying we can lift a `GLenses z i o` over an `M1` constructor by
calling `glenses` with an updated lens that will burrow through the `M1`-ness.
This transformation is completely analogous to the one we did for `K1`. Once we
have our generated lenses, we need to re-wrap the structure in an `M1`
constructor so we can transform it back into our HKD representation.

The product case looks a little trickier, but it's only because `GHC.Generics`
doesn't provide us with any useful un/wrapping combinators for the `(:*:)`
constructor.

```haskell
instance (GLenses z i o, GLenses z i' o')
    => GLenses z (i :*: i') (o :*: o') where
  glenses l = glenses (\f -> l (\(a :*: b) -> fmap (:*: b) $ f a))
          :*: glenses (\f -> l (\(a :*: b) -> fmap (a :*:) $ f b))
  {-# INLINE glenses #-}
```

We finish it off with the trivial instances for `V1` and `U1`:

```haskell
instance GLenses z V1 V1 where
  glenses l = undefined

instance GLenses z U1 U1 where
  glenses l = U1
```

And voila! Our induction is complete. Notice that we *did not* write an instance
for `(:+:)` (coproducts), because lenses are not defined for coproduct types.
This is fine for our `Person'` case, which has no coproducts, but types that do
will simply be unable to find a `GLenses` instance, and will fail to compile. No
harm, no foul.

With this out of the way, we need to write our final interface that will use all
of the generic machinery and provide nice access to all of this machinery. We're
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
and copy-pasted constraints from the error messages until the compiler was
happy.

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

Pretty sweet, ne? Now that `getLenses` has been implemented generically, it can
become library code that will work for any product-type we can throw at it.
Which means free lenses without TemplateHaskell for any types we define in the
HKD form.

This HKD pattern is useful enough that I've begun implement literally all of my
"data" (as opposed to "control") types as higher-kinded data. With an extra type
synonym `type X = X' Identity`, and `{-# LANGUAGE TypeSynonymInstances #-}`,
nobody will ever know the difference, except that it affords me the ability to
use all of this stuff in the future should I want to.

As [Conal][deno] says, all of this stuff might not necessarily be "for free" but
at the very least, it's "already paid for."

[deno]: https://www.youtube.com/watch?v=bmKYiUOEo2A

---

More shoutouts to [Travis Athougies][travis], whose sweet library [beam][beam]
uses this approach to generate lenses for working with SQL tables. I consulted
the [beam source][src] more than a couple times in writing this post. Thanks
again, Travis!

[travis]: http://travis.athougies.net/
[beam]: http://travis.athougies.net/projects/beam.html
[src]: https://github.com/tathougies/beam


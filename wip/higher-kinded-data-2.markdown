---
layout: post
title: Higher Kinded Data
date: TO_BE_DETERMINED
comments: true
tags: haskell, technical, programming
---

* *Is my return type something other than just a differently-parameterized HKD?*
  If so, factor that return type into the typeclass method (seen here by the
  `Maybe` in my signature).
* *Is there recursion anywhere in my HKD?* If so, I need to add a type parameter
  `z :: * -> *` to the typeclass, such that `z` is the original higher-kinded
  datatype I'm working over.
* *Do I need to pull data out of my original `z`?* If so, I need to add a
  parameter to my method of type `z Identity -> i p`, which acts as a selector
  that I can build inductively.

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
data Person' f = Person
  { pName :: HKD f String
  , pAge  :: HKD f Int
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


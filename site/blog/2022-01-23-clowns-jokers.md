---
layout: post
title: "Review: Clowns to the Left of Me, Jokers to the Right"
date: 2022-01-23 13:49
comments: true
tags: review, mcbride, recursion schemes, types
---

Another week, another paper. This week it's McBride's [Clowns to the Left of Me,
Jokers to the Right][cj] (CJ). At a high level, CJ generalizes the results from
[The Derivative of a Regular Type is its Type of One-Hole Contexts][onehole],
wondering about what happens to a zipper when we don't require the elements on
either side to have the same type. This turns out to be not just an idle
curiosity; the technique can be used to automatically turn a
[catamorphism][cata] into a tail-recursive function. Why is THAT useful? It lets
us run functional programs on stock hardware.

[cj]: http://strictlypositive.org/CJ.pdf
[onehole]: http://strictlypositive.org/diff.pdf
[cata]: /blog/recursion-schemes

The paper begins by reminding us that all algebraic types can be built out of
compositions of functors. Furthermore, any recursive ADT can be represented as
the fix-point of its base functor. For example, rather than writing

```haskell
data Expr = Val Int | Add Expr Expr
```

we can instead pull the recursive inlining of `Expr` out into a type argument:

```haskell
data ExprF a = ValF Int | AddF a a
```

and then can tie the knot:

```haskell
newtype Fix f = Fix { unFix :: f (Fix f) }

type Expr ~= Fix ExprF
```

This is all standard [bananas and barbed wires][cata], machinery, so refer to
that if you'd like a deeper presentation than I've provided here.

Rather than go through the paper's presentation of this section, I will merely
point out that `GHC.Generics` witnesses the "all ADTs can be built out of
functor composition," and give `ExprF` a `Generic1` instance:

```haskell
data ExprF a = ValF Int | AddF a a
  deriving stock (Functor, Generic1)
```


## Clowns and Jokers

The title of CJ is a throw-back to [some boomer
song](https://www.youtube.com/watch?v=8StG4fFWHqg), whose lyrics go

> Clowns to the left of me!
> Jokers to the right!
> Here I am stuck in the middle with you.

while this is an apt idea for what's going on in the paper, it's also an awful
mnemonic for those of us who don't have strong associations with the song. My
mnemonic is that "clowns" come sooner in a lexicographical ordering than
"jokers" do. Likewise, work you've already done comes before work you haven't
yet done, which is *really* what CJ is about.

So here's the core idea of CJ: we can "dissect" a traversal into work we've
already done, and work we haven't yet done. The work we've already done can have
a different type than the stuff left to do. These dissections are a rather
natural way of representing a suspended computation. Along with the dissection
itself is the ability to make progress. A dissection is spiritually a zipper
with different types on either side, so we can make progress by transforming the
focused element from "to-do" to "done", and then focusing on the next element
left undone.

CJ implements all of this as a typeclass with fundeps, but I prefer type
families. And furthermore, since this is all generic anyway, why not implement
it over `GHC.Generics`? So the game here is thus to compute the type of the
dissection for each of the `Generic1` constructors.

Begin by building the associated type family. The dissected version of a functor
is necessarily a bifunctor, since we want slots to store our clowns and our
jokers:

```haskell
class GDissectable p where
  type GDissected p :: Type -> Type -> Type
```

As usual, we lift `GDissectable` over `M1`:

```haskell
instance GDissectable f => GDissectable (M1 _1 _2 f) where
  type GDissected (M1 _1 _2 f) = GDissected f
```

Because a dissection is a separation of the work we have and haven't done yet,
the cases for `U1` and `K1` are uninspired --- there is no work to do, since
they're constants!

```haskell
instance GDissectable U1 where
  type GDissected U1 = K2 Void

instance GDissectable (K1 _1 a) where
  type GDissected (K1 _1 a) = K2 Void
```

where `K2` is the constant bifunctor:

```haskell
data K2 a x y = K2 a
```

A different way to think about these dissections is as generalized zippers,
which are the derivatives of their underlying types. Since `U1` and `K1` are
constants, their derivatives are zero, which we have  shown here via `K2 Void`.

The `Par1` generic constructor is used to encode usages of the functor's type
parameter. Under the view of the derivative, this is a linear use of the
variable, and thus its derivative is one:

```haskell
instance GDissectable Par1 where
  type GDissected Par1 = K2 ()
```

We're left with sums and products. Sums are easy enough: the dissection of the
sum is the sum of the dissections.

```haskell
instance (GDissectable f, GDissectable g) => GDissectable (f :+: g) where
  type GDissected (f :+: g) = Sum2 (GDissected f) (GDissected g)
```

where

```haskell
data Sum2 f g a b = L2 (f a b) | R2 (g a b)
```

Again, this aligns with our notion of the derivative, as well as with our
intuition. If I want to suspend a coproduct computation half way, I either have
an `L1` I need to suspend, or I have an `R1`. Nifty.

Finally we come to products:

```haskell
instance (GDissectable f, GDissectable g) => GDissectable (f :*: g) where
  type GDissected (f :*: g) =
    Sum2 (Product2 (GDissected f) (Joker g))
         (Product2 (Clown f) (GDissected g))
```

where

```haskell
data Clown p a b = Clown (p a)
data Joker p a b = Joker (p b)
data Product2 f g a b = Product2 (f a b) (g a b)
```

Let's reason by intuition here first. I have both an `f` and a `g` stuck
together. If I'd like to suspend a traversal through this thing, either I am
suspended in the `f`, with `g` not yet touched (`Joker g`), or I have made it
through the `f` entirely (`Clown f`), and have suspended inside of `g`.

Rather unsurprisingly (but also surprisingly, depending on your point of view!),
this corresponds exactly to the quotient chain rule:

$$
\frac{d}{dx}[f(x)\cdot{}g(x)] = f(x)\cdot{}g'(x) + f'(x)\cdot{}g(x)
$$

Curry-Howard strikes in the most interesting of places!


## Getting Started

With our dissected types defined, it's now time to put them to use. The paper
jumbles a bunch of disparate pieces together, but I'm going to split them up for
my personal understanding. The first thing we'd like to be able to do is to
begin traversing a structure, which is to say, to split it into its first
`joker` and the resulting dissection.

We'll make a helper structure:

```haskell
data Suspension p k c j
  = Done (p c)
  | More j (k c j)
  deriving Functor
```

A `Suspension p k c j` is either a `p` fully saturated with clowns (that is,
we've finished traversing it), or a joker and more structure (`k c j`) to be
traversed. `k` will always be `GDissected p`, but for technical reasons, we're
going to need to keep it as a second type parameter.

Armed with `Suspension`, we're ready to add our first method to `GDissectable`.
`gstart` takes a fully-saturated `p j` and gives us back a suspension:

```haskell
class GDissectable p where
  type GDissected p :: Type -> Type -> Type
  gstart :: p j -> Suspension p (GDissected p) c j
```

These instances are all pretty easy. Given a double natural transformation over
`Suspension`:

```haskell
bihoist
    :: (forall x. p x -> p' x)
    -> (forall a b. k a b -> k' a b)
    -> Suspension p  k  c j
    -> Suspension p' k' c j
bihoist _ g (More j kcj) = More j (g kcj)
bihoist f _ (Done pc)    = Done (f pc)
```

[Wingman][wingman] can write `U1`, `K1`, `Par1`, `M1` and `:+:` all for us:

[wingman]: https://haskellwingman.dev


```haskell
  gstart _ = Done U1

  gstart (K1 a) = Done (K1 a)

  gstart (Par1 j) = More j (K2 ())

  gstart (M1 fj) = bihoist M1 id $ gstart fj

  gstart (L1 fj) = bihoist L1 L2 $ gstart fj
  gstart (R1 gj) = bihoist R1 R2 $ gstart gj
```

For products, `gstart` attempts to start the first element, and hoists its
continuation if it got `More`. Otherwise, it starts the second element. This is
done with a couple of helper functions:

```haskell
mindp
    :: GDissectable g
    => Suspension f (GDissected f) c j
    -> g j
    -> Suspension (f :*: g)
                 (Sum2 (Product2 (GDissected f) (Joker g))
                       (Product2 (Clown f) (GDissected g)))
                 c j
mindp (More j pd) qj = More j $ L2 $ Product2 pd $ Joker qj
mindp (Done pc) qj = mindq pc (gstart qj)

mindq
    :: f c
    -> Suspension g (GDissected g) c j
    -> Suspension (f :*: g)
                 (Sum2 (Product2 (GDissected f) (Joker g))
                       (Product2 (Clown f) (GDissected g)))
                 c j
mindq pc (More j qd) = More j $ R2 $ Product2 (Clown pc) qd
mindq pc (Done qc) = Done (pc :*: qc)
```

and then

```haskell
  gstart (pj :*: qj) = mindp (gstart @f pj) qj
```


## Making Progress

Getting started is nice, but it's only the first step in the process. Once we
have a `More` suspension, how do we move the needle? Enter `gproceed`, which
takes a clown to fill the current hole and a suspension, and gives back a new
suspension corresponding to the next joker.

```haskell
class GDissectable p where
  type GDissected p :: Type -> Type -> Type
  gstart :: p j -> Suspension p (GDissected p) c j
  gproceed :: c -> GDissected p c j -> Suspension p (GDissected p) c j
```

By pumping `gproceed`, we can make our way through a suspension, transforming
each joker into a clown. Eventually our suspension will be `Done`, at which
point we've traversed the entire data structure.

For the most part, `gproceed` is also Wingman-easy:

```haskell
  -- U1
  gproceed _ (K2 v) = absurd v

  -- K1
  gproceed _ (K2 v) = absurd v

  gproceed c _ = Done (Par1 c)

  gproceed fc = bihoist M1 id . gproceed fc

  gproceed c (L2 dis) = bihoist L1 L2 $ gproceed c dis
  gproceed c (R2 dis) = bihoist R1 R2 $ gproceed c dis
```

Products are again a little tricky. If we're still working on the left half, we
want to proceed through it, unless we finish, in which case we want to start on
the right half. When the right half finishes, we need to lift that success all
the way through the product. Our helper functions `mindp` and `mindq` take care
of this:

```haskell
  gproceed c (L2 (Product2 pd (Joker qj))) = mindp (gproceed @f c pd) qj
  gproceed c (R2 (Product2 (Clown pc) qd)) = mindq pc (gproceed @g c qd)
```


## Plugging Holes

McBride points out that if we forget the distinction between jokers and clowns,
what we have is a genuine zipper. In that case, we can just plug the existing
hole, and give back a fully saturated type. This is witnessed by the final
method of `GDissectable`, `gplug`:

```haskell
class GDissectable p where
  type GDissected p :: Type -> Type -> Type
  gstart :: p j -> Suspension p (GDissected p) c j
  gproceed :: c -> GDissected p c j -> Suspension p (GDissected p) c j
  gplug :: x -> GDissected p x x -> p x
```

Again, things are Wingman-easy. This time, we can even synthesize the product
case for free:

```haskell
  -- U1
  gplug _ (K2 vo) = absurd vo

  -- K1
  gplug _ (K2 vo) = absurd vo

  gplug x _ = Par1 x

  gplug x dis = M1 $ gplug x dis

  gplug x (L2 dis) = L1 (gplug x dis)
  gplug x (R2 dis) = R1 (gplug x dis)

  gplug x (L2 (Product2 f (Joker g))) = gplug x f :*: g
  gplug x (R2 (Product2 (Clown f) g)) = f :*: gplug x g
```

This sums up `GDissectable`.


## Nongeneric Representations

`GDissectable` is great and all, but it would be nice to not need to deal with
generic representations. This bit isn't in the paper, but we can lift
everything back into the land of real types by making a copy of `GDissectable`:

```haskell
class (Functor p, Bifunctor (Dissected p)) => Dissectable p where
  type Dissected p :: Type -> Type -> Type
  start :: p j -> Suspension p (Dissected p) c j
  proceed :: c -> Dissected p c j -> Suspension p (Dissected p) c j
  plug :: x -> Dissected p x x -> p x
```

and then a little machinery to do `-XDerivingVia`:

```haskell
newtype Generically p a = Generically { unGenerically :: p a }
  deriving Functor

instance ( Generic1 p
         , Functor p
         , Bifunctor (GDissected (Rep1 p))
         , GDissectable (Rep1 p)
         )
    => Dissectable (Generically p) where
  type Dissected (Generically p) = GDissected (Rep1 p)
  start (Generically pj) =
    bihoist (Generically . to1) id $ gstart $ from1 pj
  proceed x = bihoist (Generically . to1) id . gproceed x
  plug x = Generically . to1 . gplug x
```

With this out of the way, we can now get `Dissectable` for free on `ExprF` from
above:

```haskell
data ExprF a = ValF Int | AddF a a
  deriving stock (Functor, Generic, Generic1, Show)
  deriving Dissectable via (Generically ExprF)
```


## Dissectable Fmap, Sequence and Catamorphisms

Given a `Dissectable` constraint, we can write a version of `fmap` that
explicitly walks the traversal, transforming each element as it goes. Of course,
this is silly, since we already have `Functor` for any `Dissectable`, but it's a
nice little sanity check:

```haskell
tmap :: forall p a b. Dissectable p => (a -> b) -> p a -> p b
tmap fab = pump . start
  where
    pump :: Suspension p (Dissected p) b a -> p b
    pump (More a dis) = pump $ proceed (fab a) dis
    pump (Done j) = j
```

We start the dissection, and then pump its suspension until we're done, applying
`fab` as we go.

Perhaps more interestingly, we can *almost* get `Traversable` with this
machinery:

```haskell
tsequence :: forall p f a. (Dissectable p, Monad f) => p (f a) -> f (p a)
tsequence = pump . start
  where
    pump :: Suspension p (Dissected p) a (f a) -> f (p a)
    pump (More fa dis) = do
      a <- fa
      pump $ proceed a dis
    pump (Done pa) = pure pa
```

It's not quite `Traversable`, since it requires a `Monad` instance instead of
merely `Applicative`. Why's that? I don't know, but [MonoidMusician][mm]
suggested it's because applicatives don't care about the order in which you
sequence them, but this `Dissectable` is very clearly an explicit ordering on
the data dependencies in the container. Thanks MonoidMusician!

[mm]: https://monoidmusician.github.io/monoidmusician.html

Finally, we can implement the stack-based, tail-recursive catamorphism that
we've been promised all along. The idea is simple --- we use the `Dissected`
type as our stack, pushing them on as we unfold the functor fixpoint, and
resuming them as we finish calls.

```haskell
tcata :: forall p v. Dissectable p => (p v -> v) -> Fix p -> v
tcata f t = load' t []
  where
    load'
        :: Fix p
        -> [Dissected p v (Fix p)]
        -> v
    load' (Fix t) stk = next (start t) stk

    next
        :: Suspension p (Dissected p) v (Fix p)
        -> [Dissected p v (Fix p)]
        -> v
    next (More p dis) stk = load' p (dis : stk)
    next (Done p) stk = unload' (f p) stk

    unload'
        :: v
        -> [Dissected p v (Fix p)]
        -> v
    unload' v [] = v
    unload' v (pd : stk) = next (proceed v pd) stk
```

Compare this with the usual implementation of `cata`:

```haskell
cata :: Functor f => (f a -> a) -> Fix f -> a
cata f (Fix fc) = f $ fmap (cata f) fc
```

which just goes absolutely ham, expanding nodes and fmapping over them,
destroying any chance at TCO.

The paper also has something to say about free monads, but it wasn't able to
hold my attention. It's an application of this stuff, though in my opinion the
approach is much more interesting than its applications. So we can pretend the
paper is done here.

But that's not all...


## Functor Composition

Although the paper doesn't present it, there should also be here another
instance of `GDissectable` for functor composition. Based on the composite chain
rule, it should be:

```haskell
instance (Dissectable f, GDissectable g) => GDissectable (f :.: g) where
  type GDissected (f :.: g) =
    Product2 (Compose2 (Dissected f) g)
             (GDissected g)

newtype Compose2 f g c j = Compose2 (f (g c) (g j))
```

`GDissected` is clearly correct by the chain rule, but `Compose2` isn't as
clear. We stick the clowns in the left side of the composite of `f . g`, and the
jokers on the right.

Intuitively, we've done the same trick here as the stack machine example. The
first element of the `Product2` in `GDissected` keeps track of the context of
the `f` traversal, and the second element is the `g` traversal we're working our
way through. Whenever the `g` finishes, we can get a new `g` by continuing the
`f` traversal!

It's important to note that I didn't actually reason this out---I just wrote
the chain rule from calculus and fought with everything until it typechecked.
Then I rewrote my examples that used `:+:` and `:*:` to instead compose over
`Either` and `(,)`, and amazingly *I got the same results!* Proof by
typechecker!


After a truly devoted amount of time, I managed to work out `gstart` for
composition as well.

```haskell
  gstart (Comp1 fg) =
    case start @f $ fg of
      More gj gd -> continue gj gd
      Done f -> Done $ Comp1 f
    where
      continue
          :: g j
          -> Dissected f (g c) (g j)
          -> Suspension
               (f :.: g)
               (Product2 (Compose2 (Dissected f) g) (GDissected g))
               c j
      continue gj gd =
        case gstart gj of
          More j gd' ->
            More j $ Product2 (Compose2 gd) gd'
          Done g ->
            case progress @f g gd of
              More gj gd -> continue gj gd
              Done fg -> Done $ Comp1 fg
```

The idea is that you start `f`, which gives you a `g` to start, and you need to
keep starting `g` until you find one that isn't immediately done.

`gproceed` is similar, except dual. If all goes well, we can just proceed down
the `g` we're currently working on. The tricky part is now when we finish a `g`
node, we need to keep proceeding down `f` nodes until we find one that admits a
`More`:

```haskell
  gproceed c (Product2 cfg@(Compose2 fg) gd) =
    case gproceed @g c gd of
      More j gd -> More j $ Product2 cfg gd
      Done gc -> finish gc
    where
      -- finish
      --     :: g c
      --     -> Suspension
      --          (f :.: g)
      --          (Product2 (Compose2 (Dissected f) g) (GDissected g))
      --          c j
      finish gc =
        case proceed @f gc fg of
          More gj gd ->
            case gstart gj of
              More j gd' -> More j $ Product2 (Compose2 gd) gd'
              Done gc -> finish gc
          Done f -> Done $ Comp1 f
```

I'm particularly proud of this; not only did I get the type for `GDissected`
right on my first try, I was also capable of working through these methods,
which probably took upwards of two hours.

`GHC.Generics` isn't so kind as to just let us test it, however. Due to some
quirk of the representation, we need to add an instance for `Rec1`, which is
like `K1` but for types that use the functor argument. We can give an instance
of `GDissectable` by transferring control back to *`Dissectable`*:

```haskell
instance (Generic1 f, Dissectable f) => GDissectable (Rec1 f) where
  type GDissected (Rec1 f) = Dissected f
  gstart (Rec1 f) = bihoist Rec1 id $ start f
  gproceed c f = bihoist Rec1 id $ proceed c f
  gplug x gd = Rec1 $ plug x gd
```

Now, a little work to be able to express `AddF` as a composition, rather than a
product:

```haskell
data Pair a = Pair a a
  deriving (Functor, Show, Generic1)
  deriving Dissectable via (Generically Pair)

deriving via Generically (Either a) instance Dissectable (Either a)
```

and we can rewrite `ExprF` as a composition of functors:

```haskell
data ExprF' a = ExprF (Either Int (Pair a))
  deriving stock (Functor, Generic, Generic1, Show)
  deriving Dissectable via (Generically ExprF')

pattern ValF' :: Int -> ExprF' a
pattern ValF' a = ExprF (Left a)

pattern AddF' :: a -> a -> ExprF' a
pattern AddF' a b = ExprF (Right (Pair a b))
```

Everything typechecks, and `tcata` gives us the same results for equivalent
values over `ExprF` and `ExprF'`. As one final sanity check, we can compare the
computer dissected types:


```
*> :kind! Dissected ExprF
Dissected ExprF :: * -> * -> *
= Sum2
    (K2 Void)
    (Sum2
       (Product2
          (K2 ())
          (Joker Par1))
       (Product2
          (Clown Par1)
          (K2 ())))

*> :kind! Dissected ExprF'
Dissected ExprF' :: * -> * -> *
= Product2
    (Compose2 (Sum2 (K2 Void) (K2 ())) (Rec1 Pair))
    (Sum2
       (Product2
          (K2 ())
          (Joker Par1))
       (Product2
          (Clown Par1)
          (K2 ())))
```

They're not equal, but are they isomorphic? We should hope so! The first one is
`Sum2 0 x`, which is clearly isomorphic to `x`. The second is harder:

`Product (Compose2 (Sum2 (K2 Void) (K2 ())) (Rec1 Pair)) x`

If that first argument to `Product` is 1, then these two types are isomorphic.
So let's see:

```haskell
    Compose2 (Sum2 (K2 Void) (K2 ())) (Rec1 Pair)
= symbolic rewriting
    Compose2 (0 + 1) (Rec1 Pair)
= 0 is an identity for +
    Compose2 1 (Rec1 Pair)
= definition of Compose2
    K2 () (Rec1 Pair c) (Rec1 Pair j)
= K2 () is still 1
    1
```

Look at that, baby. Isomorphic types, that compute the same answer.

As usual, today's code is available on [Github](https://gist.github.com/isovector/8a02f5c21bdb5ff5034b661ef9d28d10).


---
layout: post
title: "Review: Bananas, Lenses, Envelopes and Barbed Wire"
date: 2017-10-06 23:07
comments: true
tags: haskell, recursion-schemes, technical, review, papers
---

Today's classic functional programming paper we will review is Meijer et al.'s
[Functional Programming with Bananas, Lenses, Envelopes and Barbed
Wire][recursion]. The exciting gist of the paper is that all explicit recursion
can be factored out into a few core combinators. As such, the reasoning is that
we should instead learn these combinators (or "recursion schemes" as they're
called), rather than doing our own ad-hoc recursion whenever we need it.

[recursion]: https://maartenfokkinga.github.io/utwente/mmf91m.pdf

Despite being a marvelous paper, it falls into the all-too-common flaw of
functional programming papers, which is to have an absolutely horrible title.
"Bananas", "lenses", "envelopes" and "barbed wire" correspond to obscure pieces
of syntax invented to express these ideas. In our treatment of the literature,
we will instead use standard Haskell syntax, and refer to the paper as
Functional Programming with Recursion Schemes.


## Specialized Examples of Recursion Schemes

### Catamorphisms over Lists

**Catamorphisms** refer to a fold over a datastructure. A mnemonic to remember
this is that a *cata*morphism tears down structures, and that if that structure
were our civilization it'd be a *cata*strophe.

By way of example, Meijer et al. present the following specialization of a
catamorphism over lists:

> Let `default :: b` and `step :: a -> b -> b`, then a *list-catamorphism* `h ::
> [a] -> b` if a function of the following form:
>
> ```haskell
> h [] = default
> h (a : as) = step a (h as)
> ```

This definition should look pretty familiar; if you specialize the function
`foldr` to lists, you'll see it has the type:

```haskel
foldr :: (a -> b -> b) -> b -> [a] -> b
```

We can view `foldr` as taking our values `step :: a -> b -> b` and `default ::
b`, and then giving back a function that takes an `[a]` and computes some `b`.
For example, we can write a few of the common prelude functions over lists as
catamorphisms of this form.

```haskell
length :: [a] -> Int
length = foldr (\_ n -> n + 1) 0
```

```haskell
filter :: forall a. (a -> Bool) -> [a] -> [a]
filter p = foldr step []
  where
    step :: a -> [a] -> [a]
    step a as = if p a
                   then a : as
                   else as
```

When written this way -- Meijer et al. are quick to point out -- the so-called
"fusion" law is easily seen:

```haskell
f . foldr step default = foldr step' default'
  where
    step' a b = step a (f b)
    default'  = f default
```

which intuitively says that you can "fuse" a catamorphism with a subsequent
composition into a single catamorphism.


### Anamorphisms over Lists

If a catamorphism refers to a "fold", an **anamorphism** corresponds to an
*unfold* of a data structure. A good mnemonic for this is that an *ana*morphism
builds things up, just like *ana*bolic steroids can be an easy way to build up
muscle mass.

Meijer et al. present this concept over lists with the following (again, very
specialized) definition:

unfoldr :: (b -> Maybe (a, b)) -> b -> [a]

> Given a function `produce :: b -> Maybe (a, b)`, a list-anamorphism `h :: b ->
> [a]` is defined as:
>
> ```haskell
> h seed = case produce seed of
>            Just (a, b) = a : h b
>            Nothing     = []
> ```

As expected, this corresponds to the `unfoldr :: (b -> Maybe (a, b)) -> b ->
[a]` function from `Data.List`.

By way of example, they provide the following:

```haskell
zip :: ([a], [b]) -> [(a, b)]
zip = unfoldr produce
  where
    produce (as, bs) =
      if null as || null bs
         then Nothing
         else Just ((head as, head bs), (tail as, tail bs))
```

and

```haskell
iterate :: (a -> a) -> a -> [a]
iterate f = unfoldr (\a -> Just (a, f a))
```

An interesting case is that of `map :: (a -> b) -> [a] -> [b]`. We note that
both the input and output of this function are lists, and thus might suspect the
function can be written as either a catamorphism *or* an anamorphism. And
indeed, it can be:

```haskell
cataMap :: (a -> b) -> [a] -> [b]
cataMap f = foldr (\a bs -> f a : bs) []

anaMap :: (a -> b) -> [a] -> [b]
anaMap f = unfoldr produce
  where
    produce [] = Nothing
    produce (a : as) = Just (f a, as)
```

Neat!


### Hylomorphisms over Lists

A **hylomorphism** over lists is a recursive function of type `a -> b` whose
call-tree is isomorphic to a list. A hylomorphism turns out to be nothing more
than a catamorphism following an anamorphism; the anamorphism builds up the
call-tree, and the catamorphism evaluates it.

An easy example of hylomorphisms is the factorial function, which can be naively
(ie. without recursion schemes) implemented as follows:

```haskell
fact :: Int -> Int
fact 0 = 1
fact n = n * fact (n - 1)
```

When presented like this, it's clear that `fact` will be called a linear number
of times in a tail-recursive fashion. That sounds a lot like a list to me, and
indeed we can implement `fact` as a hylomorphism:

```haskell
fact :: Int -> Int
fact = foldr (*) 1 . unfoldr (\n -> if n == 0
                                       then Nothing
                                       else Just (n, n - 1))
```

The hylomorphic representation of `fact` works by unfolding its argument `n`
into a list `[n, n-1 .. 1]`, and then folding that list by multiplying every
element in it.

However, as Meijer et al. point out, this implementation of `fact` is a little
unsatisfactory. Recall that the natural numbers are themselves an inductive type
(`data Nat = Zero | Succ Nat`), however, according to the paper, there is no
easy catamorphism (nor anamorphism) that implements `fact`.


### Paramorphisms

Enter **paramorphisms**: intuitively catamorphisms that have access to the
current state of the structure-being-torn-down. Meijer et al.:

> [Let `init :: b` and `merge :: Nat -> b -> b`. ] For type `Nat`, a
> paramorphism is a function `h :: Nat -> b` of the form:
>
> ```haskell
> h Zero = init
> h (Succ n) = merge n (h n)
> ```

As far as I can tell, there is no function in the Haskell standard library that
corresponds to this function-as-specialized, so we will write it ourselves:

```haskell
paraNat :: (Nat -> b -> b) -> b -> Nat -> b
paraNat _ init Zero = init
paraNat merge init (Succ n) = merge n (paraNat merge init n)
```

We can thus write `fact :: Nat -> Nat` as a paramorphism:

```haskell
fact :: Nat -> Nat
fact = paraNat (\n acc -> (1 + n) * acc) 1
```

Similarly, we can define paramorphisms over lists via the function:

```haskell
paraList :: (a -> [a] -> b -> b) -> b -> [a] -> b
paraList _ init [] = init
paraList merge init (a : as) = merge a as (paraList merge init as)
```

with which we can write the function `tails :: [a] -> [[a]]`:

```haskell
tails :: forall a. [a] -> [[a]]
tails = paraList merge []
  where
    merge :: a -> [a] -> [[a]] -> [[a]]
    merge a as ass = (a : as) : ass
```


## General Recursion Schemes


### Intuition

As you've probably guessed, the reason we've been talking so much about these
recursion schemes is that they generalize to all recursive data types. The
trick, of course, is all in the representation.

Recall the standard definition of list:

```haskell
data List a = Nil
            | Cons a (List a)
```

However, there's no reason we need the explicit recursion in the `Cons` data
structure. Consider instead, an alternative, "fixable" representation:

```haskell
data List' a x = Nil'
               | Cons' a x
```

If we were somehow able to convince the typesystem to unify `x ~ List' a x`,
we'd get the type `List' a (List' a (List' a ...))`, which is obviously
isomorphic to `List a`. We'll look at how to unify this in a second, but a more
pressing question is "why would we want to express a list this way?".

It's a good question, and the answer is we'd want to do this because `List' a x`
is obviously a functor in `x`. Furthermore, in general, any datastructure we
perform this transformation on will be a functor in its previously-recursive `x`
parameter.

We're left only more curious, however. What good is it to us if `List' a x` is a
functor in `x`? It means that we can replace `x` with some other type `b` which
is *not* isomorphic to `List a`. If you squint and play a little loose with the
type isomorphisms, this specializes `fmap :: (x -> b) -> List' a x -> List' a b`
to `(List a -> b) -> List' a x -> List' a b`.

Notice the `List a -> b` part of this function -- that's a fold of a `List a`
into a `b`! Unfortunately we're still left with a `List' a b`, but this turns
out to be a problem only in our handwaving of `x ~ List' a x`, and the actual
technique will in fact give us just a `b` at the end of the day.


### Algebras

An `f`-algebra is a function of type `forall z. f z -> z`, which intuitively
removes the structure of an `f`. If you think about it, this is spiritually what
a fold does; it removes some structure as it reduces to some value.

As it happens, the type of an `f`-algebra is identical to the parameters
required by a catamorphism. Let's look at `List' a`-algebras and see how the
correspond with our previous examples of catamorphisms.


```haskell
length :: [a] -> Int
length = foldr (\_ n -> n + 1) 0

lengthAlgebra :: List' a Int -> Int
lengthAlgebra Nil'        = 0
lengthAlgebra (Cons' _ n) = n + 1
```

```haskell
filter :: forall a. (a -> Bool) -> List a -> List a
filter p = foldr step Nil
  where
    step a as =
      if p a
         then Cons a as
         else as

filterAlgebra :: (a -> Bool) -> List' a (List a) -> (List a)
filterAlgebra _  Nil'        = Nil
filterAlgebra p (Cons' a as) =
  if p a
    then Cons a as
    else as
```


### Coalgebras

`f`-algebras correspond succinctly to the parameters of catamorphisms
over `f`s. Since catamorphisms are dual to anamorphisms, we should expect
that by turning around an algebra we might get a representation of the
anamorphism parameters.

And we'd be right. Such a thing is called an `f`-coalgebra of type `forall z. z
-> f z`, and corresponds exactly to these parameters. Let's look at our previous
examples of anamorphisms through this lens:

```haskell
zip :: (List a, List b) -> List (a, b)
zip = unfoldr produce
  where
    produce (as, bs) =
      if null as || null bs
         then Nothing
         else Just ((head as, head bs), (tail as, tail bs))

zipCoalgebra :: ([a], [b]) -> List' (a, b) ([a], [b])
zipCoalgebra (as, bs) =
  if null as || null bs
     then Nil'
     else Cons (head as, head bs) (tail as, tail bs)
```

```haskell
iterate :: (a -> a) -> a -> [a]
iterate f = unfoldr (\a -> Just (a, f a))

iterateAlgebra :: (a -> a) -> a -> List' a a
iterateAlgebra f a = Cons a (f a)
```

You might have noticed that these coalgebras don't line up as nicely as the
algebras did, due namely to the `produce` functions returning a type of `Maybe
(a, b)`, while the coalgebras return a `List' a b`. Of course, these types are
isomorphic (`Nothing <=> Nil'`, `Just (a, b) <=> Cons a b`), it's just that the
authors of `unfoldr` didn't have our `List'` functor to play with.


### From Algebras to Catamorphisms

As we have seen, `f`-algebras correspond exactly to the parameters of a
catamorphism over an `f`. But how can we actually implement the catamorphism?
We're almost there, but first we need some machinery.

```haskell
type family Fixable t :: * -> *
```

The type family `Fixable` takes a type to its fixable functor representation.
For example, we can use it to connect our `List a` type to `List' a`:

```haskell
type instance Fixable (List a) = List' a
```

Now, assuming we have a function `toFixable :: t -> Fixable t t`, which for
lists looks like this:

```haskell
toFixable :: List a -> Fixable (List a) (List a)
-- equivalently: toFixable :: List a -> List' a (List a)
toFixable Nil         = Nil'
toFixable (Cons a as) = Cons' a as
```

We can now write our catamorphism!

```haskell
cata :: (Fixable t z -> z) -> (t -> z)
cata algebra = algebra
             . fmap (cata algebra)
             . toFixable
```

Very cool. What we've built here is general machinery for tearing down any
inductive data structure `t`. All we need to do it is its `Fixable t`
representation, and a function `project :: t -> Fixable t t`. These definitions
turn out to be completely mechanical, and thankfully, [can be automatically
derived][th] for you via the [recursion-schemes][schemes] package.

[th]: https://hackage.haskell.org/package/recursion-schemes-5.0.2/docs/Data-Functor-Foldable-TH.html#v:makeBaseFunctor
[schemes]: https://hackage.haskell.org/package/recursion-schemes-5.0.2


### Coalgebras and Catamorphisms

We can turn all of our machinery around in order to implement anamorphisms.
We'll present this material quickly without much commentary, since there are no
new insights here.

Given `fromFixable :: Fixable t t -> t`, we can implement `ana`:

```haskell
ana :: (z -> Fixable t z) -> z -> t
ana coalgebra = fromFixable
              . fmap (ana coalgebra)
              . coalgebra
```


### General Paramorphisms

Because there is nothing interesting about hylomorphisms when viewed via our
`Fixable` machinery, we skip directly to paramorphisms.

Recall that a paramorphism is a fold that has access to both the accumulated
value being constructed as well as the remainder of the structure at any given
point in time. We can represent such a thing "algebraically:" `Fixable t (t, z)
-> z`. With a minor tweak to `cata`, we can get `para`:

```haskell
para :: (Fixable t (t, z) -> z) -> t -> z
para alg = teardown
  where
    teardown = alg
             . fmap (\t -> (t, teardown t))
             . toFixable
```


## Miscellaneous Findings

### All Injective Functions are Catamorphisms

Meijer et al. make the somewhat-unsubstantiated claim that all injective
functions are catamorphisms. We will reproduce their proof here, and then work
through it to convince ourselves of its correctness.

> Let `f :: A -> B` be a strict function with left-inverse `g`. Then for any `φ
> :: F A -> A`, we have:
>
> ```haskell
> g . f = id
>
> f . cata φ = cata (f . φ . fmap g)
> ```
>
> Taking `φ = fromFixable$ we immediately get that any strict injective function
> can be written as a catamorphism:
>
> ```haskell
> f = cata (f . fromFixable . fmap g)
> ```

Sounds, good? I guess? Meijer et al. must think I'm very smart, because it took
me about a week of bashing my head against this proof before I got it. There
were two stumbling blocks for me which we'll tackle together.

To jog our memories, we'll look again at the definition of `cata`:

```haskell
cata φ = φ . fmap (cata φ) . toFixable
```

There are two claims we need to tackle here, the first of which is that given `φ
= fromFixable`:

```haskell
f . cata φ = cata (f . φ . fmap g)
```

We can show this by mathematical induction. We'll first prove the base case, by
analysis of the `[]` case over list-algebras.

```haskell
  cata (f . φ . fmap g) []
  -- definition of cata
= f . φ . fmap g . fmap (cata (f . φ . fmap g)) $ toFixable []
  -- definition of toFixable
= f . φ . fmap g . fmap (cata (f . φ . fmap g)) $ NilF
  -- fmap fusion
= f . φ . fmap (g . cata (f . φ . fmap g)) $ NilF
  -- NilF is a constant functor
= f . φ $ NilF
  -- substitute φ = fromFixable
= f $ fromFixable NilF
  -- definition of fromFixable
= f []
```

Great! That's the base case tackled. It's easy to see why this generalizes away
from lists to any data structure; the only way to terminate the recursion of a
`cata` is for one of the type's data constructors to not be recursive (such as
`Nil`). If the data constructor isn't recursive, its `Fixable` representation
must be a constant functor, and thus the final `fmap` will always fizzle itself
out.

Let's tackle the inductive case now. We'll look at cases of `cata` that don't
fizzle out immediately:

```haskell
  cata (f . φ . fmap g)
  -- definition of cata
= f . φ . fmap g . fmap (cata (f . φ . fmap g)) . toFixable
  -- fmap fusion
= f . φ . fmap (g . cata (f . φ . fmap g)) . toFixable
  -- definition of cata
= f . φ . fmap (g . f . φ . fmap g . fmap (cata (f . φ . fmap g)) . toFixable) . toFixable
  -- fmap fusion
= f . φ . fmap (g . f . φ . fmap (g . cata (f . φ . fmap g)) . toFixable) . toFixable
  -- g . f = id
= f . φ . fmap (id . φ . fmap (g . cata (f . φ . fmap g)) . toFixable) . toFixable
  -- definition of id
= f . φ . fmap (φ . fmap (g . cata (f . φ . fmap g)) . toFixable) . toFixable
```

As you can see here, subsequent expansions of `cata` line their `g`s and `f`s up
in such a way that they cancel out. Also, we know from our experience looking at
the base case that the final `g` will always sizzle out, and so we don't need to
worry about it only being a left-inverse.

The other stumbling block for me was that `cata fromFixable = id`, but this
turns out to be trivial:

```haskell
  cata fromFixable
= fromFixable . fmap (cata fromFixable) . toFixable
```

Eventually this will all bottom out when it hits the constant functor, which
will give us a giant chain of `fromFixable . toFixable`s, which is obviously
`id`.

To circle back to our original claim that all injective functions are
catamorphisms, we're now ready to tackle it for real.


```haskell
f . cata φ           = cata (f . φ . fmap g)
f . cata fromFixable = cata (f . fromFixable . fmap g)
f . id               = cata (f . fromFixable . fmap g)
f                    = cata (f . fromFixable . fmap g)
```

$\blacksquare$


### All Surjective Functions are Anamorphisms

Anamorphisms are dual to catamorphisms, and surjective functions are dual (in
$\mathbb{Set}$) to injective functions. Therefore, we can get this proof via
duality from the proof that injective functions are catamorphisms. $\blacksquare$


## Closing Remarks


*Functional Programming with Recursion Schemes* has some other (in my opinion)
minor contributions about this stuff, such as how catamorphisms preserve
strictness, but I feel like we've tackled the most interesting pieces of it. It
is my hope that this review will serve as a useful complement in understanding
the original paper.


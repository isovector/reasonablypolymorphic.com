---
layout: post
title: Wake Up and Smell the Cofree Comonads
date: 2016-06-05 13:37
comments: true
tags: haskell, dsl, rpg
---

In the last post in this series, we talked about the rough sketch of an idea on
how we might be able to make procedurally generated RPG stories. The general
approach is this: make a super simple core set of story primitives, and then
build more interesting abstractions on top of them.

Simplicity of our underlying language is desirable for a few reasons. The
smaller our set of primitives, the easier a time we're going to have proving
things about what we can do with them. One thing we can do with them,
particularly relevant to today's discussion, is to provide an interpretation.

If you haven't read [the previous post in this series][free], now would probably
be a good time.

[free]: /blog/free-stories

Remember, the reason we wanted to build a DSL behind our story generation was
so that we could use it to separate the *structure* of our story from its
*interpretation*.

Last time, we used free monads over our command functor to generate our DSL. I
promised today we'd use cofree comonads to interpret our language, but there is
a lot of intermediate motivating material I want to get through before we
discuss that. So without further ado, let's talk about duality.


## Duality

At first blush, duality can be understood as the mathematical version of bizarro
world.

<img src="/images/bizarro.jpg" title="Duality is just like this." width="620" />

As a good rule of thumb, if I have some interesting mathematical object $X$,
then its dual, co-$X$, is the *opposite* mathematical object, and is also
interesting.

But what does opposite mean, here?

I'm by no means a mathematician (yet!), but, to a (very) rough approximation, a
dual is constructed by flipping all of your arrows backwards. What arrows, you
might ask? Well, that's a good question. Let's look at an example. It'll involve
drawing pretty pictures, so make sure you have your copy book ready.


### Products and coproducts

Okay, so given $a \in A$ and $b \in B$, we have $(a, b)\in A \times B$, and we
call this $(a, b)$ a (cartesian) product. Intuitively, a product is pair of two things,
wrapped up together in a nice little package. The words "product" and "pair" are
interchangeable, so go wild with it!

More formally, we can encode the idea of a product thusly:

```haskell
prod :: (a -> b) -> (a -> c) -> a -> (b, c)
prod f g a = (f a, g a)
```

Which is to say, given two functions, `a -> b` and `a -> c`, we can create a new
function which maps `a -> (b, c)`. The fact that `prod` is polymorphic in all
`a`, `b`, `c` [should be telling][typesystem] that we're onto something here.

Let's dive in a little further, and investigate this notion as a [commutative
diagram][commutative], because the idea of duality is a little easier to
investigate in that context. Our `prod` function above can also be encoded
equivalently by this diagram:

$$
\begin{xy}
\xymatrix {
A \ar@/_/[ddr]_f \ar@{.>}[dr]|{prod} \ar@/^/[drr]^g \\
 & B \times C \ar[d]^{fst} \ar[r]_{snd} & C \\
 & B
}
\end{xy}
$$

If you view the capital letters as types and the arrows as functions, this
corresponds perfectly with our `product` function as written above. The solid
arrows are ones we know that exist, and the dashed line is our proposition: "if
everything else in this picture holds, this arrow exists."

So: the million dollar question. What happens when we flip all of our arrows
around? We get this diagram:

$$
\begin{xy}
\xymatrix {
& C \ar@/^/[ddr]^g \ar[d] \\
B \ar[r] \ar@/_/[drr]_f & ? \ar@{.>}[dr]|{coprod} \\
& & A
}
\end{xy}
$$

Which of course corresponds with this in Haskell:

```haskell
coprod :: (b -> a) -> (c -> a) -> Coproduct b c -> a
```

You probably know what this is, but let's pretend like we don't, and see if
Hoogle can answer this for us. Spoilers, [it can][hoogle]. That's right! It's
our old friend `either`!

```haskell
either :: (b -> a) -> (c -> a) -> Either b c -> a
```

Cool! So a coproduct is a [sum type][sum], and is the dual to the product type. For the
sake of completeness, let's fill in all of the missing labels on our diagram.

$$
\begin{xy}
\xymatrix {
& C \ar@/^/[ddr]^g \ar[d]_{Right} \\
B \ar[r]^{Left} \ar@/_/[drr]_f & B+C \ar@{.>}[dr]|{either} \\
& & A
}
\end{xy}
$$

Notice that our interesting product type had an interesting dual. This is theme
we will continuously take advantage of.

It is left as an exercise to the reader to prove that the dual of the coproduct
is the product (this is not a very hard proof since arrows only have two ends).

[typesystem]: /blog/love-types
[commutative]: https://en.wikipedia.org/wiki/Commutative_diagram
[hoogle]: https://www.haskell.org/hoogle/?hoogle=%28b+-%3E+a%29+-%3E+%28c+-%3E+a%29+-%3E+coproduct+b+c+-%3E+a
[sum]: https://en.wikipedia.org/wiki/Tagged_union


### Monads and comonads

Lovely. Armed with our new superpower of duality, we're now ready to take on
comonads. Judging from the name, we should expect them to be dual to monads.
Recall that a monad `m` is defined by two functions:

* `return :: a -> m a`
* `(>>=) :: m a -> (a -> m b) -> m b`

Let's flip the arrows around, and since we're flipping everything else, we'll
refer to our comonad as `w`, which is defined by two functions dual to the
monad's:

* `extract :: w a -> a`
* `extend :: w b -> (w b -> a) -> w a`

The full intuition behind comonads is left as an exercise to the reader ([my
monad tutorial][monads] didn't go too well), but a good starting point is this:
while monads are for building up a computation *in* a context, comonads compute
values *from* a context.

The canonical example of a comonad is [Conway's game of life][conway] (a cell is
alive or dead based on how lively its neighborhood is.)
Another particularly amazing example is [spreadsheets][spreadsheet] (the value
of a cell depends on the value of other cells it references.)

[monads]: /blog/ideas-and-men
[conway]: http://blog.emillon.org/posts/2012-10-18-comonadic-life.html
[spreadsheet]: https://vimeo.com/100176795


## Wake up and smell the cofree

Recall the definition of the free monad:

```haskell
data Free f a = Pure a
              | Bind (f (Free f a))
```

Now that I've primed you, it should be pretty clear that this is a sum type --
`Free f a` is *either* a `Pure a` *or* a `Bind (f (Free f a))`. There are no
function arrows to flip around, so we can dualize this trivially now that we
know products and coproducts are duals of one another:

```haskell
data Cofree f a = Cofree a (f (Cofree f a))
```

Again, it's hard to get a sense of what this might mean just by looking at it.
Let's throw some concrete functors at it:

```haskell
data Cofree Maybe a = Cofree a (Maybe (Cofree Maybe a))
```

Whoa! Look at that! `Cofree Maybe a` is at least one `a`, followed by maybe
more. That's just a non-null list in disguise! Veeeery interesting, no? I wonder
what happens if we slap in the list functor instead:

```haskell
data Cofree [] a = Cofree a [Cofree [] a]
```

Hey, this one is equivalent to a rose tree -- an `n-ary` tree with data *at
every branch*.

We must be onto something here -- those are pretty different data structures,
and we got them just by changing the functor underlying our `Cofree`.

As you might expect, `Cofree` is thusly named because it generates trivial
comonads for free (as in time) given a functor `f`:

```haskell
instance Functor f => Comonad (Cofree f) where
    extract   (Cofree a _ )   = a
    extend wb@(Cofree _ bc) f = Cofree (f wb) (fmap (`extend` f) bc)
```

It's probably the dumbest comonad instance imaginable -- there is no context to
extract values from, we just pull out the `a` we have. But again, it's good that
our instance is stupid. That's what we want -- that's why we made it.

Unfortunately it's a little harder for us to bask in the glory of having a
cofree comonad -- comonads don't give rise to unique syntax in Haskell, so we'll
just have to be content with the fact that our instance compiles.

This feels like a natural place to end off, so we will. Next time around we'll
take a look at adjunctions, how they give rise to pairings between functors, and
how we can use that machinery to automatically pair our cofree comonads with our
free monads into one mega DSL-implementing wonder device.

Until then!


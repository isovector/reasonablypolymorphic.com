---
layout: post
title: "Review: Codata in Action"
date: 2022-02-10 18:57
comments: true
tags: review, data, codata, downen, sullivan, ariola, spj
---

Today we're looking at [Codata in Action][paper] by Downen, Sullivan, Ariola and
Peyton Jones. Please excuse my lack of any sort of theme as I review papers, I'm
just picking things that seem interesting to me. This paper in particular was
recommended to me by [Jonathan Lorimer][jlo] in the inaugural edition of the
[Cofree Coffee Cast][podcast], which is an excellent podcast that I may or may
not be involved in.

[paper]: https://www.microsoft.com/en-us/research/uploads/prod/2020/01/CoDataInAction.pdf
[podcast]: https://anchor.fm/cofree-coffee
[jlo]: https://jonathanlorimer.dev/

So anyway, today we're looking at codata. What's that? Essentially, lazy
records. By virtue of being lazy, Haskell makes the differentiation between data
and codata rather hard to spot. The claim is that functional languages are big
on data, object-oriented languages really like codata, and that everything you
can do with one can be emulated by the other, which is useful if you'd like to
compile FP to OOP, or vice versa.

Codata, like the name implies, have a lot of duals with regular ol' data. The
paper introduces a bunch of parallels between the two:

|             Data            |                Codata               |
|:---------------------------:|:-----------------------------------:|
| Concerned with construction | Concerned with destruction          |
| Define the types of constructors | Define the types of destructors     |
| Directly observable         | Observable only via their interface |
| Common in FP                | Common in OOP                       |
| Initial algebras            | Terminal coalgebras                 |
| Algebraic data structures   | Abstract data structures |
| `data` | `class` |

The paper's claim is that codata is a very useful tool for doing real-world
work, and that we are doing ourselves a disservice by not making it first-class:

> While codata types can be seen in the shadows behind many examples of
> programming---often hand-compiled away by the programmer---not many functional
> languages have support for them.

That's a particularly interesting claim; that we're all already using codata,
but it's hidden away inside of an idiom rather than being a first-class
citizen. I'm always excited to see the ghosts behind the patterns I am already
using.

## Examples of Codata

The paper gives a big list of codata that we're all already using without
knowing it:

### Church/Boehm--Berarducci encodings

Instead of writing

```haskell
data Bool where
  True :: Bool
  False :: Bool
```

I can instead do the usual Church encoding:

```haskell
codata Bool where
  if :: Bool -> a -> a -> a
```

which I might express more naturally in Haskell via:

```haskell
ifThenElse :: Bool -> a -> a -> a
ifThenElse True  t _ = t
ifThenElse False _ f = f
```

(I suspect this is that "hand-compiling away" that the authors were talking
about)

However, in the codata presentation, I can recover `true` and `false` by
building specific objects that fiddle with their arguments just right (using
[copatterns][copatterns] from a few weeks ago):

[copatterns]:

```haskell
True : Bool
if True t _ = t

False : Bool
if False _ f = f
```

That's neat, I guess!

As a follow-up, we can try talking about `Tree`s. Rather than the usual `data`
definition:

```haskell
data Tree t where
  Leaf :: t -> Tree t
  Branch :: Tree t -> Tree t -> Tree t

walk :: (t -> a) -> (a -> a -> a) -> Tree t -> a
```

we can do it in codata:

```haskell
codata Tree t where
  walk :: Tree t -> (t -> a) -> (a -> a -> a) -> a
```

and reconstruct the "constructors:"

```haskell
Leaf x :: t -> Tree t
walk (Leaf t) mk _ = mk t

Branch :: Tree t -> Tree t -> Tree t
walk (Branch l r) mk comb = comb (walk l mk comb) (walk r mk comb)
```

The presentation in the paper hand-compiles `Tree!data` into two declarations:

```haskell
codata TreeVisitor t a where
  { visitLeaf   :: TreeVisitor t a -> t -> a
  , visitBranch :: TreeVisitor t a -> a -> a -> a
  }

codata Tree t where
  walk :: Tree t -> TreeVisitor t a -> a
```

which is the same thing, but with better named destructors.


### Demand-Driven Programming / Laziness

You know the problem. You're programming some search, and want to have a
stopping depth. Maybe you're writing a chessai and don't want to wait until the
ends of time for the search to finish. Easy enough, right? Just add an integer
that counts down whenever you recurse:

```haskell
search :: Int -> Position -> [Position]
search 0 _ = []
search n as = -- do lots of work
```

So you set `n` to something that seems reasonable, and get your moves back. But
then you realize you had more time to kill, so you'd like to resume the search
where you left off. But there's no good way to do this, and starting back from
the beginning would involve wasting a lot of effort. You can certainly program
around it, but again, it's hand-compiling away codata.

Instead, we can express the problem differently:

```haskell
codata Rose a where
  { node :: Rose a -> a
  , children :: Rose a -> [Rose a]
  }
```

Recall that codata is built-in lazy, so by repeatedly following `children` we
can further explore the tree state. In OOP I guess we'd call this a generator or
an iterator or something. Probably a factory of some sort.

But once we have `Rose` we can implement pruning:

```haskell
prune :: Int -> Rose Position -> Rose Position
node (prune n t) = node t
children (prune 0 t) = []
children (prune n t) = fmap (prune (n - 1)) $ children t
```

I *really* like copattern matching.


### Abstract Data Types


You know how we have extentional and intentional definitions for sets? Like,
compare:

```haskell
newtype Set a = Set { unSet :: [a] }

lookup :: Set a -> a -> Bool
lookup s t = elem t $ unset s
```

vs


```haskell
newtype Set a = Set { lookup :: a -> Bool }
```

That latter version is the Church-encoded version. Instead we can give an
interface for both sorts of sets as codata, defined by their *interface* as
sets. This is everyday OOP stuff, but a little weird in FP land:

```haskell
codata Set a where
  { isEmpty :: Set a -> Bool
  , lookup :: Set a -> a -> Bool
  , insert :: Set a -> a -> Set a
  , union :: Set a -> Set a -> Set a
  }
```

My dudes this is just an interface for how you might want to interact with a
Set. We can implement the listy version from above:

```haskell
listySet :: [a] -> Set a
isEmpty (listySet ls) = null ls
lookup (listySet ls) a = elem a ls
insert (listySet ls) a = listSet (a : ls)
union (listySet ls) s = foldr insert s ls
```

but we can also implement an infinitely big set akin to our functiony-version:

```haskell
evensUnion :: Set Int -> Set Int
isEmpty (evensUnion s) = False
lookup (evensUnion s) a = mod a 2 == 0 || lookup a s
insert (evensUnion s) a = evensUnion $ insert s a
union (evensUnion s) s' = evensUnion $ union s s'
```

This thing is a little odd, but `evensUnion` is the set of the even numbers
unioned with some other set. The built-in unioning is necessary to be able to
extend this thing. Maybe we might call it a decorator pattern in OOP land?


### Pre and Post Conditions

One last example, using type indices to represent the state of something. The
paper gives sockets:

```haskell
data State = Raw | Bound | Live

type Socket :: State -> Type
codata Socket i where
  { bind    :: Socket 'Raw -> String -> Socket 'Bound
  , connect :: Socket 'Bound -> Socket 'Live
  , send    :: Socket 'Live -> String -> ()
  , recv    :: Socket 'Live -> String
  , close   :: Socket 'Live -> ()
  }
```

The type indices here ensure that we've bound the socket before connecting to
it, and connected to it before we can send or receive.

Contrast this against what we can do with GADTs, which tell us how something
was built, not how it can be used.


## Converting Between Data and Codata

Unsurprisingly, data and codata are two sides of the same coin: we can
compile one to the other and vice versa.


### Data to Codata

Going from data to codata is giving a final encoding for the thing; as we've
seen, this corresponds to the Boehm-Berarducci encoding. The trick is to replace
the type with a function. Each data constructor corresponds to an argument of
the function, the type of which is another function that returns `a`, and as
arguments takes each argument to the data constructor. To tie the knot, replace
the recursive bits with `a`.

Let's take a look at a common type:

```haskell
data List a = Nil | Cons a (List a)
```

We will encode this as a function, that returns some new type variable. Let's
call it `x`:

```haskell
... -> x
```

and then we need to give eliminators for each case:

```haskell
elim_nil -> elim_cons -> x
```

and then replace each eliminator with a function that takes its arguments, and
returns `x`. For `Nil`, there are no arguments, so it's just:

```haskell
x -> elim_cons -> x
```

and then we do the same thing for `Cons :: a -> List a -> List a`:

```haskell
x -> (a -> List a -> x) -> x
```

of course, there is no `List a` type anymore, so we replace that with `x` too:

```haskell
x -> (a -> x -> x) -> x
```

And thus we have our codata-encoded list. For bonus points, we can do a little
shuffling and renaming:

```haskell
(a -> b -> b) -> b -> b
```

which looks very similar to our old friend `foldr`:

```haskell
foldr :: (a -> b -> b) -> b -> [a] -> b
```

In fact, a little more reshuffling shows us that `foldr` is exactly the codata
transformation we've been looking for:

```haskell
foldr :: [a] -> ((a -> b -> b) -> b -> b)
```

Cool. The paper calls this transformation the "visitor pattern" which I guess
makes sense; in order to call this thing we need to give instructions for what
to do in every possible case.

This is an encoding of the type itself! But we also need codata encodings for
the data constructors. The trick is to just ignore the "handlers" in the type
that don't correspond to your constructor. For example:

```haskell
Nil :: (a -> b -> b) -> b -> b
Nil _ nil = nil

Cons
    :: a
    -> ((a -> b -> b) -> b -> b)
    -> (a -> b -> b)
    -> b
    -> b
Cons head tail cons nil = cons nil (tail cons nil)
```

Really, these write themselves once you have an eye for them. One way to think
about it is that the handlers are "continuations" for how you want to continue.
This is the dreaded CPS transformation!


### Codata to Data

Let's go the other way too. Appropriately, we can use codata streams:

```haskell
codata Stream a where
  { head :: Stream a -> a
  , tail :: Stream a -> Stream a
  }
```

I'm winging it here, but it's more fun to figure out how to transform this than
to get the information from the paper.

The obvious approach here is to just turn this thing directly into a record by
dropping the `Stream a ->` part of each field:

```haskell
data Stream a = Stream
  { head :: a
  , tail :: Stream a
  }
```

While this works in Haskell, it doesn't play nicely with strict languages. So,
we can just lazify it by sticking each one behind a function:

```haskell
data Stream a = Stream
  { head :: () -> a
  , tail :: () -> Stream a
  }
```

Looks good to me. But is this what the paper does? It mentions that we can
`tabulate` a function, e.g., represent `Bool -> String` as `(String, String)`.
It doesn't say much more than this, but we can do our own research. Peep the
`Representable` class from [adjunctions][adjunctions]:

[adjunctions]: https://hackage.haskell.org/package/adjunctions-4.4/docs/Data-Functor-Rep.html#t:Representable

```haskell
class Distributive f => Representable f where
  type Rep f :: *
  tabulate :: (Rep f -> a) -> f a
  index    :: f a -> Rep f -> a
```

This thing is exactly the transformation we're looking for; we can "represent"
some structure `f a` as a function `Rep f -> a`, and tabulating gets us back the
thing we had in the first place.

So the trick here is then to determine `f` for the `Rep f` that corresponds to
our `codata` structure. Presumably that thing is exactly the record we worked
out above.

What's interesting about this approach is that it's exactly
[scrap-your-typeclasses.][sytc] And it's exactly how typeclasses are implemented
in Haskell. And last I looked, it's the approach that Elm recommends doing
instead of having typeclasses. Which makes sense why it's annoying in Elm,
because the language designers are forcing us to hand-compile our code! But I
don't need to beat that dead horse any further.

[sytc]: https://www.haskellforall.com/2012/05/scrap-your-type-classes.html

## Thoughts

Something that piqued my interest is a quote from the paper:

> Functional langauges are typically rich in data types ... but a paucity of
> codata types (usually just function types.)

This is interesting, because functions are the only non-trivial source of
contravariance in Haskell. Contravariance is the co- version of (the poorly
named, IMO) covariance. Which is a strong suggestion that functions are a source
of contravariance *because they are codata,* rather than contravariance being a
special property of functions themselves.

I asked my super smart friend [Reed Mullanix][reed] (who also has a great
podcast episode), and he said something I didn't understand about presheafs and
functors. Maybe presheafs would make a good next paper.

[reed]: https://totbwf.github.io/


## Conclusions

This was a helpful paper to to wrap my head around all this codata stuff that
smart people in my circles keep talking about. None of it is *new,* but as a
concept it helps solidify a lot of disparate facts I had rattling around in my
brain. Doing this final tagless encoding of data types gives us a fast CPS thing
that is quick as hell to run because it gets tail-optimized and doesn't need to
build any intermediary data structures, and gets driven by its consumer. The
trade-off is that CPS stuff is a damn mind-melter.

At Zurihac 2018, I met some guy (whose name I can't remember, sorry!) who was
working on a new language that supported this automatic transformation between
data and codata. I don't remember anything about it, except he would just
casually convert between data and codata whenever was convenient, and the
compiler would do the heavy lifting of making everything work out. It was cool.
I wish I knew what I was talking about.



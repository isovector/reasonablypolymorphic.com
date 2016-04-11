---
layout: post
title: Elm Is Wrong
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

A few weeks ago, on a whim [my friend][ariel] and I decided to hackathon our way
through an [app to help us learn how to play guitar][afro]. In a stroke of
inspiration, we decided to learn something new, and do the project in the [Elm
programming language][elm], about which I had heard many good things.

[ariel]: https://github.com/asweingarten
[afro]: https://github.com/isovector/afro-kravitz
[elm]:

/* TODO(sandy): it was positive at first... */

Consider this post to be *what I wished I knew about Elm before deciding to
write code in it.* Since I can't send this information into the past and save
myself a few weeks of frustration, it's too late for me, but perhaps you, gentle
reader, can avoid this egregious tarpit of a language where abstraction goes to
die.

I jest. Elm's not really that bad.

It's worse.

I realize that such harsh words are going to require a supporting argument. I'll
get there, but in the idea of fairness I want to first talk about the things I
really like in Elm:

1) It's got great documentation.
2) As a *library*, it's really pleasant to work with.
3) ...that's about it.

Unfortunately, Elm isn't a library. It's a language, which just happens to have
a great library. Elm qua the language is an unsurmountable pile of
poorly-thought-out and impossible-to-compose new ideas on top of the least
interesting pieces of Haskell.


## The Typeclass Fiasco

Elm currently doesn't have typeclasses. Evan Czaplicki, the primary
author/designer/benevolent dictator of Elm, [suggests][announce] that
typeclasses might be coming, but that was back in early 2013. As of early 2016,
they're still not around.


The Elm mores [direct][shugoff] questions of "why doesn't Elm have type classes"
to [Gabriel Gonzalez][gg]'s essay "[Scrap Your Typeclasses][sytc]" (henceforth
referred to as SYTC). I was coming
to Elm to learn new things, so I decided to suspend my disbelief and give it a
try. After all, the [blub paradox][blub] indicates we don't know recognize ideas
until it's way too late. And so I decided to play along.

If you don't want to read the essay, SYTC essentially says "hey, why don't we
pass around an object that describes the implementation of the contract that we
care about, rather than having the compiler infer it for us?". If you're
familiar with Scala, this is how they implement typeclasses in terms of
[implicit parameters][implicits]. If you're not, SYTC is equivalent to passing
around a [vtable][vtable] whenever you want to invoke code on a dynamic target.

It's a reasonable approach, and I can sympathize with the fact that actually
writing a typeclass mechanism into your language is a lot a work, especially
when you have something which accomplish the same thing.

Unfortunately for me, after a few days of fighting with the typesystem trying to
get SYTC working, it became glaringly obvious that nobody advocating SYTC in Elm
had actually implemented it. The original essay is written for Haskell,
after all.

So what went wrong? Let's look at a contrived example to get in the mood. The
following type alias might capture some of our intuitions about an enum type:

```elm
type alias Enum a = { elements : Array a }
```

This can be read as, a type `a` is an enum consisting of the values specified by
(and in the order of) `elements`.

Using it might look like this:

```elm
fromInt : Enum a -> Int -> a
fromInt witness idx = get idx witness.elements
```

This function takes a witness (proof) that `a` is an enum type (encoded by the
parameter of type `Enum a`). It then uses the known `elements` of that witness
to find an element corresponding to the `Int` passed in.

Now let's wrap up this `fromInt` with a corresponding `toInt` into a new
"typeclass", which we'll call `Ord a`. `Ord a` is a witness that type `a` is
[well-ordered][ordered], which is to say that for any two `a`s, one is
definitely less than or equal to another[^1].

[^1]: Integers have this property. Shapes don't.

In Elm:

```elm
type alias Ord a = { fromInt : Int -> a
                   , toInt   : a -> Int
                   }
```

We're kind of cheating here by getting this property via a bijection with the
integers, but it's for a good reason that I'll get into later.

/* TODO(sandy): talk about dict comparable */

For sake of example, now imagine we want to implement [bucket sort][bucket] as
generically as possible:

```elm
bucketSort : [a] -> [a]
```

/* TODO(sandy): type annotations are a single colon */

But what should `a` be, here? Clearly we can't bucket sort arbitrary data
structures. Promising `a` be an enum seems like a good start, so we add a
witness:

/* TODO(sandy): maybe rename Enum => Finite, and expound on its semantics */

```elm
bucketSort : Enum a -> [a] -> [a]
```

Unfortunately, this is breaking our abstraction barrier. The semantics we
adopted for `Enum a` are only sufficient to know that there are a finite number
of `a` values, but we don't have a canonical means of arranging buckets. For
that, we require an `Ord a` witness too:

```elm
bucketSort : Ord a -> Enum a -> [a] -> [a]
```

Our function is now implementable, but at the cost of having to pass around an
additional two arguments everywhere we go. Unpleasant, but manageable. We have
this extra problem now, is that our witnesses must be passed to the function in
the right order. The more powerful the abstractions you write, the more
constraints you need on your types, and thus the heavier these burdens become.
Haskell98, for example, defines [16 basic typeclasses][haskell98]. This is
before you start writing your *own* abstractions.

/* TODO(sandy): good place to talk about abstracting away pain */

To digress for a moment, One of Elm's features that I was genuinely excited
about was its so-called [extensible records][extensible]. These are types which
allow you to do things like this:

```elm
type alias Positioned a = { a | x : Float
                              , y : Float
                              }
```

This says that a `Positioned a` is any `a` type which has `x` and `y` fields
that are `Float`s. Despite being exceptionally poorly named (think about it --
saying something is `: Positioned a` is strictly less information than saying
it is `: a` for any non-polymorphic `a`), it's a cool feature. It means we can
project arbitrarily big types down to just the pieces that we need.

This gave me a thought. If I can build arbitrarily large types and enforce that
they have certain fields, it means we can collapse all of our witnesses into a
single "directory" which contains all of the typeclass implementations we
support. We add a new parameter to our earlier typeclass signatures, whose only
purpose is to be polymorphic.

```elm
type alias Enum t a = { t
                      | elements : Array a
                      }

type alias Ord t a = { t
                     | fromInt : Int -> a
                     , toInt   : a -> Int
                     }
```

We can look at this as now saying, a type `a` is well-ordered if and only if we
can provide a witness record of type `t` containing fields `fromInt` and `toInt`
with the correct type signatures. This record might *only* contain those fields,
but it can also contain other fields -- maybe like, fields for other
typeclasses?

Let's do a quick sanity check to make sure we haven't yet done anything
atrocious.

```elm
type Directions = North | East | West | South
witness = { elements = fromList [ North, East, West, South ]
          , fromInt  = -- elided
          , toInt    = -- elided
          }
```

To my dismay, in writing this post I learned that Elm's repl (and presumably Elm
as a language) doesn't support inline type annotations. That is to say, it's a
syntax error to write `witness : Enum t Directions` at the term-level. This is
an obvious inconsistency where these constraints can be declared at the
type-level, and then evaluated with the same terms. But I digress. Suffice to
say, our witness magic is all valid, working Elm -- so far, at least.

Let's take a moment to stop and think about what this extra type `t` has bought
us. `Enum t a` is a proof that `a` is an enum, as indicated by a witness of type
`t`. Since `t` has heretofore been polymorphic, it has conveyed no information
to us, but this is not a requirement. Consider the type `Enum (Ord t a) a`,
in which we have expanded our old polymorphic parameter into a further
constraint on our witness -- any `w : Enum (Ord t a) a` is now a witness that
`a` is both an enum *and* well-ordered.

This is a significant piece of the puzzle in our quest to *Scrap Our
Typeclasses*. We can now bundle *all* of our typeclass witnesses into a single
structure, which can be passed around freely. It's still a little more work than
having the compiler do it for us, but we've gone a long way in abstracting the
problem away from user code.

The final piece, is to provide an automatic means of deriving typeclasses and
bundling our results together. Consider this: in our toy example, `Enum t a`
already has an (ordered) list of the `elements` in the type. This ordering is
completely arbitrary and just happened to be the same as which order the
programmer typed them in, but it *is* an ordering. Knowing this, we should be
able to get Elm to write us an `Ord t a` instance for any `Enum t a` we give it
-- if we don't feel particularly in the mood to write it ourselves:

```elm
derivingOrd : Enum t a -> Ord (Enum t a) a
derivingOrd w = { w
                | fromInt = \i -> get i w.elements
                | toInt   = -- elided, but in the other direction
                }
```

We send it off to Elm, and...

> The type annotation for `derivingOrd` does not match its definition.
>
> 13│ derivingOrd : Enum t a -> Ord (Enum t a) a
>                   ^^^^^^^^^^^^^^^^^^^^^^^^^^^^

...uh oh. We've broken Elm! The issue is that `{a | b = c}` is strictly record
*update* syntax -- it requires `a` to *already have* a `b` field. There is no
corresponding syntax to *add* fields -- not even if `a` is polymorphic and we
don't know that it *doesn't* have field `b`.




[announce]: http://elm-lang.org/blog/announce/0.7
[direct]: https://github.com/elm-lang/elm-compiler/issues/38#issuecomment-116748295
[gg]: http://www.haskellforall.com/
[sytc]: http://www.haskellforall.com/2012/05/scrap-your-type-classes.html
[blub]:
[implicits]:
[vtable]:
[ordered]:
[bucket]:
[extensible]: http://elm-lang.org/docs/records#record-types
[haskell98]: https://www.haskell.org/onlinereport/basic.html#standard-classes













































I've spent the last few weeks writing an app in [Elm][elm]. My first impressions
of the language were very positive, but my complaints kept growing and growing.

no typeclasses; no means of implementing them
- just use records
- doesn't work. not reusable
- if you have overhead necessary at the library level, fine
- but if you pass this complexity off to the end uesr that is unacceptable
- that means your language is not powerful enough
- c has this problem. void* isn't powerful enough for polymorphism, so you also
    need to pass in the size of your datatype. everywhere. you can't abstract
    over it. the end user has to care about that shit.
- c++ fixes this by providing templates. now a library writer can write the
    extra complicated stuff once, but end users don't have to worry about it.
    it's a problem we have solved through abstraction

- elm doesn't have typeclasses. okay, fine. but it sort of does.
- comparable is a typeclass which dict is implemented in terms of. but you can't
    make your own instances of comparable. so you can't put user defined types
    as the keys in a dict. [scrap your typeclasses](http://www.haskellforall.com/2012/05/scrap-your-type-classes.html)
- whenevery you complain about not having typeclasses in elm, they point you at
    a paper about using records as your typeclass.
- but maybe nobody has ever taken their own advice and tried to use records as a
    typeclass. because it only superficially works
- so first, you need to reimplement dict in terms of your new recordclass thing.
    all of a sudden you lose a lot of guarantees, because you need to pass a
    witness of a constraint, which means you can use different witnesses at
    different times, and break shit. not good
- but this reimplementaiton is 100 lines of boilerplate lifting and unlifting.
    it sucks.
- but then you make a new typeclass, which is orthogonal. what it would be nice
    to do is create a SINGLE witness of all of your typeclasses for a given
    type.
- this reduces any mental overhead for a user. okay fine, the compiler can't do
    this for me, but it's 0 work. i just pass the same parameter around whenever
    i want to use a typeclass method.
- the using method can just project this big typeclass down to the piece it
    needs, and everything works lovely
- but THIS doesn't work either, because elm decided to make up some poorly
    thought out semantics for records. you can project downwards, but you can't
    perform induction
- so now you need to write O(n*2^n) different lifting functions for the combination
    of typeclasses you want. and each one has to have O(n) mechanical lines of
    code in order to construct the thing you want to construct. that is O(n^2*2^n)
    library work to get composable semantics for typeclasses
- for fucks sake

- elm gets around this complexity by just decided to do everything the hard way.
- there is not map but List.map and Dict.map and Array.map and you need to type
    it out every time. and it gets really old. the point of mapping over thigns
    is that you don't care what type the container is.
- if i make something with the wrong container type, and i want to update that
    to a semantically equivalent type for performance reasons, i need to
    refactor my ENTIRE CODEBASE to do it. this breaks the shit out of
    encapsulation
- haskell has solved this problem with typeclasses. OOP has solved this problem
    with interfaces and/or single dispatch.
- the argument against typeclasses is that they're too complicated [citation].
    but here's the thing. first of all that arugment assumes that you know best,
    and you don't.
- the other thing is that without a suitable replacement you are offloading all
    of that conceptual workload into mechanical workload, and you can't automate
    mechanical workload.
- with conceptual workload you solve it once in a library, and people never need
    to know unless they're curious

- elm has this thing called extensible types, but umm it seems to work
    backwards.
- instead of extending a type, what you're doing is projecting any record down
    to something that has these fields
- cool -- this is essentially a [structural
    type](https://twitter.github.io/scala_school/advanced-types.html#structural) in scala
```elm
type alias Positioned a =
  { a | x : Float, y : Float }
```
- this is the mechanism we'd want for projecting our typeclass witness down to
    the relevant pieces
```elm
type alias Ord t a = { t | toInt : a -> Int, fromInt : Int -> a }
```
- here `t` would be the complete typeclass witness, and `Enum t a` for a
    specific `a` and polymorphic `t` (preserving the type information of my
    other typeclass witnesses) would project it down to the bits we care
    about
- unfortunately no lifting can occur in the opposite direction:
```elm
type alias Ord t a = { t | enums : List a }

derivingOrd : Enum t a -> Ord (Enum t a) a
derivingOrd enum =
    let toInt'   e = ...
        fromInt' i = ...
    in { a | toInt = toInt'
           , fromInt = fromInt'
           }
```
- this fails with a compiler error thinking I'm trying to update a record
    instead of trying to add new fields to a record.
- but that is not what I wanted! i wanted to perform induction and say that for
    any `Enum t a` I can create a `Ord (Enum t a) a` by doing something dumb
    with my underlying list to assume they're well-ordered

- alright fine. we get it. you're hard for typeclasses. what else?
- i wanted to use a library to provide localstorage
- i can't. because evan hasn't vetted it personally.
- because that's how libraries work in elm. the guy has to personally, manually
    vet every library.
- that doesn't scale. even a little bit.
- so because this guy hasn't said "yes this code is OK to run", I can't use that
    code in MY code with any of the standard tools
- what the fuck kind of world are we living in?
- that's the thing about libraries; they're user generated content.
- if you want to do that with the standard library; great. that makes sense. all
    the power to you
- but you can't control the entire ecosystem because the ecosystem is how people
    fix problems in the original language. look at boost. look at hackage.
    people build tools that are missing, and people use them if they're the
    right tool for the job

- ok so let's talk about the elm architecture
- it's a FRP program with only one function that can accept signals -- main
- strange choice; but the argument is that this promotes pure code. that's cool.
    i can respect that
- but here's the problem; signals are a really natural paradigm for programming
    in, and lots of problems don't fit nicely into purity
- let's say we have a page that has a button on it. the button should change the
    state of this page
- because buttons produce a signal, we need to route it into main.
- but now my parent needs to know about this signal. and its parent.
- now main needs to know about this button
- the argument against monadic signals is the following dichotomy if they're
    adopted:
    * in order to be efficient, they need to be non-referentially transparent
- why? well, let's say you want to fold over the entire mouse position. either
    you need to save all of the mouse positions, in case you want to spin up a
    signal that depends on them. or you can NOT, and be able to construct two
    different signals with the same rhs which are nevertheless different.
- at first blush this is bad. at second blush, there are at least 3 functions in
    the stdlib that already have this problem: for example,
    [every](http://package.elm-lang.org/packages/elm-lang/core/3.0.0/Time#every)
- my argument is furthermore that signals are essentially `IO` anyway -- they
    can talk to the outside world, so they aren't all that pure

[elm]:


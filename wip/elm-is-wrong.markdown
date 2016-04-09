---
layout: post
title: Elm Is Wrong
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

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
type alias Ord t a = { t | enums :: List a }

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


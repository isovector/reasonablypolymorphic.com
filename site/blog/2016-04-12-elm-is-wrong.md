---
layout: post
title: Elm Is Wrong
date: 2016-04-12 08:05
comments: true
tags: rebuttal, technical, programming
---

A few weeks ago, on a whim [my friend][ariel] and I decided to hackathon our way
through an [app to help us learn how to play guitar][afro]. In a stroke of
inspiration, we decided to learn something new, and do the project in the [Elm
programming language][elm], about which I had heard many good things.

[ariel]: https://github.com/asweingarten
[afro]: https://github.com/isovector/afro-kravitz
[elm]: http://elm-lang.org

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
3) ...and well, that's about it.

Unfortunately, Elm isn't a library. It's a language, which just happens to have
a great library. Elm qua the language is an unsurmountable pile of
poorly-thought-out and impossible-to-compose new ideas on top of the least
interesting pieces of Haskell.


## Scrapping my Typeclasses

I've got a really appropriate word for dealing with dicts in Elm. *Painful.*
It's not any fault of the library, but of the language. Let's look at an
example of working with one:

```elm
insert : comparable -> v -> Dict comparable v -> Dict comparable v
```

"What is this `comparable` thing?" you might ask. A little documentation
searching leads to:

> This includes numbers, characters, strings, lists of comparable things, and
> tuples of comparable things. Note that tuples with 7 or more elements are not
> comparable; why are your tuples so big?

First of all, ever heard of the [zero-one-infinity][infinity] rule? Second of
all, fuck you and your 6-element-max comparable tuples[^3].  Anyway. The real
thing I want to discuss is how `comparable` is magical compiler stuff. I'd argue
that whenever magical compiler stuff rears its head, things are going to get
arbitrary and stupid.

[^3]: Haskell's tuples stop working in a very real way at 63 elements, but
that's at least far into the realm of [unimaginably large][17].

Lo and behold, things get arbitrary and stupid around `comparable`. Since it's
compiler magic, we mere mortals are unable to make our instances of
`comparable`, which is to say, you can't use any custom data-types as the key of
a dictionary in Elm.

[infinity]: http://www.catb.org/jargon/html/Z/Zero-One-Infinity-Rule.html
[17]: http://mindingourway.com/respect-for-large-numbers/

Did you hear that? That was the sound of type-safety dying.

Haskell solves this problem with what seams like a similar solution. In Haskell:

```haskell
insert :: Ord k => k -> a -> Map k a -> Map k a
```

Here, the bit before the `=>` is a constraint that `k` must be comparable. The
difference is that programmers in Haskell (as opposed to compiler writers) can
define their own instances of `Ord k`, and so in Haskell, the only limit is our
imagination. In Haskell, these constraints are called "typeclasses", and they're
roughly equivalent to interfaces in OOP languages (except that you don't need to
be part of the typeclass at declaration time).

Elm currently doesn't have typeclasses. Evan Czaplicki, the primary
author/designer/benevolent dictator of Elm, [suggests][announce] that
typeclasses might be coming, but that was back in early 2013. As of early 2016,
they're still not around.

The Elm mores [direct][shugoff] questions of "why doesn't Elm have type classes"
to [Gabriel Gonzalez][gg]'s essay "[Scrap Your Typeclasses][sytc]" (henceforth
referred to as SYTC). I was coming to Elm to learn new things, so I decided to
suspend my disbelief and give it a try. After all, the [blub paradox][blub]
indicates we don't know recognize ideas until it's way too late. And so I
decided to play along.

[shugoff]: https://github.com/elm-lang/elm-compiler/issues/38#issuecomment-116748295

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

This can be read as, a type `a` is an enum consisting of the unique values
specified by `elements`. We make no claims about the ordering of this `Array`.
(We can't use `Set` because it requires a `comparable` value, which is the whole
problem.)

Using it might look like this:

```elm
enumCount : Enum a -> Int
enumCount witness = Array.length witness.elements
```

This function takes a witness (proof) that `a` is an enum type (encoded by the
parameter of type `Enum a`). It then uses the known `elements` of that witness
to figure out how many different enum values of type `a` there are.

To do something a little more useful, let's wrap up a pair of functions
`fromInt` and `toInt` into a new "typeclass", which we'll call `Ord a`. `Ord a`
is a witness that type `a` is [well-ordered][ordered], which is to say that for
any two `a`s, one is definitely less than or equal to another[^1].

[^1]: Integers have this property. Shapes don't.

In Elm:

```elm
type alias Ord a = { fromInt : Int -> a
                   , toInt   : a -> Int
                   }
```

We're kind of cheating here by getting this property via a bijection with the
integers, but it's for a good reason: you can put integers into a dictionary in
Elm (they *are* `comparable`, so with one we can emulate Haskell's constraints
on dictionary keys).

For sake of example, now imagine we want to implement [bucket sort][bucket] as
generically as possible:

```elm
bucketSort : [a] -> [a]
```

But what should `a` be, here? Clearly we can't bucket sort arbitrary data
structures. Promising `a` be an enum seems like a good start, so we add a
witness:

```elm
bucketSort : Enum a -> [a] -> [a]
```

Unfortunately, this is breaking our abstraction barrier: the semantics we
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
type alias Enum t a = { t | elements : Array a
                          }

type alias Ord t a = { t | fromInt : Int -> a
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
          , fromInt  = -- elided for brevity
          , toInt    = -- elided for brevity
          }
```

To my dismay, in writing this post I learned that Elm's repl (and presumably Elm
as a language) doesn't support inline type annotations. That is to say, it's a
syntax error to write `witness : Enum t Directions` at the term-level. This is
an obvious inconsistency where these constraints can be declared at the
type-level and then evaluated with the same terms. But I digress. Suffice to
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
already has an (ordered) array of the `elements` in the type. This ordering is
*completely arbitrary* and just happened to be the same as which order the
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

<pre>
The type annotation for `derivingOrd` does not match its
definition.

13│ derivingOrd : Enum t a -> Ord (Enum t a) a
                  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^
</pre>

...uh oh. We've broken Elm! The issue is that `{a | b = c}` is strictly record
*update* syntax -- it requires `a` to *already have* a `b` field. There is no
corresponding syntax to *add* fields -- not even if `a` is polymorphic and we
don't know that it *doesn't* have field `b`.

*Prima facie*, it's reasonable to stop here and think to ourselves, "oh, well I
guess we can't do this -- there's probably a good reason." Regrettably, there is
not a good reason. Nothing we've done so far is an unreasonable expectation of
the type-checker; in fact, the only thing in our way is the parser. To
reiterate, all we're missing is the ability to add fields to a record.

[So I filed a bug][bug].

As it turns out, [Elm used to support this feature][failhard], but it was
removed because "pretty much no one ever used field addition or deletion."
Forgive me for being pedantic here, let's look at some statistics. At time of
writing, there are [119 people who write Elm on GitHub][users], who had written
a total of [866 repositories][notmany] before this feature was removed.

119 people[^2] failing to find a use-case for a bleeding-edge new feature
shouldn't be an extreme surprise to anyone, especially given that they had no
guidance from the original authors on how to use this feature. Furthermore, the
first mention of an open-union type facility (essentially what we're trying to
implement here) I can find reference to [was published in 2013][effects] -- not
a huge amount of time to work its way into the cultural memeplex.

[^2]: Of whom, we can assume the majority are web-programmers, and, by
association, that Elm's is likely the strongest type-system to which they have
been exposed.

My bug was closed with the explanation "[I don't want to readd this
feature.][closed]" If I sound salty about this, it's because I am. Here's why:

The thing that separates good programmers from OK ones is the ability to which
they can develop abstractions. From the [best][boost] [programmers][lens] we get
[libraries][jquery], and the rest of us write applications that use those
libraries. The reason we have libraries is to fix holes in the standard library,
and to allow us to accomplish things we otherwise couldn't.

Elm takes a very peculiar stance on libraries. Libraries which don't have the
blessing of Czaplicki himself [allegedly aren't allowed to be published][wat].

What. The. Fuck.

But again I digress. Libraries exist to overcome shortcomings of the language.
It's okay to make library authors do annoying, heavy-lifting so that users don't
have to. Which is why I'm particularly salty about the whole "we couldn't figure
out a use for it" thing.

Elm doesn't have typeclasses, and doesn't have a first-class solution in their
interim. Instead, the naive approach requires a linear amount of boilerplate
*per-use*, which is developer time being wasted continually reinventing the
wheel. If Elm's syntax supported it, we could solve this problem once and for
all, put it in a library somewhere, get Czaplicki's explicit go-ahead, and be
done with it. But we can't.

In the worst case, given $n$ typeclasses, the naive solution requires $O(n)$
additional witnesses to be passed around at every function call. The proposal
presented in this essay would bring this boilerplate to $O(1)$. Definitely an
improvement.

But here's the most deplorable state of affairs. Trying to power through with
our witness approach *and retain type-safety while doing it* requires in
a super-exponential amount of code to be written. Let's see why:

Given $n$ typeclasses, there are $2^n$ different combinations of
having-them-or-not. Let's group these sets by size -- ie. how many typeclasses
they contain -- and assume we only need to lift from size $k$ to size $k+1$.  In
this case, we're left with $2^{n-1}n$ separate lifting functions we need to
write in order to add any typeclass to any set of other typeclasses.  Notice
that this is not a worst-case, this is the exact solution to that problem. This
is just the number of functions. Since each lift is required to explicitly
reimplement all of the existing typeclasses, it grows at $O(n)$, giving us a
tight upper bound on the amount of code we need to write in order to achieve
type-safety and witness compacting. Ready for it?

$O(2^{n-1}n^2)$

That function grows so quickly it's no longer super-exponential. It's officially
reached super-duper-exponential. We've hit ludicrous speed here, people. And the
worst part is that it's *all* boilerplate that we know how to write (because we
already did it), but aren't allowed to because Czaplicki can't find a use-case
for this feature.

Hey! I found one! Pick me! Pick me!

Elm gets around all of this complexity by ignoring it and making us do
everything the hard way. There is no `map` function, but there are `List.map`,
`Dict.map`, `Array.map` among others, and *none of them are related to one
another*. This is not only annoying, but also breaks the abstract data-type
guarantee: our call-sites are now tightly coupled to our implementation details.
If I decide to change from a `List a` to an `Array a` for efficiency reasons, my
*whole codebase needs to know about it*.

Haskell solved this problem with typeclasses. OOP with single-dispatch. Elm
mysteriously seems to follow in PHP's footsteps of having lots-and-lots of
really similar functions (for all intents and purposes being in the same
namespace), saying "fuck it! we'll do it live!".

I have another million complaints about other semantics of Elm's design, but in
comparison they seem small and this post is already long enough. It's such a
shame that Elm is so terrible from a PL standpoint. Its rendering primitives are
state-of-the-art, and I really wanted to like it despite myself.

Too bad. As it turns out that really wanting to like Elm isn't enough to
actually like Elm.

[announce]: http://elm-lang.org/blog/announce/0.7
[direct]: https://github.com/elm-lang/elm-compiler/issues/38#issuecomment-116748295
[gg]: http://www.haskellforall.com/
[sytc]: http://www.haskellforall.com/2012/05/scrap-your-type-classes.html
[blub]: http://www.paulgraham.com/avg.html
[implicits]: http://danielwestheide.com/blog/2013/02/06/the-neophytes-guide-to-scala-part-12-type-classes.html
[vtable]: https://en.wikipedia.org/wiki/Virtual_method_table
[ordered]: https://en.wikipedia.org/wiki/Well-order
[bucket]: https://en.wikipedia.org/wiki/Bucket_sort
[extensible]: http://elm-lang.org/docs/records#record-types
[haskell98]: https://www.haskell.org/onlinereport/basic.html#standard-classes
[bug]: https://github.com/elm-lang/elm-compiler/issues/1283
[failhard]: http://elm-lang.org/blog/compilers-as-assistants
[notmany]: https://github.com/search?q=created%3A%3C2015-11-19+language%3AElm+extension%3Aelm+language%3AElm+elm&type=Repositories&ref=searchresults
[users]: https://github.com/search?o=desc&q=language%3AElm&ref=searchresults&s=repositories&type=Users&utf8=%E2%9C%93
[closed]: https://github.com/elm-lang/elm-compiler/issues/1283#issuecomment-183515916
[effects]: http://okmij.org/ftp/Haskell/extensible/exteff.pdf
[boost]: http://www.boost.org/
[lens]: https://github.com/ekmett/lens
[jquery]: https://jquery.com/
[wat]: https://github.com/xdissent/elm-localstorage/issues/1#issuecomment-122585560


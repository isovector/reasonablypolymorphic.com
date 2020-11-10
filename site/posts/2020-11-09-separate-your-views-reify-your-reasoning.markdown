---
layout: post
title: "Separate Your Views; Reify Your Reasoning"
date: 2020-11-09 21:45
comments: true
tags: haskell, tactics
---

Continuing our discussion of tactics, today I'd like to talk about my recent
diff on [hls-tactics-plugin][hls-tactics]. I learned a deep lesson about writing
software in this commit and wanted to share the insight.

[hls-tactics]: https://github.com/haskell/haskell-language-server/tree/master/plugins/tactics

Some background before we get started. The `hls-tactics-plugin` is capable of
automatically generating small snippets of Haskell code. Like how, near the end
of a proof, mathematicians will throw their hands in the air and say "the
remainder is obvious," we'd like to empower software engineers in the same way.
The idea is for the computer to pick up where you left off, and fill in
expressions that have a uniquely best solution (for some meaning of "best".) In
practice, it works quite well.

To make this happen, we need to know the desired type at the hole to be filled,
as well as what's in scope, and various other pieces of metadata --- such as
what's already been used and where values came from. The record for this data is
called the `Judgment`, and originally looked like this:

```haskell
data Judgment = Judgment
  { _jHypothesis        :: Map OccName Type
  , _jAmbientHypothesis :: Map OccName Type
  , _jDestructed        :: Set OccName
  , _jPatternVals       :: Set OccName
  , _jPositionMaps      :: Map OccName [[OccName]]
  , _jAncestry          :: Map OccName (Set OccName)
  , _jBlacklistDestruct :: Bool
  , _jWhitelistSplit    :: Bool
  , _jIsTopHole         :: Bool
  , _jGoal              :: Type
  }
```

As you can probably tell, this data structure grew organically, one field and
feature at a time. The only truly necessary fields are `_jHypothesis` and
`_jGoal`, the first of which tracks what's in scope and its type, and the second
tracks the type we're currently trying to synthesize a value of. The rest of
this stuff is used exclusively for intelligently narrowing the exponentially
large space of possible solutions we could generate. They're necessary for
getting fast/good results, but in essence, just track heuristics that in
practice help get the right answer. There's no *theoretical justification* for
them. As such, these fields are **properties of the implementation, not of the
domain.**

This is an extremely important realization. Fields like `_jDestructed` and
`_jAncestry` are [exploded views][constraints-liberate] on our data. They exist
in a non-compositional form, serving only to the ad-hoc queries I've thought of
today, and are likely unhelpful for whatever search heuristic I decide to
implement next. To illustrate this, `_jPatternVals` tracks which values came
from bindings in a pattern match (useful for generating structurally-smaller
recursive terms), while `_jAncestry` tracks if a value is descendant from
another in some way. And `_jDestructed` records whether or not we've already
pattern matched on any particular values. Clearly, there is a lot of overlap in
these fields. Taken in aggregate, they feel like a myopic, denormalized
representation of data provenance.

[constraints-liberate]: https://www.youtube.com/watch?v=GqmsQeSzMdw

As a general rule, I tend to have a great distrust in denormalized
representations. By their very nature, they blur the notion of *source of truth*
--- whom should you believe if your denormalized data sources disagree with one
another? Furthermore, almost no human domains are intrinsically denormalized; it
simply isn't how our brains our wired --- we like to think in deep notions of
identity. These concerns together suggest that denormalized representations are,
again, artifacts of the implementation, rather than meaningful carved joints in
reality. Worse, it's hard to initialize a non-empty denormalized system. Making
sure all of the data sources agree is a bigger source of bugs than sprinkling
sugar on your kitchen floor.

All of this is to say: why not just model the data provenance in `Judgment`
directly? With that as an explicit source of data, it's trivial to reimplement
the fields like `_jAncestry` et al. as views over the real datastructure.

This is a greatly under-appreciated feature of Haskell's record system. Because
field selectors are just functions whose input is the record in question, there
is no syntactic difference between them and arbitrary functions over the same
record. Most other languages enforce a syntactic difference between class fields
and class methods, which is where the [mutator method pattern][mutator] comes
from. Like most software patterns, this one too is unnecessary in Haskell.

[mutator]: https://en.wikipedia.org/wiki/Mutator_method

Instead, we can just remove the `_jAncestry` field from `Judgment`, and then
implement a function `_jAncestry :: Judgment -> Map OccName (Set OccName)`
which computes the desired view from the data provenance. Amazingly, *all calling
code will just work,* and doesn't need to know that the underlying
datastructure has changed.

Of course, the usual zealots will point out that the runtime performance will
have changed through this transformation. And that's probably true, but what's
also almost certainly true is that *it doesn't matter.* It's extremely unlikely
that this field is the linchpin of my algorithm's asymptotics, so don't worry
about it unless it becomes a problem. And if it does, I'm sure you can find a
clever way of caching this field without confusing the fact that it is a view on
data, and not data itself.

The crux of my change was to rip out all of my data views and add provenance to
the hypothesis. The diff is delightfully red:

```diff
 data Judgment = Judgment
-  { _jHypothesis        :: Map OccName Type
-  , _jAmbientHypothesis :: Map OccName Type
-  , _jDestructed        :: Set OccName
-  , _jPatternVals       :: Set OccName
-  , _jPositionMaps      :: Map OccName [[OccName]]
-  , _jAncestry          :: Map OccName (Set OccName)
+  { _jHypothesis        :: Map OccName (HyInfo Type)
   , _jBlacklistDestruct :: Bool
   , _jWhitelistSplit    :: Bool
   , _jIsTopHole         :: Bool
   , _jGoal              :: Type
   }
```

Six denormalized fields replaced with one normalized source. This is already a
huge improvement in terms of engineering confidence. The relationship between
the many maps and sets of `OccName`s in the old system is inevitably going to be
under-documented and implementation-defined. Even as the guy who wrote each of
those features, I doubt I'd be able to create a well-formed `Judgment` by hand.

The next step was to implement `HyInfo`, which tracks the type and provenance of
a value in the hypothesis:

```haskell
data HyInfo a = HyInfo
  { hi_provenance :: Provenance
  , hi_type       :: a
  }
```

To define `Provenance`, I added a data constructor for each different sort
of value that I was aware of. By explicitly tagging all of this data, we can
attach the previously-denormalized data that must exist, ensuring the
entire datastructure is correct by construction.

```haskell
data Provenance
  = TopLevelArgPrv
      OccName   -- ^ Binding function
      Int       -- ^ Argument Position
  | PatternMatchPrv
      PatVal
  | ClassMethodPrv
      Class
  | DisallowedPrv
      DisallowReason
      Provenance
```

The arguments to `PatternMatchPrv` have been factored out into their own type,
because pattern values are especially interesting and require further
processing, outside the scope of this post. Of particular interest is
`DisallowedPrv`, which we'll discuss in a moment.

In the `hls-tactics-plugin` codebase, we made judicious use of a helper function
`withHypothesis :: (Map OccName Type -> Map OccName Type) -> Judgment ->
Judgment`. Functions which, for example, wanted to introduce new values into
the hypothesis (such as after pattern matching) would call `withHypothesis` and
directly insert their values. If we wanted to exclude values from the search
space, we'd just `withHypothesis . Map.filter` them out. The result was lots of
call-sites directly fiddling with the state in unprincipled ways. Nobody
actually needed the full power of `Map OccName Type -> Map OccName Type`; it
just happened to be the only convenient way of manipulating the hypothesis.

I removed `withHypothesis`, and instead replaced it with semantically meaningful
functions, like `introduceLambdaValues`, `introducePatVals` and
`disallowUsageOf`. The implementations hadn't changed, but now they were
encapsulated into a function call, rather than be scattered about at call sites.

The `disallowUsageOf` function is particularly interesting.

Besides the importance of normalization, this change taught me one other thing:
the necessity of reifying your reasoning. Ollie Charles presents an excellent
example of this in [Who Authorized These Ghosts][ghosts], but I'd never fully
appreciated the technique until now. The gist of it is that it's important not
just to track state, but also to track why you believe the state is what it is.
In Ollie's example, he's tracking authorization status (a boolean,) but to
prevent security holes, his application internally requires a token proving the
user is allowed to act. This is [parsing, not validating][parse] taken to the
extreme; programmers are required to produce a token to call privileged
functions, and the only way of obtaining that token is by checking the
authorization state.

[ghosts]: https://ocharles.org.uk/blog/posts/2019-08-09-who-authorized-these-ghosts.html
[parse]: https://lexi-lambda.github.io/blog/2019/11/05/parse-don-t-validate/

The `disallowUsageOf` function, and corresponding `DisallowedPrv` provenance
constructor above fill a very similar role.

Attentive readers will have noticed that the `_jDestructed` field is not truly a
measure of provenance. In fact, it's tracked exclusively to prevent production
of code of the form:

```
case x of
  Blah -> case x of
    Blah -> case x of
      Blah -> ...
```

However, a good heuristic when writing Haskell code is that if possible, a value
should be used exactly one time. To a first approximation, we can produce a view
of `_jDestructed` by checking to see if any `PatternMatchPrv` is a decedent of
the value in question. However, this doesn't work for types that don't contain
product types. For example, the matches of `Bool` are `True` and `False`;
neither of which would produce a `PatternMatchPrv`.

But because `_jDestructed` is used only to prevent pattern matching, it filled a
similar role to filtering out hypotheses via `withHypothesis`. In both cases we
could have simply removed the value from hypotheses, and having removed it from
the source of truth of what's in scope would certainly prevent it from ever
being used. But this also wreaked havoc with tracking provenance, as removing
the value would also remove its provenance, so downstream children would become
orphaned and wouldn't know where they came from.

On the surface, this looks like a bug, but I don't think it's a bug in the true
sense. Instead, this is a problem of insufficient reification. Removing a value
from the in-scope set is again an *exploded view* of the data. It's again not a
feature of the problem, but the implementation. What we'd instead like to
track is that a particular value is *disallowed,* rather than *non-existent.*
And once something is declared disallowed, if we track the reason, later code
can reevaluate for themselves whether that judgment is still a reasonable means
for exclusion.

At the end of the day, I exposed a function `jHypothesis :: Judgment -> Map
OccName (HyInfo Type)` (not `_jHypothesis` --- note the underscore!) which
pro-actively filtered out all of the `DisallowedPrv` values in the
`_jHypothesis`. This means the data that the *entire program sees is itself a
view* on the real datastructure. Internally we can track disallowed values, and
externally we don't show the disallowed values unless explicitly asked for.

The result of all this refactoring is a delightfully simplified codebase.
Its core datastructure is now correct-by-construction, meaning it's impossible
to produce an inconsistent value that was so common under the old formulation.
Furthermore, no call-site needs to change; appropriate views on the data exist
as shunts, invisible massaging the new datastructure into the old. These
call-sites can (and should) be cleaned up to use the new datastructure more
directly, but that can happen incrementally in subsequent changes. And best of
all, our new data representation is infinitely more useful. Because it models
the problem domain rather than the peculiarities of the implementation, it can
be reused for future features. While the size of the old datastructure was
`O(n)` in the number of features, this new one is `O(1)`.

---

If you enjoyed this post, please consider picking up a copy of my new book
[Algebra-Driven Design][add]. In it, you'll learn techniques like this one to
dramatically improve the quality, maintainability, and reusability of your
software.

[add]: https://algebradriven.design/


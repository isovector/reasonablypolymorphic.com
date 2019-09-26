---
host: Soares Chen
github-user: maybevoid
city: Leipzig
country: Germany
project: "Compiling to Categories, Canonical Type Pragmas"
project-url: "https://github.com/isovector/compiling-to-categories-redux"
arrival-date: 2019-09-18
departure-date: 2019-09-20
---

Soares and I worked our way through Conal's [Compiling to Categories][concat]
paper, and came to the conclusion that he was doing *far too much work.* Conal's
implementation is written as a core plugin, which means he needs to do all of
the hard work of synthesizing dictionaries and fighting against the optimizer.

[concat]: https://github.com/conal/concat

Thankfully, today we have source plugins --- meaning we can implement syntactic
transformations (such as compiling to categories) as actual syntactic
transformations!

Our implementation is pretty tiny, but falls apart in all of the same ways as
Conal's --- namely, you need to be able to inline all the definitions for any
functions you call. We figured we could get around this by looking up unfoldings
and then implementing a quick `CoreExpr` to `HsExpr` pass + aggressively turning
on `-fexpose-all-unfoldings`. We lost steam on the project after realizing how
poorly the paper describes the actual implementation. Fun project, but it didn't
really go anywhere.

After that, I suggested we implement a pragma for telling GHC "this is the type
I want to see in my error messages." GHC will "helpfully" decompose types into
constituent pieces --- which admittedly is usually the right behavior --- but
this prevents you from hiding implementation details when it comes to
`Constraint`s.

The idea: mark abstraction types with a special `{-# CANONICAL #-}` pragma, that
tells error messages to never expand this type. If there's an issue with a
subconstraint, report just the canonical type instead!

We actually got most of this working, though there are still a few bugs in
propagating the pragma information from the parse tree all the way into the
constraint solver. But once the flag is in place, the error messages do the
right thing. Pretty cool, and hopefully coming soon to a GHC release near you.

In addition to all of this, Soares is the implementer of the
[implicit-effects][impl] package, and so we spent a lot of time nerding out
about effects systems. We're both convinced that such things are the solutions
to most programming problems, and just need to figure out how to convince others
of that fact.

[impl]: https://github.com/maybevoid/implicit-effects

Furthermore, Soares comes from the Javascript world, and has a refreshing take
on some of the problems we run into in Haskell that aren't in Javascript. In
particular, we got chatting about Haskell's concurrency model, and how we could
change it in order to make effect systems work better.


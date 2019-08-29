---
host: Boris Rozinov
github-user: oofp
city: Richmond Hill
country: Canada
project: "Type-Sets, Cmptype, and MagicTyFams"
project-url: "https://github.com/isovector/type-sets"
arrival-date: 2019-08-03
departure-date: 2019-08-05
---

Boris has been working on a library for tracking dependent state management of
resources over application lifetimes, complete with refinement of the
possibilities based on specific filters. It's wicked cool, though performs
compiles aggressively slowly. We looked at the performance, and realized the
primary problem is that everything is encoded as type-level lists. We thought
that maybe having a better type-level data structure would be effective.

So I implemented a plugin that solves a type-level `CmpType` for ordering types.
Such a thing means we can effectively write binary search trees for arbitrary
types of kind `*`, and now get all sorts of great performance improvements. We
hunkered down on that, and then on writing BSTs in terms of it. But then I
realized most of the work was actually in getting the plugin to solve the type
family, and not in comparing types, so we spun out another library for
generating plugins.

The result: three libraries. `type-sets`, `cmptype` and `magic-tyfams`; not bad
for a weekend of work.

On Boris' project, we found a bug in GHC's `TypeError` machinery --- it explodes
in the wrong place in the presence of partial type signatures. Having tracked
that down, we did some work on existentializing his types so the partial ty sigs
weren't required. We then thought about how to reduce the boilerplate in his
library, and came up with a combination of Servant and HKD for expressing the
state transition graph.


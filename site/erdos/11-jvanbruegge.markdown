---
host: Jan van Bruegge
github-user: jvanbruegge
city: Munich
country: Germany
project: GHC
project-url: "https://gitlab.haskell.org/ghc/ghc/merge_requests/1730"
arrival-date: 2019-09-14
departure-date: 2019-09-18
---

Jan and I spent a lot of time chatting about row types; he showed me his new
implementation in GHC and I asked lots of stupid questions about it. Together,
we worked on some patches to GHC's custom `TypeError` machinery. The [first of
which][mr1730] only emits custom type errors when they're derived constraints,
rather than the givens that cause excessively loud errors today.

[mr1730]: https://gitlab.haskell.org/ghc/ghc/merge_requests/1730

[The second][mr1739] was to add a priority to type errors. Today, whenever a
custom type error shows up, it completely erases legitimate errors from GHC.
That means an insoluble type equality (eg. asking for `String ~ Bool`) will get
swallowed up by a custom type error that happens at the same time. It's never
helpful, and means type errors are often *actively unhelpful.*

[mr1739]: https://gitlab.haskell.org/ghc/ghc/merge_requests/1739

But GHC already produces two error reports --- the first is for really bad
errors that happen (insoluble type equalities), and the second is for other
things it would like to comment on. Notably, the second report doesn't show up
if the first one happened. Jan and my work was to expose this to the type errors
API:

```haskell
data ErrorPriorty = HighPriority | LowPriority

type family TypeErrorPriorty (priority :: ErrorPriority) (msg :: ErrorMessage)

type TypeError a = TypeErrorPriority 'HighPriority a
```

This change is completely backwards compatible with `TypeError`s as they're used
today, but means we can now selectively control when a type error should be
emitted. Nice!

Besides all of the great Haskell-ing, Jan and his roommates turned out to be
some of the smartest, kindest and most fun people I've had the pleasure to ever
meet. They invited me to their band practice, we saw some break dancing
competitions, and ate an aggressive amount of traditional Bavarian food. Thanks
everyone, I love you all!


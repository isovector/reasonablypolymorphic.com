---
host: Reed Mullanix
github-user: TOTBWF
city: Vancouver
country: Canada
project: Refinery
project-url: "https://github.com/TOTBWF/refinery"
arrival-date: 2019-08-24
departure-date: 2019-08-27
---

(dates are approximate, I actually spent this week staying with Travis Willis,
but Travis and I didn't do any Haskell)

As the only known user of Reed's library `refinery`, I sat him down and had him
explain most of the machinery to me. We spent several hours debugging his new
Scott-encoded v2, eventually figuring it out, and teaching me lots about
Scott-encoding in the process.

On our second encounter, Reed and I attempted to determine whether or not
the polynomial interpretation of monads via Curry-Howard have any interesting
number-theory properties. Neither of our category theory was sufficient to come
up with any satisfactory answers, but it seems like a pretty interesting line of
inquiry.

We then looked at my Dyna editor, working through the semantics of what
structural editing should look like. We then spent some time diving into GHC's
simplifier, trying to figure out why it's so dang slow (one function is
singlehandedly responsible for 20% of compile times.) We're pretty sure that a
Scott-encoding of the `SimplCont` type would be sufficient to kick off wicked
savings, but it seems like a nightmare to actually make happen.


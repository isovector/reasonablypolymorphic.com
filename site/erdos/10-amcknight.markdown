---
host: Andrew McKnight
github-user: amcknight
city: Vancouver
country: Canada
project: GHC
project-url: "https://github.com/amcknight/scont"
arrival-date: 2019-09-07
departure-date: 2019-09-09
excellent: True
---

Andrew has some loft goals about getting AIs to optimize bad algorithms into
good ones; in other words, you write a brute force algorithm and it some how
"massages" it into something that runs fast. That seemed hard, so we instead
decided to focus on GHC's simplifier, which performs similar transformations on
Haskell code. We figured getting familiar with it might be helpful for Andrew's
longer term goals.

We took up Reed and my idea to Scott encode the simplifier --- which should
theoretically improve compiler performance by 20%+. After a few hours of
prototyping Scott-encoded things to ensure we understood how they worked and
why, we jumped into GHC and got going. In our first afternoon we got half of the
work done, and spent the rest of the evening talking about huge world-scale
projects we could tackle, and what modern super-powers would look like.

The next day we wandered around town for a bit, and then got back to business.
After getting stuck in a quagmire of biting off too much for one commit, we
undid some work and were more careful moving forwards. A lot of GHC's simplifier
is written with explicit recursion, but contains lots of ugly fall-through logic
in its pattern matching of such. It's a mess, and desugaring that into something
that can take advantage of the Scott encoding is finicky and easy to get wrong.
Would that GHC took advantage of good Haskell design principles, but alas it
does not.

All in all, 10/10 visit. Would recommend, and would definitely return!


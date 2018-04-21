---
layout: post
title: Interlude
date: 2016-11-03 20:00
comments: true
tags: foo, bar
---

## An Economic Argument

Let's put aside the computer *science* for a little bit, and discuss some of the
subtler, philosophical points at play in what we've seen so far.

In the last chapter, we looked at three new machines: the `and` gate, which
outputs 1 whenever *both* of its inputs are 1; the `or` gate, which outputs 1
whenever *either* of its inputs are 1; and the `nand` gate, which outputs 1
whenever its inputs are *not* both 1.

We spent a significant amount of time wondering about which gates were
"fundamental", ie, which gates we could use to build the others. As we saw, any
of the following combinations lead to a "fundamental" set of machines:

* `and` and `not`
* `or` and `not`
* `nand`
* `nor` (if you did the bonus exercise, which I'd highly recommend!)

We reasoned, that because `nand` is only one machine, and the `and`/`not` combo
is two, `nand` must somehow be "more fundamental". We called it "universal"
since we realized that all other machines could be built from it.

But the question remains: *who cares which machines are more fundamental?* And
it's a very good question. A very good question with a single-word answer, which
I've pulled straight out of the Oxford English Dictionary:

> par·si·mo·ny (n) <br />
> *ˈpär-sə-ˌmō-nē* <br />&nbsp;<br />
> Extreme unwillingness to spend money or use resources.

There are a few angles by which the most parsimonious approach is the best one.
The first reason is the too-real truth that humans are capable of mistakes.
Those mistakes might come in any number of forms: saying the wrong thing to your
spouse, having an awkward encounter with a coworker, accidentally stapling your
finger to "just see what would happen," and so on. But the most egregious
mistake of all is to base an argument on shaky grounds.

And make no mistake, this theory of computer science we've been building here is
nothing more than an argument. It's an argument to the universe, that *things
must be this way* because there is *no other possible way for them to be*. And
it's a particularly convincing argument, because all of this stuff actually
works.

But all arguments must rest on some assumptions, and in human affairs, it's
often in these assumptions where things go wrong. Rhetoric can be perfectly well
argued, but rest on a poor foundation, and because of that, despite its
*internal structure*, it is *ultimately wrong*.

Parsimony is thus our hedge *against ourselves*. We realize that we humans are
fallible, and, as a defense, we attempt to rest our arguments on as few
*external factors as we can*. The fewer assumptions we make, the more likely our
well-reasoned argument is to be right.

The other motivation for parsimony is one pragmatics. One of, well, parsimony,
if you will. Economic parsimony. I realize I haven't been fooling anyone here by
calling these things "diagrams"; everyone is acutely aware that we've been
discussing *electronics* over the last few chapters.

The thing about electronics is that they need to be manufactured before we can
use them. And if they're going to be manufactured, that means someone needs to
manufacture each and every piece we need. Parsimony is then a limit on how much
money we need to pay people to manufacture different parts for us. We can either
pay *two* factories to build us `and` and `or` gates, or just *one* to build us
`nand` gates, and assemble the rest ourselves.

> Takeaway: In theoretical endeavors, always aim for parsimony. It will save you
> money and, more importantly, time spent being wrong.



## ...But Why?

I touched on a point earlier: these diagrams and machines we've been designing
on paper are nothing more than electric circuits. Sure, there's a few "gotchas"
to pay attention to when building these things for real, but our imaginary
machines turn out to work just as well as real the silicon-and-copper things.

A substitute teacher of mine, Mr. Bruce, once, back in grade-school was teaching
my class about addition. He asked an idle question that I've never forgotten in
all of these years, and likely the question that set me to learn all of these
things in the first place.

> "Sure, 6 plus 9 is the same thing as 9 plus 6. *...but why?*"

Mr. Bruce thankfully didn't have an answer to this question, because if he had,
I probably wouldn't have pondered it for years forth.  It's kind of a silly
question. Obviously $6+9 = 9+6$. Everyone knows that. But again, we ask, why?

The answer itself is deep and profound, but we are not ready to learn it yet
(rest assured, we'll eventually get there.) But indeed, it's the question that's
the important part. Or, more specifically, the *form* of the question. The form
of the question, to me, is this:

> "What law of the universe forces this obvious thing to be so?"

It is in questions of this form that lead to true understanding of the universe.
If we know *why* it must be so, then we know it must be so. But in doing so,
we've added a tool to our toolbox. The entirety of the marvels of human
engineering are due to tools of this sort, and the interactions between them.

If you know enough small details about the underlying mechanics of reality, you
can jerry-rig them together in a way that the universe never anticipated, and
you can do things that humanity previously thought impossible.

This is all that invention is; it's learning small things and putting them
together in novel ways. I find it extraordinarily motivating to realize that
"intelligence" or "inherent greatness" have nothing to do with inventing novel
things that can change the world; it's all just learning things that must be so,
and exploiting that knowledge.

But I digress. I brought up the anecdote about Mr. Bruce in order to raise a
similar "obvious-but-not" question.

> "*Of course* we can design circuits on paper, and have them work on real
> hardware. *...but why?*"

Or, to be more explicit:

> "Obviously, through our actions and perception, we can freely reflect between
> ideas in our minds and externalities in the real world. We can form models of
> reality in our heads, and we can influence the real world to be more like the
> world we see in our minds. *....but why?*"

I'll let you stew on those thoughts for a while. Amazingly, computer science
*has an answer* to that question. Unfortunately, like Neo in the Matrix, you're
not ready to hear it yet. We've got a long ways to go yet.


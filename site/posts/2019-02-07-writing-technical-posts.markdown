---
layout: post
title: "How to Write Technical Posts (so people will read them)"
date: 2019-02-07 13:04
comments: true
tags: non-technical, writing, advice, guide
---

One of today's best bloggers in the functional programming space is [Chris
Penner][cp]. Despite this, Chris is criminally underrated---nobody I talk to
seems to know of his work. Go check him out as soon as you finish reading this
post!

[cp]: https://chrispenner.ca/

This is reasonably pervasive phenomenon in our subculture; there's lots of
fantastic work being produced, but for one reason or another, it falls between
the cracks. I'd propose the biggest obstacle is that most FP writing *isn't
optimized to be read.*

So I'd like to take some time today and talk about common failure modes in
technical writing. If you don't have a checklist you run through before
publishing a post, you'll probably get a lot of benefit from internalizing this
advice.

The value? You'll make it easier for people to understand what you're trying to
tell them. Which is why you're writing in the first place, right? The good news
is that none of this is magic---just some simple guidelines for structuring your
content.


## The Guiding Principle

Here's the biggest thing to keep in mind: your reader doesn't really care what
you have to say. You get maybe four sentences to convince them that your essay
is worth their time. If you haven't made your case by then, you've probably lost
them to the next tab they binge-opened.

Even after you've convinced them that it's a valuable read, you need to continue
assuring them that you're not wasting their time. If you take too long to get to
the point, or if you make the information too hard to find on a quick skim,
you've lost them again.

As a result, alongside your technical content, you have two primary goals to
focus on:

* Provide strong, concise motivations for everything you want to talk about.
* Make it easy to skim.

If you can do these two things, you're already most of the way to better
engagement.


## Writing Strong Motivations

People care about solutions to problems they have, or expect to have one day.
They care about other things too, but it's not really relevant to us today.

With this in mind, you want to tailor your motivations in terms of *solutions to
problems.*

Here are some good examples of problems that you've probably run into (and links
to their solutions for you to read later):

* [Ed Kmett writes shitty documentation][adjunctions]
* [I have lots of types that need to evolve at the same time][hkd]
* [There is no good place to learn type-level programming][book]

[adjunctions]: https://chrispenner.ca/posts/adjunction-battleship
[hkd]: /blog/higher-kinded-data/
[book]: http://thinkingwithtypes.com/

Bad examples of motivating documents are things that assume you care *simply
because they exist.* This is [pretty][pipes] [common][yesod] of libraries'
tutorials.  The same document that convinces you to use a technology should also
show you how.

[pipes]: http://hackage.haskell.org/package/pipes-4.3.9/docs/Pipes-Tutorial.html
[yesod]: http://yannesposito.com/Scratch/en/blog/Yesod-tutorial-for-newbies/

As a more general rule, focusing on *why* is going to be more valuable than on
*how.*

Why should someone care, and why your solution is a good one.

"How" without a "why" suggests a contrived solution to a made-up problem. In
other words, it's easily read as "who cares?"


## Understanding How People Read

People who spend lots of time reading have good heuristics for skipping lots of
text. If you understand these heuristics, you can make it easy for people to
find what they're looking for. And remember: they're looking for reasons to
continue reading.

There are two behaviors here. The first is what I call "skimming for
concepts"---which is that people will attempt to determine what text is about at
a high-level. They're looking for *what you're trying to tell them*, as opposed
to *what you're actually saying.*

When skimming, people are likely to read only the headings and the first
two sentences of a paragraph. If they're convinced they know what you have to
say, they'll skip to the next paragraph. If several paragraphs in a row don't
seem relevant, they'll skip to the next heading.

If the next heading also fails to grab their attention, they'll probably give
up.

The solution is to structure your argument as a tree. Headings must provide
enough information to let someone know whether or not they care about the
following prose.

This also means that the first sentence of each paragraph should be sufficient
to understand the rest of the paragraph. The remaining sentences are only
allowed to reinforce or give details of the first sentence. One paragraph equals
one idea.

Roughly speaking, the hierarchy of your document should look like this:

* Document
    * Heading
        * First sentence
            * Rest of paragraph

Maybe you feel like it's hard to know how much knowledge to assume your
readership knows. Understanding how people read makes this a non-issue. Present
as much information as is necessary to understand your point, but make it easy
to skip if people already know it. Those who don't yet know will learn, those
who do can skip past, and both camps will appreciate it.

After you've convinced your reader that they care what you have to say, they're
more willing to read what you *actually have to say.* When the reader is ready
to dive in, that's when you can make the finer points of your argument.

It's unlikely that anyone is going to read every word of your essay. It's even
less likely that they'll read them all in order.


## Stumbling Blocks

Now that you've got people ready to listen to you, it's important to keep them
on the same page as you. You really need to stay on top of anything that might
break their focus.

Use short sentences. If it's too hard to parse, people won't.

Make sure your spelling and grammar have no egregious problems. You don't need
to have perfect command of the language, but you need to be able to signal that
you're trustworthy-enough to listen to. Don't underestimate how much credibility
you'll lose from blatantly bad spelling and grammar.

This stuff is relatively common-sense.

What might be less so is that you also need to stay on top of conceptual
stumbling blocks. If your argument makes a jump that feels poorly motivated or
references something potentially unfamiliar, expect that your reader will
experience vertigo.

Most of the ideas we talk about in functional programming *are not easy,* and it
doesn't do anyone any favors to pretend this isn't so. Expect that your readers
will be pretty similar to you; if you had a problem understanding a piece of
your topic, *call that out.* Point out the obstacle. Point out what they might
be thinking, and then very explicitly show them what they should be thinking
instead.

For example, if your code sample uses a [functional dependency][fundep], it
might be worth a short sentence saying "that funny bar thing is a functional
dependency." Give a tiny summary of its purpose, and provide a link for them to
learn more if they need to.

[fundep]: https://en.wikipedia.org/wiki/Functional_dependency

Another illustration: if *you* originally got confused that an "algebra in
recursion schemes" is not the same thing as the algebra you learned in
high-school, your readers probably will too. The first time you say "algebra" in
the new context, say "this is a misleading term. This has nothing to do with
solving equations like you did in high-school."

More important than what you're saying is what you're *not saying.* If you're
giving examples of something that fits a pattern, make sure you give examples of
things that *do not* fit the pattern. A concept that is applicable everywhere is
useful nowhere.

Give lots of examples. Nobody I know learns via mathematical statements, nor do
they learn via long, wordy, abstract prose. People learn by seeing lots of
examples, and being told explicitly how these examples relate to one another.
The mathematical statements are only useful *after* you have the intuition, so
save them for an appropriate time.


## Conclusion

The takeaway advice from this essay is that *if you want lots of readers, you
must make it easy for them to read.*

To that end, pay lots of attention to motivation. Why should people care what
you have to say? What value does it give *them?*

Focus your energy on the beginnings---both of the essay as a whole, and of each
paragraph. People who are unconvinced by your essay's value will skim their way
through it, and they will do that by reading only the beginnings of things.

Make your information easy to find. Structure your argument in a tree, and make
sure it supports random-access. Nobody is going to read the whole thing from
start to finish. Instead they're going to jump around, ignoring the pieces they
already know, and looking for the bits they don't.

Use lots of short paragraphs. A paragraph should correspond to a single idea.

Anticipate which parts of your argument will be difficult for your readers, and
be proactive in trying to assuage those difficulties. Give lots of examples of
what you're talking about, and more importantly, what you're not talking about.

Point out where you went into the weeds while learning this stuff. Steer readers
away from common mistakes and misconceptions.

And finally, end on a high note. Leave people with a good feeling, and it will
incentivize them to get to the bottom of your next piece. Inspirational calls to
action are a good way to go out.

> Tell them what you're going to tell them.
> Then tell them.
> Finally, tell them what you told them.
>
> -Unknown

Funny and poignant quotes are too.


---
layout: post
title: Chunking with Conceptual LEGOs
date: 2014-05-11 08:55
comments: true
tags: pedagogy, abstraction, feels
---

{% previous affording-ascendancy %}

## Moving Along

Last week we talked about the concept of Ascendancy: the conceptual currency
that lets us buy options to help accomplish our goals. It's a generalization of
money for achievements. It's a powerful concept, especially when you realize
that because it's a currency, we can apply traditional economic theory to it.
And people have been working on traditional economic theory for a long time.

If you want the most bang for your Ascendancy buck, there are two main
considerations. The first is how much of it you possess, and the second is how
wisely you spend it. I've got a lot of topics to cover in the next year, so
we're only going to focus on how to get as much of it as possible; my argument
being it's more useful to have lots of money than to spend little money.

<!--more-->

That being said, if you're interested, conceptually the website [LessWrong][lw]
is almost entirely focused on how to efficiently spend the information (read:
a form of Ascendancy) you have in your possession. Fair warning: there is a lot
of math, because that's what budgeting is.

So, for our purposes we will only be looking at how to acquire lots of
Ascendancy. Because Ascendancy is ethereal and doesn't exist without a medium in
which it can be transmitted, we are required to find a specific form of it to
accumulate (remember, there are lots to choose from: money, power, influence,
etc). I'd argue that information is the best candidate as a way of generating
Ascendancy, mainly because we can copy it without being arrested. We can
generate information for free with no concerns of inflating the economy.

Information allows us to build affordances for *options we already have, but
don't know about*. It also gives us a framework for how we can generate new
information. Furthermore, an industrious reader should already have five ideas
about how to convert information into money.

Acquiring Ascendancy in the form of knowledge is the metaphorical equivalent of
using the money you had forgotten that you stashed in your coat pocket to buy
stocks in the Federal Mint. Or something like that. I've never been very good at
metaphors.

[lw]: http://lesswrong.com



## What Programming Feels Like on the Inside

One of my ulterior motives behind so much blogging as of late is that I want to
share what the experience of being a programmer is like. As a profession I feel
like it is one of the most misunderstood careers out there, which I think is
a shame because I see programming as beautiful and artistic. It's not the
mindless robotic busywork that most people seem to think.

I think this comic accurately conveys what programming feels like:
![The subjective experience of programming][hell]

In this comic, our stick-person hero is trying to track down a software bug
somewhere. She begins by looking at the code, and proceeds to build a mental
model of what it is trying to accomplish. She pulls in her knowledge of
surrounding pieces of code, attempting to keep the entire program in her head as
she reasons about what it is trying to do, and how it goes about doing it.

Our hero has just spent the first five panels loading up her mind with a model
of what the code is doing. She has built a map of the software territory in her
head. This acts as the context in which she can reason about it. Because
computers just do what we tell them to do, the fact that this bug exists means
someone made a mistake somewhere. In the sixth panel, our hero begins to think
about the underlying context of the problem, about who wrote which parts of the
code, and potential places for it to go wrong. Essentially she is searching the
map for things that might be broken.

And then something bad happens. Someone distracts her for a second, and her
conceptual tower comes toppling down. This happens in a lot of places that
aren't programming, but it's very evident when coding. The human brain simply
isn't meant to be able to hold so many things in attention simultaneously, and
it takes a really delicate act of balancing in order to make this happen.

The structural layout of the concepts in our hero's mind look a lot like this:
![A precarious tower][tower]

It's a total hack that this thing is standing at all. No wonder that the
slightest disturbance can destroy the entire effort.

A human brain can only really pay attention to a few things simultaneously. The
actual number is different for everyone, but it's usually somewhere in the range
between four and ten. This attention span is known as your
[working memory][memory], and it's a pretty serious limitation in all
intellectual pursuits.

So if humans can only keep a maximum of ten things in mind at once, how is the
stick woman even theoretically *possibly able* to keep track of thousands of
lines of code simultaneously, let alone reason about which ones might not be
doing what they're supposed to be doing?

Well, as you might imagine, there's a trick to it. Instead of thinking about
individual lines of code, we can think in **chunks** of code. Instead of
thinking about the individual steps being performed, we can instead think of the
higher-level goals being accomplished. We can think of sorting a list rather
than moving the individual items to their correct spots. Chunking lets us zoom
out and view our conceptual map from further away. We lose the specific details,
but we gain a better perspective.

This is why programmers seem a little strange to most people. This way of
thinking has pervaded their world-view. But insofar as programmers chunk too
much, I feel that *most people don't chunk nearly enough*.

Chunking is the process of ignoring specific details to try to understand
a concept on a higher level. It's also known as "abstracting" or "going meta".

A metaphor of mine that is *better than usual* is a LEGO kit. You can go out and
buy a LEGO kit, which comes with both the necessary pieces and an instruction
manual detailing how to go about doing it. You've now simplified the problem of
trying to keep an entire LEGO design in your mind to the easier problem of
working through the instruction manual.

To drive the analogy a littler further home, when you're drawing people, you can
either study lots of anatomy textbooks and then attempt to rotate the image of
the human body around in your mind, or you can just just go buy one of those
[little wooden people][poser], pose the damn thing, and draw what you see in
front of you. Bam! All of human still-motion has been chunked into one object.

[hell]: /images/lego/hello.png
[tower]: /images/lego/tower.jpg
[memory]: http://en.wikipedia.org/wiki/Working_memory
[poser]: http://www.ebay.com/bhp/wood-artist-figure



## The View From Way Up There

Returning to the photo of that precarious LEGO tower above, we are afforded
the ability to explore possible routes of abstraction. Starting from our
precarious tower, what's a related topic that loses some details? An obvious
next step is to think about *unstable towers in general*. To abstract again, we
can consider *unstable buildings*, and again, *instability itself*.

It's clear that each of these concepts is related to one another, but they're
looking at the same thing from different viewpoints. It's like how the ground
shrinks as you take off in a plane, and the city that used to be so big around
you is now entirely visible at once. Looking at things from high up lets you
notice patterns you would have missed from ground level.

Each level chunks the key information of the layer below it. We are
intentionally throwing away information so that we can fit the bigger picture in
our head. But that's not to say that chunking is necessarily a good thing. Each
layer of abstraction is useful in its own way.

Thinking about the tower itself, we can think about actionable changes that
would let us improve its stability. We can consider what kinds of things would
make it fall over, and the like.

Thinking about unstable towers in general affords us to consider what makes
a tower unstable. For example, we might learn that the center of mass needs to
above the base of the tower for the entire thing to not instantly tip right
over. If we wanted to build our own tower, this would be the right height to be
thinking from.

Considering unstable buildings allows us to see common trends in construction.
We would learn about which materials can support weight, how to properly
construct buildings, etc. If you were a carpenter, this is probably from where
you should be looking at the problem.

Not finally, because it's always possible to abstract harder, but terminally for
this essay, we can think about instability itself. From here we can think about
the stability of marriages, of chemicals and nuclear reactors, and of societies.

As you can see, moving up the ladder of abstraction lets you solve more and more
problems. It affords you superpowers that you wouldn't otherwise have. Take
a moment and appreciate how cool this is. We can find underlying principles
between things which at first glance appear to be unrelated. This concept is
an abstraction of science itself, and is really and truly the only reason that
human-civilization-as-we-know-it exists.

In general, as a principle, we want to solve our problems on as high a level of
abstraction as possible, so that it applies to as many problems as it can.
Solving a problem on a level of abstraction lets you solve the same problem on
every rung lower down the chunking process. Preventing your tower from falling
over is great and all, but entirely pales in comparison from preventing
*everything* from falling over.

It's like writing a how-to guide every time you make a cool design out of LEGOs.
The next time you want to do it, you can simply read the instruction manual, and
operate on autopilot because the problem has already been solved. In doing so,
you free your mind to work on [bigger and cooler LEGO designs][lego].

And then you can use those bigger and cooler designs to make even bigger and
even cooler things. And then before you know it, you've accidentally become god
and all of your problems look very trivial all of a sudden.

[lego]: https://www.youtube.com/watch?v=_d0LfkIut2M


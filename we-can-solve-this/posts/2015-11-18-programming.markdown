---
layout: post
title: On Programming
date: 2015-11-18 16:42
comments: true
tags: november
---

I've recently realized that I don't really know what most jobs entail. Like, I
vaguely know what an accountant is, but what do they *do* on a day-to-day basis?
How about lawyers? I feel like those guys do a lot of reading, and maybe they go
to court and argue sometimes, but surely that can't take all day? Probably? What
do doctors do when nobody is sick? Is there ever a time when nobody is sick? I
get the distinct impression that maybe Dr. House isn't an accurate forecasting
model for answering this question.

As an engineer it's easy to talk shit about other people's jobs, I mean, after
all, theirs probably didn't require five years of school. I really do feel like
probably I could do most jobs out there (though granted, not necessarily could I
do them *well*), but, I'm starting to feel like maybe that's just me being an
asshole. Probably, come to think of it. Anyway, that's where this question
originally stemmed from. And that got me thinking: what does *my* job entail,
really, when you get down to it? Since I don't know the answers about other
people's jobs, I thought I'd spend today writing about mine. 

I get into work around 9:00 sharp if I'm lucky, and the bus is feeling
cooperative.  Usually it's not. 9:15 is more reasonable, and on bad days it's
closer to 10:00. I grab a snack and some coffee, and get to my desk where I
spend the next few minutes going through the daily log-into-everything routine.
While I'm working my way through my snack, I'll halfheartedly check my email.
There's never anything directly for me, just newsgroup digests and things that
I'm cc'd on. If there are more than 5 emails in my inbox, I seriously consider
making some new email filters to keep them away from me. I don't have time for
emails that aren't useful. I get maybe a thousand emails a week, of which there
are maybe ten useful ones. You imagine how many email filters I have.

With that out of the way, I'll fire up my [text editor][vim] -- a program which
is *really good* at editing text. It's like notepad, but on crack -- and open up
the project I was last working on. When I get in in the morning, I'm usually
chalked full of ideas for how to solve my issue. I don't actively come up with
them, it's just my brain having churned through the problem during the time I
wasn't at work. I'd say, honestly, most of my best work gets done when I'm not
actually at the office. I'll make the changes I thought of overnight, and run it
through the test I'm currently trying to make pass. This takes around 5 minutes,
which is too short a time to start something else, but too long to wait for it
to finish. Usually I check Facebook.

When you study computer science in school, you learn about all of these really
cool approaches for solving problems. Knowing these cool approaches well enough
to write them yourself is how you get hired in this industry. A lot of it is
trying to come up with a clever way of structuring the information you have so
that it makes it easy to do the thing you want to do. I know that's abstract and
not very helpful -- I apologize -- so let me make it a little more concrete.

The problem: you have a million people in a city, all of whom have a telephone,
and you want to be able to quickly find one so you can call them. The answer, of
course, is you look in the phone book, which, if you consider it, is a pretty
clever way of structuring information. It's sorted by person's name, so you can
pretty easily track someone down. But imagine if it weren't sorted -- you'd have
to go through the entire book and hope that the person you were looking for fell
somewhere near the front. *And* you'd have to hope that you didn't get bored and
start skimming, or you might miss your friend without even realizing it. It's a
pretty obvious solution, but you'd be surprised how often the answer is "sort
the bugger and then look through it".

I know other things like this too. Most of them are general-purpose "shapes" to
put data in, all of which are good for certain things and bad for others. In
technical interviews, most of the marks come from picking the right shapes.
These shapes are things called "data structures", and as you might expect, they
are used to structure data.  Generally, if you pick the right data structure in
an interview for a non-elite company, you will solve the problem and they will
give you the job. It's as easy as that.

There's a data structure called a "stack" which corresponds in real life to
those stacks of plates at the cafeteria. If you restrict yourself to only
dealing with one plate at a time, the only things you can do to that stack are
take a plate off the top, or put a plate onto the top. The plates have an
ordering to them: *first in, last out*. As a result, the stack data structure is
good for keeping track of where you are in a problem. Like in a good discussion
with a friend, if your attention is sharp, you will make segues and digressions,
but eventually meander back to the topic before your digression. And then you'll
finish that topic, which turned out to be a digression from the thing you were
talking about earlier, and you'll return to that. And so on.

There's another one, called an "array", which is like a shopping list. It's easy
to put things on the end of it, but it's sorta hard to put something into the
middle, because you didn't leave any room to write there. But it's nice for
finding things in particular *places* (but it isn't good at finding particular
*things*). An array is like athletes finishing a race at the Olympics -- what's
important to the Olympic Committee is that it's easy to figure out whom to give
the gold to: whomever is at the first spot in the array.

I know lots of things like that. Good ways to structure information if you want
to do some things quickly, and don't care about other things. I also know what
it means for these things to be fast or slow, even when computers are trillions
of times faster than we humans could ever be. This is the interesting stuff in
my life. I spend an embarrassing amount of time thinking about these kinds of
things.

But like I said these are things you learn in school. Unfortunately, in the
industry, you get really excited when you get a chance to use these things. In
the industry, these interesting decisions and trade-offs have been made by
people with more seniority than you. My day-to-day job is spent wandering
through huge swathes of code I've never seen before, trying to read enough to
get a basic gist of it. What I'm looking for is enough of an understanding to
see if it could possibly be causing my problem or not. This is known as doing
maintanence programming, and nobody likes doing it.

Maintanence programming is like doing triage, or science, maybe. You start with
some hypothesis of what is causing your program to misbehave, and then you try
to confirm or deny that. Denying it can be as easy as chopping out 20% of the
code and seeing if your problem is still there, or more involved like trying to
find other problems that must be present if that were indeed the problem. It's
rarely the first hypothesis you consider.

Eventually, sometimes after *days* of hunting, you find where the problem is.
Note that this is the effort *just to locate* where the problem is. Finding it
is necessary to fix the issue, but it's sadly insufficient. If you're lucky, the
problem is that your coworker forgot to consider what would happen in the case
of that number over there being 0. If you're unlucky, just because you've found
the problem doesn't mean you have any idea about how to fix it. If you're really
unlucky, you spend a few hours figuring out how to fix it, and that just reveals
a related problem somewhere else. Back to step one. And if you're cursed, you
realize that the guys with seniority who did the conceptual designing of this
system didn't do their job very well, and fixing this tiny problem is going to
require a huge architectural renovation. 

That happens depressingly often.

This is what I spend my days doing. I'd say maybe 80% of my actual productive
work day is spent tracking down and subsequently thinking about how to fix these
bugs in our giant codebase. The good news is that it's always a new problem
you're working on. The bad news is that it constantly feels like you're drowning
in things you don't understand. Luckily it gets better. If you can hack it for a
year, you start getting really quick at finding and fixing these problems. Then
because management decides your efficiency is discouraging to the intern,
they'll switch you to building a system of your own. This is the everlasting
dream of all programmers: to spend all their time writing code, and leave fixing
it to the interns. I'm glad I'm not an intern anymore.

My favorite part about being a programmer is building tools for myself to
automate tedious parts of my job. For example, yesterday I needed to test the
same thing with 30 different, tiny modifications, and see if any of my tests
worked. Each edit took about 15 seconds, but running the tests took about 5
minutes. After two iterations of this, I decided to write a program that would
make the changes for me, run the tests, and start flashing at me if it found the
right answer. Writing this tool took maybe ten minutes, and saved me two hours
of tedious, can't-do-anything-else-ness. I got lucky on that one, usually
writing the tool takes as long as doing the manual labor, and doesn't work very
well, but at least it's mentally stimulating. Writing tools is like intellectual
masturbation for programmers, I swear to god.

To be a good programmer, you need to be able to focus. Intently. Remember,
you're trying figure out why a computer program doesn't work by running it on
your brain, really, really slowly. This is why programmers are stereotypically
hyper-pedantic; it's a useful skill when your livelihood depends on not making
any mental missteps when you're pretending to be a computer. Imagine pretending
to be a computer. It's not a very appealing past-time, is it?

That's not to say it's all bad. Programming gets you really good at
pattern-matching. We see the world in a way that can't possibly make sense to
anyone else. In the same way that plates at the cafeteria and discussions with
your friend and gridlock are all just stacks when you squint a little bit,
sequentiality and the future and uncertainty and incremental changes are all
just [monads][monads] if you look hard enough. 

Over time, as a programmer, your perception of reality lifts itself into the
same abstractions you use all the time at work. I no longer see the woman at the
counter at Subway as a person; for most of my intents and purposes, she's just
an abstract class which implements the `IFoodProvider` interface which can give
me back a `Future[Food]`, which if I block on, will eventually turn into real
food. I don't mean to do it, and I don't feel like a good person when I realize
it's happening, but like it not, that's my reality. Sometimes I need to work
really hard to realize there are real things like people or intentions behind
these visages I see in terms of functions and patterns.

This way of the world doesn't really paint me as being a warm and cuddly person,
but I think it's helpful. It's a buffer between me and making bad decisions. It
helps distill interactions to their constituent parts, and filter out the
irrelevant ones. I'm often told that I'm good at asking questions, and I take
this to be a direct consequence of my being good at seeing the problem at hand
and ignoring the bullshit. 

I've spent the last decade of my life doing this stuff. I feel like if properly
motivated, I would never need to stop writing this essay. There are lots of
things I want to say; lots of things I feel are misunderstood. But I won't,
because this is already long enough, and scratches enough an itch for
understanding that I'll leave it be.

If you're going to come away with anything from this essay, I'd suggest it not
be "Sandy sees me as a mathematical construct," but instead "I should talk more
about the intricacies of my job because it's misunderstood and I really like
it," or, y'know, even "wow, Sandy must be really smart" would be acceptable. I
wouldn't complain about that one.

[vim]: http://sandymaguire.me/blog/vim-is-not-about-hjkl
[monads]: http://sandymaguire.me/blog/ideas-and-men


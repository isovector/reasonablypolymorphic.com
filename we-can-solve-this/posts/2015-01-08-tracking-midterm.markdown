---
layout: post
title: "Tracking: Midterm"
date: 2015-01-08 03:02
comments: true
tags: science, life, results
---

> **Warning:** much more pragmatic than most of my posts. If you're a fan of the
> weird abstract stuff, maybe give this one a pass and collect $200.

{% previous 2014-postmortem %}

## Introduction

My goal for 2015 is to implement things in my life that I know I *should* be
doing, but am not. The stated plan is to implement one new habit every two
weeks, with a midterm review half way through, both to discuss implementation
details and progress.

The first project of the year is to install a habit of tracking my life, so that
as I install habits later this year, I'll have some idea of whether or not
they're working. Additionally, I suspect there are big wins to be had by having
a big corpus of data and being able to analyze it in batches, rather than online
through my immediate sensory experience.

This post serves as a midterm review of my progress towards installing a habit
of tracking my life.

<!--more-->



## Desiderata

I began this project with a list of desiderata for the habit: what I'm trying to
get out of it, and things to help ensure its sustainability. The former point is
relatively easy: get my hands on as much data as possible and figure out what to
do with it later. The latter point exists because I know all too well that if
the system requires any work whatsoever, I'm not going to keep doing it for very
long.

The immediate resolution to these problems is to make automatic as much data
collection as possible. When it's not possible to make it automatic, to find or
build tools to make it as easy as possible. My intuition here is that as long as
my perceived immediate utility of the recording is higher than the opportunity
cost of doing it, I'll stick with it.

Additionally, I decided to not worry very much about collecting perfect data --
anything relatively good was better than only getting a small fragment of
perfect data.

So, with a few clear goals in mind, it was time to set out and get started.



## Logistics

The first thing I did was delete the data from my old productivity system, so
that any new data wouldn't get confused with 2014. For those interested, my old
system consisted of telling my computer by a key press when I began and when I
ended working, as well as occasional updates on *what I was working on*. This
data was how I determined [last year][2014]'s productivity scores.

I wasn't happy with the old system for several reasons, but I decided to make a
few quick fixes to it to aggregate more data that I had easy access to. This
took maybe ten minutes; I figured the added data would be worthwhile. Ideally
one day I would rewrite the entire tool, but at least for the time being I could
use it to track designing how my new analytics system would work.

The next step was to update my daily review form to ask questions more relevant
to the things I wanted to track. I added questions about how much coffee, water,
calories, and sexual encounters I had had that day. These metrics were chosen
because they were notably absent from my 2014 review, and I was genuinely
interested in the trends I might see.  I explicitly decided only to ask about
things I wasn't tracking elsewhere, in order to cut down on creating makework
for myself.

Next I reconnected my bank account to [mint.com][mint] so I could use their
automatic budgeting system. This had already been setup, but after [heartbleed]
last year I'd changed my bank account password and mint hadn't been smart enough
to figure out that it was no longer collecting data. Out of all of my surprising
results from last year, the amount of money I spent was probably the scariest
one, so this was a pretty big priority.

When I told my super cool roommate about the project, he gave me a [fitbit] he
wasn't using anymore. Win! I had become a cyborg.

With the obvious low-hanging fruit out of the way, I decided to check out
[quantifiedself.com][qs] and do some research on other cool things I could
track. There were lots of good ideas, but the best ones I found were tracking my
food intake, my sleep, and the notion of delaying judgement on data for as long
as possible. For example, by the end of the year, the things I consider
productive might be different than those I currently consider productive. It's
better to record just the objective stuff and subject it to subjectivity later,
when I'm planning on actually *doing something* with the data.

The last part of the implementation was realizing that I *really really* didn't
like my current productivity tracking tool. Because it was driven with key
presses, it meant that if I forgot to press a button, there was no feasible way
of ever correcting that data. Additionally, it didn't tell me what I was working
on, just that I was working. After about an hour's worth of planning, I had a
better idea for a tool, and I got to work implementing it. It's still just a
baby project, but after about a week of work on it, it was good enough for my
purposes. The tool lets me track what I'm doing, attach metadata, and log a
start and a stop time. I'm calling it "ute: the unified tracker", and if you're
interested, you can find it [here][ute].

[mint]: http://mint.com
[2014]: /blog/2014-postmortem
[heartbleed]: http://en.wikipedia.org/wiki/Heartbleed
[ute]: https://github.com/Paamayim/ute
[qs]: http://quantifiedself.com



## Current Status

So my current state of affairs as far as tracking goes is:

* [ute] : activity tracking (semantic level)
* [RescueTime] : activity tracking (physical level)
* [mint] : money spending
* [MyFitnessPal] : food tracking and caloric intake
* [Sleep as Android][sleep] : sleep quality, durations, snoring
* [Fitbit][fitbit] : steps walked

All in all, I feel a little bit like an omniscient warlock. I've got all of this
super cool data about my life, mostly stuff I had never even *thought about*
before, mostly for free.

Right now, it's a little tedious to work with ute. It's got a lot of bugs, and
the usability isn't something I've focused on yet -- mostly I had just been
concerned with getting the basic functionality happening. The next step is to
make it controllable with single keypresses like my old system was, so I can
wield the power of my old habit to manage this one. Additionally, I'm using it
to track the metrics I'm collecting from other sources, and right now that's by
hand. It wouldn't be very hard to automate that; it just requires some time to
do. Using it in the moment to track activities, however, is awesome, so I
suspect once the automation happens it will be good enough to be long-term
sustainable.

I have a list of things to tweak in the system when I get some spare time, but
overall, it's pretty good for a first attempt. One of the more interesting
things on that list is to make a dashboard on my home-screen for a quick look at
my recent metrics, as inspired by [this talk][own-os]. It would be pretty cool
to have at-a-glance information about my recent productivity, stress levels, and
such.

My next progress report is scheduled for January 14th, in which I plan to have a
look at my data, make sure everything is still looking kosher, and to compute
some rough averages for what my baseline levels are -- for comparison later.

Until then.

[RescueTime]: https://www.rescuetime.com/
[MyFitnessPal]: http://www.myfitnesspal.com/
[sleep]: https://play.google.com/store/apps/details?id=com.urbandroid.sleep&hl=en
[own-os]: http://quantifiedself.com/2014/12/david-joerg-building-personal-operating-system/
[fitbit]: http://www.fitbit.com/


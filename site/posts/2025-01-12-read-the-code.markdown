---
layout: post
title: Read the Code, Not the Profile
date: 2025-01-12 15:29
comments: true
tags: haskell, profiling
---

At work a few weeks back, I found myself digging into profile reports, trying
to determine why our program was running so slowly. Despite having the
extremely obvious-in-retrospect data in front of me, I wasted a lot of time
speeding up code that turned out to not move the needle at all.

Although perhaps it will be interesting only to future me, I thought it would
be a good exercise to write up the experience---if only so I learn the lesson
about how to read profiles and not make the same mistake again.


## Some Context

I'm currently employed to work on a compiler. The performance has never been
stellar, in that we were usually seeing about 5s to compile programs, even
trivially small ones consisting of less than a hundred instructions. It was
painful, but not *that* painful, since the test suite still finished in
a minute or two. It was a good opportunity to get a coffee. I always assumed
that the time penalties we were seeing were constant factors; perhaps it took
a second or two to connect to Z3 or something like that.

But then we started unrolling loops, which turned *trivially* small programs
into *merely* small programs, and our performance ballooned. Now we were
looking at 45s for some of our tests! Uh oh! That's no longer in the real of
constant factors, and it was clear that something asymptotically was wrong.

So I fired up GHC with the trusty old `-prof` flag, and ran the test suite in
`+RTS -p` mode, which instruments the program with all sorts of profiling
goodies. After a few minutes, the test suite completed, and left
a `test-suite.prof` file laying around in the current directory. You can
inspect such things by hand, but tools like
[profiteur](https://github.com/jaspervdj/profiteur) make the experience much
nicer.

Without further ado, here's what our profile looked like:

```
MAIN . . . . . . . . . . . . . . . . . . . . . . . . 100%
```

Well, that's not very helpful. Of course `MAIN` takes 100% of the time. So
I expanded that, and saw:

```
MAIN . . . . . . . . . . . . . . . . . . . . . . . . 100%
└ main . . . . . . . . . . . . . . . . . . . . . . . 100%
```

No clearer. Opening up `main`:
```
MAIN . . . . . . . . . . . . . . . . . . . . . . . . 100%
└ main . . . . . . . . . . . . . . . . . . . . . . . 100%
  └ main.\ . . . . . . . . . . . . . . . . . . . . . 100%
```

Sheesh.

```
MAIN . . . . . . . . . . . . . . . . . . . . . . . . 100%
└ main . . . . . . . . . . . . . . . . . . . . . . . 100%
  └ main.\ . . . . . . . . . . . . . . . . . . . . . 100%
    └ getTest  . . . . . . . . . . . . . . . . . . . 100%
```

OH MY GOD. JUST TELL ME SOMETHING ALREADY.
```
MAIN . . . . . . . . . . . . . . . . . . . . . . . . 100%
└ main . . . . . . . . . . . . . . . . . . . . . . . 100%
  └ main.\ . . . . . . . . . . . . . . . . . . . . . 100%
    └ getTest  . . . . . . . . . . . . . . . . . . . 100%
      └ test . . . . . . . . . . . . . . . . . . . . 100%
```

Fast forwarding for *quite* a while, I opened up the entire stack until I got
to something that *didn't* take 100% of the program's runtime:

```
MAIN . . . . . . . . . . . . . . . . . . . . . . . . 100%
└ main . . . . . . . . . . . . . . . . . . . . . . . 100%
  └ main.\ . . . . . . . . . . . . . . . . . . . . . 100%
    └ getTest  . . . . . . . . . . . . . . . . . . . 100%
      └ test . . . . . . . . . . . . . . . . . . . . 100%
        └ makeTest . . . . . . . . . . . . . . . . . 100%
          └ makeTest.\ . . . . . . . . . . . . . . . 100%
            └ compileProgram . . . . . . . . . . . . 100%
              └ evalAppT . . . . . . . . . . . . . . 100%
                └ runAppT  . . . . . . . . . . . . . 100%
                  └ runAppT' . . . . . . . . . . . . 100%
                    └ withLogging  . . . . . . . . . 100%
                      └ transformSSA . . . . . . . . 100%
                        └ >>=  . . . . . . . . . . . 100%
                          └ >>>= . . . . . . . . . . 100%
                            └ ibind  . . . . . . . . 100%
                              └ ibind.\  . . . . . . 100%
                                └ ibind.\.\  . . . . 100%
                                  ├ toSSA  . . . . . 15%
                                  ├ transform1 . . . 15%
                                  ├ transform2 . . . 10%
                                  ├ transform3 . . . 10%
                                  ├ transform4 . . . 20%
                                  └ collectGarbage . 30%
```

Now we're in business. I dutifully dug into `toSSA`, the transforms, and
`collectGarbage`. I cached some things, used better data structures, stopped
appending lists, you know, the usual Haskell tricks. My work was rewarded, in
that I managed to shave 80% off the runtime of our program.

A few months later, we wrote a bigger program and fed it to the compiler. This
one didn't stop compiling. We left it overnight.

Uh oh. Turns out I hadn't fixed the problem. I'd only papered over it.


## Retrospective

So what went wrong here? Quite a lot, in fact! And worse, I had all of the
information all along, but managed to misinterpret it at several steps of the
process.

Unwinding the story stack, the most salient aspect of having not solved the
problem was reducing the runtime by *only* 80%. Dramatic percentages *feel*
like amazing improvements, but that's because human brains are poorly designed
for building software. In the real world, big percentages are fantastic. In
software, they are *linear* improvements.

That is to say that a percentage-based improvement is $O(n)$ faster in the best
case. My efforts improved our runtime from 45s to 9s. Which feels great, but
the *real* problem is that this program is *measured in seconds* at all.

It's more informative to think in terms of orders of magnitude. Taking 45s on
a ~3GHz processor is on the order of 10^11^ instructions, while 9s is 10^10^.
How the *hell* is it taking us TEN BILLION instructions to compile a dinky
little program? That's the *real problem.* Improving things from one hundred
billion down to ten billion is no longer very impressive at all.

To get a sense of the scale here, even if we spent 1M cycles (which feels
conservatively expensive) for each instruction we wanted to compile, we should
*still* be looking at < 0.1s. Somehow we are over 1000x worse than that.

So that's one mistake I made: being impressed by extremely marginal
improvements. Bad Sandy.

The other mistake came from my interpretation of the profile. As a quick pop
quiz, scroll back up to the profile and see if you can spot where the problem
is.

After expanding a few obviously-not-the-problem call centers that each were
100% of the runtime, I turned my brain off and opened *all* of the 100% nodes.
But in doing so, I accidentally breezed past the real problem. The *real*
problem is either that `compileProgram` takes 100% of the time of the test, or
that `transformSSA` takes 100% of compiling the program. Why's that? Because
unlike `main` and co, `test` does more work than just compiling the program. It
also does non-trivial IO to produce debugging outputs, and property checks the
resulting programs. Similarly for `compileProgram`, which does a great deal
more than `transformSSA`.

This is somewhat of a philosophical enlightenment. The program execution hasn't
changed at all, but our perspective has. Rather than micro-optimizing the code
that *is* running, this new perspective suggests we should focus our effort on
determining *why that code is running in the first place.*

Digging through `transformSSA` made it *very obvious* the problem was an
algorithmic one---we were running an unbounded loop that terminated on
convergence, where each step it took @O(n^2)@ work to make a single step. When
I stopped to actually *read* the code, the problem was immediate, and the
solution obvious.

The lesson? Don't read the profile. Read the code. Use the profile to focus
your attention.

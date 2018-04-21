---
layout: post
title: Our First Computer
date: 2016-11-24 14:00
comments: true
tags:
---

We spent the last chapter looking at means of making dealing with Kleisli
categories somewhat mangeable. In the end, we came up with the idea of
`do`-notation, a syntactic convention which "desugared" down to combinations of
`bind : Kliesli m => m a -> (a -> m b) -> m b` and `ignoring : Kliesli m => m a
-> m b -> m b` depending on whether or not we cared about the result of each
particular Kleisli value.

More generally, we spent part 2 of the book discussing *symbolic computation*:
what it is, and how we can use it. We've shown by now that symbolic computation
is at least as powerful as our old machine diagrams, and it is significantly
more compact. Compactness is a good thing, because we as humans have a limited
brain capacity, and so the more compact any particular concept is, the more of
them we can hold in our heads simultaneously. The claim here is that we can
build bigger, more complicated things out of symbolic computation than we ever
could out of machine diagrams. This is not for any technical reason, but for a
psychological one -- it's just too easy to "get our wires crossed" in a machine
diagram, both figuratively and literally.

## The P'' Machine

Today we're going to look at the remainder of the architecture we'll need to
support in order to build a general-purpose computer. We're going to investigate
a very primitive computer, called *P''* (pronounced "P double prime"). Although
*P''* is terribly basic, it turns out to be powerful enough to compute "anything
computable". That's not to say that you'd *actually want* to compute anything on
a *P''* computer, but in theory, you absolutely could. We'll revisit this idea
of "computability" and show why *P''* is capable of doing it at some later point
in time.

A *P''* machine is generally described in terms of **tapes**. A *tape* is
exactly like what's inside of an old VHS or cassette -- it's a roll of data with
spools on either side. However, at any particular point in time, there is only
one thing you can read from the tape, and that's the piece that isn't currently
on a spool. Unlike a VHS or cassette, these spools are infinitely large -- you
can unwind in either direction forever. Movie projector film is a good mental
model for a *tape* -- at any given moment there is exactly one frame on the
spool to be projected on the screen. We call the "frame" of the tape currently
under inspection the **read head** of the tape.

With that in mind, any particular *P''* machine needs the following things to
function:

* A "program" tape, consisting of step-by-step instructions for how to proceed.
* A "memory" tape, acting as a form of "scratch work paper", where the program
  can dump the results of things its computed.

Implicit in this definition is that each of these tapes has a *read head*, which
is to say that we can only be looking at one element on the program tape, and
one element on the memory tape at a time.

The only two questions left to ask ourselves are, "what *type* of things can we
store on the memory tape," and  "what are these instructions" that are allowed
on the program tape?

In *P''*, our memory tape consists of an infinite count of `Nat`ural numbers --
each of which has an original value of $0$. That leaves only the question of
what instructions do we have at our disposal for writing programs. In *P''*, we
are given the following, extremely restrictive set of instructions. Five of them
are very simple:

* *Halt*: Stops the machine from running any further.
* *Increment*: "Erase" the `Nat` currently at the read head of the memory tape,
  and replace it with the `succ` of that number.
* *Decrement*: Like *Increment*, but replaces the number at the read head of the
  memory tape with the `prev` of that number. If there is no `prev`, the program
  *Halts*.
* *Move Right*: Advances the memory tape by one step to the right (so that the
  read head is now pointing to a different "frame" than it was previously.)
* *Move Left*: Advances the memory tape by one step to the left.

There are two more instructions available to *P''* which might be a little
harder to wrap your head around, at least until you've begun using them in
practice.

* *Enter Loop*: If the `Nat` at the read head of the *memory tape* is $0$, then
  advance the read head of the *program tape* until the "matching" *Exit Loop*
  instruction.
* *Exit Loop*: If the `Nat` at the read head of the memory tape is **not** 0,
  then rewind the read head of the program tape to the "matching" *Enter Loop*
  instruction.

And, you might be surprised to learn, that's all there is to a computer
"powerful enough to compute anything computable." That means this dinky little
thing we just described is literally just as capable of computations as your
smartphone is. It might not be as *fast*, necessarily, but with enough time,
it'll get there. That means that *P''* can run "Flappy Bird", the "Facebook"
app, and run "Spotify", to name a few things. It sounds crazy, right? But at the
end of the day, it's really not any crazier than the fact that all electronics
can be built out of wires and `nand` gates.

There's one last thing to describe for our *P''* machine, and that is just the
fact that after running the actions associated with each instruction above, the
read head of the program tape moves forward one step. Afterward the program tape
moves forwards, it reads the next instruction and executes it. Rinse and repeat.

Let's give some more concise symbolic names to our instructions, and look at a
few examples.

* *Halt*: `¤`
* *Increment*: `+`
* *Decrement*: `-`
* *Move Right*: `→`
* *Move Left*: `←`
* *Enter Loop*: `[`
* *Exit Loop*: `]`

We can write a short program which moves the `Nat` from the first frame of the
memory tape into the second:

<div class="noborders">

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |

How does this work? Well, let's run it, one step at a time. The `↓` denotes the
current read head of the program tape (first row), and of the memory tape
(second row).

We start by placing the read heads at the beginning of each tape. We've put the
number $2$ in the first cell of the memory tape just in order to show how this
function works, but recall, usually our memory tape starts out as all $0$s.

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `2` | `0` |     |     |     |

Our *P''* machine looks at the instruction at the read head of the program tape,
and sees that it is the *Enter Loop* instruction. Because the value at the read
head of the memory tape is *not* $0$, it does not perform any action.

However, after each instruction is completed, the read head of the program tape
moves forward by one.

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     | `↓` |     |     |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `2` | `0` |     |     |     |

The instruction under the program read head is now *Move Right*, so the read
head of the memory tape moves right:

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     | `↓` |     |     |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     |     | `↓` |     |     |     |
|     |     |     | `2` | `0` |     |     |     |

And now that the instruction is finished, the program head moves forward as
well.

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     | `↓` |     |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     |     | `↓` |     |     |     |
|     |     |     | `2` | `0` |     |     |     |

The read head is now the instruction *Increment*, so we `succ` the `Nat` under
the memory read head, and then we move the program read head by one since our
instruction is finished. Our tapes now look like this:

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     | `↓` |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     |     | `↓` |     |     |     |
|     |     |     | `2` | `1` |     |     |     |

We will elide commentary for the next couple iterations of our *P''* machine.

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     |     | `↓` |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `2` | `1` |     |     |     |

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     |     |     | `↓` |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `1` | `1` |     |     |     |

Our program read head is now the *Exit Loop* instruction, so we check to see if
the memory head is *not* $0$. Because it is *not*, the *Exit Loop* instruction
moves the program head backwards until it finds a *Enter Loop* instruction which
"matches" the *Exit Loop*. For example, this machine:

|     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     |     |     |     | `↓` |
| `[` | `[` | `]` | `+` | `+` | `-` | `]` |

would rewind all the way to the `[` which "matches" the `]`:

|     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |
| `[` | `[` | `]` | `+` | `+` | `-` | `]` |

Notice that in rewinding, we "skipped" a `[`. We are not looking for the *first*
`[` -- just the one that balances out the current `]`. If our program is
misformed and there *is no* matching *Loop* instruction, we *Halt*, since it is
meaningless to go on.

Anyway, back to our worked example:

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `1` | `1` |     |     |     |

and then our read head moves forward again, and the entire procedure happens
again:

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     | `↓` |     |     |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `1` | `1` |     |     |     |

We present the remainder of the computation here, for completeness:

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     | `↓` |     |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     |     | `↓` |     |     |     |
|     |     |     | `1` | `1` |     |     |     |

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     | `↓` |     |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     |     | `↓` |     |     |     |
|     |     |     | `1` | `2` |     |     |     |

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     |     | `↓` |     |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `1` | `2` |     |     |     |

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     |     |     | `↓` |     |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `0` | `2` |     |     |     |

Here, the read head of the memory tape *is* $0$, so we do *not* jump back to the
matching `[`. Instead, no instruction occurs, so we just move through:

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     |     |     |     | `↓` |     |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     | `↓` |     |     |     |     |
|     |     |     | `0` | `2` |     |     |     |

|     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
|     |     |     |     |     |     |     | `↓` |
| `[` | `→` | `+` | `←` | `-` | `]` | `→` | `¤` |
|     |     |     |     |     |     |     |     |
|     |     |     |     | `↓` |     |     |     |
|     |     |     | `0` | `2` |     |     |     |

</div>

Our program is finished, because we've now hit a *Halt* instruction. And voila,
just like magic, we have successfully moved the value from the first memory
frame into the second memory frame. It should be obvious to you, if you followed
the execution of this machine, that the number $2$ wasn't important whatsoever.
We could have just as easily written a program to move $123812$ to the second
frame, although it might have taken *slightly* longer to actually run the thing.

Following all of that reasoning was a bit tedious, though, wasn't it? Our goal
moving forwards in this series will be to implement a *P'' emulator* -- a
computer capable of pretending to be a *P''* machine. We have to *pretend* to do
this, since we don't physically want tapes spooling and unspooling on us. Also,
that sounds like it'd be mechanically difficult to implement, and we don't have
any patience for things that might be difficult. That's why we're inventing all
of these abstractions, so we can get away from dealing with anything tedious or
difficult.

With all of that in mind, in the next two chapters we will build this *P''*
machine in its entirety. It sounds like a tall order, but in fact we already
have all of the tooling necessary to accomplish such a feat.

---

## Exercises

1) Our program to "move the value from the first memory frame into the second"
   doesn't actually work as specified. In fact, it actually "adds the value from
   the first frame into the second frame". There is a slight distinction between
   these specifications if there is already a number in the second frame. Change
   the program presented above so that it first clears the number in the second
   frame before moving the contents of the first frame into it.
2) Run through the execution of your new program with the memory cell `1,2`.


---
layout: post
title: Tying It All Together
date: 2016-11-27 01:00
comments: true
tags:
---

In the last chapter, we discussed the semantics behind what a *P''* executor
would look like, and we defined five of our machine's seven instructions. Each
instruction has the type `State P'' Bool`, where the output `Bool` corresponds
to whether or not the machine should continue running (if the machine *has
**not*** halted).

We find ourselves missing only the *Enter Loop* and *Exit Loop* instructions,
but these are non-trivial and will require some reasoning-about before we can
jump in and build their machinery. Recall the specification for *Enter Loop*:

> *Enter Loop*: If the `Nat` at the read head of the *memory tape* is $0$, then
> advance the read head of the *program tape* until the "matching" *Exit Loop*
> instruction.

Determining the value of the read head of the memory tape is obviously baby
stuff, by now we're well-versed working with our tape infrastructure. But
finding this "matching" *Exit Loop* instruction sounds like a different beast
altogether.

The problem is that we're not looking for the *next* *Exit Loop* instruction,
we're looking for one that matches. Recall that we require all *Enter Loops* to
be paired with a matching *Exit Loop*. This means that moving from left to right
through our program, we can't ever exit a loop we haven't yet entered. When
using our symbols for these instructions, this is equivalent to saying "the
brackets formed by `[` and `]` must make sense". That means the following
programs are OK:

* `[]`
* `[[][]][]`
* `[[[[[[[[[[]]]]]]]]]]`
* `[][][][][][][][][][]`

But the following programs are *invalid*:

* `[`
* `]`
* `[[[`
* `[[]`
* `]][]`

It's fine for a loop to itself contain a loop, and our *Enter Loop* and *Exit
Loop* semantics must respect this. In order to find the matching *Exit Loop*, we
must keep track of how many "unmatched" *Enter Loop* instructions we've seen.
Whenever we see an *Enter Loop* instruction, we should increase our count by
one, and whenever we see an *Exit Loop*, we should decrease this number by one.
If we ever see an *Exit Loop* instruction which moves this counter to $0$, we
have found the matching instruction!

Let's work through a quick example of this just to cement it. The downwards
arrow `↓` represents the `[` we're trying to find a match for. The upwards arrow
`↑` is the instruction we're currently scanning -- the "prospective match". The
number in the top-right-hand corner is the number of unmatched `[`s we have seen
so far.

<div class="noborders">

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $1$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
| `↑` |     |     |     |     |     |     |     |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $1$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     | `↑` |     |     |     |     |     |     |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $2$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     |     | `↑` |     |     |     |     |     |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $2$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     |     |     | `↑` |     |     |     |     |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $1$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     |     |     |     | `↑` |     |     |     |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $1$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     |     |     |     |     | `↑` |     |     |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $2$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     |     |     |     |     |     | `↑` |     |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $1$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     |     |     |     |     |     |     | `↑` |     |     |

|     |     |     |     |     |     |     |     |     |     |
|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| `↓` |     |     |     |     |     |     |     |     | $0$ |
| `[` | `→` | `[` | `-` | `]` | `←` | `[` | `]` | `]` | `¤` |
|     |     |     |     |     |     |     |     | `↑` |     |

</div>

And we're done. Because our "unmatched counter" got to $0$, it must mean that
our vertical arrows are now "not-unmatched", which is to say, they *are* in fact
matched.

We can encode this logic as a symbolic computation, `gotoExit : Nat -> State P''
Unit`, which moves the read head of the program tape to the matching `ExitLoop`
instruction. The `Nat` input is used to describe our "unmatched counter".

```
gotoExit : Nat -> State P'' Unit
gotoExit n = do
    withProgTape moveRight
    (P'' progTape _) ← get
    decide (readHead prog) n
  where
    decide : Instr -> State P'' Unit
    decide EnterLoop n        = gotoExit (n + 1)
    decide ExitLoop  Zero     = inject Unit
    decide ExitLoop  (S prev) = gotoExit prev
    decide _         n        = gotoExit n
```

The strategy is this: `moveRight`, and then look at the new instruction on the
tape. If that's an `EnterLoop`, increase the unmatched counter by one, and then
continue going to the matching *Exit Loop*. If the symbol on the tape is an
`ExitLoop` *and* our unmatched counter is $0$, output a `Unit`. If the unmatched
counter is not $0$, just decrement it by one and continue going to the exit. In
all other cases, we want to just continue moving without changing the unmatched
counter.

`gotoExit` forms the majority of the logic we want for `instrEnter`, so we write
it next:

```
instrEnter : State P'' Bool
instrEnter = do
    (P'' progTape memTape) ← get
    decide (readHead memTape)
  where
    decide : Nat -> State P'' Bool
    decide Zero    = gotoExit Zero
    decide _       = inject On
```

The lemma `decide` in `instrEnter` merely checks whether the read head of the
memory tape is `Zero`, and if it is, it calls `gotoExit`. If not, we don't do
anything.

We need still to write `instrExit`, but we will leave it as an exercise to the
reader. `instrExit` is symmetric to `instrEnter`, except that it it attempts to
find a matching `EnterLoop` (rather than a matching `ExitLoop`) if the read head
of the memory tape *is* $0$.

Now that all of our instructions are defined, we need to call the correct
`instrX` function given an `Instr` value from the program read head. This is
trivial with pattern matching:

```
run : Instr -> State P'' Bool
run Halt      = instrHalt
run MoveLeft  = instrMoveLeft
run MoveRight = instrMoveRight
run Increment = instrIncrement
run Decrement = instrDecrement
run EnterLoop = instrEnter
run ExitLoop  = instrExit
```

and we're finally ready to Kleisli-up all of the moving pieces. Behold:

```
pipeline : State P'' Unit
pipeline = do
    instr        ← read
    stillRunning ← run instr
    advanceAndRepeat stillRunning
  where
    advanceAndRepeat : Bool -> State P'' Unit
    advanceAndRepeat On  = advance » pipeline
    advanceAndRepeat Off = inject Unit
```

This `pipeline` works exactly like our specification in the last chapter -- we
`read` an instruction, and then `run` it. The result of `run` is whether or not
the machine is still running, which if it is, we need to `advance` the program
tape, and then repeat `pipeline` again. If the machine *has* halted, we do
nothing more than outputting a `Unit`.

We're so close! Can you taste it? The last step is to wrangle `pipeline : State
P'' Unit` into the right type. Recall, that the actual function we wanted was
`execute : Tape Instr -> Tape Nat`, which ran the program on a tape, and gave
back the resulting memory tape.

```
execute : Tape Instr -> Tape Nat
execute program = second (pipeline (P'' program emptyTape))
  where
    second : (a, b) -> b
    second (_, b) = b

    emptyTape : Point m => Tape m
    emptyTape = Tape [] point []
```

And we're done! We're calling `pipeline` like a function here, and that's OK
because of the equation `State s a = s -> (a, s)`. A `State s a` *is* nothing
but a function from `s -> (a, s)`. We construct a new *P''* machine by passing
in the `program` tape we were given, and by creating a new memory tape via the
`emptyTape` value.

There's really nowhere left to go from here, at least as far as *P''* machines
are concerned. It might not seem like it, but we now have a *fully functioning
computer*, capable of literally everything that the machine you read this on is
capable of. It's a huge accomplishment, and you should be proud of yourself for
having made it this far.

However, our journey into computer science is nowhere near being finished. We
now set our sights on making a machine capable of executing symbolic
computations themselves. With this in hand, we'll be able to *run the computer
on itself*, a mind-crushingly "meta" concept by any account. We'll need more
tools under our belts, but we've come a tremendous distance already.

Really, we're just getting started.


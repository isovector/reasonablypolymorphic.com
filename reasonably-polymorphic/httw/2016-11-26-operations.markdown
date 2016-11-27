---
layout: post
title: Operations
date: 2016-11-26 01:00
comments: true
tags:
---

In the last chapter, we built a `Tape a` data type to support the program and
memory tapes inside of the *P''* machine we're constructing. We made `Tape a` by
using two `List a`s as the "spools" on either end of the tape, and a single `a`
as the *read head* of the tape.

In order to achieve tapes which felt like they were infinitely long, we invented
the "`Point` of interest" pattern, which offers a `point : Point a => a` value,
indicating some value which is the (arbitrarily) *most interesting* value in a
given type `a`. Using `point`, we were able to generate extra length on either
end of the tape whenever we ran out, and as such, our tape could grow as it was
necessary.

We then built a sum type `Instr`, which represented the possible instructions
our *P''* machine could execute. Finally, we took the product type of `Tape
Instr` with a `Tape Nat` to provide program and memory tapes, and bundled them
up under the type `P''`.

Our plan today is to write a function `execute : Tape Instr -> Tape Nat`, which
takes a program tape, and outputs the resulting memory tape after the *P''*
machine running the program has *Halt*ed. Our strategy to perform this execution
will be identical to the example we worked through in the last chapter, although
this time we'll write a symbolic computation to do the actual work for us.

This "execution pipeline" will be in terms of four distinct steps:

1) *Read* the instruction from the read head of the program tape.
2) *Run* the instruction, modifying the state of the machine and halting if
   necessary.
3) *Advance* the read head of the program tape if the machine hasn't halted.
4) *Repeat* the previous three steps if the machine hasn't halted.

We can represent this pipeline in terms of Kleisli functions which need to be
`composeK`ed together, all running in the `State P''` Kleisli pattern.

The first step in this pipeline is `Read : State P'' Instr`, which simply
fetches the `readHead` of the program tape hiding inside of the state of the
*P''* machine:

```
read : State P'' Instr
read = do
    (P'' instrTape _) ← get
    inject (readHead instrTape)
```

> Side Note: We use the `inject : Kleisli m => a -> m a` function to take a
> "pure" `a` value and get it into a Kleisli context. This is important so that
> we have the correct output type for our function.

Easy. The *Advance* step of the pipeline is also particularly easy, so we'll
knock it out of the way now as well:

```
advance : State P'' Unit
advance = do
    (P'' progTape memTape) ← get
    set (P'' (moveRight progTape) memTape)
```

`advance` merely retrieves the state of the *P''* machine, moves the program
tape to the right, and updates the state of the *P''* machine so that it
reflects this. Note that this function returns `Unit`, meaning that we don't
care about it -- we're using `advance` only for the "side effects" it performs
on our state.

We find ourselves now at the part we've been avoiding, the necessity of actually
running the individual instructions available to our *P''* machine. Obviously
we'll need a function to run *each* instruction, which we can then select the
correct one to use via function pattern matching on our input instruction.

But what should the interface of these "execute an instruction" functions be?
We'll consider the kinds of things we want instructions to be able to do in
order to answer this question. Upon some inspection, there are three different
things our instructions can do: *Halt* the machine, manipulate the program tape,
or manipulate the memory tape. The last two of those are obviously just running
in the `State P''` Kleisli environment, and so all we're left with is the
*Halt*ing part.

At the end of the day, all we really care about from these instructions that can
*Halt* is "did we actually *Halt*?" As a result, we can model our instructions
as Kleisli values of the following type `State P'' Bool`. The `State P''` allows
us to manipulate the state of the *P''* machine, and the `Bool` output we'll
think of as `On` meaning "our machine is still on (we haven't *Halt*ed)" and
`Off` meaning "our machine is off (we have, in fact,  *Halt*ed)".

The *Halt* instruction is the simplest, so we can start there:

```
instrHalt : State P'' Bool
instrHalt = inject Off
```

`instrHalt` is the instruction which *always halts*, and so the only thing it
needs to do is to output `Off` and it's done. Nothing to it, really.

The *Move Left* and *Move Right* instructions are also easy, since we already
have the necessary functions to move the memory tape. Furthermore, these
instructions can never *Halt*, and so there's really no trick to them:

```
instrMoveLeft : State P'' Bool
instrMoveLeft = do
    (P'' progTape memTape) ← get
    set (P'' progTape (moveLeft memTape))
    inject On
```

```
instrMoveRight : State P'' Bool
instrMoveRight = do
    (P'' progTape memTape) ← get
    set (P'' progTape (moveRight memTape))
    inject On
```

Simple as borscht, really. These functions are identical to one another, except
that "Left" has been replaced by "Right". That's good, but we find ourselves
having to write a lot of "boilerplate" in order to accomplish things here. The
pattern is always the same: read the state, and then replace part of the state
with an updated value. Instead, we'll write a lemma to help with this pattern:

```
withMemTape : (Tape Nat -> Tape Nat) -> State P'' Unit
withMemTape f = do
    (P'' progTape memTape) ← get
    set (P'' progTape (f memTape))
```

`withMemTape` abstracts away a lot of that "get, change, set" pattern that we
found ourselves writing for `instrMoveLeft` and `instrMoveRight`. `withMemTape`
simply takes a function which describes how to change the memory tape, and it
performs that change for you.  We can thus rewrite our move instructions in
terms of this new abstraction:

```
instrMoveLeft : State P'' Bool
instrMoveLeft = do
    withMemTape moveLeft
    inject On
```

```
instrMoveRight : State P'' Bool
instrMoveRight = do
    withMemTape moveRight
    inject On
```

To my eyes, this is much more clear in terms of what it's accomplishing --
describing "what's going on" rather than "how to actually do it". Notice that we
could have shortened these functions a little more if we had moved the `inject
On` action into the `withMemTape` lemma, but that would have had strange
semantics, because it's unclear what a `Bool` coming from `withMemTape` might
mean. As such, we keep `withMemTape` outputting a `Unit`, encoding the concept
that it only changes the state directly into something meaningful in its type.

Before getting to the *Increment* and *Decrement* instructions, we'll need
another helper lemma. It's signature is `modHead: (a -> a) -> Tape a -> Tape a`,
which as you might expect from the name, *modifies the value at the read head*
of a tape:

```
modHead : (a -> a) -> Tape a -> Tape a
modHead f (Tape ls a rs) = Tape ls (f a) rs
```

With `modHead`, writing *Increment* is now simple:

```
instrIncrement : State P'' Bool
instrIncrement = do
    withMemTape (modHead succ)
    inject On
```

This might look a little strange if you haven't yet quite become comfortable
with the idea of function currying we looked at a few chapters ago. `modHead`'s
(specialized for here, non-polymorphic) type is `(Nat -> Nat) -> Tape Nat ->
Tape Nat`, but `withMemTape` is expecting an input of type `Tape Nat -> Tape
Nat`. We can wrestle `modHead`'s type into the correct "shape" by giving it
exactly one input -- the function it should use to manipulate the read head.
Here we pass `succ`, our old friend to find the successor of a `Nat`. With the
`succ` input snugly in place, `modHead succ` now has the type `Tape Nat -> Tape
Nat`, which is exactly the right shape to be plugged into `withMemTape`.

We turn our attention to the *Decrement* instruction, which will cause us a
little bit of grief, because it can *Halt* if the value at the read head of the
memory tape is `Zero`.

```
instrDecrement : State P'' Bool
instrDecrement = do
    (P'' progTape memTape) ← get
    attemptDecr (readHead memTape)
  where
    attemptDecr : Nat -> State P'' Bool
    attemptDecr Zero    = inject Off
    attemptDecr (S num) = do
        withMemTape (always num)
        inject On
```

`instrDecrement` is written in two parts -- first it pulls out the `readHead` of
the memory tape, and then passes that as an input to a local lemma defined in
the where-block: `attemptDecr`. This lemma pattern matches on its input; if that
input is `Zero`, we simply give back `Off`, which indicates we have halted.

Otherwise, `attemptDecr` updates the value at the read head of the memory tape
with the number `num` (which is one less than it used to be, due to the pattern
matching with `S`). We use the `always : x -> y -> x` function to get a function
which will always give back `num`, rather than depend on the current value at
the read head. We can get away with doing that because we've already computed
what it should be.

We're on the home stretch! Can you feel it? All that's left is to write the
*Enter Loop* and *Exit Loop* instructions, and then wire the whole thing
together. They're a little more involved, however, so we'll leave them until
the next chapter.

---

## Exercises

1) Define an analogous `withProgTape : (Tape Instr -> Tape Instr) -> State P'' Unit`
   function.
2) Rewrite the `instrDecrement` action in terms of the `decr : Nat -> Maybe Nat`
   function we defined when we were first looking at `Nat`s.

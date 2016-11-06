---
layout: post
title: Arithmetic
date: 2016-11-05 12:12
comments: true
tags:
---

In the last chapter we discussed the derivation of how to represent numbers in
our machine diagrams. However, the *representing* something is meaningless if
you don't have any means of interacting with that thing. In this chapter we will
come up with a way of working with numbers, and implement it as a machine
diagram. This is going to be the "heaviest" chapter yet, but the material is
surprisingly easy to follow as long as you Don't Panic!

> Takeaway: Take complicated-seeming things slow and make sure you Don't Panic!



## Addition as a Syntactic Operation

Now that we have a notion of numbers, there are two natural things we might want
to use them for: adding two numbers together, and describing how many times we
want some "action" done. Because we don't yet have a notion of what an "action"
might be (remember, our machine diagrams never change, once they've been given
their inputs), it seems more prudent to look into adding two numbers together.

Just like when we started looking for a way of representing numbers, our
approach will be to study how adding numbers works *in a symbolic sense.* Asking
about some kind of *meaning* behind adding two numbers can't possibly be a
fruitful endeavor, since we can't teach our diagrams about meaning.

This approach is know as being **syntactic** in nature, which means it follows
the *structure* of what the problem "looks like". Syntax is in strict dichotomy
with **semantics**, which describe the *meaning and interpretation* of
something.

A useful intuition behind syntax and semantics is that syntax exists *in the
world*, and semantics exist *in our minds*. Obviously, syntax is going to be the
easier thing to work with in most cases.

> Takeaway: Syntax is the factual structure of something, while semantics is the
> interpretation we put on that structure.

The divide between syntax and semantics requires a much deeper philosophical
dive than we will devote to it here today, but we'll discuss it in the next
interlude. In particular, the interplay between syntax and semantics goes a long
way to answering some of our earlier philosophical questions behind "why does
any of this work?"

But I digress. The question we're asking is "how does addition between numbers
work?" and furthermore, "what does addition look like on a syntactic level?"

The good news is that you already know the answer to both of these things. Pop
quiz: using a pen and paper, compute the answer to $1243+412$. I'll give you a
second.

Done? Good. Unless you're a math wizard, your approach to computing this sum
probably looked something like filling in this table, one column at a time:

|   |   |   |   |   |
|---|---|---|---|---|
|   | 1 | 2 | 4 | 3 |
| + | 0 | 4 | 1 | 2 |
|   |   |   |   |   |
|&nbsp;|&nbsp;|&nbsp;|&nbsp;|&nbsp;|

The approach is this: starting from the right, add the two symbols together
(which you've memorized), fill that symbol into the bottom line in the same
column, and repeat with the column to the left of it.

Make no mistake, this computation we've performed was *purely syntactic*. You
didn't have to know anything about numbers to do it. In fact, if we completely
jumbled up all symbols with ones you'd never seen before, and gave you a book
about how to add any two of these new symbols, you'd still do just fine.

Let's do one more example, just to make sure we've got it down:

|   |   |   |   |   |
|---|---|---|---|---|
|   | 2 | 4 | 7 | 7 |
| + | 0 | 4 | 2 | 6 |
|   |   |   |   |   |
|&nbsp;|&nbsp;|&nbsp;|&nbsp;|&nbsp;|

Keep the syntactic process we just discussed in mind as you work through this
example.

Uh oh! Notice anything wrong? Our original strategy forgot to take into account
what happens when we add up two numbers and they're larger than ten. We forgot
we sometimes needed to carry a one between columns!

> Takeaway: Always check a couple of examples before assuming you got it right.

Let's fill in the table from the last example together.

|   |   |   |   |   |
|---|---|---|---|---|
|   |   | 1 | 1 |   |
|   | 2 | 4 | 7 | 7 |
| + | 0 | 4 | 2 | 6 |
|   |   |   |   |   |
|   | 2 | 9 | 0 | 3 |

Whenever one column overflows ten, we need to do our old shuffle again, where we
move the 1 over to the next column. Furthermore, we realize that each column is
potentially a sum of *three* numbers -- the two we're adding, and a carry from
the last column, if necessary.

Great! So we have some idea of what we need to do. Again, like with our number
representation, all we need to do to translate this knowledge to binary is to
replace the word "ten" with "two" in the entire analysis. It might not be
immediately obvious why this is a safe thing to do, but it is because we never
did any analysis that depended on the number ten itself. If we had made a claim
like "because 10 is 2 more than 8", then we might be in hot water, but we didn't
so we're cool.

Because our analysis of how to perform addition is on a per-column basis, our
machine diagram of addition should itself be in terms of how to add a column. We
said that addition of a column depends on three things: the two numbers being
added, and a value being carried in from the previous column. The output is the
sum to put in this column, and the carry to move to the next column.

In short, we want a machine that looks like this:

``` {#black_box_adder}
circuit = runCircuit $ void $ do
  m <- liftDia $ machine ["A", "B", "Cin"] ["S", "Cout"] "Add"
  s <- liftDia $ fmap (||| inputWire) bend
  assertSame m (Out 0) s Split
  cout <- liftDia $ fmap (||| inputWire) bend
  assertSame m (Out 1) cout Split
```

(where `Cin` is short for "carry-in", `Cout` is likewise "carry-out", and `S` is
the sum for the column)


## Pack Up and Carry Out

What we need now is to determine the function table for such a machine. We'll
start with `Cout`, since it's easier to reason about. We need to carry a 1 when
our column has overflown. Our column can store a maximum of $1\text{b}$, but
we're adding three wires together, which is potentially as large as $11\text[b]
= 3$. Therefore, we want to output a 1 on `Cout` whenever two-or-more of our
inputs are 1.

Our function table for `Cout` must then look like this:

| A | B | Cin | Cout |
|:-:|:-:|:---:|:----:|
| 0 | 0 | 0   | 0    |
| 0 | 0 | 1   | 0    |
| 0 | 1 | 1   | 1    |
| 0 | 1 | 0   | 0    |
| 1 | 1 | 0   | 1    |
| 1 | 1 | 1   | 1    |
| 1 | 0 | 1   | 1    |
| 1 | 0 | 0   | 0    |

Turning function tables into combinations of gates is a bit of an art, but
thankfully it's pretty easy to reason our way through this one. We want to
output a 1 whenever two-or-more of our inputs are 1.

We know how to output a 1 if two inputs are 1 (an `and` gate), and we know how
to output a 1 if any of our inputs is a 1 (an `or` gate), so we've already done
most of the work.

If we make an `and` gate for every combination of our inputs, each `and` gate
will tell us if *both* of them are set. If we then combine each of the output of
those `and` gates with an `or` gate, we'll learn if *any* two of them are set.
Makes sense?

Armed with this knowledge, we draw out our machine to calculate `Cout`:

``` {#cout}
circuit = labeled "Cout" $ runCircuit $ void $ do
  let input l = do
        i <- liftDia $ fmap (\x -> wireLabel l ||| inputWire ||| x) bend
        icon <- liftDia con
        liftCircuit $ constrainWith hcat [i, icon]
        return i
  a <- input "A"
  b <- input "B"
  c <- input "Cin"
  andAB <- liftDia andGate
  andAC <- liftDia $ fmap (||| inputWire) andGate
  andACcon <- liftDia con
  liftCircuit $ constrainWith hcat [andAC, andACcon]
  andBC <- liftDia andGate
  orABAC <- liftDia $ (||| inputWire) <$> orGate
  orABACcon <- liftDia bend
  liftCircuit $ constrainWith hcat [orABAC, orABACcon]
  orACBC <- liftDia $ (||| inputWire) <$> orGate
  orACBCcon <- liftDia bend
  liftCircuit $ constrainWith hcat [orACBC, orACBCcon]
  orABC  <- liftDia $ fmap (\x -> x ||| inputWire ||| wireLabel "Cout") orGate

  liftCircuit $ constrainWith (vsep 1.1) [a, b, c]
  liftCircuit $ constrainWith (vsep 0.3) [andAB, andAC, andBC]
  liftCircuit $ constrainWith (vsep 1.5) [orABAC, orACBC]

  spaceH 1 a andAB
  spaceH 0.55 andAB orABAC
  spaceH 0.0001 orABAC orABC

  sameY andAC orABC

  arr (a, Split) (andAB, (In 0))
  arr (a, Split) (andAC, (In 0))

  arr (b, Split) (andAB, (In 1))
  arr (b, Split) (andBC, (In 0))

  arr (c, Split) (andAC, (In 1))
  arr (c, Split) (andBC, (In 1))

  arr (andAB, (Out 0)) (orABAC, (In 0))
  arr (andACcon, Split) (orABAC, (In 1))
  arr (orABACcon, Split) (orABC, (In 0))

  arr (andACcon, Split) (orACBC, (In 0))
  arr (andBC, (Out 0)) (orACBC, (In 1))
  arr (orACBCcon, Split) (orABC, (In 1))
```

It's kind of crazy, I know, but **Don't Panic!** While there's a lot going on
here, we don't need to pay attention to all of it simultaneously. Let's trace
through this diagram together.

Start on the left, at input `A`. Track its wire, and see that it feeds into both
the first and second `and` gates. There's nowhere else to go here, because we
don't know where the other inputs to those `and` gates are coming from.

So we go and we look at input `B`. We follow its wire, and see that it goes into
the first and third `and` gates. Now, the first `and` gate is fully connected,
so we know its output must be 1 only when `A` and `B` are both 1. The result of
this `and` gate flows to the top-most `or` gate, but we don't know where the
other one comes from, so we stop this line of inquiry.

All the way back to the beginning, where we look at input `C`. Its wire connects
to the second and third `and` gates, both of which are now fully connected. The
second `and` gate computes an "and" of `A` and `C`, while the third `and`
computes an "and" of `B` and `C`.

So far, so good. We've computed the "and" of every possible pair of `A`, `B`,
and `C`. If we follow the outputs of these, we see the top-most `or` gate now
answers the "or" of `A and B` or `A and C`. The bottom-most `or` gate answers `A
and C` or `B and C`.

Finally, we get to the last `or` gate, which computes `A and B` or `A and C` or
`B and C`. Which is to say, it computes whether any two of `A`, `B`, and `C` are
1. Exactly what we wanted.

**Wow! What an ordeal.** Give yourself a pat on the back if you made it through
that entire line of reasoning. Give yourself one even if you just managed to
read all of it without skimming through.

You might have noticed that we did strictly more work than was necessary; in
particular, we computed an `or` with `A and C` *twice*. You can actually *see*
it in the diagram -- it's the big left-half of a rectangle of wires coming out
of the `A and C` gate. Doing more work than necessary isn't a problem, and it
helped make the diagram a little prettier.



## Being More Exclusive

Before we get into figuring out how to compute the `S` output of our `Add`
machine, let's take a short intermission and build a gate that will turn out to
be very helpful in our endeavors.

When you think about it, the *semantics* of the `or` gate are kinda funky.
Recall that `or` is 1 if either *or both* of its inputs is 1. That's generally
not how humans think about "or". If your friend asked you whether you wanted to
go skiing this weekend or next, and you replied "yes", they'd probably be rather
surprised if you meant that you wanted to go *both* weekends.

When humans say "or", we usually mean "one or the other, *but not both*". This
is what's known as an **exclusive or**, or **xor** for short. Let's take a peek
at its function table.

| A | B | A xor B |
|:-:|:-:|:-------:|
| 0 | 0 | 0       |
| 0 | 1 | 1       |
| 1 | 1 | 0       |
| 1 | 0 | 1       |

(We've labeled the `Output` column to be `A xor B` here as a shorthand -- since
`xor` (and the other gates we've looked at) only ever give us back one output,
it's unambiguous to refer to this output as the result of the gate on the
inputs.)

Study the function table above -- notice that `A xor B` is 1 *only when `A` and
`B` have different values*.

We can use the same trick we did for `Cout` to write this function table out in
gates: we want `A and (not B)` or `(not A) and B`. The phrasing of that sentence
should be very suggestive of what the implementation of this machine will be.

``` {#xor_impl}
circuit = labeled "Xor" $ runCircuit $ void $ do
  ab' <- liftDia $ scale 0.5 <$> andGate
  a'b <- liftDia $ scale 0.5 <$> andGate
  or <- liftDia $ fmap (\x -> x # scale 1.3 ||| inputWire) orGate
  notA <- liftDia $ scale 0.3 <$> notGate
  notB <- liftDia $ scale 0.3 <$> notGate

  let input = do
        i <- liftDia $ fmap (inputWire |||) bend
        icon <- liftDia con
        liftCircuit $ constrainWith hcat [i, icon]
        p <- getPort icon Split
        return (icon, p)

  (a, acon) <- input
  (b, bcon) <- input

  assertSame notA (Out 0) a'b (In 0)
  assertSame notB (Out 0) ab' (In 1)

  spaceH 1.3 a ab'

  sameX ab' a'b
  sameX a b

  assertSame or (In 0) ab' (Out 0)
  assertSame or (In 1) a'b (Out 0)

  getPort ab' (In 0) >>= \p -> do
    leftOf acon p
    arr (a, Split) (ab', In 0)
    arr (a, Split) (notA, In 0)

  getPort a'b (In 1) >>= \p -> do
    leftOf bcon p
    arr (b, Split) (a'b, In 1)
    arr (b, Split) (notB, In 0)
```

Which, of course, we give a new symbol due to popularity:

``` {#xor_gate}
circuit = xorGate undefined ||| inputWire
```

> Takeaway: `xor` determines whether two inputs have different values.



## Some (Sum) Output

Back, finally, to the task at hand: defining the column sum of `A`, `B`, and
`Cin`. We wanted to do that a long time ago, though you've probably forgotten
since we've been through such a journey to get here. Don't give up, the finish
line is in sight!

We built all of that `xor` stuff because `xor` has an interesting property: it's
output looks a lot like the sum of two binary numbers, if you ignore carrying.

No! It's not just crazy talk! Let's take a look at a few examples:

* `0 xor 0` is 0, which is the same as $0\text{b}+0\text{b}=0\text{b}$
* `0 xor 1` is 1, which is the same as $0\text{b}+1\text{b}=1\text{b}$
* `1 xor 1` is 0, which is the same as $1\text{b}+1\text{b}=10\text{b}$ if we
    focus only on the rightmost digit

At first blush, that "focusing only on the rightmost digit" is a little
worrisome, until you realize that *that is exactly the semantics we want for the
sum*. Why? Because the sum is supposed to be the result we leave in a column
after addition *completely ignoring any carries*. Another way to think of `xor`
is addition that doesn't care about carries.

Which, of course, makes our implementation of the adder sum very simple -- we
just need to `xor` "add" our three inputs together, and the result is what we
want.

Let's do it. Last one for today, I promise.

``` {#sum}
circuit = labeled "Sum" $ runCircuit $ void $ do
  a <- liftDia $ fmap (\x -> wireLabel "A" ||| inputWire ||| x) bend
  b <- liftDia $ fmap (\x -> wireLabel "B" ||| inputWire ||| x) bend
  c <- liftDia $ fmap (\x -> wireLabel "Cin" ||| inputWire ||| x) bend
  acon <- getPort a Split
  bcon <- getPort b Split
  ccon <- getPort c Split

  ab <- liftDia $ scale 0.7 <$> xorGate
  abc <- liftDia $ (||| inputWire) <$> xorGate
  assertSame ab (Out 0) abc (In 0)
  spaceH 0.2 a ab

  sameX a b
  sameX a c

  getPort ab (In 0) >>= \p -> do
    leftOf acon p
    arr (a, Split) (ab, In 0)
  getPort ab (In 1) >>= \p -> do
    leftOf bcon p
    arr (b, Split) (ab, In 1)
  getPort abc (In 1) >>= \p -> do
    leftOf ccon p
    arr (c, Split) (abc, In 1)
```

Easy. Nothin' to it. All that's left is to implement `Add` in terms of `Cout`
and `Sum` by routing `A`, `B`, and `Cin` to the same input wires in both of our
smaller, "helper" machines. If you want to try your hand at it, go ahead, but
I'll assume you know how to (literally) connect the dots.

In the next chapter we'll hook up several of these column adders in a chain, and
tie all of the pieces together. We'll then take a break from numbers for a while
and discuss some ways of making these messes of machine diagrams a little easier
to work with.

---

## Exercises

None. Take a break. You've earned it.


---
layout: post
title: Abstraction
date: 2016-11-06 20:00
comments: true
tags:
---

In the last chapter, we (painstakingly) crafted a machine capable of computing
the `sum` and `carry` of column-wise addition for a binary digit. In this
chapter, we'll synthesis the last two chapters, connecting our numeric
representation in wires with our `Add` machine, and deal with any problems in
our notation as they come up.

The first thing to notice as we put our abstract ideas into practice is that our
machine diagrams are not infinitely large. Unfortunately there are infinite
numbers, and because we're representing numbers as wires (which have a size),
there's no way we can *possibly* fit a representation of *every* number into our
diagram. We simply don't have space for them all.

As a practical consideration, we'll need to decide *beforehand* how many wires
we're going to dedicate to the representation of numbers. Our wire-count is
going to have real, visible, implications on *the largest number we can
represent*, which as we will see, will later affect all sorts of things we might
want to do with numbers.

In the same way that choosing three decimal digits allowed us to represent
$10\times 10\times 10=1000$ different numbers, if we pick three wires to
describe our binary number, we'll get $2\times 2\times 2=8$ numbers to play with.

$\renewcommand{bin}[1]{#1\text{b}}$ Interestingly, we can write the equation
$2\times 2\times 2=8$ as $\bin{10}\times\bin{10}\times\bin{10}=\bin{1000}$,
which looks a lot like our original reasoning in the decimal number system. I
wonder why that is?

The wire count we choose to let us describe numbers is our machines is known as
our **bit count**, and each of the wires respectively is known as a **bit**.
You've probably heard this before -- a few years ago there was a lot of talk
about moving all of our *32-bit computers* to be *64-bit computers*.
Intuitively, you can think of the bit-count as controlling how big the biggest
number our machines can work with.

| Bits | Total Numbers | Biggest Number |
|:-:|:-:|:-------:|
| $1$  | $2^1$    | $1$                    |
| $2$  | $2^2$    | $3$                    |
| $4$  | $2^4$    | $15$                   |
| $8$  | $2^8$    | $255$                  |
| $16$ | $2^{16}$ | $65535$                |
| $32$ | $2^{32}$ | $4294967295$           |
| $64$ | $2^{64}$ | $18446744073709551615$ |
| $n$  | $2^n$    | $2^n-1$                 |

As you can see, every time we add a bit (wire), we *double* the total count of
numbers we can represent. That means when we moved from 32-bit to 64-computers,
we didn't get numbers $2\times$ as large, we got numbers $4294967295\times$ as
large!

That's a lot of numbers. Probably more than we'll ever need. Definitely more
than we'll need for the purposes of this book. *We're going to arbitrarily
decide on **4 bits*** for our machines, because it's large enough that we can
get a sense of how to work with these things, but it's not so big that the
majority of our diagrams are going to just be shuffling bits around.

In most computers, the smallest thing you can work with is *8 bits*, and it's
called a *byte*. We'll call the collection of our 4 bits a **nybble**, since
it's half a byte.

You'll either be delighted or terribly upset that I didn't make that joke up.
That's what these things are called.

Enough jibber-jabber. Let's get to drawing these things. Here's how we draw a
nybble:

``` {#nybble}
circuit = vsep 0.1 $ replicate 4 inputWire
```

As a matter of convention, we'll decide that the least-significant (lowest
bit-number, therefore contributes the least to the total number) wire is on the
bottom.

``` {#nybble_nums}
circuit = vsep 0.1 $ fmap (\x -> wireLabel (show x) # scale 0.3 ||| inputWire ||| inputWire) [8, 4, 2, 1]
```

Remember, the way we interpret what number this nybble represents is by adding
together the numbers labeled on this wires *if that wire is high*. If the top
and bottom wires were on, but the middle two were off, this nybble would
represent the number $8+1=9$.

Let's now finish up the work we did last chapter, and make a machine that will
add two nybbles together, by using the `Add` machine we made!

``` {#nybble_add}
addScale = 0.3
nybble s = vsep 0.1 $ fmap (\x -> inputWire ||| mkCon s (Out x)) [3, 2, 1, 0]
deWire s = mkCon s (In 0) ||| inputWire # scale addScale ||| mkCon s (Out 0)
vdeWire s = (mkCon s (In 0) ||| inputWire # scale addScale ||| mkCon s (Out 0)) # rotate (-1/4 @@ turn)
add n n1 n2 = do
  m <- liftDia $ (# scale addScale) <$> machine ["A", "B", "Cin"] ["Cout", "S"] "Add"
  cin <- liftDia $ vdeWire
  cout' <- liftDia $ deWire
  cout <- liftDia $ vdeWire
  s <- liftDia $ (scale (1 / addScale)) <$> deWire
  assertSame m (Named "Cin") cin (In 0)
  assertSame m (Named "Cout") cout' (In 0)
  assertSame cout' (Out 0) cout (Out 0)
  assertSame m (Named "S") s (In 0)
  arr (n1, (Out n)) (m, (In 0))
  arr (n2, (Out n)) (m, (In 1))
  return (m, cin, cout)
cons s = mkCon s (Out 0) === circle 0.05

circuit = labeled "Add4" $ runCircuit $ void $ do
  n1 <- liftDia nybble
  n2 <- liftDia nybble
  (a1, a1in, a1out) <- add 0 n1 n2
  (a2, a2in, a2out) <- add 1 n1 n2
  (a3, a3in, a3out) <- add 2 n1 n2
  (a4, a4in, a4out) <- add 3 n1 n2
  c <- liftDia cons

  arr (a1out, (In 0)) (a2in, (Out 0))
  arr (a2out, (In 0)) (a3in, (Out 0))
  arr (a3out, (In 0)) (a4in, (Out 0))

  assertSame c (Out 0) a1in (Out 0)

  spaceV 1 n1 n2
  liftCircuit $ constrainWith (hsep 2) [n1, a4]
  liftCircuit $ constrainWith (vsep 0.1) [a4, a3, a2, a1]
```

Don't Panic! There's a lot going on here, but it's actually not that bad at all.

As inputs to `Add4`, we're taking two nybbles. As per our convention, the
bottom-most wire in each nybble is the smallest bit in it. Both of these
least-significant bits are moved to the bottom-most `Add` machine. Because we
have nothing to "carry-in" at this point, we always input a 0 to this `Cin`
(indicated by the circle leading into it).

The `S` of this `Add` machine is output as the least-significant bit of the
nybble we're computing. The `Cout` is carried over to the next adder's `Cin`.

See, it's really not very complicated conceptually; it's just that our diagrams
aren't very powerful -- they require us to draw a wire for every bit in our
nybble. The problem is that we want to deal with nybbles directly, but we don't
have an abstraction mechanism for wires. In the case of machines, we can just
draw a big box around the internals of it, and then use a box with a name (like
we did for `Add`, above), which effectively allows us to *abstract away the
details of a machine*.

Similarly, it's pretty evident that we're going to need a strategy for
describing patterns in our wiring if we're going to make things any larger than
this `Add4` machine.



## Multiwires

This is a multiwire.

```{#multiwire}
circuit = polyIn ||| (wireLabel ": 8" # scale 0.5 # translateX 0.15 <> inputWire) ||| inputWire
```



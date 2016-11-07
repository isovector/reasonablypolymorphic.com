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
circuit = text "}" # scale 0.15 # translateY (-0.003) ||| inputWire
```

You can think of a multiwire as several wires all drawn together as one. The `}`
symbol is sort of like "braiding" several wires into one single strand. In doing
so, we've lost track of the underlying details of what the wires used to look
like, which is kind of what we wanted. What we don't want, however, is for those
details to be lost entirely; we want to tuck them away for most of the time, but
be able to get them back when we're interested. Like with machines, we can hide
the details by drawing a box with a label on it, but if we're interested in how
it works, we can always go back and find the diagram we drew for its internals.

To keep track of what a multiwire actually looks like in reality, we'll annotate
it. For example, a nybble would look like this:

```{#multiwire_annotate}
circuit = text "}" # scale 0.15 # translateY (-0.003) ||| (wireLabel ": 4" # scale 0.5 # translateX 0.15 <> inputWire)
```

Here, the `:4` annotation on the wire indicates that this multiwire is actually
a stand-in for 4 wires -- ie. it's a nybble.

Great! So multiwires let us move several wires around at once; but how do we
actually work with them? The easiest way is for us to just treat them as a group
of wires. For example, we could draw the `Add` machine (which we skipped in the
last chapter, due to not wanting to have to draw all of the lines) like this:

```{#mw_add}
wireLabel s = topLeftText s # scale textSize # translate (r2 (-0.2, 0.3))
mw a = text "}" # scale 0.5 # translateY (-0.003) ||| inputWire ||| wireLabel ": (A,B,Cin)" ||| inputWire ||| mkCon a (Out 0)
deWire s = mkCon s (In 0) ||| inputWire ||| mkCon s (Out 0)

circuit = labeled "Add" $ runCircuit $ void $ do
    i <- liftDia mw
    -- TODO(sandy): stupid stuff here to get the machines to not look like crap
    add <- liftDia $ machine ["*"] ["", "S", " "] "Sum"
    cout <- liftDia $ machine ["*"] [" ", "Cout", ""] "Cout"
    coutWire <- liftDia deWire
    b <- liftDia con
    b' <- liftDia bend
    assertSame i (Out 0) add (In 0)
    assertSame i (Out 0) b Split
    assertSame cout (Out 1) coutWire (In 0)
    arr (b, Split) (cout, In 0)
    liftCircuit $ constrainWith (vsep 0.1) [add, cout]
    getPort b' Split >>= \p0 ->
      getPort coutWire (Out 0) >>= \p1 ->
      getPort add (Out 1) >>= \p2 -> do
        above p0 p1
        leftOf p2 p0
        arr (add, Out 1) (b', Split)
```

Here we've annotated our multiwire with `(A, B, Cout)`, which, as you can
probably guess, means we have 3 wires "inside" of our multiwire. We've changed
the inputs on our `Sum` and `Cout` machines to be `*`, which we will use to
indicate that the multiwire fits "just right".

Which is really cool! We've just saved ourselves a lot of time and paper for
drawing these things. Unfortunately, this usage of a multiwire doesn't fit all
of our desired use-cases. Consider our implementation of `Add4` above -- we had
to do a huge amount of wire branching in order to get everything to do what we
wanted.

What we also want to do is to be able to describe "split *each* of the wires of
this multiwire into a copy of this machine." Such capabilities allow us to
implement `Add4` more concisely like this:

```{#mw_add_four}
wireLabel s = topLeftText s # scale textSize # translate (r2 (-0.2, 0.3))
mw l a = mkCon a (In 0) ||| text "}" # scale 0.5 # translateY (-0.003) ||| inputWire ||| wireLabel l ||| inputWire ||| text "{" # scale 0.5 ||| mkCon a (Out 0)
mw' l a = (mkCon a (In 0) <> text "}" # scale 0.5 # translateY (-0.003) # translateX 0.1) ||| inputWire ||| wireLabel l ||| inputWire
deWire s = mkCon s (In 0) ||| inputWire ||| mkCon s (Out 0)
vdeWire s = (mkCon s (In 0) ||| inputWire ||| mkCon s (Out 0)) # rotate (-1/4 @@ turn)

circuit = labeled "Add4" $ runCircuit $ void $ do
  n1 <- liftDia $ mw ":4"
  n2 <- liftDia $ mw ":4"
  m <- liftDia $ machine [ "A", "B", "Cin" ] [ "S", "Cout" ] "Add"
  assertSame n1 (Out 0) m (In 0)
  assertSame n2 (Out 0) m (In 1)
  cin <- liftDia vdeWire
  cout <- liftDia deWire
  cout' <- liftDia $ scale 1.5 <$> vdeWire
  s <- liftDia $ mw' ":4"
  assertSame m (In 2) cin (In 0)
  assertSame m (Out 1) cout (In 0)
  assertSame m (Out 0) s (In 0)
  assertSame cout (Out 0) cout' (In 0)
  arr (cin, Out 0) (cout', Out 0)
```

We use a "backwards" multiwire symbol to indicate that we want to "separate" the
multiwire out and make a copy of the machine on the other end for every wire
inside of the multiwire. Because both the `A` and `B` inputs have same-sized
multiwires fanning into them, this means we want to process the multiwires at
the same time. Meaning, we will make four copies of the `Add` machine. To one of
them, we will  take the least-significant bit from both of our multiwires and
connect them to the `A` and `B` inputs, respectively. Another copy of the
machine will get both second-least-significant bits, and so on.

On the other side of our `Add` machine, we use multiwire notation on the `S`
output to indicate we want to put all of the `S` results from the machines
(remember, there are 4 of them hiding in this diagram, because we make a copy
for every one in the multiwire fanning *into* it). Therefore, the result of this
machine is a nybble.

The other funky thing we need to notice is that we have a wire connecting `Cin`
to `Cout`. This is clearly nonsensical, so we decide by fiat that it means "take
`Cout` from this machine, and connect it to the `Cin` for the
next-most-significant machine". If there is no less-significant-machine to take
a `Cin` from, we assume a value of 0 was passed in by default.

If this is all a little confusing to you, don't worry. We've jumped up a huge
level of abstraction, and that takes a lot of getting-used to. There will be a
lot of practice in the upcoming chapters to make sure you've really nailed this
stuff, but the takeaway is that the diagram we just drew out describes *exactly
the same thing* as this one we built earlier.

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

In the next chapter, we'll build some new machines to take advantage of all of
this multiwire stuff, and see what else we can do with it.

---

## Exercises

1) Study both the original `Add4` and the multiwire `Add4` diagrams. Try to get
   a sense of what the multiwires must be doing in order for these diagrams to
   be the same.
2) Use our new multiwire diagrams to build a machine that takes two nybbles and
   outputs a nybble that has performed an `and` gate on them, wire-wise. That is to
   say, the most-significant bit of your output nybble should be the `and` of the
   most-significant bits in either of the nybbles.
3) Assuming you have an `and` gate which can accept a multiwire, and outputs a
   single wire with value 1 *if all of the wires in the multiwire were 1*,
   construct a machine which computes whether two nybbles represent the same
   number.


---
layout: post
title: Symbolic Evaluation and Equational Reasoning
date: 2016-11-14 14:00
comments: On
tags:
---

In the last chapter, we discussed the composition mechanics of machines in our
new system of symbolic computation. The claim is that symbolic computation is
actually a means of computation, and today we're going to look at how that can
be so. We'll discuss a technique called **equational reasoning** and use it to
-- you guessed it -- reason about all of this mumbo jumbo.

We've now introduced our notation for machine implementations a few times, but
we will re-examine our `nandn` example from last chapter.

```
nand : Bool -> Bool -> Bool
nandn a b = not (and (not a) b)
```

Let's say we'd like to evaluate (determine) the output of `nandn` with inputs
`On` and `Off`. Recall, that we can write this output as `nandn On Off`.
Although we are currently unaware of the value of `nandn On Off`, we know that
it will indeed have some value, because our function tables must be *total*
(they must be defined for all possible inputs).

We call such a thing -- something which has a value, even one that we haven't
yet evaluated -- an **expression**. Expressions are everywhere, and they are the
bread and butter of our symbolic computation. `On` is an expression, because it
has a value (which is just itself.) `not On` is another expression, because we
can run `On` as an input to the `not` gate, and retrieve a value as its output.

However, `and On` is *not* an expression, because it is missing an input. `and`
gates always have two inputs, but `and On` is only supplying one input, and so
it cannot have a value, and it is therefore not an expression.

Expressions have one primary desire in life, and that is to be evaluated -- that
is, to determine what value they eventually end up as. Evaluating an expression
is easy -- so easy that even a stupid electronic circuit can do it. Let's
continue with our `nandn On Off` example.

The first step to evaluating an expression is to have all of the function tables
it's made out of handy. If you don't have all of the function tables, you're
eventually going to get stuck, since a function table is necessary to reduce a
machine's expression to its final value.

Once you have all of the machine implementations in front of you, it's time to
get to work. Replace any machines in your expression with their definition,
remembering to substitute the bindings in the definition with the ones you
started with. We can use our definition of `nandn` to partially evaluate `nandn
On Off` as follows:

```
not (and (not On) Off)
```

Don't forget to replace bindings! Here, because `On` was the first input to
`nandn`, we replaced all of the bindings `a` in the definition of `nandn` with
`On`, and all of the bindings of `b` with `Off`. If we had had `nandn Off Off`
instead, we would have replaced `a` with `Off`.

*Make sure you replace **all** of your bindings before proceeding.* If you don't
get all of them, you'll probably get confused somewhere down the line when you
expand another machine that uses some of the same letters for binding. Remember,
just like in our machine diagrams, the *same* letter means *different* things
when used in different machines. This is the most critical part of the whole
technique, and it bears repeating. Many a beginner have lost their way at this
step.

Now that you've successfully replaced all of your bindings with the correct
inputs, you're ready to rinse and repeat! But all of a sudden we've got this
expression which is actually longer than what we started with! So much for
reducing it!

This is the way that things always are. Evaluating an expression always balloons
up in complexity before it settles down into something more manageable. This
seems like it might be annoying, but it turns out to be one of the most
important parts. It's great that the thing we start with is small and simple,
because that allows us to perform abstraction, and to keep more things in our
heads simultaneously. It's good at the end result is simple, because it *has* to
terminate in a single value eventually. And it's good that it balloons up,
because that means our abstractions are doing lots of work for us (whenever
we're not *explicitly performing evaluations by hand*).

This last part is worth mentioning again -- we usually don't need to evaluate by
hand. Most of the time it's clear how a machine will behave, and so evaluation
isn't necessary. But it's a nice technique to have under your belt, just in
case you find yourself in a pickle one day, a pickle that only symbolic
evaluation can get you out of. It could happen. You never know.

The good news for our interpreting selves is that this process of expanding out
a machine's definition and replacing the bindings will *always* result in an
expression with at least one machine whose inputs are all raw values, and that
means we have a place to proceed the simplification process.

However, the other good news is that I'm not your dad -- you can pick any
machine you'd like to expand out next. The most natural order is probably
inside-out (starting from the most parenthetical machine, and working your way
backwards), but you can do whatever you'd like. We'll proceed with the
expression's evaluation here.

```
not (and Off Off)
```

```
not Off
```

```
On
```

And there you have it! A value comes forth from whence there was none
originally.


## Equational Reasoning

Ready for something completely wild? Because of a thing called **equational
reasoning**, we can actually work backwards, and build expressions that evaluate
to a particular value. As long as we replace something in our expression with an
expression that has the same output as what we replaced, we are guaranteed to
never go wrong.

Let's try an example:

```
Off = Off
```

```
Off = xor Off Off
```

```
Off = xor (and On Off) Off
```

```
Off = xor (and On Off) (not On)
```

This isn't a particularly useful thing in-and-of-itself, but the point of the
exercise is to demonstrate that we don't lose anything going one way or the
other. This is why we use an equals sign when defining the outputs of our
machines -- it's because these things really are equal, and there's absolutely
no test "inside the system" (which is to say, not "looking at the paper you
wrote down") to distinguish `xor On Off` from `On`. It just can't be done, and
that's a nice property to have.

Why? Because it means we are free to abstract at will, and no-one will be any
the wiser. It means that at the end of the day, a smart solution to a problem
works just as well as a stupid one, and that as long as we're following all the
rules, we're safe to do whatever we please -- content in the knowledge that
we're not "losing anything" when we work in more convenient settings.

> Takeaway: Equational reasoning means that it's safe to work at whatever level
> of abstraction we feel most comfortable in. It's a promise that nothing can
> "go wrong" when we move between levels of abstraction, so long as our
> individual steps are all honest.

Equational reasoning fills another role in our toolkit, however, and that's for
proving **algebraic identities**. An *algebraic identity* is two expressions
which are always equal. What's that mean?

Well, suppose I go and implement some convoluted machine that computes a
particular function, but evaluating it takes 100 steps. You, being the more
clever of my friends, come up with a machine you swear to me is the same -- in
the sense that it matches outputs with mine, input for input. If my machine
takes 20 inputs, that's not a thing I want to try to verify by hand. Instead, we
could work together to try and derive an *algebraic identity* between our
machines, a proof that they are one-and-the-same.

This is why being able to work forwards and backwards is important for our
reasoning when doing symbolic evaluation. Just like doing a pen-and-paper maze,
it can be helpful to work forwards and backwards at the same time -- attempting
to meet in the middle.

As an example, let's work through a proof of an algebraic identity for
*de Morgan*'s laws.

```
and a b = not (or (not a) (not b))
```

We know that there are two cases for `a`, either `On` or `Off`, so we can try
both:

```
and On b  = not (or (not On) (not b))

and Off b = not (or (not Off) (not b))
```

Remember, that whenever we replace a binding, we need to change all instances of
that binding to the same expression. We can continue on, by simplifying our
`not`s now:

```
and On b  = not (or Off (not b))

and Off b = not (or On (not b))
```

We know that anything `and`ed with `On` keeps its value, and anything `and`ed
with `Off` has value `Off`, so we can evaluate our left-hand-sides:

```
b = not (or Off (not b))

Off = not (or On (not b))
```

Likewise, we know that an `or` against `On` is always `On`, and that an `or`
against `Off` keeps its value, so we can go on:

```
b = not (not b)

Off = not On
```

and we're left with very simple things to prove the equivalency of. Dead simple
when you get down to it.

We'll revisit equational reasoning again when we build stronger abstractions
which require "laws" -- inviolable algebraic identities for defining machines.
Well chosen laws allow us the luxury of building loosely-defined machines
"molds", particular machine "shapes" which we can reason about for any machine
definition respecting the laws. This probably doesn't sound too powerful to you
yet, but as we'll see, it's truly one of the most powerful forces in the logical
universe.

In the next chapter, we'll investigate moving more of our old machine diagrams
to symbolic computation, and solve some of the remaining challenges that come
up.

---

## Exercises

1) Fully evaluate (walk through all the steps of it) the expression `or (xor
(and On Off) Off) (or Off (not Off))`.
2) ok

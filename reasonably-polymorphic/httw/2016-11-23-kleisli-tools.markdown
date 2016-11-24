---
layout: post
title: Kleisli Tools
date: 2016-11-23 20:00
comments: true
tags:
---

Welcome back! Thanks for not having torn your eyes out with disgust at how
egregiously difficult it was to use our Kleisli category for `State s` in the
last chapter. Our plan for this chapter, as promised, is to derive some useful
lemma machines to allow us to work with Kleisli categories more easily.



## Lambda Abstraction

The first tool we'll need isn't particularly tied to Kleisli categories, but
it's what you might call a "quality of life" improvement, in that it will allow
us to write symbolic computations a little more tersely. This tool comes
directly from the realization that although we have been saying that our
machines are just values, they're obviously different somehow. We can see this
in the sense that our symbolic computations require a "special" syntax to make
machines. Let's take a closer look.

In order to evaluate, for example, our machine `map : Kliesli m => (a -> b) -> m
a -> m b`, we need a function of type `a -> b` to give it as an input.
Evaluating it might look something like this:

```
addTwo : Nat -> Nat
addTwo n = n + 2

> map addTwo (Just 8) = Just 10
```

This works well enough, but it's rather annoying that we need to make a new
machine definition every time we want to use a higher-order function (such as
`map`). Especially if this machine is nothing but a lemma and won't be useful
anywhere else, it'd be nice if we could somehow define our function *where we
want to use it*, rather than somewhere above or below.

With this in mind, our first tool will be a means of describing simple machines
locally at the place they're needed. As an example of this, will can rewrite our
above example with our new tool:

```
> map (λn. n + 2) (Just 8) = Just 10
```

Much simpler! What a welcome change that is. We call this `λn. n + 2` a **lambda
abstraction**, a **lambda expression**, or if you're a fan of brevity, it's also
known as just a **lambda**.

There are a few rules around the syntax of *lambda abstractions*. The lambda
symbol `λ` introduces a new *lambda expression*, which takes inputs separated by
spaces until the next `.`. Each of these inputs is bound in the *lambda*
machine, and refers to a new binding that didn't exist before. That means if
there is already a binding called `x` when we create our *lambda* `λx. x`, the
`x` inside of the lambda refers to the input bound by the lambda, not to the one
that existed beforehand. That being said, a lambda can refer to any bindings that
existed already so long as they don't share a name.

Such a property (stealing the name of binding if it conflicts) is known as
**lexical scoping** of bindings. Our entire system of symbolic computations is
*lexically scoped*, and so *lambdas* share the same rules as the rest of the
language. Parsimony!

The other syntactic rule of *lambdas* is that their function definition extends
as far as it can. This means that

```
map λn. n + 2 (Just 8)
```

is *not* equivalent to the one given earlier. This represents attempting to pass
a single machine defined as `λn. n + 2 (Just 8)` as the first input to `map`,
which doesn't make any sense, and obviously isn't what we meant. In order to
delimit the contents of a *lambda*, we must enclose it in parentheses.

This rule of "extending as far as you can" has the interesting property that it
allows us to write *lambdas* inside of *lambdas*:

```
λx. λy. x + y
```

is a lambda which binds `x`, and then outputs a lambda which binds `y` and then
outputs `x + y`. You'll recall that all of our machines are *curried* like this,
so there's nothing new here, but it's nice to know that the same rules apply.
This will come in handy in a second.

Before we move on, we should note that *lambdas*, just like regular machines, may
take multiple inputs:

```
λx y z. x + y + z
```

and this behaves exactly as you'd expect it to -- taking three inputs, `x`, `y`,
and `z`, and then adding them together.


## Kleisli Bind

The next tool we'll formalize is actually one we've already seen. Recall our
definition of `hold` from the previous chapter:

```
hold : Bool -> State Bool Bool
hold val = bind get withState
  where
    bind : State Bool a -> (a -> State Bool b) -> State Bool b
    bind ma f = (composeK (always m) f) Unit

    always : x -> (y -> x)
    always x _ = x

    withState : Bool -> State Bool Bool
    withState s = bind (set (or val s)) (always get)
```

This `bind` thing seems rather odd -- it doesn't appear to have anything to do
with `State` or even with the computation behind `hold`. All we need it for is
as an "adapter" to allow us to start our Kliesli composition. By that we mean
that if we have a function of type `a -> m b`, and we have an `m a`, how can we
apply our function to the `m a`? `bind` is the solution to this problem.

We have a quick lemma to look at before getting around to bind, however:

```
always : x -> y -> x
always x _ = x
```

`always` is one of those "adapter" higher-order machines. `always` takes two
inputs, and regardless of what the second one is, it returns the first input.
This means if we fill in the first input but leave the second empty, we get a
machine that "always" spits out the first input we put in, no matter what this
machine is called with. That means we can use it to transform our `m a` into a
`y -> m a`, allowing us to begin Kleisli composing things together.

With `always` under our belt, we're ready to look at `bind` proper.

```
bind : Kleisli m
    => m a
    -> (a -> m b)
    -> m b
bind ma f = (composeK (always ma) f) Unit
```

We can use `always ma` to get a function of type `y -> m a` (here `a` is no
longer a type variable -- it's fixed to be the same `a` as was in our `ma : m
a`. `y`, however is still polymorphic). With this function, we can `composeK` it
with `f : a -> m b`, the result of which is `y -> m b` for some polymorphic `y`.
Because `y` is polymorphic, it can be anything, so we fill it with a `Unit`, and
out pops a value of type `m b`.

`bind` can be thought of like this: it allows us to supply a value existing in a
context, to a computation which itself runs in a context. It's analogous to
"running a pure computation with a pure input", except now we're running
*Kleisli* compositions with *Kleisli* inputs.

As it happens, `bind` plays a very important role in the Kleisli tool ecosystem.
In fact, it's so important that we will come up with a symbolic name for it (in
the same way that we had special symbols for our core gates back when we were
doing machine diagrams). The symbol we use is `»=`, but is still pronounced
"bind". Because of this symbol, the two following expressions are equivalent:

```
> bind ma f
```

and

```
> ma »= f
```


## Hold, Revisited

Recall, our original definition for `hold`. It's still just as ugly as it ever
was:

```
hold : Bool -> State Bool Bool
hold val = bind get withState
  where
    bind : State Bool a -> (a -> State Bool b) -> State Bool b
    bind ma f = (composeK (always m) f) Unit

    always : x -> (y -> x)
    always x _ = x

    withState : Bool -> State Bool Bool
    withState s = bind (set (or val s)) (always get)
```

however, armed with our new tools, we can write `hold` in this much prettier
form:

```
hold : Bool -> State Bool Bool
hold val =     get
        »= λs. set (or val s)
        »= λ_. get
```

Regardless of your political, racial, historical, or desktop background, you
must admit that this is much nicer to deal with and to reason about. When
presented in this format, it's pretty clear that there are some series of steps
happening to compute the result. First, we `get` the current state, and bind it
to `s`. We then `set` the state to `or val s`, and then output the new state.

Because of our rules about the extent of *lambda abstracts*, after `s` is bound
on the second line, it would be available anywhere after that, should it be
necessary. We ignore the output coming out of `set` (`λ_.`) because if you
remember, `set` always returns `Unit`, which is uninformative for us to bind.

As a matter of fact, we'll see that we usually don't care about the output of a
particular Kleisli computation -- often we're just composing them in order to
run their "side effects" on the context/environment. This use case is so common
that we present one last lemma: `ignoring`.

```
ignoring : Kleisli m
        => m a
        -> m b
        -> m b
ignoring ma mb =     ma
              »= λ_. mb
```

which goes by the special symbol `»`. Ignoring performs the "side effects" of
its first input, but actually returns just its second input. You can keep `bind`
(`»=`) separate from `ignoring` (`»`) in your mind by remembering that bind
allows you to "equate" a binding, so it's the one that has the equals sign.

With `ignoring`, we can write `hold` again:

```
hold : Bool -> State Bool Bool
hold val =     get
        »= λs. set (or val s)
        »      get
```

This is pretty good, all things considered. We have one final complaint,
however. The binding `s` gets it value from the first `get`, but the first
sighting of `s` is on the next line! That's bad for those of us with slight
obsessive compulsions, and so we'll introduce one final syntactic piece of
"sugar" to help us along. It's called `do`-notation, and we can use it to
rewrite `hold` one last time:

```
hold : Bool -> State Bool Bool
hold val = do
    s ← get
    set (or val s)
    get
```

In `do`-notation, we introduce a new "block" in which Kleisli values are written
one-a-line. If the result of any particular Kleisli value is interesting to us,
we can bind it via the `←` symbol. This new binding is available to us for all
Kleisli values below the current line, because behind the scenes, all
`do`-notation is doing for us is giving us a less-boilerplate way of writing
nested *lambdas* and `bind`s.

Whenever a binding is required, say `s ← get`, `do`-notation "de-sugars" down
to `get »= λs. ` and the computation carries on its merry way. If a binding
*isn't* required, `do` uses `ignoring` (`»`) to discard that particular value.

It's finally time to rejoice. With `do`-notation, our deep dive into *Kleisli
categories* is complete, and we find ourselves with *all the tools* necessary to
continue doing work on the computer we've been wanting to build for this entire
time. We'll really and truly get back to that in the next chapter, an with our
new tools, the remainder of our project will be surprisingly easy.

---

## Exercises

1) Rewrite `map : Kleisli m => (a -> b) -> m a -> m b` from the last chapter in
   terms of `do`-notation.
2) Manually desugar the following `do`-notation to make sure you've got the hang
   of it:

```
modifyAndAdd : (Nat -> Nat) -> State Nat Nat
modifyAndAdd f = do
    oldState ← get
    set (f oldState)
    newState ← get
    inject (oldState + newState)
```

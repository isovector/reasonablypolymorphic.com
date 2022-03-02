---
layout: post
title: Of Ideas and Men
date: 2015-07-07 17:16
comments: true
tags: haskell, technical
---

## I

You know when you're writing imperative code, and you start swearing because you
just realized you need a variable that you haven't had in scope for like ten
frames on the call-stack? We've all been there, and we've all come up with some
expressions worthy of a sailor.

Let's say maybe you're writing the drawing code for a game, and have lots of
methods like this:

```cpp
void Scene::draw(RenderTarget& target) const {
    for (Drawable &child : children_) {
        child.draw(target);
    }
}

void Character::draw(RenderTarget& target) const {
    head_.draw(target);
    torso_.draw(target);
    feet_.draw(target);
    fancyParticleSystem_.draw(target);
}
```

And everything is going fine and dandy, until you realize that your fancy
particle system needs the time elapsed since the last frame in order to do fancy
particle things.

I'm speaking from experience, here. This exact situation has happened to me, at
least twice; you'd think I'd learn.

You stop for a second to think about how you're going to fix this. Continuing to
curse isn't going to help anything, so otherwise you have two options going
forwards: you can either change every call-site of `draw` to ensure that
you can get the elapsed time to the particle system, or you can phone it in and
make the damn thing global.

You feel drawn towards the making-it-global solution, but you'd feel bad about
it the next day, and besides, we both know it wouldn't pass code review. With a
sigh, you resign yourself to updating the method signature:

```cpp
void Drawable::draw(RenderTarget& target, float delta) const;
```

In our small example here, there are *seven* lines you need to change in
order to make it happen. Just imagine how much refactoring would be necessary in
a *real* codebase!

Two hours later, you realize you need another parameter. You go through
everything again, plumbing it through. It's tedious, and you can't help but feel
like maybe there's a better way of doing this.

<!--more-->

***


Or perhaps you're writing some Javascript, and the seemingly innocuous line

```javascript
var cash = bank.currentUser.account.getValue();
```

crashes in a firey wreck with the demonstrably-evil error **undefined is not a
function**. Apparently *one* of those properties doesn't exist, but you're not
sure which. Because you are a seasoned veteran, you know what the fix is; you
need to make sure that each of those properties exists before indexing into it.
With celerity (and some indignation that the API guys don't seem to be able to
do their job properly), you hammer out the solution:

```javascript
var cash;
if (bank && bank.currentUser && bank.currentUser.account) {
    cash = bank.currentUser.account.getValue();
} else {
    return null;
}
```

Great. You've gone from one line to five, but hey, at least it will work. So you
hit F5 in your browser, and your heart sinks. Now the *call-site* is missing a
null check, so you go to fix that too, this time carefully crawling upwards
making sure nothing else will explode.

You find yourself writing dozens of snippets along the lines of "check if it's
null, if it is, return null, otherwise do what you were doing anyway". It's not
a fun experience, and somewhere deep down you feel like this should be the kind
of problem the runtime should be able to solve for you; after all, it's a purely
mechanical change requiring no thought whatsoever.

Isn't that the kind of thing computers are *really good at*?

***


Maybe instead of being a hip Javascript developer, you're a crusty, suit-wearing
and fun-hating programmer who works for a bank. The Man has gotten on your case
because sometimes the code that is supposed to transfer money from one bank
account to another crashes half way through, and one account ends up not being
credited. The bank is losing money, and it's your ass on the line.

After some inspired grepping, you track down the offending function:

```cpp
void transfer(int amount, int src, int dst) {
    getAccount(dst).addFunds(amount);
    getAccount(src).addFunds(-amount);
}
```

The code itself was written years ago, and nobody has really looked at it since.
Since you're on a deadline (and a maintenance programmer at a bank), you don't
have the time or patience to familiarize yourself with every last detail. You
decide to just throw everything into a transaction and be done with it.

Unfortunately, your code-base is in C++[^1], which means you don't *have* any
transaction primitives. You slap together some [RAII][raii] voodoo that will
reset a variable back to its old value unless the `commit` method is called on
it before the end of scope. It's a good enough solution, and you're happy with
it.

[^1]: Here is where the allegory breaks down because if you're working at a bank
you'd be writing in COBOL, not C++, but just go with me on this one, OK?

[raii]: https://en.wikipedia.org/wiki/Resource_Acquisition_Is_Initialization

And then you go to actually use your new voodoo scope guard, and realize that
it's going to take a lot of refactoring to get it to do what you want. You need
to add two lines for every variable that could change. It's going to be a
maintenance nightmare, but hey, that's what the other guys are for.

Your code ends up looking like this:

```cpp
void transfer(int amount, int src, int dst) {
    Account &debit = getAccount(src);
    Account &credit = getAccount(dst);

    {
        Transaction _debit(debit, &debit);
        Transaction _credit(credit, &credit);

        credit.addFunds(amount);
        debit.addFunds(-amount);

        _debit.commit();
        _credit.commit();
    }
}
```

The two lines of actual code have ballooned into eight, and six of them do
nothing but book-keeping for the logic you actually want. That's a lot of
boilerplate that had to be written, and it's going to be hard to maintain if
anyone ever wants to expand the function.

Despite being a dull corporate drone, you can't help but wonder, since the
compiler is keeping track of which variables are changing anyway, why it can't
also automatically generate these scope guards for you?

***


Are you noticing a trend yet? There's a common theme to these examples: you find
yourself writing lots of boilerplate that is mindless and seems like the
compiler should be able to do for you. In every case it's a solved problem --
there's some particular functionality you're trying to plug in that *doesn't
really depend on the existing code* (accessing the environment, doing error
handling, performing transactions).

Like, in principle you could write code that would make these changes for you,
but where would you put it? The language doesn't support it, and everyone is
going to hate you if you go mucking with the build system trying to inject it
yourself. For all intents and purposes, you seem to be SOL.

And so you find yourself in a pickle. Here you are, a programmer -- someone who
gets *paid* to automate tedious things -- and you can't figure out a means of
automating the most tedious part of your day-to-day programming. There is
something *very* wrong here.



## II

It's probably not going to surprise you when I say that there is an abstraction
that fixes all of these issues for us. Sadly, it's widely misunderstood and
mostly feared by any who are (un)lucky enough to hear its name spoken aloud.

If you've [been paying attention][types], you might have noticed I've been
talking about Haskell lately, and you've probably guessed what abstraction I'm
alluding to.

[types]: /blog/love-types

That's right.

**Monads**.

No! *Stop!* Do *not* close the tab. You know the immense frustration that you
have with non-technical people when they see a math problem and give up
immediately without thinking about it for even two seconds? Those are the same
people who close browser tabs when they see the word "monad". Don't be one of
those people. You're better than that.

Monads are poorly understood somewhat because they're weird and abstract, but
mostly because everyone who knows about this stuff is notoriously bad at
pedagogy. They say things like "[a monad is just a monoid in the category of
endofunctors][fuckyou]". Thanks for that, Captain Helpful!

[fuckyou]: http://stackoverflow.com/questions/3870088/a-monad-is-just-a-monoid-in-the-category-of-endofunctors-whats-the-problem

Monads have been described as many things, notably burritos, boxes that you can
put something into, and descriptions of computation. But that's all bullshit.
What a monad *actually is* is something we'll get to in a little bit, but here's
what a monad does for you, *insofar as you care right now*:

**Monads are reusable, modular pieces which provide invisible plumbing for
you.** After a monad has been written once, it can be used as library-code to
provide drop-in support for idioms.

Need error handling? There's a monad for that. Non-determinism?  There's a monad
for that too! Don't want to write your own undo/redo system? You guessed it --
there's a monad for that.

[I could keep going][list] for a while, but I'm sure you get the picture.

[list]: https://wiki.haskell.org/Monad#Interesting_monads



## III

Let's go through an example, shall we? The `Maybe` monad has traditionally been
the "hello world" of monads, so we'll start there, because who am I to break
tradition? The `Maybe` monad provides drop-in support for `null` checks and
propagation (ie. error handling). Consider the following Haskell function, which
performs division:

```haskell
divide :: Int -> Int -> Int
divide x y = x `div` y
```

In the unfortunate case of $y = 0$, this seemingly innocuous function will crash
your Haskell program with a **Exception: divide by zero**. That's to be
expected, but it would be nice if the whole thing wouldn't explode. Let's change
our function to be a little safer:

```haskell
safeDivide :: Int -> Int -> Maybe Int
safeDivide _ 0 = Nothing
safeDivide x y = Just (x `div` y)
```

*Aside:* You'll notice we have two definitions for `safeDivide`, here. The first
one is specialized (think template specialization in C++) for the case of $y = 0$,
and the second is the general case. In Haskell, this is known as *pattern
matching*.

Anyway, the most salient change here is the new return type: `Maybe Int`. Though
it's not technically true, we can think of this type as meaning "we have a
computation of type `Int` that we want to use in the `Maybe` monad". In
general, we will use `(Monad m) => m a` to describe a computation of an `a` with
associated monadic functionality `m`.

And so if the return type of `safeDivide` is `Maybe Int`, it logically follows
that `Maybe Int` must be a type, which implies it has values. But what are these
values? They can't be integers (1, 5, -64), since those are of type `Int`, and
remember, Haskell is *very picky* about its types.

Instead, values of `Maybe Int` are either something (`Just 1`, `Just 5`, `Just
-64`), or `Nothing`. You can think of `Nothing` as being essentially a `null`,
except that it is not a [bottom value][bottom] (it *only* exists in the context
of `Maybe a`; it can't be assigned to arbitrary reference-types).

[bottom]: https://en.wikipedia.org/wiki/Bottom_type

Our `safeDivide` function can now be understood thusly: if $y = 0$, the result
of our division is `Nothing` (a failed computation), otherwise the result is
`Just z`, where $z = x \div y$. Remember, the `Just` bit is there to specify we
have a value of type `Maybe Int` (which can be `Nothing`), and not an `Int`
(which can't).

Another way to think of this is that we've transformed `divide` which isn't a
total function (it's undefined for $y=0$), into a total function (defined
everywhere).

At first it doesn't seem like we've really gained much, besides annotating that
our `safeDivide` function can fail. But let's see what happens when we use our
new function:

```haskell
divPlusFive :: Int -> Int -> Maybe Int
divPlusFive x y = do divided <- safeDivide x y
                     return (divided + 5)
```

If you squint and look at `<-` as an `=`, this looks a lot like imperative code.
We first compute the result of `safeDivide x y`, and then "return"[^4] that plus
five.  There is seemingly nothing of interest here, until you look at the type
of `divePlusFive`: it *also* returns a `Maybe Int`, but we didn't have to write
any code to explicitly make that happen -- it looks like we're just dealing with
`Int`s, since we can explicitly add an `Int` to it! But indeed, the result of
`divPlusFive 5 0` is actually `Nothing`. What gives?

[^4]: We will talk more about these scare quotes in the section V.

Here's the idea: when you're working inside a `(Monad m) => m a`, the code *you*
write deals only with the `a` bit, and Haskell silently transforms it into a
monadic context (read: provides plumbing) for you. In the case of `Maybe a`,
Haskell generates a dependency graph for every expression you write. If the
result of any subexpression is `Nothing`, that will propagate downstream
throughout the graph (and can explicitly be handled, if you want to provide
sensible defaults, or something).

`divePlusFive 5 0` first computes `safeDivide 5 0`, which is `Nothing`, and
since `divided + 5` depends on this, it too becomes `Nothing`. What we've done
here is captured the semantics of

```javascript
var divided = safeDivide(x, y);
if (divided == null) return null;
return divided + 5;
```

except that we don't need to explicitly write that `null` check anywhere. The
`Maybe` monad handles all of that plumbing for us (including upwards in the
call-stack, if that too is in the `Maybe` monad)!

And just like that, we never need to write another `null` check ever again.



## IV

The obvious question to be asked here is "how the hell did it do that?", and
that's a fantastic question. I'm glad you asked. The secret is in that little
`do` keyword, which looks like it drops you into imperative mode.

But it doesn't.

The `do` block in Haskell is actually just syntactic sugar for an environment
which transforms your implicit semicolons into a user-defined operator called
`>>=` (pronounced "bind"). This transformation turns

```haskell
divPlusFive x y = do divided <- safeDivide x y
                     return (divided + 5)
```

into

```haskell
divPlusFive x y = (safeDivide x y) >>= (\divided -> return (divided + 5))
```

where `\x -> y` is an anonymous function taking `x` and returning `y`. The
magic, it would seem, is all in this `>>=` operator, but what *is* it? As usual,
we will begin with looking at its type (specialized on the `Maybe` monad), and
seeing what we can deduce from it.

```haskell
(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
```

So, `>>=` takes two parameters, a `Maybe a` (type `a` wrapped in the `Maybe`
monad), and a function `a -> Maybe b`. From [last time][types], we know that
since there are no constraints on `a`, we can't construct one out of thin air,
so `>>=` must be somehow feeding the `a` from `Maybe a` into this function.

In effect, this is why we were able to pretend we were computing an `Int` in our
function that was supposed to return a `Maybe Int`. Here, `>>=` has been
silently composing together our functions which might individually fail
(`safeDivide`), into a single function (`divPlusFive`) that might fail.

Perhaps you are beginning to see why monads are an abstraction capable of
solving all of our original problems: they are silently adding the notion of a
particular context to computations that didn't originally care.

Let's look at the implementation for `>>=`, which turns out to be surprisingly
simple for `Maybe`:

```haskell
(>>=) :: Maybe a -> (a -> Maybe b) -> Maybe b
(>>=) Nothing  _ = Nothing
(>>=) (Just x) f = f x
```

Again, this is function is pattern-matched, first for the case of trying to bind
`Nothing` with any function (it doesn't matter what the function is; our
computation has already failed). The other option for a `Maybe a` is to be
`Just x`, the result of which is applying `x` to the function `f` .

Because Haskell has lazy evaluation, this operator definition is semantically
equivalent to the short-circuiting `&&` operator in C++: as soon as you get a
`Nothing`, it will stop processing and give you back a `Nothing`. Cool!

To reiterate: after a monad has been written once (essentially, given a suitable
implementation of `>>=`), it becomes library-code. If you annotate your return
type as `(Monad m) => m a`, anything inside of a `do` block will be transformed
to use the monad you asked for. **Haskell essentially begins injecting
user-defined code for you after each semicolon.**



## V

OK, this is all really cool stuff. But what *is a monad, actually*?

Well, just like a right-angled triangle is any object $(a, b, c)$ that satisfies
the constraint $a^2 + b^2 = c^2$, a monad is any object $(m, \text{return},
\gg\!\!=)$ subject to [some constraints][laws] (essentially some rules about
what cancels out) that ensure it behaves sensibly in monadic contexts.

`m` is the monadic type itself, with `return` being a primitive to "get into"[^2]
the monad[^3]. Together, these things formally define a monad.

[laws]: https://wiki.haskell.org/Monad_laws

[^2]: There is conspicuously no way of "getting out" of a monad; many monads
*do* provide this functionality, but it is not part of the definition of a
monad, since it doesn't always make sense. For example, if you could get "out"
of a transaction, it no longer provides a transaction, now does it?

[^3]: Amusingly, comonads (the "opposite" of a monad) provides no way of getting
*into* the comonad; *you can only get out*.

It's important to note that *anything* which has this signature $(m,
\text{return}, \gg\!\!=)$ that follows [the laws][laws] is a monad, regardless of
whether it appeals to our (naive) intuitions about "programmable semicolons". In
fact, in a few posts we will discuss the "free monad" which is a monad that does
absolutely nothing of the sort.

However, as a first look at monads, our thusly developed intuition will be good
enough for the time being: monads provide invisible plumbing in a modular and
reusable fashion.

But getting back to the definition, what is this `return`, thing? We haven't
talked about that yet. As usual, we'll look at its type to see what we can suss
out.

```haskell
return :: (Monad m) => a -> m a
```

Well, that's actually really easy; it just takes an `a` and puts it into a
monad. For `Maybe`, this is defined as:

```haskell
return :: a -> Maybe a
return x = Just x
```

Pretty basic, huh? All this does is, given an `a`, transforms it into a `Maybe
a` by saying it's not `Nothing`, but is in fact `Just` the value that it is.

Earlier, when squinting at `divPlusFive` as imperative code, I put "return" in
scare quotes. You can see why, now -- it's not doing at all what we thought it
was! To refresh your memory, here's the function again:

```haskell
divPlusFive :: Int -> Int -> Maybe Int
divPlusFive x y = do divided <- safeDivide x y
                     return (divided + 5)
```

Here, `return` isn't the thing you're used to in imperative code; it's actually
just this function that's part of the monad. Let's go through why it's
necessary really quickly.

Notice that `divided + 5` *must* be of type `Int`, since addition is over two
parameters of the same type, and 5 is most definitely an `Int`. But
`divPlusFive` is supposed to result in a value of type `Maybe Int`! In order to
clear up this discrepancy, we just `return` it, the types work out, and Haskell
doesn't yell at us. Awesome!

We should probably go through a few more examples of monads and their
implementations in order to get a solid conceptual grasp of what's going on, but
this post is already long enough. We'll save a few for next time to ensure we
don't get burned out.

That being said, hopefully this post has served as motivation for "why we want
monads" and given *some* idea of what the hell they are: modular, reusable
abstractions which provide plumbing. They work by silently transforming your
computation of `a` into a computation of `(Monad m) => m a`, stitching together
individual subexpressions with a user-defined operator `>>=`. In the case of
`Maybe`, this operator computes as usual until it gets a `Nothing`, and then
just fast-forwards that to the final result.

Despite their bad reputation, monads really aren't all that scary! Now aren't
you glad you didn't close the tab?


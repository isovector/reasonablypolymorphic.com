---
layout: post
title: "Towards Tactic Metaprogramming in Haskell"
date: 2020-10-12 00:40
comments: true
tags: haskell, hls, tactics
---

<center><img src="/images/fmaptree.gif"></center>

Isn't it weird that we treat source code as text? That is, we have this
extremely well-structured and strongly-typed object --- the abstract syntax tree
--- that exists conceptually in our minds, and in actuality inside of our
compiler, but for some reason we pretend it's just a pile of bytes and edit it
byte-by-byte rather than semantically?

When you stop and think about it, that's like the stupidest idea ever. We as the
authors don't think of our code as bytes, nor does our interpreter or compiler.
But instead we take the semantic understanding inside of our heads, serialize it
into bytes, and then get the compiler to parse and rediscover the ideas inside
our head. What a waste of effort.

Instead, you can use the incredible [TOTBWF](https://totbwf.github.io/) and my
new Tactics Plugin for the [Haskell Language
Server](https://github.com/haskell/haskell-language-server), which will
automatically and intelligently fill holes in your Haskell programs.

This blog post describes what a tactics engine is and why you want one, and is a
good introduction to how in the hell we can automatically write your code for
you.


## Tactics

Imagine you're pair programming with a junior engineer. In the navigator seat,
you'll be guiding your partner through the implementation, guiding them through
the high-level strokes and letting them actually do the coding part. In order to
implement `foldr :: (a -> b -> b) -> b -> [a] -> b`, for example, the guidance
you give your partner might be:

1. Bind the function arguments
2. Case split on the `[a]` parameter
3. If it's `[]`, do the obvious thing
4. Otherwise call your function and recurse.

These instructions aren't a real program by any means, but you might call them a
"program sketch." The hard part of programming (thinking about what to do) is
captured here, but *actually doing it* is left as an exercise to the reader.

A tactics engine transforms a program sketch like the above into an actual
program. Tactics free us from the tyranny of text editing and pedantic details,
allowing us to work at a higher semantic level of programming.

Tactics correspond to semantic operations over our program. Much like how the
primitive commands in text editors (delete to end of line, insert parentheses,
etc) can be composed to refine the textual representation of one program into
the textual representation of another, we can compose small tactics in order to
build larger ideas.

As an example, consider how we can fill in the following hole:

```haskell
data Id a = Id a

instance Functor Id where
  fmap :: (a -> b) -> Id a -> Id b
  fmap = _
```

Rather than writing this function all at once, we can instead build it, one idea
at a time. The first step is obviously to bind function arguments (the `intros`
tactic), which results in the refined expression:

```haskell
fmap :: (a -> b) -> Id a -> Id b
fmap = \fab ida -> _
```

We're left with a new hole, but this one is "smaller" than the old one; we've
refined the previous hole, filling in some of its structure. As a result, the
type of our new hole is `Id b`, and we now have both `fab :: a -> b` and `ida ::
Id a` in scope. We can simplify the hole further by now pattern matching on
`ida` (the `destruct ida` tactic):

```haskell
fmap :: (a -> b) -> Id a -> Id b
fmap = \fab ida -> case ida of
  Id a -> _
```

The resulting hole still has type `Id b`, but we've now introduced `a :: a` in
scope. Our next step is to build an `Id` value, which we can do by producing its
data constructor (the `split` tactic):

```haskell
fmap :: (a -> b) -> Id a -> Id b
fmap = \fab ida -> case ida of
  Id a -> Id _
```

Again we've shrunk the problem --- now our hole has type `b`. At this point we
can call the `fab` function to produce a `b` (via the `apply fab` tactic):

```haskell
fmap :: (a -> b) -> Id a -> Id b
fmap = \fab ida -> case ida of
  Id a -> Id (fab _)
```

All that's left is a hole with type `a`. Fortunately, we have `a :: a`  in
scope, so we can just plop that in to the hole via the `assumption` tactic:

```haskell
fmap :: (a -> b) -> Id a -> Id b
fmap = \fab ida -> case ida of
  Id a -> Id (fab a)
```

And just like that, we've produced an implementation of our desired function! By
thinking in terms of the semantic operations we'd like to perform at each hole
(instead of how to manipulate the bytes of text), we've changed the level of
abstraction at which we think about editing. The implications of this might not
be immediately obvious, so let's explore them together.

Let's list the tactic steps we took to derive `fmap`:

```haskell
intros
destruct ida
split
apply fab
assumption
```

Up to alpha renaming, this composition of tactics is sufficient to derive `fmap`
for any sum or product type that doesn't do anything "exciting" with its type
variable. By running the same steps, we can implement `fmap` for any of the
following types:

```haskell
(a, b)
Either a b
Maybe a
Const a b
```

Let's convince ourselves of this by quickly running through the derivation for
`Maybe a`. We start again with `fmap` and its type:

```haskell
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap = _
```

After running `intros`:

```haskell
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap = \fab ma -> _
```

and then `destruct ma`

```haskell
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap = \fab ma -> case ma of
  Nothing -> _
  Just a  -> _
```

Applying `split` here is a little tricky; technically it will force us to try
both `Nothing` and `Just _` at each hole in a weird sort of quantum
superposition. Let's ignore this detail for right now, and come back to it
immediately after finishing the derivation. Assuming we pick the right data
cons, after `split` our program looks like this:

```haskell
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap = \fab ma -> case ma of
  Nothing -> Nothing
  Just a  -> Just _
```

Now we run `apply fab`. Because `Nothing` doesn't take any arguments, it didn't
produce any holes, so we need look only at the `Just` case:

```haskell
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap = \fab ma -> case ma of
  Nothing -> Nothing
  Just a  -> Just (fab _)
```

and finally we run `assumption` to fill in the hole:

```haskell
fmap :: (a -> b) -> Maybe a -> Maybe b
fmap = \fab ma -> case ma of
  Nothing -> Nothing
  Just a  -> Just (fab a)
```

Look at that! Even though it would require significantly different editing
commands to write the syntax of these two functor instances, they are both
descried by the same composition of tactics. This is what I mean by "semantic
editing," we're moving the algorithm for producing functor instances out of our
heads and reifying it into something the computer understands. In essence, by
writing `fmap` once, we can teach the computer how to write it for us in the
future.

I mentioned earlier that `split` gives us some issues here. Reading closely,
you'll notice that there is nothing in our tactics that say we need to `split`
the same data constructor that we just `destruct`ed. In actuality there are four
different, valid programs that can be produced by the above set of tactics:

```haskell
fmap = \fab ma -> case ma of
  Nothing -> Nothing
  Just a  -> Nothing

fmap = \fab ma -> case ma of
  Nothing -> Nothing
  Just a  -> Just (fab a)

fmap = \fab ma -> case ma of
  Nothing -> Just _
  Just a  -> Nothing

fmap = \fab ma -> case ma of
  Nothing -> Just _
  Just a  -> Just (fab a)
```

Choosing the "best" implementation of these possibilities is largely a matter of
heuristics, which I plan to describe in a later post. For now, let's just assume
our tactics engine is smart enough to come up with the one you had in mind.

Of course, the real issue here is that nothing forces our `destruct` and `split`
tactics to use the same data constructor. We can eliminate this ambiguity by
noticing that in `fmap`, we're not actually trying to destruct and then split,
but instead we're trying to implement a homomorphism (a structure-preserving
function.) In order to preserve structure, we'd better map a data constructor to
itself. So instead, let's use the `homo` tactic instead of `destruct` and
`split`. Our new tactics metaprogram for writing functor instances is thus:

```haskell
intros
homo ida
apply fab
assumption
```

This new version now can no longer generate any of the pathological `fmap`
implementations for `Maybe`, as they are not structure preserving. We're left
only with the good implementation. Let's do one more derivation, this time for
`Either c a`. After `intros` and `homo eca`, we're left with:

```haskell
fmap :: (a -> b) -> Either c a -> Either c b
fmap = \fab ma -> case eca of
  Left  c -> Left _
  Right a -> Right _
```

For the first time, we're now left with *two* holes. The default behavior is for
a tactic to apply to all holes (although there are combinators for "zipping"
holes), meaning that the `apply fab` tactic will be run on both holes. For the
`Left` case, our hole has type `c`, but `fab _` has type `b`, so this tactic
*fails to apply here.* Tactic failure is per-hole, so we can still apply it to
the other hole, resulting in:

```haskell
fmap :: (a -> b) -> Either c a -> Either c b
fmap = \fab ma -> case eca of
  Left  c -> Left _
  Right a -> Right (fab _)
```

And finally, `assumption` fills the hole with whatever would typecheck. In the
first hole that's `c`, and in the second it's `a` as before.

```haskell
fmap :: (a -> b) -> Either c a -> Either c b
fmap = \fab ma -> case eca of
  Left  c -> Left c
  Right a -> Right (fab a)
```

Amazing! Three different functor implementations, with different numbers of data
constructors, type variables, and cardinalities. By programming at the level of
tactics rather than bytes, we can ignore the superficial differences between
these implementations, focusing instead on the fact that they're all derived the
same way.

Hopefully this post has given you some insight into what tactics are and why
they're valuable. In the next post we'll look at how this stuff is implemented
behind the scenes, and the difficulties we've had integrating it into the
language server. Stay tuned!


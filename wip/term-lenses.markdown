---
layout: post
title: A New Perspective on Lenses
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

I've always considered lenses to be a bit uncomfortable. While they're
occasionally useful for doing deeply nested record updates, they often seem to
be more trouble than they're worth. There's a temptation in the novice
programmer, to `^..` and `folded` their way to a solution that is much more
naturally written merely as `toList`. And don't get me started about the
stateful operators like `<<+=` and their friends. Many programs which can be
more naturally written functionally accidentally end up being imperative due to
somebody finding a weird lens combinator and trying to use it in anger. Much
like a serious drug collection, the tendency is to push it as far as you can.

Thus, my response has usually been one of pushback and moderation. I don't
avoid lenses at all costs, but I do try to limit myself to the prime types
(`Lens'`, `Prism'`, `Iso'`), and to the boring combinators (`view`, `set`,
`modify`). I feel like these give me most of the benefits of lenses, without
sending me tumbling down the rabbit hole.

All of this is to say that my grokkage of lenses has always been one of
*generalized injections and projections*, for a rather shallow definition of
"generalized". That is, I've grown accustomed to thinking about *lenses* as
getter/setter pairs for data structures---eg, I've got a big product type and
I want to pull a smaller piece out of it, or modify a smaller piece in a larger
structure. I think about prisms as the dual structure over
coproducts---"generalized" injecting and pattern matching.

And this is all true; but I've been missing the forest for the trees on this
one. That's not to say that I want to write *lensier* code, but that I should
be taking the "generalized" part much more seriously.

The big theme of my intellectual development over the last few years has been
thinking about abstractions as *shared vocabularies.* Monoids are not
*inherently* interesting; they're interesting because of how they let you
quotient seemingly-unrelated problems by their monoidal structure. Applicatives
are cool *because* once you've grokked them, you begin to see them everywhere.
Anywhere you've got conceptually-parallel, data-independent computations,
you've got an applicative lurking somewhere under the surface (even if it
happens to be merely the `Identity` applicative.)

I've had a similar insight about lenses, and that's what I wanted to write
about today.


## The Context

At work, I've been thinking a lot about compilers and memory layout lately.
I won't get into the specifics of why, but we can come up with an inspired
example. Imagine we'd like to use Haskell to write a little eDSL that we will
use to generate x86 machine code.

The trick of course, is that we're writing Haskell in order to *not* write
machine code. So the goal is to design high-level combinators in Haskell that
express our intent, while simultaneously generating machine code that
faithfully implements the intention.

One particularly desirable feature about eDSLs is that they allow us to reuse
Haskell's type system. Thus, imagine we have some type:

```haskell
type Code :: Type -> Type
data Code a = Code
  { getMachineCode :: [X86OpCode]
  }
```

Notice that the `a` parameter here is entirely phantom; it serves only to
annotate the type of the value produced by executing `getMachineCode`. For
today's purpose, we'll ignore all the details about calling conventions and
register layout and what not; let's just assume a `Code a` corresponds to
a computation that leaves a value (or pointer) to something of type `a` in
a well-known place, whether that be the top of the stack, or `eax` or
something. It doesn't matter!

Since the type parameter to `Code` is phantom, we need to think about what
[role](https://reasonablypolymorphic.com/blog/roles/index.html) it should have.
Keeping it at `phantom` would be disastrous, since this type isn't used by
*Haskell*, but it is certainly used to ensure our program is correct.
Similarly, `representational` seems wrong, since `coerce` is meaningful only
when thinking about Haskell; which this thing decidedly is not. Thus, our only
other option is:

```haskell
type role Code nominal
```

Frustratingly, due to very similar reasoning, `Code` cannot be a functor,
because there's no way[^concat] to lift an arbitrary Haskell function `a -> b`
into a corresponding function `Code a -> Code b`. If there were, we'd be in the
clear! But alas, we are not.

[^concat]: Short of [compiling to categories](http://conal.net/papers/compiling-to-categories/compiling-to-categories.pdf) via something like [categorifier](https://github.com/con-kitty/categorifier).


## The Problem

All of the above is to say that we are reusing Haskell's *type system*, but not
its *values*. An expression of type `Code Bool` has *absolutely no relation* to
the values `True` or `False`---except that we could write, by hand, a function
`litBool :: Bool -> Code Bool` which happened to do the right thing.

It is tempting, however, to make new Haskell types in order to help constrain
the assembly code we end up writing. For example, maybe we want to write
a DSP for efficiently decoding audio. We can use Haskell's types to organize
our thoughts and prevent ourselves from making any stupid mistakes:

```haskell
data Decoder = Decoder
  { format :: Format
  , seekPos :: Int
  , state :: ParserState
  }

data Chunk = ...

createDecoder :: Code MediaHandle -> Code Decoder
decodeChunk :: Code Decoder -> (Code Decoder, Code Chunk)
```

We now have a nice interface in our eDSL to guide end-users along the blessed
path of signal decoding. We have documented what we are trying to do, and how
it can be used once it's implemented. But due to our phantom, yet `nominal`,
parameter to `Code`, this is all just make believe. There is absolutely no
correlation between what we've written down and how we can use it. The problem
arises when we go to implement `decodeChunk`. We'll need to know what state
we're in, which means we'll need some function:

```haskell
decoderState :: Code Decoder -> Code ParserState
decoderState = ???
```

In a world where `Code` is a functor, this is implemented trivially as `fmap
state`. *But `Code` is not a functor!* Alas! Woe!






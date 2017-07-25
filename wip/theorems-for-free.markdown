---
layout: post
title: Theorems for Free
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

I've been reading through [Wadler's][wadler] classic paper [Theorem's for
Free][tff].

[wadler]: https://homepages.inf.ed.ac.uk/wadler/
[tff]: http://ecee.colorado.edu/ecen5533/fall11/reading/free.pdf

The thesis of the paper is that given a most-general[^mostgeneral] polymorphic
type signature, we can generate for free a theorem to which any inhabitant of
such a type must adhere.

[^mostgeneral]: TODO(sandy)

Translating into familiar Haskell notation, Wadler gives the following example:

```haskell
r :: [x] -> [x]
```

> From this, as we shall see, it is possible to conclude that `r` satisfies the
> following theorem: for all types `a` and `b` and every total function `f : a -> b`
> we have:
>
> ```haskell
> map f . r = r . map f
> ```

He explains:

> The intuitive explanation of this result is that `r` must work on lists of `x`
> for *any* type `x`. Since `r` is provided with no operations on values of type
> `x`, all it can do is rearrange such lists, independent of the values
> contained in them. Thus applying a to each element of a list and then
> rearranging yields the same result as rearranging and then applying `f` to
> each element.

This passage is somewhat misleading: `r` above is not restricted only to
rearrangements, it can also structurally manipulate the list; for example, it
can duplicate the first element and drop the middle three if it so pleases.

Wadler continues, with what might be one of the greatest lines in an academic
paper:

> This theorem about functions of type `[x] -> [x]` is pleasant but not
> earth-shaking. What is more exciting is that a similar theorem can be derived
> for *every* type.

"Exciting" isn't exactly the word I'd use, but I'd certainly settle for "neat"!
What I do find exciting, however, is that Wadler makes the claim that these
theorems can be derived not only for Hindley-Milner type systems, but also for
System-F. Hindley-Milner is Haskell98's everyday type system; System-F is what
you get when you turn on `RankNTypes` too.

But enough foreplay. If you're anything like me, you're just *aching* to know
what the secret here is. And it's this: we can build a structurally inductive
function from types to set-theoretic mathematical relations. The elements of the
relations are theorems about inhabitants of the original type: our "theorems for
free".

Wadler gives this inductive function (which I am calling $\omega$, since it sort
of looks like a 'W') for concrete types, product types, lists, function types,
and for universal quantification. They are provided here, in what I consider to
be a more readable format than presented in the paper, with commentary:

$$
\newcommand{\myset}[2]{\left\{(#1) \mid #2\right\}}
\omega(\text{T}) = \myset{t, t}{t \in \text{T}}
$$

All inhabitants of a concrete type $\text{T}$ are related only to themselves.

$$
\omega(A \times B) = \myset{(a, b), (a', b')}{(a, a') \in \omega(A),\; (b, b')
\in \omega(B)}
$$

Inhabitants of a product type are related if each of their projections (`fst`,
`snd`) are related.

$$
\omega([A]) = \myset{[x_1,\ldots,x_n],[x_1',\ldots,x_n']}{(x_1, x_1') \in
\omega(A),\; \ldots,\; (x_n, x_n') \in \omega(A)}
$$

Two terms of type `[A]` are related if they have the same `length` and if their
corresponding elements are related[^errata].

[^errata]: The original paper writes $(x_1, x_1') \in A$ as $(x_1, x_1') \in a$,
which I believe is an erratum, since there is no $a$ in scope.

$$
\omega(A \to B) = \myset{f, f'}{(a, a') \in \omega(A),\; (f\;a, f'\;a') \in
\omega(B)}
$$

Two functions are related if they map related values in the domain to related
values in the codomain.

$$
\omega(\forall X \ldotp F(X)) = \myset{g, g'}{\forall A \ldotp
\left(g\big\rvert_{X = A}, g'\big\rvert_{X = A}\right)
\in \omega(F(A))}
$$

And finally, a universally qualified type depending on the type variable $X$ has
related terms if they are related under every possible substitution of $X$ with
another type.

The attentive reader might be rather perplexed right now; why are we given
induction rules for *list* and not *coproducts*? I don't have a good answer,
other than that this paper was originally written in 1989 and maybe they didn't
know about coproducts back then.

To make you feel better, we can derive the "obvious" rule for the relatedness of
coproducts ourselves:

$$
\omega(A|B) = \myset{\text{inl}\;a, \text{inl}\;a'}{(a, a') \in \omega(A)}
\cup \myset{\text{inr}\;b, \text{inr}\;b'}{(b, b') \in \omega(B)}
$$

Which is to say that two terms of a coproduct are related if they share the
constructor and their contents are related.

With $\omega$ under our belts, lets see what it can do for us. Wadler takes us
through the derivation of the paper's first presented theorem:

```haskell
r :: [x] -> [x]
```

Remember that there is an implicit `forall x.` hiding at the beginning of that
type signature. Running through the end of all hoops, we get the following
derivation:


------------------------------------------------------------------------------


attempt 2

If you're not super comfortable with what it means to be a relation (I wasn't
when I started writing this), it's a set of pairs of things which are related
somehow. For example, we can write less-than for the natural numbers as a
relation:

* $(0, 1) \in (<_\mathbb{N})$
* $(0, 2) \in (<_\mathbb{N})$
* $(1, 2) \in (<_\mathbb{N})$
* $(0, 3) \in (<_\mathbb{N})$
* $(1, 3) \in (<_\mathbb{N})$
* $(2, 3) \in (<_\mathbb{N})$
* $(0, 4) \in (<_\mathbb{N})$
* ... and so on

Here, $(<_\mathbb{N})$ is understood to be the name of the relation/set. We can
write it more formally in set-builder notation:

$$
\newcommand{\reln}[1]{\boldsymbol{\mathcal{#1}}}
\newcommand{\rel}[3]{\reln{#1} : #2\Leftrightarrow#3}
\myset{x, y}{x \in \mathbb{N},\;y \in \mathbb{N},\;x < y}
$$

which says that the pair $(x, y)$, plucking $x \in \mathbb{N}$ and $y \in
\mathbb{N}$ is in our set only when $x < y$.

It is interesting to note that a function $f : A \to B$ is a special case of a
relation. We will call such a function-viewed-as-a-relation $\reln{\hat{f}}$,
since we are computer scientists, and to us, functions are not sets. We can
define $\reln{\hat{f}}$ as:

$$
\reln{\hat{f}} = \myset{a, f\;a}{a \in A}
$$

As a notational convention, we will name particular relations with scripted
letters (eg. $\reln{A}$) and write out the sets they are a relation *between* as
$X \Leftrightarrow Y$. Therefore, $\rel{A}{X}{Y}$ is a relation named $\reln{A}$
which relates the sets $X$ and $Y$.

And so the trick is as follows; we can inductively transform type constructors
into relations. It is these relations which are the "theorems for free" we have
been hearing so much about. Wadler gives the following constructions:


### Concrete Types

A concrete type $T$ (for example, `Bool` or `Char`) has only the following
relation:

$$
\rel{T}{T}{T} = \myset{x, x}{x \in T}
$$

This is an "identity relation", and it states that values of concrete types are
related only to themselves. Unsurprisingly, this relation can be expressed in
Haskell as the (monomorphized) `id :: T -> T` function.

All this is to say that we can't get any "interesting" theorems for free if we
only have monomorphic types to deal with.


### Product Types

Given a two relationships $\rel{A}{A}{A'}$ and $\rel{B}{B}{B'}$, we can form a
product relation $\rel{A\times B}{(A\times B)}{(A' \times B')}$ by the
construction:

$$
\myset{(a, b), (a', b')}{(a, a') \in \reln{A},\;(b, b') \in \reln{B}}
$$

Wadler explains:

> That is, pairs are related if their corresponding components are related.

Recall that functions are themselves relations, and in that case that $\reln{A}$
and $\reln{B}$ are both functions, the above construction simplifies to:

$$
\reln{\widehat{f \times g}} = \myset{(a, b), (f\;a,g\;b)}{a \in A,\; b \in B}
$$

or, alternatively, could be written in Haskell as:

```haskell
prodRel :: (a -> a') (b -> b') -> (a, b) -> (a', b')
prodRel f g (a, b) = (f a, g b)
```

If you're familiar with the `bimap` function provided by the `Bifunctor` class,
`prodRel` is a special case of that.

This technique of specializing a relation $\reln{A}$ to a function
$\reln{\hat{f}}$ turns out to be a very useful trick for actually getting
results out of the technique. I'm trying to emphasize this point since I missed
it my first few times through the paper, and was subsequently rather stumped.


### List Types

If we have a relation $\reln{A}$, we can construct a relation
$\rel{[A]}{[A]}{[A]}$:

$$
\myset{[x_1,\;\ldots,\;x_n], [x_1',\;\ldots,\;x_n']}{(x_1, x_1') \in
\reln{A},\;\ldots,\;(x_n, x_n') \in \reln{A}}
$$

Which Wadler describes as

> That is, lists are related if they have the same length and corresponding
> elements are related. In the special case where $\reln{A}$ is a function,
> $\reln{[A]}$ is the familiar `map :: (a -> b) -> [a] -> [b]` function.


### Function Types

We can construct the function relation $\rel{A\to B}{(A\to B)}{(A'\to B')}$, by
taking relations $\rel{A}{A}{A'}$ and $\rel{B}{B}{B'}$ to:

$$
\myset{f, f'}{(a, a')\in\reln{A},\;(f\;a, f\;a')\in\reln{B}}
$$

This can be understood as related functions take a related values in the domain
to related values in the codomain.

Wadler is careful to point out that even if $\reln{\hat{g}}$ and
$\reln{\reln{h}}$ are functions, the resulting relation
$\reln{\hat{g}\to\hat{h}}$ is *not* a function, but instead a proof that $f'
\circ g = h \circ f$, given any pair $(f, f')\in\reln{\hat{g}\to\hat{h}}$.


### Universally Qualified Types

Finally, Wadler brings us to types of the form `forall x. f x`, where `f` is
some type alias of kind `* -> *`. For example, we might use the type alias `type
F z = [z] -> [z]` in order to denote the Haskell type `forall x. [x] -> [x]`.

Wadler:

> Let $\reln{F(X)}$ be a relation depending on $X$. Then $\reln{F}$ corresponds
> to a function from relations to relations, such that for every relation
> $\rel{A}{A}{A'}$ there is a corresponding relation $\rel{F(A)}{F(A)}{F(A')}$.

There is nothing interesting going on here except for the substitution of the
type $\reln{A}$ for the type variable $\reln{X}$.

This universally quantified relation $\rel{\forall X\ldotp
F(X)}{\forall X\ldotp F(X)}{\forall X'\ldotp F'(X')}$ can be constructedthusly:

$$
\myset{g, g'}{\forall \rel{A}{A}{A'}\ldotp \left(g_A, g'_{A'}\right)\in\reln{F(A)}}
$$

We can interpret this as two polymorphic expressions are related if they
preserve their relationship under being monomorphized to any possible type. This
property can be hard to see in Haskell, since it's a pretty hard thing to
violate there.


### Coproduct Types

As an attentive reader, you might be scratching your head right now. Why were we
given constructions on lists, but not on coproducts? The paper is mysteriously
quiet on this point; my best guess is that it was written in 1989 and perhaps
that was before coproducts were well understood.

Regardless, with the practice we've gained from going through the above
constructions, we should be able to build the coproduct relation ourselves.

Given two relations, $\rel{A}{A}{A'}$ and $\rel{B}{B}{B'}$, we can construct the
coproduct relation $\rel{(A|B)}{(A|B)}{(A'|B')}$ as follows:

$$
\myset{\text{inl}\;a, \text{inl}\;a'}{(a, a')\in\reln{A}}\cup
\myset{\text{inr}\;b, \text{inr}\;b'}{(b, b')\in\reln{B}}
$$

In the special case that $\reln{\hat{f}}$ and $\reln{\hat{g}}$ are functions,
the relation $\reln{(\hat{f}|\hat{g})}$ is a function:

```haskell
coprodRel :: (a -> a') -> (b -> b') -> Either a b -> Either a' b'
coprodRel f _ (Left a)  = Left  (f a)
coprodRel _ g (Right b) = Right (g b)
```

which again, if you're familiar with `Bifunctor`, is just `bimap` in disguise



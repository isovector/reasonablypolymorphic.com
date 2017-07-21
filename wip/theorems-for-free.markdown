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
\omega(A \to B) = \myset{f, f'}{(a, a') \in \omega{A},\; (f\;a, f'\;a') \in
\omega{B}}
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

$$
\begin{align*}
  & \omega(\forall X\ldotp [X] \to [X]) \\
=\; & \myset{g, g'}{\forall A \ldotp \left(g\big\rvert_{X = A}, g'\big\rvert_{X =
A}\right) \in \omega([A] \to [A])} \\
=\; & \myset{f, f'}{(a, a') \in \omega([A]),\; (f\;a, f'\;a') \in \omega([A])} \\
=\; & \myset{[x_1,\ldots,x_n],[x_1',\ldots,x_n']}{(x_1, x_1') \in \omega(A),\; \ldots,\; (x_n, x_n') \in \omega(A)}
\end{align*}
$$

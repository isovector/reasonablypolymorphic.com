---
layout: post
title: "Review: Theorems for Free"
date: 2017-07-29 13:15
comments: true
tags: papers, review, wadler, haskell, category theory
---

I've been reading through [Wadler's][wadler] classic paper "[Theorems for
Free][tff]".

[wadler]: https://homepages.inf.ed.ac.uk/wadler/
[tff]: http://ecee.colorado.edu/ecen5533/fall11/reading/free.pdf

The thesis of the paper is that given a most-general (taking as few constraints
on its values as possible) polymorphic type signature, we can generate for free
a theorem to which any inhabitant of such a type must adhere.

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
rearrangements, `r` can also structurally manipulate the list; for example, it
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

But enough dilly dally. If you're anything like me, you're just *aching* to know
what the secret here is. And it's this: we can build a structurally inductive
function from types to set-theoretic mathematical relations. The elements of the
relations are theorems about inhabitants of the original type: our "theorems for
free".


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
\newcommand{\myset}[2]{\left\{(#1) \mid #2\right\}}
\newcommand{\reln}[1]{\boldsymbol{\mathcal{#1}}}
\newcommand{\rel}[3]{\reln{#1} : #2\Leftrightarrow#3}
\myset{x, y}{x \in \mathbb{N},\;y \in \mathbb{N},\;x < y}
$$

which says that the pair $(x, y)$, plucking $x \in \mathbb{N}$ and $y \in
\mathbb{N}$ is in our set only when $x < y$.

It is interesting to note that a function $f : A \to B$ is a special case of a
relation. We will denote such a function-viewed-as-a-relation $\reln{\hat{f}}$,
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

Given two relationships $\rel{A}{A}{A'}$ and $\rel{B}{B}{B'}$, we can form a
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
\reln{\hat{f}\times\hat{g}} = \myset{(a, b), (f\;a,g\;b)}{a \in A,\; b \in B}
$$

or, alternatively, could be written in Haskell as:

```haskell
prodRel :: (a -> a') -> (b -> b') -> (a, b) -> (a', b')
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
\myset{f, f'}{(a, a')\in\reln{A},\;(f\;a, f'\;a')\in\reln{B}}
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
F(X)}{\forall X\ldotp F(X)}{\forall X'\ldotp F'(X')}$ can be constructed thusly:

$$
\myset{g, g'}{\forall \rel{A}{A}{A'}\ldotp \left(g_A, g'_{A'}\right)\in\reln{F(A)}}
$$

We can interpret this as two polymorphic expressions are related if they
preserve their relationship under being monomorphized to any possible type. This
property can be hard to see in Haskell, since the language makes it a difficult
thing to violate.


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

where $\text{inl}$ and $\text{inr}$ are more commonly known in Haskell under the
guises `Left` and `Right`.

In the special case that $\reln{\hat{f}}$ and $\reln{\hat{g}}$ are functions,
the relation $\reln{(\hat{f}|\hat{g})}$ is itself a function:

```haskell
coprodRel :: (a -> a') -> (b -> b') -> Either a b -> Either a' b'
coprodRel f _ (Left a)  = Left  (f a)
coprodRel _ g (Right b) = Right (g b)
```

which again, if you're familiar with `Bifunctor`, is just `bimap` in disguise



## Generating Free Theorems

With all of that foreplay out of the way, we're now ready to tackle the meat of
the paper. Wadler gives his contribution of the article:

> **Proposition.** (Parametricity.) If `t` is a ... term of type `T`, then $(t,
> t) \in \reln{T}$ where $\reln{T}$ is the relation corresponding to the type
> `T`.

That this is a proposition (ie. "assumed to be true") is troubling, given that
we just went through all of the work to construct these relations. But we will
persevere, and in fact, see later, why this must in fact be true.

We will repeat Wadler's derivation of the originally presented theorem here:

Given a function `r :: forall x. [x] -> [x]`, by parametricity we get $(r, r)
\in \reln{\forall X\ldotp [X]\to[X]}$.

We can expand out the definition of the universally quantified type relation:

$$
\begin{align*}
& \text{forall}\;\rel{A}{A}{A'}\ldotp \\
&\quad \left(r_A, r_{A'}\right)\in \reln{[A]\to[A]}
\end{align*}
$$

and again, we expand the definition of the function relation:

$$
\begin{align*}
& \text{forall}\;\rel{A}{A}{A'}\ldotp \\
&\quad \text{forall}\; (xs, xs') \in \reln{[A]} \\
&\quad\quad \left(r_A\;xs, r_{A'}\;xs'\right)\in \reln{[A]}
\end{align*}
$$

We can now specialize this with the trick above -- assume our relation is a
function. In particular, we will simplify our derivation by equating
$\rel{A}{A}{A'}=\reln{\hat{f}} : A\to A'$.

This substitution means that we now know $(x, f\;x)\in\reln{\hat{f}}$. We also
know the special case of the list relation means that the relation
$\reln{[\hat{f}]}$ contains only pairs of the form $(xs, \text{map}\;f\;xs)$.

We can use these facts to rewrite the above:

$$
\begin{align*}
& \text{forall}\;\reln{\hat{f}} : A\to A'\ldotp \\
&\quad \text{forall}\; xs \in [A] \\
&\quad\quad \text{let}\;xs' = \text{map}\;f\;xs \\
&\quad\quad \text{in}\;\text{map}\;f\;(r_A\;xs) = r_{A'}\;xs'
\end{align*}
$$

Notice here that we're pulling out terms `xs` from *type* (not relation) `[A]`.
Finally, we can complete the derivation by inlining our `let` binding:

$$
\begin{align*}
& \text{forall}\;\reln{\hat{f}} : A\to A'\ldotp \\
&\quad \text{forall}\; xs \in [A] \\
&\quad\quad \text{map}\;f\;(r_A\;xs) = r_{A'}\;(\text{map}\;f\;xs)
\end{align*}
$$

That's pretty cool, if you come to think about it. We came up with a theorem
about our function `r` knowing nothing more about it than its type. This implies
that *every* function of type `forall x. [x] -> [x]` will share this property,
and more generally, that all expressions with the same type will share the same
free theorem.

Wadler's next example is folds of type `forall x y. (x -> y -> y) -> y -> [x] ->
y`. However, if you can follow the above derivation, you'll be able to follow
his working of folds. I wanted to go out on my own and find a free theorem not
provided by the paper.

Although `id :: forall a. a -> a` seemed to be too trivial, I still wanted an
easy example, so I went for `const :: forall a b. a -> b -> a`. Before cranking
out the theorem, I wasn't sure what it would look like, so it seemed like a good
candidate. My derivation is as follows:

By parametricity, any function `c :: forall a b. a -> b -> a` gives us $(c, c)
\in \reln{\forall A\ldotp\forall B\ldotp A\to B\to A}$. We can apply universal
quantification twice, and get:

$$
\begin{align*}
& \text{forall}\;\rel{A}{A}{A'}\ldotp \\
&\quad \text{forall}\;\rel{B}{B}{B'}\ldotp \\
&\quad\quad \left(c_{AB},\;c_{A'B'}\right) \in \reln{A\to B\to A}
\end{align*}
$$

We apply the definition of the function relation, recalling that the arrow
associates to the right:


$$
\begin{align*}
& \text{forall}\;\rel{A}{A}{A'}\ldotp \\
&\quad \text{forall}\;\rel{B}{B}{B'}\ldotp \\
&\quad\quad \text{forall}\;(a, a') \in \reln{A} \\
&\quad\quad\quad \left(c_{AB}\;a,\;c_{A'B'}\;a'\right) \in \reln{B\to A}
\end{align*}
$$

We can now specialize $\rel{A}{A}{A'} = \reln{\hat{f}} : A\to A'$:

$$
\begin{align*}
& \text{forall}\;\reln{\hat{f}} : A\to A'\ldotp \\
&\quad \text{forall}\;\rel{B}{B}{B'}\ldotp \\
&\quad\quad \text{forall}\;a \in A \\
&\quad\quad\quad \left(c_{AB}\;a,\;c_{A'B'}\;(f\;a)\right) \in \reln{B\to \hat{f}}
\end{align*}
$$

and then specializing $\rel{B}{B}{B'} = \reln{\hat{g}} : B\to B'$:

$$
\begin{align*}
& \text{forall}\;\reln{\hat{f}} : A\to A'\ldotp \\
&\quad \text{forall}\;\reln{\hat{g}} : B\to B'\ldotp \\
&\quad\quad \text{forall}\;a \in A \\
&\quad\quad\quad \left(c_{AB}\;a,\;c_{A'B'}\;(f\;a)\right) \in \reln{\hat{g}\to\hat{f}}
\end{align*}
$$

Finally, recall that a function relation between two functions is not itself a
function, but instead an identity proof:

$$
\begin{align*}
& \text{forall}\;\reln{\hat{f}} : A\to A'\ldotp \\
&\quad \text{forall}\;\reln{\hat{g}} : B\to B'\ldotp \\
&\quad\quad \text{forall}\;a \in A \\
&\quad\quad\quad c_{A'B'}\;(f\;a) \circ g = f \circ (c_{AB}\;a)
\end{align*}
$$

This theorem can be read out in Haskell as the equality `const (f a) . g = f .
const a`, which is true! We can add back the points to it in order to see this
fact more clearly:

```haskell
const (f a) (g b) = f (const a b)
```

It's an exceptionally short proof to show the correctness of this, so we'll go
through the motions

```haskell
const (f a) (g b)  -- given
f a                -- definition of `const`

=

f (const a b)      -- given
f a                -- definition of `const`
```

Very snazzy! Maybe Wadler is onto something with all of this stuff. The
remainder of the paper is a tighter formalization of the preceding, as well as
an extension of it into System F. Finally it provides a proof that fixpoints
don't violate parametricity, which crucially gives us access to inductive types
and recursive functions.

At this point, however, we have enough of an understanding of the technique for
the purpose of this essay, and we'll accept the remainder of Wadler89 without
further ado.


## Commentary (on the computer science)

Neat! The fact that we can derive theorems for terms given *their most general
type* means that giving functions the "correct" type must be important. For
example, if we monomorphize a function of type `a -> b -> a` to `Bool -> String
-> Bool`, we can no longer reason about it; despite its implementation being
identical.

What's perhaps more interesting about this to me is what it implies about
*looking* for functions. I recall once asking some coworkers if they had an
implementation of `Int -> [a] -> [[a]]`, which they suggested could be
`replicate @[a]`. While it typechecks, it's obviously not the implementation I
wanted, since that is not the most general type of `replicate : Int -> a ->
[a]`.

I think this realization is the most important contribution of the paper for an
every-day Haskell programmer. Darn! We could have skipped all of the math!



## Commentary (on the mathematics)

Three observations of this paper stopped to give me pause.

The first curious feature is that all of Wadler's examples of generating
theorems for free involve specialization of the relation $\rel{A}{A}{A'} =
\reln{\hat{a}}:A\to A'$. Why is this? Is the relation machinery itself
overkill?

The second odd thing is that when the relations are specialized to functions in
the constructions of the product, coproduct, and list relations all just happen
to be instances of `Bifunctor` (just squint and pretend like lists have a
phantom type parameter to make this statement true). Suspicious, no?

The coup de grace is that when its arguments are specialized to functions, the
function relation $(f, f') \in \reln{\hat{g}\to\hat{h}}$ itself reduces to a
proof of $f' \circ g = h \circ f$. Call me crazy, but that looks like too big a
coincidence to be... well, a coincidence.

What do I mean? Good question. The definition of a natural transformation
$\mathcal{N} : F\to G$ between two functors (for convenience, let's say they're
both $\mathcal{Hask}\to\mathcal{Hask}$: the traditional functors we think about
in everyday Haskell), is:

$$
\begin{array}[t]{c @{} c @{} c}
\begin{xy}
\xymatrix {
A \ar[d]_f \\
B
}
\end{xy}
& {{\;}\\[2ex]\mapsto} &
\begin{xy}
\xymatrix {
FA\ar[d]_{Ff}\ar[r]^{\mathcal{N}_A} & GA\ar[d]^{Gf}\\
FB\ar[r]_{\mathcal{N}_B} & GB
}
\end{xy}
\end{array}
$$

We can understand such a thing in Haskell as looking at the arrows as functions,
and the objects (the things that the functions are *between*) as types.
Therefore, a natural transformation $\mathcal{N} : F\to G$ takes a function `f
:: A -> B` to the equation $\mathcal{N}_B \circ Ff = Gf \circ \mathcal{N}_A$.
Remind you of anything we've looked at recently?

A natural transformation is a mapping from one functor to another; which we can
express in Haskell as:

```haskell
type Nat f g = (Functor f, Functor g) => forall x. f x -> g x
```

Remember how our relation constructors when specialized to functions turned out
to be (bi)functors? As a matter of fact, we can view our relation for concrete
types as the `Identity` functor, and so the rabbit hole continues.

But why must we specialize our relations to functions in all of our free theorem
analysis? Well by specializing to functions, we ensure they're arrows in
$\mathcal{Hask}$. Given that our identity, product, coproduct, and list relation
constructions are functors from $\mathcal{Hask}\to\mathcal{Hask}$ (ie.
"endofunctors"), this means our analysis must stay in the realm of Haskell.
Which makes sense, since our original goal was to prove things about Haskell
types.

The pieces of the puzzle have mostly come together. We must specialize our
relations to arrows in order to force our other relations to form (endo)functors
in Haskell. Once we have endofunctors, we can use our function relation as a
natural transformation as the only way of introducing non-trivial equations into
our analysis (the so-called naturality condition). All that's left before we can
definitively claim that Wadler's free theorems are nothing more than basic
applications of category theory[^sandy] is a categorical notion of the
universally quantified relation.

[^sandy]: Which would make sense, because I have a conjecture: all laws in
Haskell are just the category laws disguised in different categories.

Let's look again at the definition of our universally quantified construction:

$$
\myset{g, g'}{\forall \rel{A}{A}{A'}\ldotp \left(g_A, g'_{A'}\right)\in\reln{F(A)}}
$$

Two universally quantified expressions are related if they maintain relatedness
under any substitution of their type variable. Honestly, I don't have a great
idea about where to go from here, but I've got three intuitions about how to
proceed. In order of obviousness:

* The $\forall$ here looks like a smoking gun compared to the expression of a
  natural transformation in Haskell. Maybe this construction is just an artifact
  of being expressed in set theory, and in fact is the other side of the coin as
  the function relation's natural transformation.
* Relatedly, would we get more insight if we looked at a universally quantified
  type in Haskell that *didn't* contain a function type?
* Do we get any hints if we specialize the $\reln{F(A)}$ relation to a function?

The first bullet isn't actionable, so we'll keep it in mind as we go through the
other points.

However, the second bullet is interesting. Interesting because if we look at any
universally qualified types that *don't* involve functions, we'll find that they
*aren't* interesting. For example:

```haskell
universalMaybe :: forall a. Maybe a
universalMaybe = Nothing  -- the only inhabitant of our type

universalList :: forall a. [a]
universalList = []        -- the only inhabitant of our type

universalEither :: forall a b. Either a b
universalEither = undefined  -- no inhabitants of this type!
```

The only inhabitants of these types are ones that don't contain any `a`s at all.
Given this realization, it seems safe to say that our first bullet point is
correct; that universal construction is the other side of the coin to the
natural transformation created by our function relation, manifest as an artifact
for reasons only the eldritch set-theoretical gods know.

---

Thanks to [J Haigh][j] for proofreading an early version of this post.

[j]: https://github.com/DebugSteven


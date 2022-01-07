---
layout: post
title: Review: Adders and Arrows
date: 2022-01-07 14:27
comments: true
tags: papers, review, elliott, category theory, agda, circuits
---

This year my goal is to go through one paper a week, and produce some resulting
artifact to help hammer in my understanding. Today's paper is [Conal
Elliott's][conal]'s [Adders and Arrows][paper].

[conal]: http://conal.net/
[paper]: http://conal.net/papers/drafts/adders-and-arrows.pdf

In my opinion, Adders and Arrows is an attempt to answer the questions "where do
digital circuits come from?" and "how can we be convinced our digital circuits
do what they claim?" by focusing on the concrete case of adders. What's quite
remarkable to me is that the paper takes 17 pages to build up to the
"known" ripple-carry adder, which is essentially day 1 of any digital circuitry
class. This feels a bit ridiculous at first blush, but immediately pays off for
itself by using the same machinery to derive a carry-forward adder.
Carry-forward adders come like a week later in circuitry class, and are
completely unrelated to ripple-carry adders, but Elliott derives them
essentially for free. He then gives a third variation on the theme, which is a
ripple-carry adder *in time,* rather than space, and again gets it in one page.

So that's the impressive stuff. What's also important is that the paper doesn't
require us to trust that the corresponding circuits do what they claim --- the
underlying machinery passes around a big chain of equivalence proofs, which
automatically get composed and witness that addition over the naturals is a
model for each circuit.

Something I really liked about this paper is that it's the first time I've ever
gotten a glimpse of why it might be valuable to understand category theory. It's
not just good for classifying things! Turns out you can do cool things with it
too. But nobody who teaches it ever says that.

The paper itself is only a draft, and it shows in several places. Notably, the
core abstraction (the arrow category) is missing, and the paper ends extremely
abruptly. After some spelunking, I managed to track down the implementation of
the arrow category, and was pleased to realize I'd already implemented it
independently.

We'll proceed section by section.


## Section 1: A model of addition

Section 1 gives us a model of the natural numbers via the Peano encoding, and
also defines addition. It drives home the point that this unary encoding is only
the model of our computation --- its specification --- and not the actual
implementation. This is a common theme in Elliott's work: "how do we even know
what question we're trying to answer?" We know by posing the dumbest possible
model of the problem, and then proving any actual solution to the problem is
equivalent. He stresses that the "dumbest possible" thing is an important
quality --- this is the only part of the problem we get no checks or balances
on, so our only hope is to make it so simple that we can't screw it up.

```agda
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat

_+_ : Nat -> Nat -> Nat
zero  + n = n
suc m + n = suc (m + n)
```

Because arbitrary categories don't support currying, we can uncurry addition,
which will come in handy later:

```agda
<+> : Nat2 -> Nat
<+> (x , y) = x + y
```


## Section 2: Bounded numbers

Section 2 is defines the `Fin`iteary numbers, which are natural numbers
guaranteed to be smaller than a given upper bound.

```agda
data Fin : N -> Set where
  zero : {n : N} -> Fin (suc n)
  suc  : {n : N} -> Fin n -> Fin (suc n)
```

Thus, `Fin 2` is the type of binary digits, and `Fin 10` is that of decimal
digits.

Elliott gives us an observation of `Fin` in terms of `Nat`:

```agda
toN : {n : Nat} -> Fin n -> Nat
toN zero    = zero
toN (suc f) = suc (toN f)
```

We'd like to find a model-preserving implementation of `+` over `Fin` (let's
call it `<+F>`.) But what does model-preserving meaning? As usual, the answer is
"homomorphism", and namely, that the following square must commute:

```agda
<+> . bimap toN toN = toN . <+F>
```

The paper says "solving this equation for `<+F>` yields the following recursive
definition." It's unclear if this answer was "solved for" in the sense of being
manipulated algebraically, or if it just happens to be a solution to the
problem. I hope it's the former, because I would love to see how to do that, but
I suspect it's the latter. Anyway, the definition of `_+F_` is given below, plus
the work I needed to do to get everything to typecheck.

```agda
n+suc : (n m : Nat) -> n + suc m == suc (n + m)
n+suc zero m = refl
n+suc (suc n) m rewrite n+suc n m = refl

weaken : ∀ {m} {n} (y : Fin n) -> Fin (m + n)
weaken {zero} y = y
weaken {suc m} zero = zero
weaken {suc m} {suc n} (suc y) rewrite n+suc m n = suc (weaken y)

infixl 5 _+F_
_+F_ : {m n : Nat} -> Fin (suc m) -> Fin n -> Fin (m + n)
_+F_ {m} zero y = weaken y
_+F_ {suc _} (suc x) y = suc (x +F y)
```

Something that ended up challenging me here was that Elliott uses extensional
equality of functions for his commutative diagrams, but my implementation of
arrow categories (coming up) requires a propositional equality. I got around the
problem by postulating extensionality (which I stole from McBride), and then by
defining a type-alias for extensional equality that plays well with
`extensionality`:


```agda
postulate
  extensionality : {S : Set}{T : S -> Set}
                   {f g : (x : S) -> T x} ->
                   ((x : S) -> f x == g x) ->
                   f == g

infix 1 _=o=_
_=o=_ : {A B : Set} -> (A -> B) -> (A -> B) -> Set
_=o=_ {A} f g = (x : A) -> f x == g x
```

and then we can give *most* (it's hard to prove things, OK?) of the proof for
the commutative diagram:

```agda
toN-weaken : {m n : Nat} -> (y : Fin n) -> toN (weaken {m} y) == toN y
toN-weaken {zero} y = refl
toN-weaken {suc m} zero = refl
toN-weaken {suc m} (suc y) = ?

toN-+F : ∀ {(m , n) : Nat2} -> toN {m + n} ∘ <+F> =o= <+> ∘ toN2 {suc m , n}
toN-+F {zero , n} (zero , y) = refl
toN-+F {suc m , n} (zero , y)
  rewrite toN-+F {m , n} (zero , y)
        | toN-weaken {suc m} y = refl
toN-+F {suc m , n} (suc x , y) rewrite toN-+F {m , n} (x , y) = refl
```


## Section 3: The arrow category

Section 3 presents the fact that we can bundle up the commutative diagram with
its proof into an object. Unfortunately, it only gives the *barest hint* about
how to actually go about doing that. I'm presenting here what I think it is, but
if something goes wrong in the rest of the paper, here's where the problem is.

The paper is keen to point out that we have five things we're bundling together:

1. A mapping from implementation input to specification input.
2. A mapping from implementation output to specification output.
3. An implementation.
4. A specification.
5. A proof that the square commutes.

Colloquially, I'd call the first two points our "observations" of the system.

The idea is, we'd like to bundle all of these things together, ideally in some
sort of composable packaging. Composable usually means categorical, so we should
look at our old friend `SET`, the category whose objects are types and arrows
are functions. By itself, `SET` doesn't give us any of the machinery we'd want
for thinking about commutative squares. So instead, we'll construct the arrow
category over `SET`. Let's call it `>-SET->`.

But what is the arrow category? The paper is quiet on this front, but my
understanding is that it transforms the *arrows* in `SET` into *objects* in
`>-SET->`. An arrow in `>-SET->` is thus a pair of arrows in `SET` which form a
commutative square. For example, consider the arrows in `SET`:

```
Fin n x Fin n        Nat x Nat
      |                  |
      | <+F>             | <+>
      v                  v
    Fin n               Nat
```

In `>-SET->`, these are just two objects, and a morphism between them is
something that makes the whole square commute. In `>-SET->`:

```
       bimap toNat toNat
<+F>  ------------------>  <+>
             toNat
```

and again in `SET`:

```
                bimap toNat toNat
Fin n x Fin n  ------------------> Nat x Nat
      |                                |
      | <+F>                           | <+>
      v               toNat            v
    Fin n      ------------------>    Nat
```

So we can consider the arrow category to be a "view" on its underlying category,
like how databases present views over their data. The arrow category lets us
talk about arrows directly, and *ensures* the commutativity of any constructions
we're able to form. As such, it's a natural fit for our purposes of
specification --- we are literally unable to construct any arrows in `>-SET->`
which violate our specification.


### Building Categories

How do we go about actually building an arrow category? First, some
preliminaries to build a category:

```agda
record Category : Set where
  infix 6 _~>_
  field
    Obj : Set
    _~>_ : (A B : Obj) -> Set

    id : {A : Obj} -> A ~> A
    _>>_ : {A B C : Obj} -> A ~> B -> B ~> C -> A ~> C

    id-l : {A B : Obj} (f : A ~> B) -> id >> f == f
    id-r : {A B : Obj} (f : A ~> B) -> f >> id == f
    >>-assoc : {A B C D : Obj}
               (f : A ~> B)
            -> (g : B ~> C)
            -> (h : C ~> D)
            -> f >> (g >> h) == (f >> g) >> h
```

And I have some syntactic sugar for dealing with arrows and composition in an
arbitrary category:

```agda
infix 5 _[_,_]
_[_,_] : (C : Category) -> Obj C -> Obj C -> Set
C [ X , Y ] = _~>_ C X Y

infix 5 _[_>>_]
_[_>>_] : (C : Category)
       -> {X Y Z : Obj C}
       -> C [ X , Y ]
       -> C [ Y , Z ]
       -> C [ X , Z ]
C [ f >> g ] = _>>_ C f g
```

With this, we can describe an arrow in `SET` via `SET [ A , B ]`, and
composition via `SET [ foo >> bar ]`.


### Building arrow categories

An arrow category is parameterizd by the category whose arrows form its objects:

```haskell
module ARROW (C : Category) where
  open Category
  open _=>_

  record ArrowObj : Set where
    constructor arrow-obj
    field
      {alpha} : Obj A
      {beta}  : Obj B
      hom : C [ alpha , beta ]

  open ArrowObj

  record ArrowArr (X Y : ArrowObj) : Set where
    constructor arrow-hom
    field
      f : A [ X .alpha , Y .alpha ]
      g : B [ X .beta , Y .beta ]
      commute : C [ f >> Y .hom ] == C [ X .hom >> g ]

  Arrow : Category
  Obj Arrow = ArrowObj
  _~>_ Arrow = ArrowArr
  -- ...
```

My implementation for `Arrow` is actually in terms of the arrow category, which
is the same idea except it does some functor stuff. In the code accompanying
this post, `ARROW {c}` is implemented as `COMMA {c} ID=> ID=>` where `ID=>` is
the identity functor.


### Back to section 3

For convenience, the paper implicitly defines a type synonym for constructing
arrows in the arrow category. This is called `_⮆_` in the paper, but I hate
unicode, so mine is defined as `=>>`:


```agda
infix 0 _=>>_
_=>>_ : ∀ {s1 t1 : Set}
          {s2 t2 : Set}
    → (s1 -> s2) -> (t1 -> t2) -> Set
g =>> h = ArrowArr (arrow-obj g) (arrow-obj h)
```

With all of this machinery in place, we're now ready to continue on the paper.
We can construct a morphism in the arrow category corresponding to the fact that
`<+>` is a model for `<+F>`, as witnessed by `toN-+F`:

```agda
+=>> : {(m , n) : Nat × Nat} -> toN2 { suc m , n } =>> toN { m + n }
+=>> = arrow-hom <+F> <+> $ extensionality toN-+F
```

Again, the necessity of `extensionality` here is a byproduct of me not having
parameterized my `Category` by a notion of equivalence. The arrow category wants
to use extensional equality, but I've hard-baked in propositional equality, and
didn't have time to fix it before my deadline to get this post out.

Although not presented in the paper, arrow categories also have a notion of
"transposition," corresponding to flipping which arrows (in `SET`) lay on the
horizontal and vertical axes. Because `_=>>_` names two arrows, leaving the
other two implicit, transposition changes the type of our arrows --- making the
implicit ones explicit and vice versa. We'll need this later in section 7.

```agda
transpose : {A B : CommaObj} ((comma-hom f g _) : CommaArr A B) -> f =>> g
transpose {comma-obj h} {comma-obj h'} (comma-hom f g p)
  = comma-hom h h' (sym p)
```

As an aside, it's super cool that Agda can do this sort of pattern matching in a
type signature.


## Section 4: Carry-in

In order to make non-unary adders compositional, we need to support carrying-in.
The play is familiar. Define what we want (the specifiation) over the naturals,
write it over `Fin`, and then give an equivalence proof. The paper defines some
type synonyms:

```agda
Nat3 : Set
Nat3 = Nat × Nat2

Fin3 : Nat3 -> Set
Fin3 (m , n) = Fin m × Fin2 n

toN3 : {(c , m , n) : Nat3} -> Fin3 (c , m , n) -> Nat3
toN3 (c , mn) = toN c , toN2 mn
```

(where `Nat2` and `Fin2` are exactly what you'd expect.)

It's easy to define the specification (`addN`), and implementation (`addF`), and
the proof is trivial too:


```agda
addN : Nat3 -> Nat
addN (c , a , b) = c + a + b

addF : {(m , n) : Nat2} -> Fin3 (2 , m , n) -> Fin (m + n)
addF (c , a , b) = c +F a +F b

toN-addF : ∀ {mn@(m , n) : Nat2} →
     SET [ addF >> toN ] =o= SET [ toN3 >> addN ]
toN-addF {mn} (c , a , b)
  rewrite toN-+F {mn} (c +F a , b)
        | toN-+F (c , a) = refl
```

Bundling these up into an arrow proves that `addN` is a model for `addF`:

```agda
add=>>0 : {(m , n) : Nat2} -> toN3 {2 , m , n} =>> toN {m + n}
add=>>0 = comma-hom addF addN $ extensionality toN-addF
```

The paper also makes clear that we can show that `<+>` is a model for `addN` via
`carryIn`:

```agda
carryIn : Nat3 -> Nat2
carryIn (c , a , b) = c + a , b

addN=>> : carryIn =>> id {A = Nat}
addN=>> = comma-hom addN <+> refl
```


## Commentary

At this point, it's starting to become clear what this paper is really *about.*
The idea is that we specify super simple pieces, and then build slightly more
complicated things, showing equivalence to the last piece we built. In this way,
we can slowly derive complexity. Not only does it give us a fool-proof means of
getting results, but it also means we can reuse the proof work. As someone whose
first real project in Agda was to implement and prove the correctness of a few
adders, this is a godsend. I wrote a ripple-carry adder, but was unable to use
my half-adder proof to prove it correctly implements addition. And then I had to
throw all of that work away when I wanted to subsequently write and prove a
carry-forward adder.


## Section 5: Category stuff

This section shows we went through too much effort to implement `add=>>0`.
Really what's going on here is we're doing three things in a row, for the
specification, implementation and proof. First, we're reassociating the tuple,
from `N x (N x N)` to `(N x N) x N`. Then we're doing addition on the first
element of the pair, and then doing addition on the resulting pair.

This is all stuff you can do in any category with all finite products. But I was
too lazy to implement that in full generality, so I hard-coded it. Because arrow
categories lift products, and in `SET` products are just the product type, it's
easy to implement categorical objects:

```agda
_×C_ : Obj Comma -> Obj Comma -> Obj Comma
_×C_ (comma-obj {A1} {B1} f) (comma-obj {A2} {B2} g) =
  comma-obj {A1 × A2} {B1 × B2} λ { (x , y) → (f x , g y) }
```

And then we can implement `first` and `assoc`:

```agda
first :  {A B X : Obj Comma} -> Comma [ A , B ] -> Comma [ (A ×C X) , (B ×C X) ]
first {A} {B} {X} (comma-hom f g p) =
  comma-hom (do-first f) (do-first g) $ cong (\k (a , x) -> k a , xf x) p
  where
    do-first : {A B X : Set} -> (A -> B) -> A × X -> B × X
    do-first f = (λ { (a , x) → f a , x })

assoc : {A B X : Obj Comma} -> Comma [ A ×C (B ×C X) , (A ×C B) ×C X ]
assoc =
  comma-hom reassoc reassoc ?
  where
    reassoc : {A B C : Set} -> A × (B × C) -> (A × B) × C
    reassoc = (λ { (a , b , c) → (a , b) , c })
```

where the proof is left as an exercise to the reader :)

We can now implement `add=>>` more succinctly:

```agda
add=>> : {(m , n) : Nat2} -> toN3 {2 , m , n} =>> toN {m + n}
add=>> = Comma [ Comma [ assoc >> first +=>> ] >> +=>> ]
```

While this is cool, I must admit I'm a little confused. Do `first` and `assoc`
have most-general types when expressd via `_=>>_`? Thinking aloud here, I think
not. Using the `_=>>_` notation is for choosing two *particular* morphisms in
`SET`, while using the more general `COMMA [ X , Y ]` is for *any* pair
morphisms in `SET` with the right type. But I'm not confident about this.


## Section 6: Carrying out

Carry-in is great, but what about going the other direction?

Elliott starts by makig the following observation: if we fix `m = n`, then the
type of our finitary adder is `Fin2 (m , m) -> Fin (m + m)`, which we can
rewrite the codomain as `Fin (2 * m)` and then reinterpret as `Fin 2 x Fin m`.
That is to say, the type of finitary adding is to output a single digit in base
`m`, and a bit corresponding to whether or not a carry occurred. This is a great
little reminder in the value of type isomorphisms. How cool is it that we can
get carry-outs for free just with some algebraic manipulations?

Of course, the trick is to prove it. Start by defining two helper type synonyms:


```agda
CarryIn : Nat -> Set
CarryIn m = Fin3 (2 , m , m)

CarryOut : Nat -> Set
CarryOut m = Fin2 (2 , m)
```

Elliott presents the following "puzzle" of a commutative diagram:

```
              addF
CarryIn m   --------> Fin (m + m)
   ^                      ^
id |                      | ?
   |           ?          |
CarryIn m   --------> Fin (2 * m)
   ^                      ^
id |                      | ?
   |           ?          |
CarryIn m   --------> CarryOut m
```

It's unclear how exactly one formulates these diagrams in the first place. I
guess the top is pinned by `addF`, while the bottom corners are pinned by our
desired carrying out. The middle is thus the isomorphism presented immediately
before this. All of that makes sense, but I'm not convinced I could reproduce it
on my own yet.

So the game now is to fill in the question marks. I don't know how to get Agda
to help me with this, so I'm just going to try literally putting question marks
in and seeing what happens. When doing that, we get this:

```agda
puzzle1 : {m : Nat}
       -> Comma [ comma-obj {CarryIn m}   {CarryIn m}   id
                , comma-obj {Fin (2 * m)} {Fin (m + m)} ?
                ]
puzzle1 = comma-hom ? addF ?
```

Figuring out the first question-mark is simple enough, it's an isomorphism on
`Fin`:

```agda
n+zero : (n : Nat) -> n + zero == n
n+zero zero = refl
n+zero (suc n) rewrite n+zero n = refl

2*m==m+m : (m : Nat) -> (2 * m) == m + m
2*m==m+m zero = refl
2*m==m+m (suc m) rewrite 2*m==m+m m | n+zero m = refl

castF : {m n : Nat} -> (m == n) -> Fin m -> Fin n
castF p rewrite p = id
```

Our first hole is thus `cast $ 2*m==m+m m`.  Interestingly, this doesn't refine
our other hole, since it's already fully specified by the vertial components of
`idA` and the horizontal component of `addF`. However, as the paper points out,
we can get the second hole for free. Because `cast` is invertable, we can make
this square commute by taking `id >> addF >> cast-1`. It feels a bit like
cheating, but it does indeed satisfy the commutativity diagram:

```agda
puzzle1 : {m : Nat}
       -> Comma [ comma-obj {CarryIn m}   {CarryIn m}   id
                , comma-obj {Fin (2 * m)} {Fin (m + m)} (cast $ 2*m==m+m m)
                ]
puzzle1 {m} =
  comma-hom
    (SET [ addF >> cast $ sym $ 2*m==m+m m ])
    addF
    ?
```

where the proof is trivial (but I don't know how to make it terse):

```agda
   SET [ SET [ addF >> cast (sym (2*m==m+m m)) ] >> cast $ 2*m==m+m m ]
== SET [ id >> addF ]
```

Probably there is a category of proofs, where I can just do `reassoc >> second
sym (sym-is-id $ 2*m==m+m m) >> id-r addF >> sym (id-l addF)`. But I don't have
that setup, and this would be annoying to do in the equational reasoning style.
So it remains a hole, and you, gentle reader, can fill it in if you are keen.
Also, I'd love to know how to write a proof as simple as my sketch above.

So that gives us the first half of our puzzle. Now that we have the middle
arrow, let's play the same game:

```
                          addF
CarryIn m   -------------------------------> Fin (m + m)
   ^                                           ^
id |                                           | cast $ 2*m==m+m m
   |                                           |
   |          addF >> cast (sym (2*m==m+m m))  |
CarryIn m   -------------------------------> Fin (2 * m)
   ^                                           ^
id |                                           | ?
   |                       ?                   |
CarryIn m   -----------------------------> CarryOut m
```

So how do we turn a `CarryOut m = Fin2 (2 , m)` into a `Fin (2 * m)`?
Algebraically I think this is a bit tricky, but thankfully `Data.Fin.Base` has
us covered:

```agda
combine : ∀ {n k} → Fin n → Fin k → Fin (n * k)
```

which we can uncurry:

```agda
comb : {m n : Nat} -> Fin2 (m , n) -> Fin (m * n)
comb (f1 , f2) = combine f1 f2
```

and then use this to fill in the vertical arrow. Because `comb` is one half of
an isomorphism (the other half is formed by `remQuot : ∀ {n} k → Fin (n * k) →
Fin n × Fin k`), we can do the same trick to get the horizontal arrow for free:

```agda
puzzle2 : {m : Nat}
      -> Comma [ comma-obj {CarryIn m}  {CarryIn m}   id
               , comma-obj {CarryOut m} {Fin (2 * m)} comb
               ]
puzzle2 {m} =
  comma-hom
    (SET [ SET [ addF >> cast (sym (2*m==m+m m)) ] >> remQuot m ])
    (SET [ addF >> cast (sym (2*m==m+m m)) ])
    ?
```

The proof is again trivial but verbose.

Let's call the implementation arrow `addCarry`, because we'll need it in section
8.

```agda
addCarry : {m : Nat} -> SET [ CarryIn m , CarryOut m ]
addCarry {m} =
  SET [ SET [ addF >> cast (sym (2*m==m+m m)) ] >> remQuot m ]
```

## Section 7: Vertical composition

Finally, we can use *vertical* composition to combine our two puzzles:

```agda
puzzle : {m : Nat} -> id =>> (cast (2*m==m+m m) ∘ comb {2} {m})
puzzle = transpose $ Comma [ transpose puzzle2 >> transpose puzzle1 ]
```

using our `transpose` machinery from earlier. Vertical composition composes
along the axis of specification --- if the implementation of one arrow matches
the specification another, we can combine them into one.


## Section 8: Moving away from unary representations

Unary sucks. Let's generalize our adding machinery to any arbitrary type. First
we'll make types corresponding to `CarryIn` and `CarryOut`:

```agda
DIn : Set -> Set
DIn t = Bool × t × t

DOut : Set -> Set
DOut t = t × Bool
```

I'm going to go rogue for a while, and try to do this section without
referencing the paper. We want to make a morphism in the arrow category
corresponding to using `addCarry` as the specification for addition over `DIn`
and `DOut`. Let's play the same puzzle game, and set up a commutative diagram.

At the top is our specification, `addCarry : CarryIn m -> CarryOut m`. That then
pins our top two objects, and obviously our bottom two are `DIn t` and `DOut t`:

```
                          addCarry
              CarryIn m  --------->  CarryOut m
                 ^                      ^
 bval x (μ x μ)  |                      | μ x bval
                 |         addD         |
               DIn t  ------------->  DOut t
```

where `bval : Bool -> Fin 2`. Here, `μ` plays the part of `toNat`, and `addD` is
addition over `D t`-indexed numbers.

We can package this up into a record indexed by `μ`:

```agda
record Adder {t : Set} {m : Nat} (μ : t -> Fin m) : Set where
  constructor _-|_
  field
    addD : DIn t -> DOut t
    is-adder : SET [ addD >> bimap μ bval ]
            == SET [ bimap bval (bimap μ μ) >> addCarry ]
```

and trivially construct the desired commutative diagram from an `Adder`:

```agda
Adder=>> : {t : Set} {m : Nat} {μ : t -> Fin m}
        -> Adder μ
        -> bimap bval (bimap μ μ) =>> bimap μ bval
Adder=>> (addD -| proof) = comma-hom addD addCarry proof
```


So let's implement a full-adder. This is a "well-known" result, but I didn't
know it offhand. I'm sure I could have sussed this out on my own, but instead I
just found it on Wikipedia:

```agda
and : Bool -> Bool -> Bool
and true b = b
and false b = false

or : Bool -> Bool -> Bool
or true b = true
or false b = b

xor : Bool -> Bool -> Bool
xor true true = false
xor true false = true
xor false true = true
xor false false = false

full-add : DIn Bool -> DOut Bool
full-add (cin , a , b) =
  let o = xor a b
   in xor o cin , or (and a b) (and o cin)
```

We can construct an `Adder` for `full-add` with observation `bval` by
case-bashing our way through the proof:

```agda
BitAdder : Adder bval
BitAdder = full-add -| extensionality
  \ { (false , false , false) -> refl
    ; (false , false , true) -> refl
    ; (false , true , false) -> refl
    ; (false , true , true) -> refl
    ; (true , false , false) -> refl
    ; (true , false , true) -> refl
    ; (true , true , false) -> refl
    ; (true , true , true) -> refl
    }
```

The next step is obviously to figure out how to compose `Adder`s --- ideally to
construct adders for vectors. But I don't know how to do this offhand. So it's
time to look back at the paper.

OK, right. So we have an obvious tensor over `μ`, which is just to lift two of
them over a pair:

```agda
tensorμ
    : {tm tn : Set}
   -> {m n : Nat}
   -> (tm -> Fin m)
   -> (tn -> Fin n)
   -> (tm × tn -> Fin (n * m))
tensorμ μm μn (tm , tn) = comb $ μn tn , μm tm
```

Likewise, we have one over the adding functions themselves, pushing the
carry-out of one into the carry-in of the next:

```agda
tensorAdd
    : {m n : Set}
   -> (DIn m -> DOut m)
   -> (DIn n -> DOut n)
   -> (DIn (m × n) -> DOut (m × n))
tensorAdd addm addn (cin , (ma , na) , (mb , nb)) =
  let (m , cin') = addm $ cin  , ma , mb
      (n , cout) = addn $ cin' , na , nb
   in (m , n) , cout
```

Allegedly these form a true adder as witnessed by `Adder (tensorμ μm μn)`, but
the proof isn't included in the paper, and I had a hard time tracking it down in
the source code. So rather than taking this by fiat, let's see if we can
convince ourselves.

As a first attempt of convincing myself, I tried to construct `adder22 : Adder
(tensorμ bval bval)` which is a tensor of two full-adders. I constructed a
case bash for the proof, and Agda complained! After some sleuthing, I had missed
a swap somewhere in the paper, and thus had my carry bit in the wrong place in
`full-adder`.

After sorting that out, the case bash works on `adder22`. So that's a good
sanity check that this works as promised. But, why? Presuably I should be able
to run my commutative diagram all the way to its specification to debug what's
going on.

A few hours later...

I came up with the following, which can run a commutative diagram:

```agda
arrowOf : {A B : CommaObj} -> CommaArr A B -> CommaObj × CommaObj
arrowOf {A} {B} _ = A , B

debug : {A B C D : Set} -> {f : A -> B} -> {g : C -> D} -> f =>> g -> A -> D
debug arr x =
  let (_ , comma-obj y) = arrowOf arr
      (comma-hom f _ _) = arr
  in y (f x)
```

Of course, the diagrams we get from `Adder=>>` only get us as far as `addCarry`.
In order to get all the way to `Nat`s, we need to vertically compose a bunch of
other diagrams too. In order, they're `puzzle`, `addF=>>` and `addN=>>`. The
actual diagram I came up with was this attrocious thing:

```agda
Adder=>>N
    : Cat2.CommaArr.f
        (Comma [
         Comma [ Comma [ transpose (Adder=>> adder22) >> transpose puzzle ]
         >> transpose addF=>> ]
         >> transpose addN=>> ]) =>> Cat2.CommaArr.g
                 (Comma [
                  Comma [ Comma [ transpose (Adder=>> adder22)
                               >> transpose puzzle ]
                  >> transpose addF=>> ]
                  >> transpose addN=>> ])
Adder=>>N = transpose $
  Comma
    [ Comma
    [ Comma
    [ transpose (Adder=>> adder22)
   >> transpose puzzle ]
   >> transpose addF=>> ]
   >> transpose addN=>> ]
```

and finally, I can evaluate the thing:

```agda
debug' : Nat
debug' = debug Adder=>>N (false , (true , false) , (true , false))
```

Nice. OK, so back to answering the question. Each of the `Bool x Bool` tuples is
a little-endian vector, which get added together, plus the carry. In the process
of doing all of this work, I inadvertantly figured out how the tensoring works.
What's more interesting is tensoring together two different adders. For example,
the `trivial-add` (section 8.3):

```agda
data One : Set where
  one : One

oneval : One -> Fin 1
oneval one = zero

trivial-add : DIn One -> DOut One
trivial-add (b , _ , _) = one , b
```

If we construct `tensorAdder trivial-add BitAdder`, we get an adder whose
vectors are `One x Bool`. This is an extremely interesting representation, as it
means our number system doesn't need to have the same base for each digit. In
fact, that's where the compositionality comes from. We're pretty comfortable
assigning `2^i` to each digit position, but this representation makes it clear
that there's nothing stopping us from choosing arbitrary numbers. What's really
doing the work here is our old friend `comb : {m n : Nat} -> Fin2 (m , n) -> Fin
(n * m)`. Expanding the type synonym makes it a little clearer `comb : {m n :
Nat} -> Fin m x Fin n -> Fin (n * m)` --- this thing is literally multiplying
two finite numbers into one!

Looking at `tensorAdd` under this new lens makes it clearer too. Recall:

```agda
tensorAdd addm addn (cin , (ma , na) , (mb , nb)) =
  let (m , cin') = addm $ cin  , ma , mb
      (n , cout) = addn $ cin' , na , nb
   in (m , n) , cout
```

Here we're pointwise adding the digits, where `m` is the least significant of
the two digits. Our carry-in goes into the `m`, and its carry-out goes into `n`.
OK, so this thing is just doing adder-chaining.

Section 8.4 talks about extending this to vectors, but the trick is just to fold
them via `tensorAdd`. The paper uses a right-fold. I'm curious about what
happens if you do a left fold, but might circle back around to that question
since I only have a few more hours to get this post out and I want to spend some
time *in* Mexico while I'm here. Upon deeper thought, I don't think anythig
would change --- we'd still get a ripple carry adder. Worth playing around with
though.


## Section 9: Speculation

Section 9 is the most exciting part of the paper in my eyes. It defines
speculation, which Elliott uses to implement a carry-ahead adder. I think the
paper cheats a bit in this section --- and makes it clear that we might have
been cheating a bit earlier too. But first some preliminaries. The paper defines
`speculate`:

```agda
speculate : {A C : Set} -> (Bool × A -> C) -> (Bool × A -> C)
speculate f (b , a) = if b then f (true , a) else f (false , a)
```

This looks like it should be a no-op, and indeed, there's a trivial proof that
`speculate f =o= f`. The trick then is to lift `speculate` over an adder:

```agda
spec
    : {t : Set} {m : Nat} {μ : t -> Fin m}
   -> Adder μ
   -> Adder μ
spec (adder -| proof) = speculate adder -| ?
```

and the claim is that if we now do the same vector fold over `spec a` instead of
`a`, we will get a carry-ahead adder! Sorcery! Magic!

But also... wat? Is that actually true?

I think here is where the paper is playing fast and loose. In `SET`, `speculate
a` is exactly `a`. But the paper shows us a circuit diagram for this speculated
fold, and it does indeed show the right behavior. So what's going on?

What's going on is that the paper isn't actually working in `SET`. Well, it is.
Sorta. In fact, I think there's some fancy-pants compiling-to-categories going
on here. In the same way that `xor` presented above is a `SET`-equivalent
version of the `xor` operation in the `CIRCUIT` category (but is not actually
`xor` in `CIRCUIT`), `if_then_else_` is actually the `SET` version of an
equivalent operation in `CIRCUIT`. In `CIRCUIT`, `if_then_else_` is actually
implemented as inlining both its true and false branches, and switching
between them by `and`ing their outputs against the conditional.

So, the carry-ahead adder is not nearly as simple as it's presented in this
paper. There's a huge amount of work going on behind the scenes:

1. defining the `CIRCUIT` category
2. implementing `if_then_else_` in `CIRCUIT`
3. showing that the arrow category lifts `if_then_else_`

Furthermore, I'm not exactly sure how this all *works.* Like, when we define
`speculate` as `if b then f (true , a) else f (false , a)`, are we literally
inlining `f` with the conditional fixed, and *simplfying* the resulting circuit?
I mean, we could just fix `true` by tying it to `HIGH`, but the diagrams
included in the paper don't appear to do that. If so, who is responsible for
simplfying? Does it matter? This is a big hole in the paper, and in my opinion,
greatly diminishes its impact, since it's the claim I was most excited about.

To the paper's credit, the vector fold and speculative fold turn into nice
combinators, and give us a little language for building adders, which is
extremely cool.


## Section 10: Reusing circuitry over time

Ripple-carry adders are slow but use few gates. Carry-ahead adders are much
faster, but use asymptotically more gates. Clearly there is a tradeoff here
between latency and manufacturing cost. Section 10 gives us another point in the
design space where we just build one full-adder, and loop it into itself. This
also sounds exciting, but I'm a bit wary after section 9.

And as presented, I don't think I trust the paper to deliver on this front.
There is some finagling, but at it's core, we are given a looping construct:

```agda
loop
    : {A B S : Set}
   -> {n : Nat}
   -> (S × A -> B × S)
   -> S × Vec A n
   -> Vec B n × S
loop f (s , nil) = nil , s
loop f (s , cons a v) =
  let b , s' = f (s , a)
   in bimap (cons b) id (loop f (s' , v))
```

Thinking about what this would mean in `CIRCUIT` makes it unclear how we would
go about implementing such a thing in real hardware --- especially so if the
embedding sticks `f` into the hardware and then loops over it over time. You're
going to need some sort of ring buffer to read off the outputs and stick them in
the resulting vector. You're going to need timing signals to know when your ring
buffer is consistent. There's clearly a lot going on in this section that is
left unsaid, and there aren't even any pretty pictures to help us reverse
engineer the missing bits.

So I'm going to leave it there.


## Conclusion

*Adders and Arrows* was a fun paper to go through. It forced me to up my
category game, and I got a much better sense of what the arrow category does,
and how it can be useful. Furthermore, just going through a non-trivial project
aggressively improved my Agda competencies, and I'm excited to do more along
these lines.

The paper itself is a bit too terse for my liking. I would have liked a section
saying "here's what we're going to do, and here's how we're going to go about
it," rather than just being thrown in and trying to deduce this for myself. In
particular, it took me an embarassing amount of time to realize how to get
natural numbers out of my adder arrows, and why the first 6 sections were
worth having done.

Technically, I found the ergonomics of working with arrow-category arrows very
challenging. Two of the `SET` morphisms show up in the type, but the other two
show up as values, and there is no easy way to see which diagrams can be
vertically composed. My `Adder=>>N` arrow abve shows the pain of trying to give
a type to such a thing.

I had two major points of complaint about this paper. The first is that the
source code isn't very accessible. It exists in a repo, but is scattered around
a bunch of modules and whenever I wanted to find something I resorted to just
looking at each --- being unable to make rhyme or reason of how things were
organized. Worse, a huge chunk of the underlying machinery is in a separate
repo, one which is significantly more advanced in its Agda usage than I am. A
proliferation of weird unicode symbols that aren't the ones that show up in the
PDF make this especially challenging to navigate.

My other major complaint is that sections 9 and 10 were extremely underwhelming,
though. If the paper does what it promises, it doesn't actually show *how.*
There is a lot going on behind the scenes that aren't even alluded to in the
paper. Granted, the version I'm reading is a draft, so hopefully this will be
cleared up.

I don't yet have a major takeaway from this paper, other than that arrow
categories are cool for specifying problems and proving that your
implementations adhere to those specifications. But as implemented, for my given
adeptness at Agda, they are too hard to use. Composition is tricky to wrap ones
head around given the type signatures used in this paper, but hopefully that's
an aesthetic problem more than a fundamental issue. In particular, `tranpose`
needs to have type `CommaArr A B C D -> CommaArr C D A B` --- this would make
vertical and horizontal composition much easier to think about.

All in all, powering through this paper has given me some new tools for thought,
and helped me see how category theory might be useful to mere mortals.

[My implementation of this code is available on Github.](https://github.com/isovector/agda-playground/blob/88dabf47b5e251cad55dd4cce3b54df5ab4aff13/AddArrows.agda)


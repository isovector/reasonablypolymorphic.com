---
layout: post
title: "Review: Sorting with Bialgebras and Distributive Laws"
date: 2022-02-05 17:59
comments: true
tags: review, hinze, recursion schemes, haskell, sorting
---

Today's paper is [Sorting with Bialgebras and Distributive Laws][paper] by Hinze
et al. The main thrust of the paper is that many well-known sorting algorithms
are categorical duals of one another! As seems to be usual for the papers I
review, there's a lot of [recursion scheme][bananas] stuff here, so go read that
first if you're unfamiliar with it.

Something that's stymied me while working through *Sorting with Bialgebras* is
that whatever it is we're doing here, it's not observable. All sorting functions
are extentionally equal --- so the work being done here is necessarily below the
level of equality. This doesn't jive well with how I usually think about
programming, and has made it very hard for me to see exactly what the purpose of
all of this is. But I digress.

[paper]: http://www.cs.ox.ac.uk/people/daniel.james/sorting/sorting.pdf
[bananas]: /blog/recursion-schemes

## Bubblesort and Naive Insertion Sort

Hinze et al. begin by showing us that insertion sort and bubble sort have terse
implementations:

```haskell
insertSort :: Ord a => [a] -> [a]
insertSort = foldr insert []

selectSort :: forall a. Ord a => [a] -> [a]
selectSort = unfoldr select
  where
    select :: [a] -> Maybe (a, [a])
    select [] = Nothing
    select as =
      let x = minimum as
          xs = delete x as
       in Just (x, xs)
```

and that there are two dualities here, `foldr` is dual to `unfoldr`, and `insert
:: Ord a => a -> [a] -> [a]` is dual to `select :: Ord a => [a] -> Maybe (a,
[a])`.

The rest of the paper is pulling on this thread to see where it goes. As a first
step, it's noted that `foldr` and `unfoldr` are hiding a lot of interesting
details, so instead we will divide the sorting problem into two halves: a
catamorphism to tear down the unsorted list, and an anamorphism to build up the
sorted version.

Begin by defining `Mu` and `Nu`, which are identical in Haskell. The intention
here is that we can tear down `Mu`s, and build up `Nu`s:

```haskell
newtype Mu f = Mu { unMu :: f (Mu f) }

newtype Nu f = Nu { unNu :: f (Nu f) }
```

as witnessed by `cata` and `ana`:

```haskell
cata :: Functor f => (f a -> a) -> Mu f -> a
cata f = f . fmap (cata f) . unMu

ana :: Functor f => (a -> f a) -> a -> Nu f
ana f = Nu . fmap (ana f) . f
```

We'll also need a pattern functor to talk about lists:

```haskell
data ListF (t :: Tag) a k = Nil | a :> k
  deriving (Eq, Ord, Show, Functor)

infixr 5 :>
```

This `Tag` thing is of my own devising, it's a phantom type to track whether or
not our list is sorted:

```haskell
data Tag = UnsortedTag | SortedTag

type Unsorted = ListF 'UnsortedTag
type Sorted = ListF 'SortedTag
```

Note that in Haskell, nothing ensures that `Sorted` values are actually sorted!
This is just some extra machinery to get more informative types.

With everything in place, we can now write the type of a sorting function:

```haskell
type SortingFunc a = Ord a => Mu (Unsorted a) -> Nu (Sorted a)
```

that is, a sorting function is something that tears down an unsorted list, and
builds up a sorted list in its place. Makes sense, and the extra typing helps us
keep track of which bits are doing what.

Most of the paper stems from the fact that we can implement a `SortingFunc` in
two ways. We can either:

1. write a `cata` that tears down the `Mu` by building up a `Nu` via `ana`, or
2. write an `ana` that builds up the `Nu` that tears down the `Mu` via
  `cata`

Let's look at the first case:

```haskell
naiveInsertSort :: SortingFunc a
naiveInsertSort = cata $ ana _
```

this hole has type

```haskell
               Unsorted a (Nu (Sorted a))
  -> Sorted a (Unsorted a (Nu (Sorted a)))
```

which we can think of as having stuck an element on the front of an
otherwise sorted list, and then needing to push that unsortedness one layer
deeper. That does indeed sound like insertion sort: take a sorted list, and then
traverse through it, sticking the unsorted element in the right place. It's
"naive" because the recursion doesn't stop once it's in the right place ---
since the remainder of the list is already sorted, it's OK to stop.

The paper deals with this issue later.

Let's write a function with this type:

```haskell
naiveIns
    :: Ord a
    => Unsorted a (Nu (Sorted a))
    -> Sorted a (Unsorted a (Nu (Sorted a)))
naiveIns Nil                 = Nil
naiveIns (a :> Nu Nil)       = a :> Nil
naiveIns (a :> Nu (b :> x))
  | a <= b                   = a :> b :> x
  | otherwise                = b :> a :> x
```

The first two cases are uninteresting. But the cons-cons case is --- we need to
pick whichever of the two elements is smaller, and stick it in front. In doing
so, we have sorted the first element in the list, and pushed the unsortedness
deeper.

This all makes sense to me. But I find the dual harder to think about. Instead
of making a `cata . ana`, let's go the other way with an `ana . cata`:

```haskell
bubbleSort :: SortingFunc a
bubbleSort = ana $ cata _
```

this hole now has type:

```haskell
     Unsorted a (Sorted a (Mu (Unsorted a)))
  -> Sorted a (Mu (Unsorted a))
```

which is now an unsorted element in front of a sorted element, in front of the
remainder of an unsorted list. What does it mean to be a single sorted element?
Well, it must be the smallest element in the otherwise unsorted list. Thus, the
smallest element in a list bubbles its way to the front.

On my first reading of this, I thought to myself "that sure sounds a lot like
selection sort!" But upon close reading later, it's not. Insertion sort knows
where to put the smallest element it's found, and does that in constant time.
Bubble sort instead swaps adjacent elements, slowly getting the smallest element
closer and closer to the front.

Let's implement a function with this type:

```haskell
bub
    :: Ord a
    => Unsorted a (Sorted a (Mu (Unsorted a)))
    -> Sorted a (Mu (Unsorted a))
bub Nil            = Nil
bub (a :> Nil)     = a :> Mu Nil
bub (a :> b :> x)
  | a <= b         = a :> Mu (b :> x)
  | otherwise      = b :> Mu (a :> x)
```

While `naiveIns` pushes unsorted elements inwards, `bub` pulls sorted elements
outwards. But, when you look at the implementations of `bub` and `naiveIns`,
they're awfully similar! This is the main thrust of the paper --- we can factor
out a common core of `naiveIns` and `bub`:

```haskell
swap
    :: Ord a
    => Unsorted a (Sorted a x)
    -> Sorted a (Unsorted a x)
swap Nil            = Nil
swap (a :> Nil)     = a :> Nil
swap (a :> b :> x)
  | a <= b          = a :> b :> x
  | otherwise       = b :> a :> x
```

It wasn't immediately clear to me why this works, since the types of `bub` and
`ins` seem to be more different than this. But when we compare them, this is
mostly an artifact of the clunky fixed-point encodings:

```haskell
-- type of bub

   Unsorted a (Sorted a (Mu (Unsorted a)))
-> Sorted a (Mu (Unsorted a))

-- unroll a Mu:

   Unsorted a (Sorted a (Mu (Unsorted a)))
-> Sorted a (Unsorted a (Mu (Unsorted a)))

-- let x ~ Mu (Unsorted a)

   Unsorted a (Sorted a x)
-> Sorted a (Unsorted a x)

-- let x ~ Nu (Sorted a)

   Unsorted a (Sorted a (Nu (Sorted a))
-> Sorted a (Unsorted a (Nu (Sorted a)))

-- unroll a Nu

   Unsorted a (Sorted a (Nu (Sorted a)))
-> Sorted a (Unsorted a (Nu (Sorted a)))

-- type of naiveIns
```

The only difference here is we are no longer packing `Mu`s and unpacking `Nu`s.
We can pull that stuff out:

```haskell
bubbleSort'' :: SortingFunc a
bubbleSort'' = ana $ cata $ fmap Mu . swap

naiveInsertSort'' :: SortingFunc a
naiveInsertSort'' = cata $ ana $ swap . fmap unNu
```

and thus have shown that `bubbleSort''` and `naiveInsertSort''` are duals of one
another.


## Bialgebras

Allegedly, this stuff is all "just a bialgebra." So, uh, what's that? The
authors draw a bunch of cool looking commutative diagrams that I would love to
try to prove, but my attempts to do this paper in Agda were stymied by `Mu` and
`Nu` being too recursive. So instead we'll have to puzzle through it like
peasants instead.

The universal mapping property of initial algebras (here, `Mu`) is the
following:

```haskell
cata f . Mu = f . fmap (cata f)
```

and dually, for terminal coalgebras (`Nu`):

```haskell
unNu . ana f = fmap (ana f) . f
```

Let's work on the `cata` diagram, WLOG. This UMP gives us:

```
                     fmap (cata bub)
Unsorted (Mu Unsorted)  --------->  Unsorted (Sorted (Mu Unsorted))
         |                                      |
     Mu  |                                      |  bub
         v                                      v
   Mu Unsorted  ---------------------->  Sorted (Mu Unsorted)
                     cata bub
```

but as we saw in `bubbleSort''`, `bub = fmap Mu . swap`, thus:

```
                     fmap (cata bub)
Unsorted (Mu Unsorted)  --------->  Unsorted (Sorted (Mu Unsorted))
         |                                      |
         |                                      |  swap
         |                                      v
     Mu  |                        Sorted (Unsorted (Mu Unsorted))
         |                                      |
         |                                      |  fmap Mu
         v                                      v
   Mu Unsorted  ---------------------->  Sorted (Mu Unsorted)
                     cata bub
```

If we let `c = cata bub` and `a = Mu`, this diagram becomes

```
                          fmap c
Unsorted (Mu Unsorted)  --------->  Unsorted (Sorted (Mu Unsorted))
         |                                      |
         |                                      |  swap
         |                                      v
      a  |                        Sorted (Unsorted (Mu Unsorted))
         |                                      |
         |                                      |  fmap a
         v                                      v
   Mu Unsorted  ---------------------->  Sorted (Mu Unsorted)
                          c
```

and allgedly, this is the general shape of an `f`-*bialgebra*:

```haskell
c . a = fmap a . f . fmap c
```

where `a : forall x. F x -> x` and `c : forall x. x -> G x`, thus `f : forall x.
F (G x) -> G (F x)`. In Agda:

```agda
record Bialgebra
       {F G : Set → Set}
       {F-functor : Functor F}
       {G-functor : Functor G}
       (f : {X : Set} → F (G X) → G (F X)) : Set where
  field
    a : {X : Set} → F X → X
    c : {X : Set} → X → G X
    bialgebra-proof
      : {X : Set}
      → c {X} ∘ a ≡ map G-functor a ∘ f ∘ map F-functor c
```

where we can build two separate `Bialgebra swap`s:

```agda
bubbleSort : Bialgebra swap
Bialgebra.a bubbleSort = cata bub
Bialgebra.c bubbleSort = Mu
Bialgebra.bialgebra-proof bubbleSort = -- left as homework
```

and

```agda
naiveInsertSort : Bialgebra swap
Bialgebra.a naiveInsertSort = unNu
Bialgebra.c naiveInsertSort = ana bub
Bialgebra.bialgebra-proof naiveInsertSort = -- left as homework
```

I'm not entirely confident about this, since as said earlier, I don't have this
formalized in Agda. It's a shame, because this looks like it would be a lot of
fun to do. We're left with a final diagram, equaqting `cata (ana naiveIns)` and
`ana (cata bub)`:

```
                  ?fmap (cata (ana naiveIns))?
 Unsorted (Mu Unsorted)  - - - - ->  Unsorted (Nu Sorted)
          |                                      |
      Mu  |                                      |  ana naiveIns
          v           cata (ana naiveIns)        v
      Mu Unsorted  - - - - - -|| - - - - ->  Nu Sorted
          |             ana (cata bub)           |
cata bub  |                                      |  unNu
          v                                      v
   Sorted (Mu Unsorted)  - - - - - ->  Sorted (Nu Sorted)
                   ?fmap (ana (cata bub)?
```

The morphisms surrounded by question marks aren't given in the paper, but I've
attempted to fill them in. The ones I've given complete the square, but they're
the opposite of what I'd expect from the initial algebra / terminal coalgebra
UMPs. This is something to come back to, I think, but is rather annoying since
Agda would just tell me the damn answer.


## Paramorphisms and Apomorphisms

Standard recursion scheme machinery:

```haskell
para :: Functor f => (f (Mu f, a) -> a) -> Mu f -> a
para f = f . fmap (id &&& para f) . unMu

apo :: Functor f => (a -> f (Either (Nu f) a)) -> a -> Nu f
apo f = Nu . fmap (either id (apo f)) . f
```

The idea is that `para`s can look at all the structure that hasn't yet been
folded, while `apo`s can exit early by giving a `Left`.


## Insertion and Selection Sort

The paper brings us back to insertion sort. Instead of writing the naive version
as a `cata . ana`, we will now try writing it as a `cata . apo`. Under this new
phrasing, we get the type:

```haskell
     Unsorted a (Nu (Sorted a))
  -> Sorted a (Either (Nu (Sorted a))
                      (Unsorted a (Nu (Sorted a))))
```

which is quite a meaningful type. Now, our type can signal that the resuling
list is already sorted all the way through, or that we had to push an unsorted
value inwards. As a result, `ins` looks exactly like `bub`, except that we can
stop early in most cases, safe in the knowledge that we haven't changed the
sortedness of the rest of the list. The `b < a` case is the only one which
requires further recursion.

```haskell
ins
    :: Ord a
    => Unsorted a (Nu (Sorted a))
    -> Sorted a (Either (Nu (Sorted a))
                        (Unsorted a (Nu (Sorted a))))
ins Nil                 = Nil
ins (a :> Nu Nil)       = a :> Left (Nu Nil)
ins (a :> Nu (b :> x))
  | a <= b              = a :> Left (Nu (b :> x))  -- already sorted!
  | otherwise           = b :> Right (a :> x)
```

Let's think now about selection sort. Which should be an `ana . para` by
duality, with the resulting type:

```haskell
     Unsorted a ( Mu (Unsorted a)
                , Sorted a (Mu (Unsorted a))
                )
  -> Sorted a (Mu (Unsorted a))
```

It's much harder for me to parse any sort of meaning out of this type. Now our
input has both all the unsorted remaining input, as well as a single term
bubbling up. I actually can't figure out how this helps us; presumably it's
something about laziness and not needing to do something with the sorted side's
unsorted tail? But I don't know. Maybe a reader can drop a helpful comment.

Anyway, the paper gives us `sel` which implements the type:

```
sel
    :: Ord a
    => Unsorted a ( Mu (Unsorted a)
                  , Sorted a (Mu (Unsorted a))
                  )
    -> Sorted a (Mu (Unsorted a))
sel Nil                  = Nil
sel (a :> (x, Nil))      = a :> x
sel (a :> (x, b :> x'))
  | a <= b               = a :> x
  | otherwise            = b :> Mu (a :> x')
```

Getting an intution here as to why the `otherwise` case uses `x'` instead of `x`
is an exercise left to the reader, who can hopefully let me in on the secret.

As before, we can pull a bialgebra out of `ins` and `sel`. This time, the
input side uses the `(,)`, and the output uses `Either`, and I suppose we get
the best of both worlds: early stopping, and presumably whatever caching comes
from `(,)`:

```haskell
swop
    :: Ord a
    => Unsorted a (x, Sorted a x)
    -> Sorted a (Either x (Unsorted a x))
swop Nil                    = Nil
swop (a :> (x, Nil))        = a :> (Left x)
swop (a :> (x, (b :> x')))
  | a <= b                  = a :> Left x
  | otherwise               = b :> Right (a :> x')
```

This time our bialgebras are:

```agda
insertSort : Bialgebra swop
Bialgebra.a insertSort = apo ins
Bialgebra.c insertSort = id &&& unNu
Bialgebra.bialgebra-proof insertSort = -- left as homework
```

and

```agda
selectSort : Bialgebra swop
Bialgebra.a selectSort = para sel
Bialgebra.c selectSort = either id Mu
Bialgebra.bialgebra-proof selectSort = -- left as homework
```


## Quicksort and Treesort

Lots of the same techniques, and I'm running out of time, so we'll go quickly.
The key insight thus far is that select sort and insert sort both suck. How do
we go faster than $O(n^2)$? Quicksort, and Treesort!

What's interesting to me is I never considered Quicksort to be a tree-sorting
algorithm. But of course it is; it's recursively dividing an array in half,
sorting each, and then putting them back together. But that fact is obscured by
all of this "pivoting" nonsense; it's just a [tree algorithm projected onto
arrays][tensor].

[tensor]: https://www.youtube.com/watch?v=oaIMMclGuog

Hinze et al. present specialized versions of Quicksort and Treesort, but we're
just going to skip to the bialgebra bits:

```haskell
data Tree a k = Empty | Node k a k
  deriving (Eq, Ord, Show, Functor)

sprout
    :: Ord a
    => Unsorted a (x, Tree a x)
    -> Tree a (Either x (Unsorted a x))
sprout Nil                = Empty
sprout (a :> (x, Empty))  = Node (Left x) a (Left x)
sprout (a :> (x, (Node l b r)))
  | a <= b                = Node (Right (a :> l)) b (Left r)
  | otherwise             = Node (Left l) b (Right (a :> r))
```

This is the creation of a binary search tree. `Left` trees don't need to be
manipulated, and `Right` ones need to have the new unsorted element pushed down.
The other half of the problem is to extract elements from the BST:

```haskell
wither
    :: Tree a (x, Sorted a x)
    -> Sorted a (Either x (Tree a x))
wither Empty                        = Nil
wither (Node (_, Nil) a (r, _))     = a :> Left r
wither (Node (_, b :> l') a (r, _)) = b :> Right (Node l' a r)
```

I think I understand what's going on here. We have a tree with nodes `a` and
"subtrees" `Sorted a x`, where remember, `x` ties the knot. Thus, in the first
level of the tree, our root node is the pivot, and then the left "subtree" is
the subtree itself, plus a view on it corresponding to the smallest element in
it. That is, in `(x, Sorted a x)`, the `fst` is the tree, and the `snd` is the
smallest element that has already been pulled out.

So, if we have a left cons, we want to return that, since it's necessarily
smaller than our root. But we continue (via `Right`) with a new tree, using the
same root and right sides, letting the recursion scheme machinery reduce that
into its smallest term.

But I must admit that I'm hand-waving on this one. I suspect better
understanding would come from getting better intutions behind `para` and `apo`.

Let's tie things off then, since I've clearly hit my limit of understanding on
this paper for this week. While having a deadline is a nice forcing function to
actually go through papers, it's not always the best for deeply understanding
them! Alas, something to think about for the future.

We're given two implementations of `grow`:

```haskell
grow, grow' :: Mu Unsorted -> Nu Tree
grow  = ana  . para $ fmap (either id unNu) . sprout
grow' = cata . apo  $ sprout . fmap (id &&& Mu)
```

as well as two for `flatten`:

```haskell
flatten, flatten' :: Mu Tree -> Nu Sorted
grow  = cata . apo  $ wither . fmap (id &&& unNu)
grow' = ana  . para $ fmap (either id Mu) . wither
```

and then finally, give us `quickSort` and `treeSort`:

```haskell
quickSort, treeSort :: SortingFunc a
quickSort = flatten  . downcast . grow
treeSort  = flatten' . downcast . grow'
```

where `downcast` was given earlier as:

```haskell
downcast :: Functor f => Nu f -> Mu f
downcast = Mu . fmap downcast . unNu
```

This is interesting, but comes with an obvious questions: what if we intermix
`flatten` with `grow'`, and vice versa? Rather unexcitingly, they still sort the
list, and don't seem to have different asymptotics. As a collorary, we must thus
be excited, and assume that these are two "new" sorting functions, at least,
ones without names. I guess that's not too surprising; there are probably
infinite families of sorting functions.


## Conclusions / Notes to Self

What a fun paper! I did a bad thing by jumping into Agda too quickly, hoping it
would let me formalize the "this is a sorted list" stuff. But that turned out to
be premature, since the `Sorted` wrapper is only ever a pair, and exists only to
signal some information to the reader. Thus, I spent six hours working through
the Agda stuff before realizing my deadline was coming up sooner than later.

Implicit in that paragraph is that I started implementing before I had read
through the entire paper, which was unwise, as it meant I spent a lot of time on
things that turned out to be completely unrelated. Note to self to not do this
next time.

Also, it turns out I'm not as firm on recursion schemes as I thought! It'd be
valuable for me to go through `para`s in much more depth than I have now, and to
work harder at following the stuff in this paper. How do the authors keep
everything straight? Do they just have more experience, or are they using better
tools than I am?


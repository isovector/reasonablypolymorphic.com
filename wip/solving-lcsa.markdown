---
layout: post
title: solving-lcsa
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

Usually I write about *solutions* to problems I've worked out, but I've found
myself increasingly becoming interesting in *where solutions come from.* Maybe
it's because I've been reading Boorstin's excellent [The
Discoverers](https://en.wikipedia.org/wiki/The_Discoverers), which I'd strongly
recommend.

Regardless of why, I thought I'd switch up the usual dance step today, and
discuss what solving my most-recent-big-problem actually looked like, in terms
of what I tried, where I looked, and what the timeline was.


## The Problem

The problem is to serialize a program graph into a series of let-bindings. For
example, given the following graph:

```
      +
    /   \
  f ---> g
  |     / \
  a     \ /
      expensive
```

which represents the program:

```haskell
f a (g expensive expensive) + g expensive expensive
```

Unfortunately, this is a naive representation of the program, since it
duplicates the work required to compute `expensive` four times, and `g expensive
expensive` twice. Instead, we would prefer to generate the
equivalent-but-more-efficient program:

```haskell
let $0 = expensive
    $1 = g $0 $0
 in f a $1 + $1
```

This transformation is affectionately known as *sharing*, since it shares the
computed answer whenever there is repeated work to be done.

In order to understand some of my attempted solutions, it's worth noting that
our final solution should build something of type `Expr`, and the original graph
is represented as a `IntMap (ExprF Int)`. `ExprF` is the
[`Base`](https://hackage.haskell.org/package/recursion-schemes-5.2.3/docs/Data-Functor-Foldable.html#t:Base)
functor of `Expr`, with all of its self-references replaced by some type
variable, in this case `Int`. Thus, the graph above looks much more like:

```haskell
_ : IntMap (ExprF Int)
_ = IM.fromList
  [ (0, Apply "+" [1, 3])
  , (1, Apply "f" [2, 3]
  , (2, ...)  -- a
  , (3, Apply "g" [4, 4])
  , (4, ...)  -- expensive
  ]
```


## The Original Solution

My first solution to this problem was to write a fold over the
topologically-sorted graph. The insight being that we should start at the leaves
of the graph, fold those into an `Expr`, and then work our way backwards. If the
node you're on has multiple out-edges to the same node, immediately let-bind
that node before emitting the code.

As a little trick, we can avoid the need to topologically-sort our *input* graph
by computing the least fixpoint of the graph *output* graph:

```haskell
withSharing :: IntMap (ExprF Int) -> IntMap Expr
withSharing gr = fix $ \result -> IM.fromList $ do
  (ix, base) <- IM.toList gr
  let result = fmap (result IM.!) base :: ExprF Expr
  ...
```

Laziness here allows us to "tie the knot." Notice that topologically-sorting the
graph is only useful insofar as it gives us a *linear traversal order* over the
graph, where we can ensure our childrens' results have already been computed
before we start work on the parent. But laziness lets us ignore this constraint
entirely --- by using `fix` we can get an explicit handle to the result we're
still in the middle of building. And what's cool is we can just look up our
children in the final result to see what they folded to.


## Unfolding a Solution

## Performance Woes

## Finding the Kernel

## Hitting the Stacks

## The First Implementer

## Stupid Imperative Solution



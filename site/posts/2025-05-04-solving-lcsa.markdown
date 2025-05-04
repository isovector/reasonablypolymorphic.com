---
layout: post
title: Using Obscure Graph Theory to solve PL Problems
date: 2025-05-04 08:05
comments: true
tags: graph theory, development, haskell
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

So this is what we're trying to do. Given the original graph, determine the best
place to insert these let-bindings, for some reasonable definition of "best." We
can assume there are no side effects involved, so any place that an expression
is well-scoped is an acceptable solution.

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

I spent over a year trying to solve this problem, with various mostly-working
solutions during that time. My strategy here was to think really hard, write up
some algorithm that seemed plausible, and then run it against our (small)
battery of integration tests to make sure it got the same answer as before.

Why not property test it? I tried, but found it very challenging to implement
well-typed generators that would reliably introduce shared thunks. But maybe
there's a different lesson to be learned here about writing good generators.

Anyway. For eight months, one of these think-really-hard algorithms fit the bill
and didn't give us any problems. It was a weird, bespoke solution to the problem
that independetly kept track of all of the free variables in every graph
fragment, and tried to let-bind a fragment as soon as we landed in a context
where all of the free variables were in scope. It seemed to work, but it was
extremely messy and unmaintainable.

At the time of writing, this sharing algorithm was the only source of let-binds
in our entire language, which meant that it didn't need to account for let-binds
*in* the program.

Of course, that invariant eventually changed. We added a way in the source
langauge to introduce `let`s, which meant my algorithm was wrong. And I had
written it sufficiently long ago that I no longer remembered *exactly why it
worked.* Which meant the [theory of my program was lost, and thus that we ought
to rewrite it.](https://pages.cs.wisc.edu/~remzi/Naur.pdf)


## Unfolding a Solution

I went back to the problem statement, and stared at it for a long time (back to
the think-really-hard algorithm!) Upon staring at the problem, I realized that
what I was really trying to do was determine where diamond patterns arose in
the propgram graph.

Recall our original graph:

```
      +
    /   \
  f ---> g
  |     / \
  a     \ /
      expensive
```

If we redraw it such that `g` is on a different rank than `f`, then the two
diamond patterns become much clearer:

```
      +
    /  \
  f     |
  | \   |
  a  \ /
      g
     / \
     \ /
   expensive
```

The insight I came up with is that if a node `n` is the source of a diamond,
then we must let-bind the sink of the diamond immediately before inlining the
definition of `n`.

This gives rise to the question of "how do we identify a diamond?" What we can
do is give a mapping from each node to its reachable set of nodes. For example,
in the above, we'd compute the map:

```
+         -> {+, f, a, g, expensive}
f         -> {f, a, g, expensive}
a         -> {a}
g         -> {g, expensive}
expensive -> {expensive}
```

Then when we go to inline a node, say, `+`, we can look for any nodes that are
reachable via more than one of its immediate subterms. Since the immediate
subterms of `+` are `f` and `g`, we can take the intersections of their
reachable sets:

```
{f, a, g, expensive} union {g, expensive}
```

giving us

```
{g, expensive}
```

which is exactly the set of nodes that we need to perform sharing on. If you
topologically sort this set, it gives you the order that you should perform your
let bindings.

EXCEPT there's a kink in the whole thing. What happens if one of the terms in
this diamond contains free variables? In particular, we might have something
like this:


```
      +
    /  \
  f     |
  | \   |
  a  \ /
      λx
     / \
     \ /
   expensive
      |
      x
```

This gives us an analogous set of reachable nodes when we look at `+`, but we
obviously can't lift `expensive x` above the lambda.

Resolving this problem required giving up on the notion of memoizing the entire
reachable set of nodes, and to instead crawl the graph ensuring that everything
is well-scoped.


## Performance Woes

My algorithm looked fine, and, importantly, got the right answer in a reasonable
amount of time on our (small) battery of integration tests. So I shipped it,
commended myself on a job well done, and thought nothing more about it. For
about a week, until a bug report came in saying that our compiler now seemed to
hang on big programs.

Which was something I hadn't noticed, since we didn't have any big programs in
our integration tests.

Damn!

Upon digging in to what exactly was so slow, I noticed that my algorithm was
[accidentally quadratic](https://accidentallyquadratic.tumblr.com/). I needed to
fold over every node in the graph, and that required looking at the entire
reachable set underneath it. I had put in some of the obvious safeguards, hoping
that they would prune the search tree early, but it wasn't enough sacrifice for
the Great God of Asymptotes.

Did I mention that at this point in the story, having this algorithm working
fast was on the critical path of the company? Everybody else was blocked on me
figuring this out. Talk about pressure!

Anyway. You'll notice above that in my description of the algorithm, everything
sounds fine. But the juice is in the details, as the common saying goes.
Computing reachability isn't quite the right thing to be using here, as it gave
us the wrong answer for the lambda example above. Which is unfortunate because
reachability is something we can do in linear time.

And then when reachability didn't work, I just threw away the fast performance
and hoped my bespoke algorithm would do the job. My only redemption comes from
the fact that at least it got the right answer, even if it did so very slowly.


## Finding the Kernel

Back to the drawing board.

Whenever I have graph theory problems, I call up my boy Vikrem. He's good at
nerd stuff like this.

We [rubberducked](https://en.wikipedia.org/wiki/Rubber_duck_debugging) the
problem, and tried to reframe the problem in the language of graph theory. We
had a Merkiv--Maguire moment where we indepdently realized that the goal was
somehow related to finding the *lowest common ancestor* (LCA) of a node.

Which is to say, roughly, that we are looking for forks in the diamond diagram.
Which we already knew, but it was nice to have some language for.

Our new problem is that LCA is defined only over trees. There are some
extensions to DAGs, but none of them seem to be particularly well founded.
However, searching for exactly that brought me to [this stackoverflow
question](https://stackoverflow.com/questions/14865081/algorithm-to-find-lowest-common-ancestor-in-directed-acyclic-graph),
where nestled in the comments is someone suggesting that the poster isn't
looking for LCA, but instead for a related notion the *lowest **single** common
ancestor.* LSCA is defined in a 2010 paper [New common ancestor problems in
trees and directed acyclic graphs](https://www.sciencedirect.com/science/article/abs/pii/S0020019010000487).

The standard definition of `LCA(x, y) = l` is that "`l` is an ancestor of `x`
and of `y`, and that no descendent of `l` has this property."

But the definition of `LSCA(x, y) = l` is that "`l` lies on all root-to-`x`
paths, and that `l` lies on all root-to-`y` paths, and that no descendent of `l`
has this property."

The distinction between the two is easily seen in the following graph:

```
  0
 / \
1   2
| X |
3   4
```

Under the standard definition, LCA is not uniquely defined for DAGs. That is,
`LCA(3, 4) = {1, 2}`. But neither 1 nor 2 lies on *all* paths from the root.
Under LSCA therefore we get `LSCA(3, 4) = 0`, which is the obviously-correct
place to let-bind 3 and 4.

The paper gives a preprocessing scheme for computing LSCA by building a "lowest
single ancestor" (LSA) tree. The LSA of a node is the LSCA of all of its
in-edges. This definition cashes out to mean "the most immediate diamond above
any node." Finally! This is exactly what we're looking for, since this is where
we must insert our let-bindings! Even better, the paper gives us an algorithm
for computing the LSA tree in linear time!


## The First Implementer

Of course, I'm lazy and would prefer not to implement this thing. So instead
I searched on hackage for `lsca`, and found nothing. But then I searched for
`lca` and found that, like always, [Ed Kmett was 13 years ahead of
me.](https://hackage.haskell.org/package/lca)

The `lca` package implements an $O(log n)$ algorithm for computing the LCA of
any two nodes in a graph. Which is very convenient for me, since the LSCA
algorithm requires being able to do this.

Time to roll up the sleeves and get cracking I suppose.

The paper was surprisingly straightforward, and my first attempt implemented the
(imperative) algorithms as given (imperatively.) The first step is to do
a topological sort on the DAG in order to know in which order one ought to
unfold the LSA tree.

But as is so often the case, this topological sort isn't actually relevant to
the algorithm; it's just an encoding detail of expressing the algorithm
imperatively. But you don't need that when you've got laziness on your side!
Instead you can just tie the know and do something cool like this:

```haskell
lsaTree :: Ord v => Map v (Set v) -> Map v (Path v)
lsaTree input = fix $ \result -> M.fromList $ do
  (node, parents) <- M.toList input
  let parentResults = fmap (result M.!) parents
  ...
```

Notice how we use `fix` to bind the eventual result of the final computation.
Then we can chase pointers by looking them up in `result`---even though it's not
yet "computed." Who cares what order the computer does it in. Why is that
a thing I should need to specify?

Anyway. The exact details of implementing LSA are not particularly important for
the remainder of this blog post. If you're interested, you can peep the PR,
which is [delightfully small](https://github.com/ekmett/lca/pull/8).


## Tying It All Back Together

Equipped with my LSA tree, I was now ready to go back and solve the original
problem of figuring out where to stick let-bindings. It's easy now. Given the
original program graph, find the LSA for each node. The LSA is the place you
should insert the let binding.

So given the map of nodes to their LSAs, invert that map and get back a map of
nodes to descendents who have this node as an LSA. Now when you go to inline a
node, just look up everything in this map and inline it first.

It turns out to be a very elegant solution. It's one third of the length of my
horrible ad-hoc implementations, and it runs in linear time of the number of
nodes in the graph. All in all, very good.

More often than I'm comfortable about, people will ask me how I can have so many
good ideas. And what I like about this story is that it's pretty typical of how
I actually "have" "good" ideas. I'm reminded of the fact that [luck favors the
prepared mind](https://fs.blog/great-talks/richard-hamming-your-research/).
Attentive readers will notice that *none* of this process was due to brilliance
on my part. I happened to know Vikrem who's a genius. Together we pulled at some
ancient graph theory strings and remembered a fact that someone else had thought
important to teach us. That wasn't actually the right path, but it lead us to
stackoverflow where someone had linked to a relevant paper. I implemented the
paper using a library that someone else had done the heavy lifting on, and
simplified the implementation using this knot-tying trick I picked up somewhere
along the way.

Also, I'm just really pleased that the solution came from trying to reverse
engineer the relevant graph-theory search terms. Maybe that's the actual
takeaway here.

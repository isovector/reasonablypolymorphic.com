---
layout: page
title: Self-assembling LEGO Structures
sharing: false
---

## Desiderata

1) make required computation per agent as small as possible
2) only indirect communication: environmental
3) the structure in progress shouldn't fall over while being built
4) no backtracking



## Precomputation

Given a unlabled, connected graph $G=(V,E_G)$ where $V$ are positions we wish
our agents to fill, and $E_G$ describes which agents should connect with
another. Additionally, we will choose a vertex $s \in V$ to act as our starting
point when building the structure.

Let $n = \left\vert V \right\vert$, the number of vertices, and by association,
the number of agents required to build this structure.

To satisfy desiderata #1, we will consider any agent-level pathfinding algorithm
with a time-complexity of $O(n)$ or worse to be unacceptable; it is assumed that
$n$ is proportional to an inverse exponent of the computing power of any given
agent. This rules out all general-purpose pathfinding algorithms, and so we must
look to other means.

Note that pathfinding over a binary search tree has a time-complexity of
$O(\log{n})$. While it is impossible in general to construct a binary tree from
$G$, we instead will content ourselves with constructing a *somewhat-full*
$k$-ary tree capable of element-lookup in $O(k \log{n})$ where $k = \max_{v
\in V}{\text{deg}(v)}$.

Construct a spanning tree $T' = (V,E') = \text{bfs}(G, s)$ where $\text{bfs}(G,
s)$ represents a breadth-first search of $G$ starting from $s$. This
construction should add edge $(v_1, v_2) \in E_G$ to $E'$ if $v_2$ is being
discovered for the first time.

The agents will use $T'$ to traverse the structure-being-built; by virtue of $G$
being connected, there exists a path from $s$ to any $v \in V$, and by being a
spanning tree of $G$, $T'$ retains this property.

It is now necessary to label $T'$ in order to facilitate pathfinding. Label $v
\in V$ as $n-t$ where $t$ is the time at which $v$ is finished being explored by
$\text{dfs}(T', s)$ -- a depth-first traversal of $T'$. We will use the notation
$v_i$ to describe a vertex labeled $i$. Note that under this labeling scheme, $s
= v_0$.

TODO: need to assume there exists a default ordering on edges

However, for the purposes of pathfinding, it is more helpful to instead have
labeled *edges* rather than labeled vertices. Construct $E = \bigcup_{(v_i, v_j)
\in E'}\>(v_i, v_j, \max(i, j))$, where the third index of the tuple is the label
of the edge.

Finally, we will construct our final spanning tree $T = (\{v_{-1}\}\cup V,
\{(v_{-1},v_0,0)\}\cup E')$. Here, $v_{-1}$ is to be understood as an
implementation detail for the algorithm, as it will facilitate initial
coordination between our original agents.

Let $h(x) = x\cdot p \pmod{k}$, where $p$ is any integer coprime to $n$. The
choice[^1] of $p$ should attempt to maximize $\left\vert h(i+1) -
h(i)\right\vert$.

[^1]: There is probably a straightforward means of calculating $p$, but I'm not
sure what it is off-hand. Consider this an exercise left to the reader

Transmit $T$, $G$, and $h(x)$ to all agents. The remainder of this paper
describes the algorithm taken by each agent to build $G$.



## Agent's Algorithm

We will assume there exists a persistent pheromone-value $x_i \in \mathbb{N}$
which is located at node $v_i$ in the graph. $x_i$ can be read or added-to
by agent $a$ only when $a$ is located at $v_i$. We further assume agent $a$ has
internal memory $x_a$ which can be read and written at will.

Let

$$
\bar{v_i} = \begin{cases}
    1 & \text{if an agent has settled into position at $v_i$} \\\\
    0 & \text{otherwise}
\end{cases}
$$

At first, $\bar{v_i} = 0$ for all $i \in [0, 1, \dots, n]$, and the algorithm is
to be considered finished when all $\bar{v_i} = 1$.

Given $n$ agents, once building has been signaled to begin, they are to make
their way to $v_{-1}$. It is assumed all agents know how to get there, and that
they will arrive at unique times.

When agent $a$ arrives at $v_{-1}$, it stores $x_a \leftarrow h(x_{-1})$
internally, and writes $x_{-1} \leftarrow x_{-1} + 1$. As such, $x_{-1}$ acts as
a counter and assigns an ordering over the agents. $a$ then attempts to
pathfind to vertex $v_{h(x_a)}$. For conceptual convenience, we will define $g_a
= x_a$ -- the goal of agent $a$.

The purpose of pathfinding to vertex $h(x_{-1})$ rather than $x_{-1}$ is that
this allows us to distribute agents uniformly over the structure, satisfying
desiderata #3 -- assuming structures will only fall over if they are not built
in a breadth-first manner.

If agent $a$ arrives at $v_i$ such that $\bar{v_i} = 0$, it settles at $v_i$. In
doing so, it makes $\bar{v_i} = 1$ now. Additionally, if $i \neq g_a$, it
writes $x_i \leftarrow g_a$.

Otherwise, if agent $a$ arrives at $i = g_a$ but $\bar{v_i} = 1$, it instead
writes $x_a \leftarrow x_i$. This is equivalent to "trading" its' goal with the
agent who settled where $a$ originally wanted to. $a$ then heads towards the new
$g_a$.

```java
func pathfind(Node cur, Int g_a) {
    if (cur.label == g_a) {
        if (cur.settled)
            g_a = cur.pheromone;
        else
            settle(cur);
    }

    if (!cur.settled) {
        cur.pheromone = g_a;
        settle(from);
    }

    edge[] edges = cur.getEdges();
    for (int i = 0; i < k; i++) {
        if (g_a >= edge.label)
            pathfind(edge.dest, g_a);
    }
}
```

---
layout: post
title: Jujutsu Strategies
date: 2024-05-18 18:03
comments: true
tags: jj, version control, git
---


Today I want to talk about [jujutsu](https://github.com/martinvonz/jj), aka
`jj`, which describes itself as being "a Git-compatible VCS that is both simple
and powerful". This is selling itself short. Picking up `jj` has been the best
change I've made to my developer workflow in over a decade.

Before `jj`, I was your ordinary git user. I did things on Github and knew a
handful of git commands. Sometimes I did cherry picks. *Very* occasionally I'd do
a non-trivial rebase, but I had learned to stay away from that unless necessary,
because rebasing things was a perfect way of fucking up the git repo. And then,
God forbid, I'd have to re-learn about the reflog and try to unhose myself.

You know. Just everyday git stuff.

What I hadn't realized until picking up `jj` was just how awful the whole git
experience is. Like, everything about it sucks. With git, you need to pick a
branch name for your feature *before* you've made the feature. What if while
doing the work you come up with a better understanding of the problem?

With git, you *can* stack PRs, but if you do, you'd better hope the reviewers
don't want any non-trivial changes in the first PR, or else you'll be playing
commit tag, trying to make sure all of your branches agree on the state of the
world.

With git, you can do an interactive rebase and move things relative to a merge
commit, but you'd better make sure you know how `rerere` works, or else you're
going to spend the next several hours resolving the same conflicts across
**every single commit** from the merge.

We all know our commit history should tell the story of how our code has
evolved. But with git, we all feel a little bit ashamed that our commit
histories *don't*, because doing so requires a huge amount of extra work after
the fact, and means you'll probably run into all of the problems listed above.

Somehow, that's just the state of the world that we all take for granted.
Version control Stockholm syndrome. Git sucks.

And jujutsu is the answer.

The first half of this post is an amuse bouche to pique your interest, and
hopefully convince you to give `jj` a go. You won't regret it. The second half
is on effective strategies I've found for using `jj` in my day to day job.


## Changes vs Commits

In git, the default unit of work is a "commit." In `jj`, it's a "change." In
practice, the two are interchangeable. The difference is all in the perspective.

A commit is a unit of work that you've committed to the git log. And having done
that, you're *committed* to it. If that unit of work turns out to not have been
the entire story (and it rarely is), you must make another commit on top that
fixes the problem. The only choice you have is whether or not you want to squash
rebase it on top of the original change.

A change, on the other hand, is just a unit of work. If you want, you can
pretend it's a commit. But the difference is that you can always go back and
edit it. At any time. When you're done, `jj` automatically rebases all
subsequent changes on top of it. It's amazing, and makes you feel like a time
traveler.

Let's take a real example from my day job. At work, I'm currently finessing a
giant refactor, which involves reverse engineering what the code currently does,
making a generic interface for that operation, pulling apart the inline code
into instances of that interface, and then rewriting the original callsite
against the interface. After an honest day's work, my `jj log` looked something
like this:

```
@  qq
│  Rewrite first callsite
◉  pp
│  Give vector implementation
◉  oo
│  Give image implementation
◉  nn
│  Add interface for FileIO
◉  mm
│  (empty) ∅
~
```

This is the `jj` version of the `git log`. On the left, we see a (linear) ascii
tree of changes, with the most recent being at the top. The current change,
marked with `@` has id `qq` and description `Rewrite first callsite`. I'm now ready to
add a new change, which I can do via `jj new -m 'Rewrite second callsite'`:

```
@  rr
│  Rewrite second callsite
◉  qq
│  Rewrite first callsite
◉  pp
│  Give vector implementation
◉  oo
│  Give image implementation
◉  nn
│  Add interface for FileIO
◉  mm
│  (empty) ∅
~
```

I then went on my merry way, rewriting the second callsite. And then, suddenly,
out of nowhere, DISASTER. While working on the second callsite, I realized my
original `FileIO` abstraction didn't actually help at callsite 2. I had gotten
the interface wrong.

In git land, situations like these are hard. Do you just add a new commit,
changing the interface, and hope your coworkers don't notice lest they look down
on you? Or do you do a rebase? Or do you just abandon the branch entirely, and
hope that you can cherry pick the intermediary commits.

In `jj`, you just go fix the `Add interface for FileIO` change via `jj edit nn`:

```
◉  rr
│  Rewrite second callsite
◉  qq
│  Rewrite first callsite
◉  pp
│  Give vector implementation
◉  oo
│  Give image implementation
@  nn
│  Add interface for FileIO
◉  mm
│  (empty) ∅
~
```

and then you update your interface before jumping back (`jj edit rr`) to get the
job done. Honestly, time traveler stuff.

Of course, sometimes doing this results in a conflict, but `jj` is happy to just
keep the conflict markers around for you. It's much, much less traumatic than in
git.


## Stacked PRs

Branches play a much diminished role in `jj`. Changes don't need to be
associated to any branch, which means you're usually working in what git calls a
*detached head* state. This probably makes you nervous if you've still got the
git Stockholm syndrome, but it's not a big deal in `jj`. In `jj`, the only
reason you need branches is to ship code off to your git-loving colleagues.

Because changes don't need to be associated to a branch, this allows for
workflows that git might consider "unnatural," or at least unwieldy. For
example, I'll often just do a bunch of work (rewriting history as I go), and
figure out how to split it into PRs after the fact. Once I'm ~ten changes away
from an obvious stopping point, I'll go back, mark one of the change as the head
of a branch `jj branch create -r rr feat-fileio`, and then continue on my way.

This marks change `rr` as the head of a branch `feat-fileio`, but this action
doesn't otherwise have any significance to `jj`; my change tree hasn't changed
in the slightest. It now looks like this:

```
@  uu
|  Update ObjectName
◉  tt
|  Changes to pubsub
◉  ss
|  Fix shape policy
◉  rr feat-fileio
│  Rewrite second callsite
◉  qq
│  Rewrite first callsite
◉  pp
│  Give vector implementation
◉  oo
│  Give image implementation
◉  nn
│  Add interface for FileIO
◉  mm
│  (empty) ∅
~
```

where the only difference is the line `◉  rr feat-fileio`. Now when `jj` sends
this off to git, the branch `feat-fileio` will have one commit for each change
in `mm..rr`. If my colleagues ask for changes during code review, I just add the
change somewhere in my change tree, and it automatically propagates downstream
to the changes that will be in my next PR. No more cherry picking. No more
inter-branch merge commits. I use the same workflow I would in `jj` that I would
if there weren't a PR in progress. It just works. It's amazing.


## The Dev Branch

[The use and abuse of the dev branch
pattern](https://qword.net/2023/10/22/the-use-and-abuse-of-the-dev-branch),
makes a great argument for a particular git workflow in which you have all of
your branches based on a local `dev` branch. Inside of this `dev` branch, you
make any changes relevant to your local developer experience, where you change
default configuration options, or add extra logging, or whatever. The idea is
that you want to keep all of your private changes somewhere organized, but not
have to worry about those changes accidentally ending up in your PRs.

I've never actually used this in a git workflow, but it makes even more sense in
a `jj` repository. At time of writing, my change tree at work looks something
like the following:

```
◉  wq
╷  reactor: Cleanup singleton usage
╷ ◉  pv
╭─╯  feat: Optimize image rendering
╷ ◉  u
╷ |  fix: Fix bug in networking code
╷ | ◉  wo
╷ ╭─╯  feat: Finish porting to FileIO
╷ ◉  rr
╭─╯  feat: Add interface for FileIO
@  dev
│  (empty) ∅
◉  main@origin
│  Remove unused actions (#1074)
```

Here you can see I've got quite a few things on the go! `wq`, `pv` and `rr` are
all branched directly off of `dev`, which correspond to PRs I currently have
waiting for review. `u` and `wo` are stacked changes, waiting on `rr` to land.
The ascii tree here is worth its weight in gold in keeping track of where all my
changes are.

You'll notice that my `dev` branch is labeled as `(empty)`, which is to say it's
a change with no diff. But even so, I've found it immensely helpful to keep
around. Because when my coworkers' changes land in `main`, I need only rebase
`dev` on top of the new changes to `main`, and `jj` will do the rest. Let's say
`rr` now has conflicts. I can just go and edit `rr` to fix the conflicts, and
that fix will be propagated to `u` and `wo`!!!!

YOU JUST FIX THE CONFLICT ONCE, FOR ALL OF YOUR PULL REQUESTS. IT'S ACTUALLY
AMAZING.


## Revsets

In `jj`, sets of changes are first class objects, known (somewhat surprisingly)
as *revsets.* Revsets are created algebraically by way of a little, purely
functional language that manipulates sets. The id of any change is a singleton
revset. We can take the union of two revsets with `|`, and the intersection with
`&`. We can take the complement of a revset via `~`. We can get descendants of
a revset `x` via `x::`, and its ancestors in the obvious way.

Revsets took me a little work to wrap my head around, but it's been well worth
the investment. Yesterday I somehow borked my `dev` change (????), so I just made
`new-dev`, and then reparented the immediate children of `dev` over to `new-dev`
in one go. You can get the children of a revset `x` via `x+`, so this was done
via `jj rebase -s dev+ -d new-dev`.

Stuff like that is kinda neat, but the best use of revsets in my opinion is to
customize the `jj` experience in exactly the right way for you. For example, I
do a lot of stacked PRs, and I want my `jj log` to reflect that. So my default
revset for `jj log` only shows me the changes that are in my "current PR". It's
a bit hard to explain, but it works like an accordion. I mark my PRs with
branches, and my revset will only show me the changes from the most immediate
ancestral branch to the most immediate descendant branch. That is, my log acts
as an accordion, and collapses any changes that are not part of the PR I'm
currently looking at.

But, it's helpful to keep track of where I am in the bigger change tree, so my
default revset will also show me how my PR is related to all of my other PRs.
The tree we looked at earlier is in fact the closed version of this accordion.
When you change `@` to be inside of one of the PRs, it immediately expands to
give you all of the local context, without sacrificing how it fits into the
larger whole:

```
◉  wq
╷  reactor: Cleanup singleton usage
╷ ◉  pv
╭─╯  feat: Optimize image rendering
╷ ◉  u
╷ |  fix: Fix bug in networking code
╷ | ◉  wo
╷ | |  feat: Finish porting to FileIO
╷ | ◉  sn
╷ | |  Newtype deriving for Tracker
╷ | @  pm
╷ | |  Add dependency on monoidal-map
╷ | ◉  vw
╷ | |  Fix bamboozler
╷ | ◉  ozy
╷ ╭─╯  update InClientRam
╷ ◉  rr
╭─╯  feat: Add interface for FileIO
◉  dev
│  (empty) ∅
```

The coolest part about the revset UI is that you can make your own named
revsets, by adding them as aliases to `jj/config.toml`. Here's the definition of
my accordioning revset:


```toml
[revsets]
log = "@ | bases | branches | curbranch::@ | @::nextbranch | downstream(@, branchesandheads)"

[revset-aliases]
'bases' = 'dev'
'downstream(x,y)' = '(x::y) & y'
'branches' = 'downstream(trunk(), branches()) & mine()'
'branchesandheads' = 'branches | (heads(trunk()::) & mine())'
'curbranch' = 'latest(branches::@- & branches)'
'nextbranch' = 'roots(@:: & branchesandheads)'
```

You can see from `log` that we always show `@` (the current edit), all of the
named bases (currently just `dev`, but you might want to add `main`), and all of
the named branches. It then shows everything from `curbranch` to `@`, which is
to say, the changes in the branch leading up to `@`, as well as everything from
`@` to the beginning of the next (stacked) branch. Finally, we show all the
leafs of the change tree downstream of `@`, which is nice when you haven't yet
done enough work to consider sending off a PR.


## Conclusion

Jujutsu is absolutely amazing, and is well worth the four hours of your life it
will take you to pick up. If you're looking for some more introductory material,
look at [jj init](https://v5.chriskrycho.com/essays/jj-init/) and [Steve's
jujutsu tutorial](https://steveklabnik.github.io/jujutsu-tutorial/)



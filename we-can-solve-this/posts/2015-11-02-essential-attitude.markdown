---
layout: post
title: The Essential Attitude
date: 2015-11-02 18:29
comments: true
tags: vim, november, tools
---

Something I probably should have remembered to write yesterday: it's officially
[National Novel Writing Month][nanowrimo]. I'm not actually writing a novel this
month, but instead am writing the equivalent number of words as blog posts.
Unfortunately for you, there are no rewards [this time around][previous], but
you can still cheer me on if you want by enjoying my content if it's good, and
telling me if it isn't.

I'm kind of cheating this year, since `wc -w posts/2015-11-*` is how I'm
counting words across my blog posts. That's going to include markdown semantics,
but I'm going to count it anyway because anything else would involve doing
work. In my defense, writing blog posts is probably harder than writing a novel
I'd never publish; my last NaNoWriMo had a chapter in a children's book on
advanced mathematics, and one narrated by a hard-boiled detective down in his
luck who had somehow found his way into Narnia.

Since I'd be relatively embarrassed to write a blog post about the exact details
on how I put peanut butter on my sandwiches[^lol], there's probably more
cognitive effort required here than in a novel. That being said, since I have a
full time job, a somewhat active social life, am trying to pick up the
guitar right now, and the average blog post takes me 10 hours to write, try not
to expect too much from the posts this month.

But I'll do my best.

[nanowrimo]: http://nanowrimo.org/
[previous]: http://sandymaguire.me/blog/nanowrimo

[^lol]: This is not an exaggeration; it was my contingency plan to beef up my
word count should I need it.



## Introduction

[Yesterday's post][yesterday] had significantly better responses than I was
expecting, and, not being one to miss an opportunity to milk a dead horse (or
mix metaphors), I thought we'd continue today along the same theme.

[yesterday]: http://sandymaguire.me/blog/vim-is-not-about-hjkl

I have to admit. I have a pet peeve. It's when my heroes who are really good at
something don't post any resources on how they go about being really good at
those things. I'm not the world's best vim user, but I'd say I'm probably above
average, and so this blog post is going to be my modest attempt to not
contribute to my personal annoyances.

While my previous post was more about the motivation behind getting good at vim,
this one aims to be more *how I actually do it*. If that doesn't interest you,
I'll get back to more regularly scheduled blogging in a few days when I've got
some time to do some thought cataloging.

Without further ado: getting good at vim.



## The Basics

Before getting too heavy with modding vim, you should probably get an idea of
what you can do without mods. A really good starting place for this is the
`vimtutor` program, which will take maybe a half hour, but ensure that you have
the fundamentals.

There are two simple concepts you should grasp in vim: movements and operators.


### Movements

Movements are your basic way of getting around. The ones you definitely know
about are `hjkl`, which move you one character at a time. Most of the time,
however, you want to be moving more than one character at a time. Here are some
movements you might *not* know about, sorted roughly in order of ascending
distance.

- `e`: move to the end of the current word
- `w`: move a vim-word forward (vim has a strange idea of what constitutes a
    word)
- `W`: move a human-word forward
- `tx`: move to just before the next 'x' character (mnemonic: un**t**il)
- `fy`: move to the next 'y' character (mnemonic: **f**ind)
- `$`: move to the end of the line (mnemonic: same as in regex)
- `)`: move to the end of this sentence
- `])`: move to the next unmatched ')'
- `]s`: move to the next misspelled word
- `}`: move to the end of this paragraph
- `]}`: move to the next unmatched '}'
- `/regex\<CR>`: move to the next occurrence of a regular expression
- `G`: move to the end of the file

In addition, all of these movements can be prefixed with a number, to repeat the
movement that many times. For example, `5}` moves you down five paragraphs;
`3ti` moves you ahead three 'i's (something I always mess up: `t3i` moves to the
next '3' and enters insert mode). Putting a number before `G` will move you to
that line number.

In order to move backwards similar amounts, you can use `T` or `F`, for the
first two commands, or switch the directions of any of the brackety-type ones
(eg. `[(` moves back to the previous unmatched '(').


### Operators

Operators are normal-mode commands. You're probably familiar with a few of them.
Here's a random list of some that I use often:

- `d`: delete
- `y`: yank
- `c`: change
- `=`: re-indent
- `gq`: wrap text
- `gc`: comment (if you install [vim-commentary][commentary] later)

Pressing the last letter of the operator again will apply the operator to the
current line (this is why `dd` deletes a line). With the notable exception of
yanking, using a capital letter for the operator will act on the *rest* of the
line.

But really, the interesting part of operators is that they compose with
movements. `ct(` deletes everything up until the next '(' character and leaves
you in insert mode to replace it how you please. `y2{` yanks the text earlier in
your current paragraph, and the paragraph above that.  `=G` fixes your indenting
for the rest of the file.

This system is really cool, because it means you can learn movements
individually, and you can learn operators on their own, but as soon as you learn
a new one, it works with all the knowledge you've already solidified. Learning a
new movement makes all of your operators that much stronger; learning a new
operator will play nicely with all the movements you know.

In editors that aren't vim, getting all of these combinations requires writing
$O(|m|\cdot |o|)$ functions, but in vim this is only $O(|m|+|o|)$ pieces of code
in vim. You might not appreciate the difference in this (after all, it's the
programmers of the editor who have to code them, not you). The benefit is
twin-fold: there's less for you to remember, and when you start writing your own
operators or movements, you don't need to worry about getting all the edge
cases. It Just Works&trade;.

In addition to movements, all operators also support what are known as *text
objects*: sequences of characters which are somehow context-aware. Text objects
usually come in two flavors of the same object: *in* and *around* (or *a*).

Text objects don't exist by themselves, so I'll present a few of them here in
terms of random operators:

- `gqip`: reflow the text which comprises of the paragraph I'm currently in
- `di}`: delete the text inside of (but excluding) the pair of braces I'm
    currently in
- `da)`: delete the text inside of (and including) the pair of parentheses I'm
    currently in
- `cis`: change inside sentence
- `yab`: yank a block (what a "block" is is language dependent)

As as a general rule, the **i** versions of text objects don't operate on the
surround context, but the **a** versions do. What context means for a particular
text object isn't always exactly what you'd expect it to be a priori, but it
usually works well enough.

Text objects are generally more useful than movements, and there are like a
million plugins that add new ones. As such, finding text objects is a great way
to build your editing speed.



## Infrastructure

Cool. So now that we have basic vim out of the way, let's get started building
some infrastructure for our modifications.

First of all, go install a plugin manager. I recommend [vim-plug][plug] because
it's what I use and I don't know any better, but I don't have any complaints
with it.  Some vim plugins are so essential that I have no idea how people
manage without them. A couple of essential starting points are:

- [vim-commentary][commentary]: Quickly comment out things in any language
- [vim-surround][surround]: Surround a text object with delimiters
- [vim-repeat][repeat]: Lets you repeat plugins which support it by pressing `.`
- [rainbow_parentheses][rainbow]: Make matching characters change colors as they
    become more nested. As a matter of fact, while typing this sentence I
    noticed that one of my previous links was unmatched because all of a sudden
    my other links changed colors. Super useful, especially for lisp-y
    languages.
- [textobj-variable-segment][varSegs]: Target individual sections of camelCase
    and snake_case identifiers. This is probably the plugin I use the most
    often.

[plug]: https://github.com/junegunn/vim-plug
[commentary]: https://github.com/tpope/vim-commentary
[surround]: https://github.com/tpope/vim-surround
[repeat]: https://github.com/tpope/vim-repeat
[rainbow]: https://github.com/junegunn/rainbow_parentheses.vim
[varSegs]: https://github.com/Julian/vim-textobj-variable-segment

Once you've finished with this section, call `:PlugInstall` to install your new
plugins.

While I have you here, working on your .vimrc, I'd also add the boiler-plate
removing stuff I mentioned yesterday. I'll reproduce it here so as to inflate my
word count, if not my page-view count by making you read it again.

```viml
" Edit .vimrc
nnoremap <leader>ev :e ~/.vimrc<CR>

" Reload any changes whenever you save .vimrc
augroup automaticallySourceVimrc
  au!
  au bufwritepost .vimrc source ~/.vimrc
augroup END
```

I've also added this command which quickly inserts plugin entries for me:

```viml
" Insert vim-plug style plugins from the system clipboard
nnoremap <leader>pg o<ESC>"+pkddA'<ESC>0iPlug '<ESC>0
```

This is probably enough infrastructure to get you going. Again, the point here
is to minimize any friction you might have when trying to make changes to vim.
As a bonus exercise, try adding a leader command to run `:PlugInstall` to update
your plugins for you. Hint: `<CR>` is how you press enter.



## Essential Attitude

Here's the kicker. This is the section that will really begin to help you
improve. The essential attitude you need to develop is to **hate repeating
yourself**. You need to hate doing repetitive things. Every time you find
yourself pressing the same few keys in succession, ask yourself whether it would
be amenable to abstracting. It usually will be.

If the keys you're pressing are unlikely to be necessary ever again (some kind
of specific formatting, usually), consider a macro: press `qx`, where 'x' is any
letter you please, and then make a single one of the repetitive edits you need
to make. When you're done, hit `q` again. Now you can type `@x` to have vim
press that exact sequence of keys for you again.

Wrapping your mind around which kinds of things work well in macros (hint, not
`hjkl` or doing anything in insert mode other than *inserting*) takes a lot of
work, but is definitely worth the effort. Expect your first hundred macros to
mess up on at least one of the edits you're trying to make, but they'll get
better quickly enough. I use a macro ever hour or so; you can do the math on how
many days of work it'll take you to get up to speed on them.

On the other hand, if the edits you're making are likely to generalize, add a
leader command to your .vimrc. Give them a mnemonic name that is short, but
related to what thought goes through your head when you think "oh, I need to do
$x$ to this."

The essential attitude, actually generalizes a little harder than just *hate
repeating yourself* to **hate when vim doesn't do what you want**. If you find
yourself accidentally hitting the wrong key all of the time, consider mapping
that key to do the thing you were actually trying to press. Consider mapping
both the super annoying keys `<F1>` and `Q` to `<nop>` (the do-nothing key),
because you'll inevitably hit them and it will disrupt your flow.

The possibilities here are endless, but the attitude is simple: take a minute
every time something annoys you to ensure it never annoys you again. Over a
surprisingly short period of time, these changes will add up into that optimal
editor I was talking about yesterday. It's an incremental process, and this is
how it happens.

It also helps if you become passionate about making the ideal editor. Once you
have the drive, you'll find yourself [cruising around github][vimrcs] looking
through other people's .vimrcs for little snippets you can steal and make your
experience that much better.

[vimrcs]: https://github.com/search?q=.vimrc

Anyway, I think that's probably enough rambling about vim for today. That's
really all I have to say about vim for at least a week, but if you *really need
more*, I'd recommend watching Ben Orenstein's [video][expert]. A lot of the
ideas I've presented here were originally taken from there, but I think his
presentation is better (as he probably didn't write it stream-of-consciousness
with a minimal amount of editing.)

[expert]: https://www.youtube.com/watch?v=SkdrYWhh-8s


---

But before I go, lest you think that my claims in yesterday's post were
hyperbole, here's a good example of a change I made to my .vimrc while writing
this post:

```viml
imap \m <ESC>maT]y$}o<ESC>p0ys$]A:<ESC>'a$T]ys$]A
```

It's disgusting; I know. Unforuntately until you're really good at vim (and even
then, one could argue), vim mappings have a tendency to be *write-only*. Let's
break it down:

- `imap`: make a *recursive* binding in insert mode
- `\m`: bound to pressing `\m`
- `<ESC>`: leave insert mode
- `ma`: set mark $a$ where my cursor currently is, so we can come back later
- `T]`: move the cursor backwards to the previous ']' character
- `y$`: yank the remainder of the line
- `}}`: move down two paragraphs (the end of this one, and then the end of my
    links section)
- `o<ESC>`: make a new line
- `p0`: paste the anchor name, and move to the beginning of the line
- `ys$]`: surround the line with square brackets (via [vim-surround][surround])
- `A:<ESC>`: append a ':' to the end of the line
- `'a`: move back to mark $a$ (where our cursor was when we called the function)
- `$T]`: move again to the previous ']' character
- `ys$]`: surround the anchor with square brackets
- `A`: and finally, move back to insert mode at the end of the line

I mean, it's not the world's most efficient vim command, but it gets the job
done and it's the first thing that came to my mind. I'm not saying it'll win any
[games of golf][golf], but then again, I'm not playing any.

[golf]: http://www.vimgolf.com/

Later, for that list of plugins, I wrote a couple of link texts with their
desired anchors in a list like this: '- [text]anchor', and then pressed
`vip:norm A\m` to generate anchors links for each one.

The point is not to demonstrate how clever I am at vim, but rather to show you
how low my repetition tolerance is. That's the essential attitude. Internalize
it, and you can do great things.


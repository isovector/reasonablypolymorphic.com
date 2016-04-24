---
layout: post
title: vim Is Not About hjkl
date: 2015-11-01 19:26
comments: true
tags: vim, november, tools
---

Every once in a while, people make a pained kind of face when I tell them I do
all of my text editing in [vim]. Their expression feels a lot like they're
saying "oh, that's cute." When they ask me why I don't use, for example,
[Sublime Text][sublime], I inevitably answer, "because it's not vim."

[vim]: http://www.vim.org/
[sublime]: http://www.sublimetext.com/

"But there are vim bindings for Sublime Text," they respond, confused. "Why not
just use those? It's just like vim, but better."

Herein lies a misconception that seems to bite even advanced vim users; *vim is
not about hjkl*, by which I mean, it's not the keybindings that make vim great.
Don't get me wrong, vim's mnemonic bindings are *really, really good*. Being
able to type `dap` to **d**elete **a** **p**aragraph is pretty clever, and is
probably in line with what is going through your head when you actually want to
delete a paragraph.

Yes, using vim bindings will make you a faster programmer. Probably
significantly, if you're using some other defaults in your text editor. But
neither the keybindings (nor relatedly, its modality) is really the point of
vim.

The point of vim is that it's a language, in the same way that C++ or Haskell is
a language. vim, however, is a language whose purpose is to edit text, and like
any language, it is extensible in interesting ways. Let's look at an example.

vim is full of all sorts of commands which don't seem to be very useful at first
glance. Take, for example, the `:global/abc` command, which in this case, shows
you any lines in which *abc* occur. Kinda cool, I guess, but not much more
useful than searching for the string with `/abc`. However, you can actually
append global with a slash and another command. If you wanted to delete every
line on which *abc* occurs, you could instead do `:g/abc/d`[^1], or, if you're
not into the whole brevity thing: `:global/abc/delete`.

[^1]: The default action on the `g` operator is `p`, for print. This turns out
to be where we get the word "grep" from: `:g/re/p`.

You can maybe think of a few uses for `:g` if you really try hard, but here's a
more challenging puzzle: the `:normal` command. Normal is the command that
presses keys for you. Try it! Typing `:norm gg` will bring you to the top line
of your file, because when it runs it just presses `gg` *for you*. But notice
that you still had to type it out, plus a few keystrokes for "normal", so we're
not really ahead.

Figured out why this might be useful, yet?

One answer is that we can combine it with `:g`, to press keys for us on any line
that has a match. `:g/abc/norm $x` deletes the last character on any line that
has the substring "abc", while `:g/xyz/norm @p` runs the *p* macro on every line
containing "xyz".

And here's the rub. vim commands compose beautifully, just like real languages
do. There's amazing power at your fingertips with the ability to write *very
specific* editing commands that simply *don't exist* in other editors due to
being too specialized.

Sublime Text, while it emulates the basic vim movements, fails to emulate any ex
commands (except for maybe `:%s`. I haven't checked, but this seems to be the
only ex command that vim emulations emulate.) And really, ex commands are why
vim is a powerful editor. vim is not about hjkl.

Speaking of commands which are too specialized to be implemented by your editor:
you will likely find yourself doing the same kinds of mechanical editing over
and over, simply because your editor doesn't provide any abstractions over it.
Me, for example, I leave behind a lot of *TODO*s, because I'm a shit programmer
who never finishes anything all the way. In order to leave behind a *TODO*, here
are the steps I need to take:

- `O` to open insert on a newline above my cursor
- Remember how to make a comment in my current language
- Type `TODO(sandy): `
- Type out what I'm supposed to do
- Hit `ESC`

I leave maybe five *TODO*s per day, which if you do the math, is approximately
$90$ keystrokes a day of boilerplate around *TODO*s. Over the course of my
career, that's roughly $900,000$ keystrokes that I didn't really want to be
typing anyway. Almost a million keystrokes in my life will be dedicated to
leaving myself notes for things I couldn't actually be fucked to do. That sounds
like a pretty bum deal if you ask me.

Consider what happens in real life when you find yourself describing the same
long concept over and over again. After a while you get annoyed and decide to
fix the damn problem, save yourself some effort and just make up a new word that
means what you've been saying this whole time, in fewer words. In fact, over
time, having relatively short words for big concepts is what allows us to build
on top of the concepts; our attention spans aren't very long, and if we spent
all of them keeping track of long descriptions, we'd never get anywhere.

Remember, vim is a language too. It seems like we should be able to abstract
this line of reasoning to vim, and indeed we can. In what turns out to be very
convenient to my argument, as a matter of fact, my .vimrc[^2] file currently has
the following in it:

[^2]: If you didn't know, .vimrc is vim's configuration file. It's where you
should put all of your swanky new vim commands.

```viml
nmap <leader>td OTODO(sandy): <ESC>gccA
```

I'll be the first to admit that [viml] isn't the world's prettiest programming
language, but unfortunately, it's what we've got. With the help of the
[vim-commentary] plugin, this line of code reduces my previous 18 keystrokes of
boilerplate to make a *TODO* down to only three. Pressing `<leader>td`[^3] while
in normal mode creates an empty *TODO* in the line above my cursor, and leaves
me hanging in insert mode to fill in what needs doing.

`:nmap abc xyz` is a command which remaps the key combination `abc` when in
normal mode to instead press `xyz` for you. This is maybe a bad example, because
you should almost always use `:nnoremap` instead of `:nmap`, but until you know
why, just trust me and use `:nnoremap`. Or read `:help nnoremap`.

[viml]: http://learnvimscriptthehardway.stevelosh.com/
[vim-commentary]: https://github.com/tpope/vim-commentary

[^3]: The `<leader>` is a key you define to prefix all of your user-defined commands
with. By default it's backspace, but I've got mine set to the spacebar, since
it's easier to hit.

And just like that, I've created a new command. You'll notice how terse it is.
`nmap` to tell vim what I'm doing, `<leader>td` to tell it what my command is
called, and `OTODO(sandy): <ESC>gccA` for the buttons it should press for me
when I run the command.

Imagine trying to do this in Sublime Text: you need to scan through some menus
--  **Preferences &rarr; Key Bindings &rarr; User** -- and then write some Python
dictionary or JSON or something. *And* you'd have to look up what the command
you want to run is, because you can't refer to things by the keys you'd press.

For those of you keeping score at home, that's another point for vim.

"But Sandy! That's not fair!" I hear you argue. "There's boilerplate in vim for
me to add this to my .vimrc file. I don't see you counting *that*." That's true.
You're right. But I know something you don't. I've got this in my .vimrc:


```viml
nnoremap <leader>ev :e ~/.vimrc<CR>
```

Now `<leader>ev` (mnemonic: **e**dit **v**imrc) fires up .vimrc to be edited, by
typing out `:e`, the path to my .vimrc, and then pressing Enter (known in vim as
*carriage return*).  But there's still some boilerplate to actually reload
.vimrc (since it is not automatically updated). So I automated that too:

```viml
augroup automaticallySourceVimrc
  au!
  au bufwritepost .vimrc source ~/.vimrc
augroup END
```

This watches for whenever I save .vimrc, and runs `:source ~/.vimrc` when I do
-- updating any new bindings or settings I may have added to it. If you don't
feel like you know what all of these lines do, feel free to have a look at
`:help :au`.

Here's what the end-goal is to all of this. What we're trying to accomplish here
is to minimize the friction between things you find annoying in vim, and the
time it takes you to fix them. I make at least four changes to my .vimrc every
day, and I can afford to do this because it's easy and quick.

vim is not about hjkl. It isn't even really about the ability to compose
commands together[^4]. vim is about being a language for editing. Actually
that's not entirely true either; vim is about being *your* language for editing.
What you're really trying to accomplish is to write your own editing language,
one that is perfectly in sync with the way you think about editing code. If you
can minimize the difference between what you think and what you need to type to
make it happen, *you win*.

[^4]: I was lying to you earlier.

I was pair programming with someone the other day in a stock vim config. Given
that I've been using vim as my primary editor for two years now, you might
assume I'd feel right at home. But as a matter of fact, I couldn't do
*anything*.

Whenever I tried to save, my cursor jumped to the end of the line instead.
Trying to run ex commands simply moved my cursor down a line. It took me a few
tries just to get out of insert mode. The best part? I was elated about the
whole thing. That meant what I was doing was working; I was slowly migrating
towards the perfect editor for me. Notice that that's not the *perfect editor*,
but the perfect editor *for me*. I had kept the pieces that made sense to me,
and ruthlessly changed the pieces that didn't,

If you are a sysadmin, this is not behavior you want. If you aren't, and spend
90+% of your time coding at a single computer, it makes a lot of sense to try to
optimize your experience on it. Most programmers aren't sysadmins, and most of
them spend most of their time coding at a single computer. Actually consider it
before blithely arguing that you need to keep your vim stock so that you can use
it when you migrate, or if someone else is at your terminal.

Those things don't happen very often. I am probably going to type fewer than
$900,000$ keystrokes at someone else's computer over my career, so adding that
*TODO* binding alone is worthwhile. Seriously, consider it.

We're programmers for fuck's sake. We spend our entire careers building tools
that reduce the amount of manual labor required in the world. But for some
spooky reason (I can only assume voodoo), most programmers don't apply this
to themselves and their own tools. They use what they're given, and maybe
grumble about them once in a while. This is what vim is: a good *starting point*
for the optimal tool. But it's not there yet, and it's up to you to sculpt it
into what you need.

And please, for the love of god, try not to wiggle your eyebrows so smugly the
next time you suggest that Sublime Text with vim bindings is much better than
vim alone.

---

**Addendum**: as a little something to get your creative juices flowing, I'm going
to toot my own horn here a little and point out some of my more favorite changes
to vim. The objective is to give you a sense of what's possible, and how little
you need to put up with if there's something you don't like in vim.

They're in no particular order.

- [Added a way to track down all of those *TODO*s I left behind][vim-todos].
- [Remapped `:` to `<CR>`][vim-cr]. This makes ex commands into a kind of `<CR>`
    sandwich.
- [Added bindings to create newlines without entering insert
    mode][vim-newlines].
- [Minimized the keystrokes necessary to switch buffers][vim-buffers].
- [Made indenting commands repeatable in visual mode][vim-indent].
- [Disabled a bunch of dumb keys I accidentally hit all the time][vim-no-q].
- [Added an easy way to switch between header and implementation files in
    C][vim-c].
- [Bound save to `;;`][vim-save].
- [Changed capslock to `<ESC>`][vim-esc]. This one is kind of a cheat, because
    it's actually xmodmap and not vim. But hey, it's awesome anyway.

[vim-todos]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L126
[vim-cr]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L214
[vim-newlines]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L278-L279
[vim-buffers]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L695-L711
[vim-indent]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L220-L221
[vim-no-q]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L204-L210
[vim-c]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L181-L182
[vim-save]: https://github.com/isovector/tino/blob/0bf7c9f567a10d6cdc053d4c81dd7a880c090d43/.vimrc#L264
[vim-esc]: https://github.com/isovector/tino/blob/master/.xmodmaprc#L3-L4

Bonus: I extract the links in that [list above][src] and wrote markdown anchors
for them with this: <br /> `:g/\]\[vim-/exec "norm $T[yi]Go\<ESC>p0ys$]A: \<ESC>"`.

[src]: https://raw.githubusercontent.com/isovector/we-can-really-solve-this/master/posts/2015-11-01-vim-is-not-about-hjkl.markdown

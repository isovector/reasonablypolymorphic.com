---
layout: post
title: Underlining the Bugs
date: 2022-01-31 21:46
comments: true
tags: foo, bar
---

I had a magical Haskell experience today, and want to share the story.

My current big programming project is [`cornelis`][cornelis] --- a vim plugin
for interacting with Agda. The Agda compiler is really good at doing interactive
programming, but until `cornelis`, all of this functionality has been locked
away, only to be used by blessed emacs developers.

Tooling for (neo)vim has gotten really good since I last looked at it, and these
days you can write plugins in a language of your choice. For anyone lucky enough
to not appreciate how lovely this is, vimscript's comparison operator checks a
global flag to see if it should be case-sensitive or not. From that perspective,
it's truly a testament that *anyone* has managed to write *anything* for vim.

[cornelis]: https://github.com/isovector/cornelis

The Haskell library for talking to (neo)vim is [particularly
excellent][nvim-hs], and I would strongly recommend it if you're thinking about
writing a vim plugin.

[nvim-hs]: https://github.com/neovimhaskell/nvim-hs

So anyway, the Agda compiler has this cool mode where you can send it queries
about your code, and it gives back answers in JSON. For example, you might ask
"what type does this thing have?" or "please case split this for me" and Agda
will give you back answers. A plugin like `cornelis` or `agda-mode` (for emacs)
can turn Agda's responses into a lovely editing environment, where the computer
does most of the work of programming for you.

Agda doesn't actually make any changes for you, it just says things like
"replace from characters 5 to 10 on line 17 with `foo`." This is nice for editor
integration, since Agda doesn't assume anything about your editing environment.

Rather interestingly, Agda even does its *syntax* highlighting like this. You
ask the compiler what colors things should have, and it responds. Editor plugins
just need to attach that information to the buffer, and you never need to write
another janky regex.

One of the first things I implemented in `cornelis` was this syntax
highlighting. My first attempt looked something like this:

![Syntax Highlighting](/images/underline/highlighting.png)

It's... *almost* right. But those deep yellows should extend to the end of each
line! However, notice that each of the light yellows on the left of the `:`s are
right. So whatever's going wrong here is getting reset every line.

Looking closely at the subscript 1 on `f` gives us a clue what's going wrong ---
unicode characters are throwing off the highlighting ranges! Some swearing and
digging into the vim documentation shows that vim expects its highlighting
ranges to be *byte-indexed* for some insane reason. Agda uses a lot of unicode,
and (rightly) reports locations by their character-index, not their byte-index.

The solution was to get the text being highlighted, and count its actual bytes
in order to fix the numbers being sent to vim. Annoying, but workable. I left a
comment and went on with my day.

The next day, I was working on another feature, which is essentially interacting
with typed-holes. The idea is you move your cursor over the hole, and then ask
Agda to do something with it. But, sometimes, Agda would yell at me and say
there was no hole there! Sure enough, that sometimes was when there was a
unicode character earlier on the line. Same bug, same fix.

Then the day after that, another bug caused by this unicode length stuff. OK,
three strikes and you're out. It was time to fix this bug once and for all.
Fundamentally, the issue is that Agda-offsets don't agree with Vim-offsets,
which sounds like a type error to me. It seemed hard to patch the vim API, but I
controlled all of the Agda-serialization stuff, so I [made a patch][diff]:

[diff]: https://github.com/isovector/cornelis/commit/d52708164d9e1e34a3ef941235d1396bacc937f7

```diff
+ data OffsetType = Line | File
+
+ newtype Offset (a :: OffsetType) = Offset Int32
+   deriving stock Data
+   deriving newtype (Eq, Ord, Show, Read, FromJSON)
+
+ type BufferOffset = Offset 'File
+ type LineOffset = Offset 'Line

  data Position' a = Pn
    { srcFile :: !a
-   , posPos  :: !Int32
+   , posPos  :: !BufferOffset
    , posLine :: !Int32
-   , posCol  :: !Int32
+   , posCol  :: !LineOffset
    }
```

and then changed the types of the bug-fixing functions:

```diff
- toBytes :: Text -> Int -> Int
+ toBytes :: Text -> Offset a -> Int
- fromBytes :: Text -> Int -> Int
+ fromBytes :: Text -> Int -> Offset a
```

After doing some plumbing to change all the function types to refer to
`BufferOffset` and `LineOffset` rather than `Int`, I was left with a few type
errors in the program: *corresponding exactly with the bug I had set out to fix,
and two others I didn't know about!*

![Underlined Bugs](/images/underline/underline.png)

Let me restate that. The computer *underlined the bugs* in my program. It found
bugs in code I'd already written.

If this isn't one of the best arguments for static typing, I can't imagine what
would be.


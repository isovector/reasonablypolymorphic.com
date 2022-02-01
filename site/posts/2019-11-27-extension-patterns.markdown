---
layout: post
title: "Low-Tech AST Extensibility with Extension Patterns"
date: 2019-11-27 22:15
comments: true
tags: haskell
---

Today I want to share a common pattern I've been using for extending AST-like
data structures that I don't own. It's an extremely low-tech solution to the
problem (as opposed to something like the dreaded [Trees That Grow][ttg], which
is more far complicated than any problem is worth.)

[ttg]: https://www.microsoft.com/en-us/research/uploads/prod/2016/11/trees-that-grow.pdf

A common problem I run into is wanting to add custom annotations to abstract
syntax trees. As one example, a while back I was writing a Haskell editor that
would *write Haskell code for you.* The idea was to get rid of the text
representation of code entirely, and work directly with the Haskell AST.
However, it's often useful to insert metadata into the AST --- for example,
which bit of the tree you're currently editing.

As another example, I'm currently writing a book in markdown, and want to
express high-level concepts that markdown doesn't have any primitives for ---
things like *exercises* or *inline this snippet of code from a real codebase* or
*this thing is like a footnote, but should have a special graphic.* If I were a
pleb, I'd just manually write the low-level markdown necessary to achieve the
visual goal I want.

But: two problems. Firstly, I did that on the last book, and it turned out to be
the biggest mistake I've made in quite a long time. The issue is that while this
works for the representation you're currently looking at, it all falls apart
when you want to change the representation. My book looked great as a PDF, but
it took me weeks and literal tears to turn that thing into an e-book.

Secondly, this book I'm writing is *all about* how the root of all evil is a
premature loss of precision --- which is to say, it's about designing and using
abstractions. The irony would be too salty if I didn't take my own advice here
and build my book out of the abstractions I claim are so valuable.

So this is the question: how can we add new abstraction primitives to a datatype
that we don't control?

Let's take a particular example that I implemented today. In [The Hardest
Program I've Ever Written][dartfmt], Bob Nystrom walks through the
implementation of an interesting program. Throughout the prose, there are little
skulls which are footnotes describing a wrong path he took during the
implementation. These mistakes are, in my opinion, more interesting than the
essay itself.

[dartfmt]: http://journal.stuffwithstuff.com/2015/09/08/the-hardest-program-ive-ever-written/

My book has a few case studies in which I work through building a real program
using the techniques I'm advocating. The idea is to give readers an actual taste
of how it works in practice, and to show that often times the journey is more
valuable than the destination. As such, I thought Bob's skull footnotes would
make an excellent addition to these chapters.

I dug in to see how Bob had implement his, and I was amazed! [The poor bastard
had done it all by hand!][source] My god, if that's not commitment, I don't know
what is. There are like seventeen footnotes in that blog post. Someone should
probably make Bob a saint for just how patient he must be.

[source]: https://raw.githubusercontent.com/munificent/journal/master/_posts/2015-09-08-the-hardest-program-ive-ever-written.md

While this is commendable, it is antithetical to our purposes. This is clearly
an abstraction leak; markdown is supposed to be human-readable format that
eschews 15th-century technology like HTML. As soon as you have an abstraction
leak, your abstraction is worth nothing. At this point it will only bring you
pain.

But what can we do instead?

Well, my book is being authored in markdown, and then processed via
[pandoc][pandoc] to turn it into pretty PDFs. I've separated the semantic bits
from the presentation bits, in an act of forward thinking for when I make an
e-book copy. What this means is that, *even though I'm writing markdown,* my
book is actually a Pandoc document. Which is to say, there is a
[Text.Pandoc.Definition.Block][block] somewhere in the platonic realm that
describes my book.

[pandoc]: https://pandoc.org/
[block]: https://hackage.haskell.org/package/pandoc-types-1.17.6.1/docs/Text-Pandoc-Definition.html#t:Block

And so we return to the question of how to annotate ASTs. The [Pandoc
AST][block] is a rather expressive format, but it primarily describes basic
typographic elements. It primarily captures meaning as to how to layout a
document, rather than capturing the meaning of *what is being expressed.*

While Pandoc already has the option to [annotate a Footnote][footnote], I don't
want to replace all footnotes with deathnotes (as I've taken to calling these
little skull things.)

[footnote]: https://hackage.haskell.org/package/pandoc-types-1.17.6.1/docs/Text-Pandoc-Definition.html#t:Inline

The trick is a rather stupid one. While usual footnotes are written in markdown
like this:

```markdown
This is some prose[^1]

[^1]: This is a footnote.
```

I've decided to annotate my deathnotes like this:

```markdown
This is some prose[^1]

[^1]: death This is a deathnote.
```

The only difference is that the text of a deathnote starts with the word
`death`. That's it. There is nothing clever going on here. When parsed into a
`Block`, the above has this structure:

```haskell
Para
  [ Str "This"
  , Space
  , Str "is"
  , Space
  , Str "some"
  , Space
  , Str "prose"
  , Note
    [ Para
      [ Str "death"
      , Space
      , Str "This"
      , Space
      , Str "is"
      , Space
      , Str "a"
      , Space
      , Str "deathnote."
      ]
    ]
  ]
```

The bit of interest to us is the part of the AST that begins `Note [ Para [ Str
"death"`. Because this is an easy thing to annotate directly in markdown, and
because it won't happen by accident, we can decide that this is the canonical
representation for annotating a deathnote.

Here's the trick: we can reify that decision in Haskell via a pattern synonym.
If you're unfamiliar with pattern synonyms, they allow you to "create" "new"
data constructors, which are just synonyms for arbitrary patterns you'd like to
pick out. In our case, we want to pick out that `Note [ Para [ Str "death"`
structure.

We begin by writing a little function that will pattern match on the part we
want, and remove the word `"death"` from the first paragraph.

```haskell
splitDeathNote :: [Block] -> Maybe [Block]
splitDeathNote (Para (Str "death" : ps) : bs)
  = Just (Para (dropWhile (== Space) ps) : bs)
splitDeathNote _ = Nothing
```

The function `splitDeathNote` will try to match our deathnote pattern, and if it
succeeds, give back the rest of the content. As a second step, we enable
`-XViewPatterns` and `-XPatternSynonyms` and write a pattern:

```haskell
pattern DeathNote :: [Block] -> Inline
pattern DeathNote bs <- Note (splitDeathNote -> Just bs)
  where
    DeathNote (Para ps : bs) = Note $ Para (Str "death" : Space : ps) : bs
    DeathNote bs             = Note $ Para [Str "death"] : bs
```

Patterns have egregious syntax, but it can be read in two parts. The first bit
is the `pattern DeathNote bs <- Note ...` bit, which is used for defining a
*pattern match.* It says, "if you do a pattern match on the thing left of the
`<-`, instead replace it with the pattern match on the right. This weird `->`
thing is a *view pattern,* which says "run the `splitDeathNote` function, and
only match if it returns a `Just`."

The other part of the pattern synonym, the part after the `where`, allows us to
*build an `Inline` out of a [Block].* Which is to say, it works like a data
constructor; we can write something like `let foo = DeathNote blah`.

In other words, after defining the `DeathNote` pattern synonym, for all intents
and purposes it's like we've added a new data constructor to the pandoc `Inline`
type. For example, we can write a function that pattern matches on it:

```haskell
isDeathNote :: Inline -> Bool
isDeathNote (DeathNote _) = True
isDeathNote _ = False
```

GHC will happily compile this thing, and it will work as expected! Cool!

The final step to actually getting these things working is to walk the pandoc
AST, and transform our nice, newly-annotated deathnotes into something more
amenable for a PDF. But! We want to do this *as part of generating a PDF.* That
way we hold onto our semantic annotations until the *very last moment,* i.e.,
when we send our document to the printers.

We can get this transformation for free via [Scrap Your Boilerplate][syb](SYB
for short.) SYB lets us write tiny transformations that operate only on a piece
of data that we care about, and then lift that into a leaf-first transformation
over arbitrarily large data structures.

[syb]: https://www.stackage.org/lts-14.16/package/syb-0.7.1

In our case, we can write a function like this:

```haskell
renderDeathNoteForLatex :: Inline -> Inline
renderDeathNoteForLatex (DeathNote bs) =
  RawInline "latex" $
    mconcat
      [ "\\deathnote{"
      , show bs  -- the real implementation doesn't use show
      , "}"
      ]
renderDeathNoteForLatex x = x  -- just id for all other nodes
```

And then use SYB to lift it over the entire `Pandoc` structure

```haskell
latexPreProcess :: Pandoc -> Pandoc
latexPreProcess = everywhere (mkT renderDeathNoteForLatex)
  -- we can potentially run other transformations here at the same time
```

And just like that, we've added a custom annotation to markdown, and separately
given a presentation strategy for it. We can use [`toJSONFilter`][json] to
connect our little `latePreProcess` transformation to `pandoc`, and no one is
any the wiser.

[json]: http://hackage.haskell.org/package/pandoc-types-1.20/docs/Text-Pandoc-JSON.html#v:toJSONFilter


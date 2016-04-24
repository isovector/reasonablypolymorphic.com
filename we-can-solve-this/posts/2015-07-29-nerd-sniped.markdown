---
layout: post
title: A Nerd-Snipe of Epic Proportions
date: 2015-07-29 02:20
comments: true
tags: site, technical, haskell, vim
---

## Down the Rabbit Hole

So last week as I was writing a [blog post][ideas], I found myself switching
back and forth between two buffers in [vim][vim]. A lot. So much that my hands
actually started hurting, and I realized something: <code>:4b&#9166;</code> is
*five* keystrokes.

Who has the time or wrist capacity to type *five* keystrokes every time they
want to switch buffers? Not me.

[ideas]: /blog/sandy-runback
[vim]: https://en.wikipedia.org/wiki/Vim_(text_editor)

Clearly something had to change. Because I had just finished reading [Learn
Vimscript the Hard Way][vimscript], I put my writing on hold, and switched to
`.vimrc` where I hacked together a little something. After lots of research and
false starts, I got `4t` to switch to buffer 4, but for `tx` to work like usual
and move to the next occurrence of 'x'. This was implemented with some magic
trickery by checking what the number prefix had been set to, and to use the
default implementation when that number was 1.

[vimscript]: http://learnvimscriptthehardway.stevelosh.com/

(I don't have enough patience to count more than 1 for move-aheads, so this
behavior is OK by me.)

This lead to an unfortunate situation where buffer 1 couldn't be switched to via
my lovely new method. A discrepancy! Since there's no way to renumber buffers, I
decided just to make buffer 1 get destroyed by default. It's a kinda shitty
solution, but poorly hacking things together is oddly cathartic.

Here's what I ended up dumping into `.vimrc` by the time all was said and done:

```php
function! s:bufSwitch(count)
    if count ># 1
        return ":\<C-U>" . count . "b\<CR>"
    endif
    return 't'
endfunction
nnoremap <expr> t <SID>bufSwitch(v:count1)

au VimEnter * if v:progname ==# "gvim" && expand('%') ==# "" |
                \ execute "normal! ihello\<Esc>:bw!\<CR>"    |
                \ endif
```

In my excitement, I wanted to post this fantastic solution on my blog to share
with all of the world. But there was a problem: I didn't want to post it in the
*main* section of my blog[^1], since my usual readership has plummeted over the
last few technical posts, and it's probably not a very good idea to alienate
most of ones readers. It seemed like a good idea to separate out the technical
content into a new mostly-independent blog.

[^1]: I realize the irony, thank you.

One would expect this to be a relatively simple job. But it wasn't. My blog used
to run on [Octopress][op], which is pretty cool if you want something to Just
Work(TM). Unfortunately, it is written in Ruby, and like most things written in
Ruby, the whole thing runs on magic. Running on magic is good if you want things
to happen, but it is *not very good whatsoever* if you want to change things.

[op]: http://octopress.org/

And I wanted to change things.

And I'm pretty sure it's impossible to change.

After three hours of fighting with the damn thing, I decided just to port the
whole mess over to [Hakyll][hakyll] -- a spiritual relative of Octopress, but
written in Haskell and, more importantly, not completely shit.

[hakyll]: http://jaspervdj.be/hakyll/

Since I didn't really know how the Octopress stuff worked, porting the site
as-was turned out to be more work than I cared for, so I decided that I might as
well just do an entire redesign while I was at it. The old templates had all
sorts of weird things that I couldn't account for: random whitespace, a million
files that never seemed to actually be used, and the weirdest CSS pipeline in
existence.

I nuked the whole thing from orbit.



## The Devil's in the Details

Starting entirely from scratch, I coded up the first HTML document I've done in
years. I don't know exactly how Web 2.0(TM) Ready it is -- there is a lot of
new technology these days that I'd never heard of -- but hey, it works. And it
doesn't have a single &lt;table&gt; tag. Good enough for me.

<script type="text/javascript">
var toggled = false;
function toggleLines() {
    toggled = !toggled;
    if (toggled) {
        $('article').css('background-image', 'url(data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAIAAAAUCAYAAACnOeyiAAAAF0lEQVQIW2NkgALGwc8oLy//39nZyQgAG6YEFW6EBNcAAAAASUVORK5CYII=)');
        $('nav').css('background-image', 'url(data:image/png;base64,iVBORw0KGgoAAAANSUhEUgAAAAIAAAAQCAYAAAA8qK60AAAAF0lEQVQIW2NkgALGgWWUl5f/7+zsZAQAGOgEEZMPrH4AAAAASUVORK5CYII=)');
    } else {
        $('article').css('background-image', 'none');
        $('nav').css('background-image', 'none');
    }
}
</script>

The layout stuff, of course, was easy. Conceptually I know what the structure of
my page should be: a central column, a sidebar, what have you. The HTML, now
that's baby stuff. But styling it? An entirely different story.

I probably spent three works tweaking color-schemes. I'm an idiot and shouldn't
have spent this long, because I could have been doing it in photoshop (which
would be fast), but instead was editing CSS by hand (which wasn't fast).

Tweaking colors got tedious, so I started looking for a program I could drop
into my test page and preview colors in real time. To my unlimited surprise, no
such thing existed. You can guess where this is going... I decided to write one.

I found a color-scheme library, and hooked it up to some sliders that would
jigger all the colors on my page simultaneously. I got something up and running,
but soon found out there was a good reason no such thing existed: it wasn't very
helpful. I scrapped it, and started looking through color swatches.

With the colors out of the way, I decided that if I was going to do this, I was
going to do it *right*. One of my heroes had [recently written][typography]
about all the typography work that had gone into producing his most recent book.
I was inspired, and decided to learn about typography.

[typography]: http://journal.stuffwithstuff.com/2014/11/03/bringing-my-web-book-to-print-and-ebook/

The next few hours were spent reading about things like [vertical rhythm][vr]
and how to go about sizing fonts relative to one another. Learning the stuff was
easy; implementing it on the web is a whole different ball game. Thankfully
there is a [tool][vrtool] that figures out a lot of it for you, but there's
always a catch. When you do them right, sizes on the web are all relative to one
another, but structure embeds arbitrarily.

[vr]: http://typecast.com/blog/4-simple-steps-to-vertical-rhythm
[vrtool]: https://drewish.com/tools/vertical-rhythm/

Four hours went by, with me meticulously rendering pages, ensuring their
vertical rhythm worked, and tweaking the CSS if it didn't. I usually broke other
bits of the website while tweaking. It wasn't fun.

The *good news* is that my meticulous work has paid off. <a
onclick="toggleLines();" href="#">Click here</a> to see just how perfect the
vertical rhythm is. Amazing stuff.

Click that link again if you want to make the pretty rule lines go away. But I'm
not sure why you'd want to. They're gorgeous, aren't they?



## Hakyll Hacking

> Feel free to skip the rest of this post if you don't care about the technical
> issues and solutions I ran into while setting up the rest of the site.

Design? Officially done. All that was left was to get Hakyll setup properly. How
hard could that be, right?

See, the problem with that line of reasoning was that I had forgotten that I'm
not really all that good with real-world Haskell. It's one thing to write your
own code, but interacting with other people's is entirely different.

The first thing to do was getting it to render [MathJax][math], but thankfully
this was already a [solved problem][pandocmath]. So far, so good.

[math]: https://www.mathjax.org/
[pandocmath]: http://jdreaver.com/posts/2014-06-22-math-programming-blog-hakyll.html

Getting RSS/Atom set up was also [surprisingly easy][rss].

[rss]: http://jaspervdj.be/hakyll/tutorials/05-snapshots-feeds.html

Next, I ensured I wouldn't break any existing links to my website. My [markdown
files][markdown] have paths of the form `posts/yyyy-mm-dd-slug.markdown`, but I
wanted `blog/slug`. Octopress would rewrite them as `blog/slug/index.html` and
then silently trim off the `index.html` bits, but when I tried this approach,
Hakyll wasn't very happy. In the end, I settled for writing the HTML files
without an extension, and changing nginx to have a default MIME type of
`text/html`. Ultra yucky, but it gets the job done.

In the end, my posts routing looked like this:

[markdown]: https://github.com/isovector/we-can-really-solve-this/tree/master/posts

```haskell
match "posts/*" $ do
    postMatches <- getMatches "posts/*"
    route $   gsubRoute "posts/" (const "blog/")
          <+> gsubRoute "/[0-9]{4}-[0-9]{2}-[0-9]{2}-" (const "/")
          <+> setExtension ""
    compile $ do
        -- etc
  where (<+>) = composeRoutes
```

The `(<+>)` operator is there because `Routes` *has* a `Monoid` instance, but
`mappend` is **not** defined as `composeRoutes`. That means it'll compile if you
treat it like a monoid, but it won't work properly. This caught me up, and is
particularly egregious because every other `Monoid` instance works as expected
in Hakyll.

The next step was to get the home page serving the most recent blog post. This
was deceptively hard: I managed to implement it in 20 minutes by getting Hakyll
to copy the most recent post to `index.html`, but there was a problem. The title
didn't say "Home", because it was a copy. A minor problem, but since this
project was all about perfectionism, I wasn't willing to give up.

This one turned out to be a big hack too: the template thought it was going to
render all of the posts, but I only ever gave it the most recent one.

```haskell
create ["index.html"] $ do
    route idRoute
    compile $ do
        posts <- recentFirst =<< loadAll postsDir
        let indexCtx = mconcat
                [ listField "posts" postCtxTags (return $ take 1 posts)
                , constField "title" "Home"
                , defaultContext
                ]
        contentCompiler "templates/index.html" indexCtx
```

Notice that I'm giving it a "list" of one post. The template
`templates/index.html` looks stupid, but it's good enough for the internet:

```html
$for(posts)$
$body$
$endfor$
```

The home stretch was in sight. All that was left was to get little forward and
backwards arrows on posts for easy navigation. This turned out to be *brutal*,
but I eventually [found a solution][sortid] deep within an old commit on GitHub.

[sortid]: https://github.com/rgoulter/my-hakyll-blog/commit/47f854501395146655967db82ac740e762ef89d0

Marvelous! Everything was done! Or so I thought.



## Burning the Books

One of the lesser-known features of my website is that I collect [quotes that I
like from books that I've read][books]. I do all of my reading on a Kindle,
which has a great feature called "My Clippings" that lets you underline and save
text. Every couple of books I synchronize these clippings onto my website and
build a big index.

[books]: /books/

This has always been a huge kludge; the old Octopress site had a hand-run
[gnarly-ass python script][clipit] that would pre-process and poorly parse the
Kindle files into Markdown, and then throw the resulting files somewhere
Octopress could find them for its next build. It was gross, but it mostly
worked. That seems to be a theme today.

[clipit]: https://github.com/isovector/we-can-really-solve-this/blob/f0a5a0191f531453b2bd6cac5eddd3e80fe08336/octo-clip-it/clip-it.py

The problem was that it *mostly* worked. There were a bunch of things I had
overlooked in my parsing: most prominently the byte-order-mark which lead to my
script sometimes generating two copies of the same book with different titles.

Since Hakyll wants to be the end-all-and-be-all of your site generation, I
decided I'd better port over this mess as well. I learned how to use
[parsec][parsec], the Haskell parser combinator library. I'm sure it would
have been great if a) the Kindle files were in any sensible format and b) I had
known how to use parsec properly.

[parsec]: https://hackage.haskell.org/package/parsec

Neither of these were the case. I ended up doing most of the parsing with
parsec, but resorted to a bodacious regex to get the title and author meta-data
out. Here's a little sample for you:

```haskell
clipping :: GenParser Char st Clipping
clipping = do
    meta <- line
    let regex = mkRegex "^(.*?) \\(([^)]*)\\)$|^(.*?) \\- (.*)$"
        matches = matchRegex regex meta
        ((book, subtitle), authorName) =
            case matches of
                Just xs  -> case xs !! 0 of
                        ""   -> (parseSubtitle $ xs !! 2, xs !! 3)
                        name -> (parseSubtitle name, xs !! 1)
                Nothing  -> (("", Nothing), "")
    -- so, so much more
```

I still feel dirty.

After all that work, it turns out [there already is][clippings] a Haskell library
to parse these damn files. I felt better when I saw that it doesn't seem like it
works anymore. If I am motivated, I might clean up my copy and submit it to
Hackage so nobody else needs ever again to deal with this stupid file format.

[clippings]: https://hackage.haskell.org/package/clippings

I had now *parsed* the book data, but had yet to actually put it on the website.
None of my initial attempts of manipulating the existing `create` directives did
the trick, [so I dove into the type system][typelove].

[typelove]: /blog/love-types

As far as I can tell, there is *no information* about this on the internet, so
I'll explain what I did -- hopefully as a result, someone in the future will
tear out less of their hair than I did.



### The Theoretical

Your templates can dive into a `$for(list)$` block whenever `list` has been
provided in the `Context` as a `listField`. When specifying the `listField`, you
need to give it a `[Item a]` and a `Context a`, where `Item a` is a unique
handle for the data you want to iterate over, and the context is a way of
getting data out of it.

You'll need to transform any `[a]` you want to iterate over into a `[Item a]`,
which is luckily just `mapM makeItem as`.

Here's the kicker: diving into that `$for(list)$` block *changes* the context,
and once you do, you're have a completely different variable scope. It is
**not** lexically scoped. Right?

```haskell
forM_ clippingsByBook $ \book -> do
    let clipItems = sortBy (comparing dateAdded) book
        curBook = head book
        name = canonicalName curBook

    create [fromFilePath $ "books/" ++ name] $ do
        route $ setExtension "html"
        compile $ do
            let ctx = mconcat
                    [ constField "title"    $ bookName curBook
                    , constField "author"   $ author curBook
                    , listField "clippings"   clippingCtx (mapM makeItem clipItems)
                    , defaultContext
                    ]
            contentCompiler "templates/book.html" ctx
```

The `ctx` here is the context for the embedding page, but the `clippingCtx` is
the context for whenever you're in `$for(clippings)$`. Here's what that context
looks like:

```haskell
liftClip :: (Clipping -> String) -> Item Clipping -> Compiler String
liftClip f = return . f . itemBody

clippingCtx :: Context Clipping
clippingCtx = mconcat
    [ field "body"      $ liftClip contents
    , field "url"       $ liftClip canonicalName
    , field "author"    $ liftClip author
    , field "bookName"  $ liftClip bookName
    ]
```

Types. Blegh.



## Infrastructure

Alright! So now everything was ported, and looking *fresh*. But since I'm
working on all this infrastructure anyway, there was one last piece to do. My
old deploy procedure looked something like this:

1) ssh into the box
2) press up
3) hope I hadn't done anything else on the box to change my history
4) hit enter
5) wait *forever* because Octopress is hella slow

Yuck. Not something that would pass the [Joel Test][joel]. After a little
thinking, I came up with a script that checks if it's on the right box and
performs the deploy if so. If it's not, it ssh's to the box and then quines
itself. I was pretty stoked with it, so I'll include it here since I'm already
tooting my own horn:

[joel]: http://www.joelonsoftware.com/articles/fog0000000043.html

```bash
#!/bin/bash

if [ "$(whoami)" == "server" ]; then
    cd /data/blog
    git pull origin master
    make
else
    echo "deploying on server..."
    ssh server@sandymaguire.me 'bash -s' < $0
fi
```

Genius. And more impressively, it actually works.

Well, at least, in principle. I tried it, and my box exploded because it had ran
out of RAM, because I hadn't set up a swap, because I'm a shitty sysadmin, and
was an even worse one when I set it up four years ago.

After fighting with it for a little bit, I took the nuclear option once again. I
nuked the entire instance. And I also learned I had been paying a bunch of money
to Amazon for other instances I wasn't using. Kinda lame, but better late than
never!

Setting up EC2 is always a bigger pain than one would expect, but in the end,
everything was up and running. But I couldn't launch it, because people would
see the FANCY NEW DESIGN but wouldn't have any fantastic blog post to elucidate
them on what happened.

If you're interested, all the source code for my labors of love can be found on
[GitHub][repo].

[repo]: https://github.com/isovector/we-can-really-solve-this

It's been a busy week. It's been a really busy week. And the worst part is, this
is the only thing I've been working on for that *entire time*. And now it's
done and it's only 2am and I can spend the rest of the night finding something
new and trivial to work on.

*Muahahahaha.*


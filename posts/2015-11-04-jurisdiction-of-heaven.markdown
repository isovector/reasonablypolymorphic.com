---
layout: post
title: The Jurisdiction of Heaven
date: 2015-11-04 08:37
comments: true
tags: haskell, technical, november
---

With yesterdays feels safely out of the way, let's turn our attention back to
the one of the finer things in life: functional programming. If you're a fan of
[the feels][feels], consider [filing a bug][bug] against me; until you do, I'm
going to assume my "peeps" want gnarly haskell stuff.

[feels]: http://sandymaguire.me/tags/feels.html
[bug]: https://github.com/isovector/we-can-really-solve-this/issues/1

You probably don't know it, but I'm writing a [vim clone][eden] in Haskell
(don't worry, this post isn't about vim after this paragraph.) One of the huge
problems with vim that [neovim][neovim] and others are trying to solve is that
the vim codebase is crunchy. [Bram][bram] is very hesitant to merge pull
requests as of late, since the code is such a mess of spaghetti that it's hard
to tell a priori what is going to tear down beloved piece of text-editing
infrastructure.  vim is written in C, and unfortunately C is very amenable to
this kind of situation. In addition, vimscript is [atrocious][vimscript]. This
got me thinking, is there a way we can solve all of these problems
simultaneously?

[neovim]: https://neovim.io/
[bram]: https://en.wikipedia.org/wiki/Bram_Moolenaar
[vimscript]: http://learnvimscriptthehardway.stevelosh.com/chapters/21.html

The answer, as you might expect, is Haskell. We can [exploit the
typesystem][types] to enforce a no-spaghetti policy, and we can rewrite
vimscript as a [domain specific language][dsl] using [free monads][free].
Additionally, Haskell composes well, which [is nice][vim] for implementing a lot
of vim features.

[types]: http://sandymaguire.me/blog/love-types
[dsl]: https://en.wikipedia.org/wiki/Domain-specific_language
[free]: http://dlaing.org/cofun/posts/free_and_cofree.html
[vim]: http://sandymaguire.me/blog/vim-is-not-about-hjkl

Unfortunately, text editors are programs that are chalked full of
state<sup>[citation needed]</sup>, and, as you might remember, Haskell isn't a
huge fan of state. [Lenses][lens] and the `State` monad can alleviate a lot of the
potential issues with trying to work with state, but as I dug deeper and deeper
into what I wanted to accomplish, I quickly realized something. The typesystem
had no mechanism for some of the constraints I wanted to express.

[lens]: https://hackage.haskell.org/package/lens

Consider this. The `State` monad gives us a single datum as state, with which we
need to encapsulate our entire world (which for simplicity we will express in
this post as being of type `data World`.) For our purposes, the world will only
contain the current editor mode, and a collection of buffers:

```haskell
data Buffer =
    Buffer
    { _bFilename :: FilePath
    , _bContent  :: String
    }
makeLenses ''Buffer

data World =
    World
    { _wBuffers :: [Buffer]
    , _wCurrent :: Int
    , _wMode    :: Mode
    }
makeLenses ''World
```

The leading underscores are a convention when working with lenses; `makeLenses`
will generate non-prefixed lenses for each of our records. In order to avoid
spaghetti state (where anybody can do anything to any piece of the state), it
would be nice to be able to be able to restrict functions to a subtree of the
state. A bug in the `change` operator shouldn't be able to close inactive
buffers, for example.

A few minutes of googling later, I found the <tt>Control.Lens.Zoom</tt>[^1]
package, which provides `zoom :: Lens s r -> State r -> State s`[^2]. `zoom`
lifts a `Lens s r` over a `State s` monad, which as you might expect from the
name, behaves just like zooming on a microscope. It lets you look at a deeper
piece of state without needing to pay attention to any of the underlying
context.

[^1]: I absolutely love the naming scheme in the optics packages.
[^2]: This is not its real type, but it's true at least conceptually.

So I hooked up all the necessary infrastructure to use `zoom`, and after some
wrangling, got it to typecheck. I ran it. It worked. But there was a conceptual
problem: zooming turns out to not be what I wanted.

Remember that a `zoom` ignores the underlying context; which means when we zoom
into our `Buffer` record, we can no longer determine what the value of `wMode`
 (the editor mode) is. It turns out `zoom` enforces too strong a constraint --
that the only piece of state you're allowed to read is the bit you're allowed to
write. But this isn't useful to us: we want to be able to *read* the whole
state, but only *write* over the piece we've been restricted to.

Despair. I spent a day trying to hook up some monad transformer stacks of
various combinations of `StateT` and `ReaderT`, hoping to be able to use the
`MonadReader` instance to give me access to the whole state, but `zoom` over the
`MonadState`. I actually managed to get an implementation of this "working", but
it had some issues -- the most egregious of which was that writing state would
desynchronize `get` and `view lensesCurrentlyRestrictedOver <$> ask`, even
though conceptually they should have been the same thing.

Eventually it became painfully clear that `zoom` wasn't the right tool for the
job. Even more painful was that it appeared that no tool was right for the job.
Somehow, nobody had never (published) needing to do what I wanted. I'm pretty
sure about this; I spent *several* hours googling. So I decided to write my own
monad to do what I wanted.

Behold, `Jurisdiction s r a`:

```haskell
type RLens r s = Lens s s r r

newtype Jurisdiction s r a =
    Jurisdiction
    { runJurisdiction' :: RLens r s -> s -> (a, s, RLens r s) }
    deriving (Functor)
```

`Jurisdiction s r` is a monad (which we'll derive in a bit) you can interpret as
a `State r` monad combined with a `Reader s` instance, except that `get` and
`view restrictions <$> ask` always remain synchronized. What this means is that
we can now express our buffer constraint earlier as `Jurisdiction World Buffer`
-- any function whose type is this can read the entire `World`, but only write
to a restricted `Buffer` subset of that world.

This was the first monad I've ever implemented, and conceptually I wasn't really
clear on what I needed to do. So I closely followed Bartosz Milewski's [great
tutorial][tutorial] on implementing the `State` monad, which is pretty much what
I wanted. But because I'm lazy, I used `deriving Functor`. No judgment.

[tutorial]: https://www.fpcomplete.com/school/starting-with-haskell/basics-of-haskell/12-State-Monad

I had to do some mental gymnastics to figure out what this monad actually is,
but the answer is "it's a function `RLens r s -> s -> (a s, RLens r s)` that
composes with itself." Thats why we're going to keep seeing `Jurisdiction $ \l s
->` in the forthcoming code snippets. I guess this makes sense when you look at
its only record, `runJurisdiction'`, but this took me a few days to wrap my mind
around.

I wrote my monad instance by following Milewski's code, and then randomly making
changes until it typechecked with `Jurisdiction s r`. I had originally written a
bunch of text here explaining the code with inline snippets, but that felt
gratuitous, so instead I'll skip past all of the different `Monad*` instances
and jump into the bits that make `Jurisdiction` interesting. If you're curious
in the implementation, you can check it out [on github][source]

[source]: https://github.com/isovector/eden/blob/master/src/Control/Monad/Jurisdiction.hs

However, the `MonadState` instance has some inside baseball that is worth taking
a look at.

```haskell
instance MonadState r (Jurisdiction s r) where
    get   = Jurisdiction $ \l s -> (view l s, s,         l)
    put v = Jurisdiction $ \l s -> ((),       set l v s, l)
```

Recall that the first element of our resulting tuple is the result of our monad,
the second is the state contained in it, and the third is the current lens which
acts as a filter over what we're allowed to touch. `get` pulls our state through
the lens `l` at the very last second, so there's no chance for it to get out of
sync with the state. Likewise, `set` pushes the state through the lens in order
to change its value.

But just because `Jurisdiction` is now a `MonadState` and a `MonadReader` (a
very boring implementation[^3]) doesn't actually mean it's useful yet. So far we
have no means of restricting the scope of our jurisdiction, and without that,
it's just a clunky `State`.  Instead, we introduce `restrict`, which takes a
lens into our restricted scope from our current scope, and a `Jurisdiction` in
that restricted scope, giving us back one in the unrestricted scope.

[^3]: Except that `local` would break our invariant. As an exercise to the
reader, see if you can prove it.

At first glance, this might sound like our types are backwards; relative to the
callee, `restrict` is actually widening their scope. We want to *widen*
restricted scopes so they apply to the *entire* state by the time they've made
it to the point where the user will call `runJurisdiction`. But to calling code,
`restrict` behaves as intended, it takes the current scope and runs something
with less scope. Confused yet? I was the first three times I tried to write this
function.

So let's take a look at the code.

```haskell
restrict :: RLens r' r
         -> Jurisdiction s r' a
         -> Jurisdiction s r  a
restrict l' j = Jurisdiction $ \l s ->
    let (a, s', _) = runJurisdiction' j (l . l') s
     in (a, s', l)
```

The moving part here is is the composition of our lenses. Recall `l` is the
current lens, and `l'` is a lens relative to it. These two lenses therefore
compose, and thusly we get that `restrict` composes with itself for free. This
is a good thing; we'd be in trouble if it didn't. When we run our restricted
`Jurisdiction`, we simply swap out our lens with the composed lens, which will
necessary narrow its scope. Cool!

I want to say here that I checked all the [monad][monadlaws] and
[functor][functorlaws] laws, but I didn't
actually. I couldn't be fucked, but I'd be very surprised if I had violated them
somewhere.

[monadlaws]: https://wiki.haskell.org/Monad_laws
[functorlaws]: https://wiki.haskell.org/Functor

Anyway, everything seems to be in place now, all that's left is a friendly
interface for users to call. Because the lens is an implementation detail, and
we should always start the state with unrestricted access, we hide it.
Coincidentally, this is why our `runJurisdiction'` has had the trailing prime;
my motives are revealed at last!

```haskell
runJurisdiction :: JurisdictionT s s a
                -> s
                -> (a, s)
runJurisdiction j = (\(a, s, l) -> (a, s)) $ runJurisdiction' j id
```

With what seemed like everything in order, I went back to my little vim clone
and went to try it out. Because my underlying state is always going to be
`World`, I made a new type:

```haskell
type Eden r a = Jurisdiction World r a
```

and went on to write a command to put me into insert mode.

```haskell
enterInsertMode :: Eden Mode ()
enterInsertMode = put INSERT
```

The actual test was a little more involved than this (it loaded a prompt and let
you run commands in a big loop), but it is more than enough to demonstrate the
point. What I really like about this is that it's now self-evident that our
constraint is satisfied; `enterInsertMode` has *literally* no way to express
anything except how to change the mode. In my mind, this is a huge win for
functional programming; if you can't express something in the language, there's
*no way* for it to go wrong.

Basking in my success, I went to write `appendToBuffer`:

```haskell
appendToBuffer :: String -> Eden Buffer ()
appendToBuffer str = proclaims bContent (++ str)
```

where `proclaims` is a helper function[^4] which `get`s the current value, applies a
function to it, and `put`s the result back. So far, so good, but then something
bad happened. How do I get a lens to the current buffer?

[^4]: My attempt at naming things with as consistent a metaphor as the lens
people appears like it might have been taken too far.

A quick google search led me to the `ix` function. I hopefully (and naively)
tried `restrict (wBuffers . ix 0)` as a test to see if I could get the first
element of my list, but to no avail. GHC complained that my lens type in
`Jurisdiction` now needed to be an `Applicative`, when a `Functor` had been good
enough before this foray.

So I listened to GHC, and changed all of my constraints to require `Applicative`
lenses. It felt dirty, but as they say, make it typecheck and worry about the
consequences later. I made it typecheck, but the consequences were bad. The
compiler had crunched the types and the results were in: any scope I wanted to
restrict to now needed to be an instance of `Monoid`. The good news was that
`[Buffer]` *is* a `Monoid`. The bad news is that most things aren't.

This was unacceptable. I reverted my changes, and looked for another way.
Expanding out the `RLens [r] r` type, I found that it was `(Functor f) => (r -> f
r) -> [r] -> f [r]`. If only, I thought, I could find a function of this form,
it might behave as the proper lens. There were a few magical hours of trying to
conditionally filter over a list to see if I had the right index, but all was
for naught. In fact, even a trivial implementation of this function is
surprisingly hard. Give it a try; I'd love to see what you come up with.

In a moment of insight, I realized there was a function I had seen during my
perusal of the <tt>Control.Lens</tt> library that I'd forgotten about. It was
called `at`, and I had passed it over because it didn't typecheck with `[a]`.
`at`'s semantics allow it to insert or delete from its container if the key
doesn't exist, or if you return a `None`. Obviously this doesn't work for `[a]`,
as it's impossible to meaningfully insert at index 1000 into an empty list.

But the insight remained. Maybe `_wBuffers :: [Buffer]` had the wrong type! I
eagerly changed it to `_wBuffers :: IntMap Buffer`, and lo and behold, `at`
typechecked, though `appendToBuffer` needed some changes:

```haskell
{-# LANGUAGE LambdaCase #-}
appendToBuffer :: String -> Eden (Maybe Buffer) ()
appendToBuffer str = get >>= put . Just . \case
    -- there's a nicer way to do this but I'm doing it from memory
    Just x  -> x { _bContents = (view bContents x) ++ str }
    Nothing -> emptyBuffer { _bContents = str }
```

All of a sudden, we get some cool magic for free! We can *create* buffers where
none existed before. What might be more interesting is now the user can close
the first buffer but keep the number ordering on the remaining ones. This is
something that vim does, and we've accidentally implemented it by doing no extra
work.

If that's not divine mandate that this project is the right and holy
implementation of vim, I don't know what is.

---

If you're interested in seeing the whole source for this post, following
the development of eden, or contributing yourself, the project can be found
[here][eden].

[eden]: https://github.com/isovector/eden

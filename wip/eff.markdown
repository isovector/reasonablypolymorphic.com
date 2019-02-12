---
layout: post
title: eff
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

Every two weeks in the [functional programming slack][fpchat], we get into a big
argument about "the right way to structure programs." The debate goes around and
around in circles; names get called; feelings get hurt. We never get anywhere,
and the whole process starts again 14 days later. Frankly, it's exhausting.

[fpchat]:

As best I can tell, the community fragments itself along three lines---those who
like [mtl][mtl], those who say ["just do everything in a Reader over IO"][rio],
and those who think [free(r) monads][freer] are worth their weight in gold.

[mtl]:
[rio]:
[freer]:

Being in the latter camp is frustrating, because everyone has strongly negative
opinions on freer monads, and as best I can tell, nobody seems to have ever
actually used them.

As one of the few people in the Haskell-sphere who has actually used freer
monads both *in anger* and *in production,* I wanted to set the record straight.
So today, let's talk about freer monads---what they are, what they buy you, how
they work, what wide-scale adoption could buy us, and yes, I'll talk about what
their weaknesses are.


## What's the Problem?

Before diving in, I think it's worth mentioning where I'm coming from with all
of this. My professional background has significantly shaped what problems I'm
optimizing for solving.

I've worked at some pretty dysfunctional places.

One place in particular had a legacy codebase rapidly put together. It was the
result of an extremely aggressive first-to-market strategy---managed by
non-technical execs and built by contractors who didn't know any Haskell "best
practices." Contractors who wanted to get the thing done as quickly as possible.

TODO talk about jason being the one guy who knew anything

The result was what you'd expect; lots of odd monad stacks and `IO` everywhere.
It was directed by a leadership team that was willing to sacrifice everything in
the name of getting the next release out on time. Which meant that *nobody had
time* to do things the right way---people simply fixed bugs wherever was most
convenient, without any foresight as to how that would affect the future of the
project.

Because `IO` was always available, people started doing bad things with it.
Functions that could have been pure weren't, and then someone thought "hey,
let's just call an external service in the middle of it."

But that got slow, so they built a caching layer that also operated in `IO` and
was entirely localized in this part of the code base.

In its defense, all of this code *was* tested, but only via integration
tests---because nobody knew how to test it in any other way. Everything did `IO`
everywhere; unit testing was more-or-less impossible. But the services had too
many dependencies to do any sort of real integration testing, so someone
copy-and-pasted the `main` function and hacked around in it so that it do the
right thing. They called it `debugMain`.

Whenever you changed `main`, you needed to remember to keep it up to date with
`debugMain`. God help you if you didn't.

TODO: eventually the contractors took off

And then, one day, somebody accidentally introduced a heinous bug. A bug that
essentially started printing money for our customers---at our expense. It was a
mistake that *easily* could have bankrupted the company. Luckily we caught it in
time, but it was a rude wake-up call.

The codebase was too complicated to test thoroughly, and so nobody did. You can
sort of get away with informal reasoning for a while, but sooner or later you're
going to have a problem. Like when you have a codebase on the order of 100k SLOC
that is doing arbitrary IO in arbitrary places.

It was obvious that dramatic refactoring as necessary to get the codebase in
shape, but refactoring an untested system is rarely a wise idea. If you don't
know how the system behaves before the refactor, how will you know if it behaves
the same afterwards? NB: Usually refactoring Haskell is quite a joy, but less so
when everything runs in `IO` to begin with.

Clearly the first step was to write tests for the system. Which meant untangling
a year of rabidly built spaghetti. My first goal was to see if I could run the
service entirely locally, which was much harder than it sounds. For example, the
binary would refuse to start if it couldn't talk to the monitoring API. This is
good in production, but locally I don't give a shit about monitoring. There were
lots of other dependencies that the core logic didn't care about, but got in the
way of testing it regardless.

So I started stubbing out the monitoring machinery. I moved all of the
monitoring stuff into `MonadMonitoring`, and then moved its implementation into
an instance `MonadMonitoring IO`. This worked fine.

But now I wanted to *disable* monitoring, so I made a new monad transformer
`NoMonitoringT` and gave it a vacuous instance of `MonadMonitoring`. But because
our codebase was huge and spanned tens of services written by tens of different
people, it meant I needed a gamut of weird typeclasses for `NoMonitoringT`. I
spent probably a day tracking down and writing all of the instances I needed.

A few days later I got to the point where I could successfully stub out our
monitoring. The next week I spent doing the same thing to stub out our logging.
And then our statistics.

The statistics stuff is actually pretty useful though; especially in a testing
environment. I might not want to log these statistics to our dashboards, but in
the absence of unit tests, it's pretty cool to be able to test "this code path
should attempt to do X exactly 9 times."

Over time, our codebase slowly got to the point where we could actually test
the big changes we were being mandated to make. I haven't touched the codebase
for a few years now, but my understanding is that people are *still* unraveling
this mess of spaghetti.

http://magnus.therning.org/posts/2019-02-02-000-the-readert-design-pattern-or-tagless-final-.html


## Understanding Freer Monads

Traditional monad stacks can be understood as "a small, established toolbox for
side effects." You say "I want some state, so I will add a `StateT`
transformer," with the understanding that *this state is isomorphic to `s -> (s,
a)`.* That means it only ever does *local state.*

I'd suggest we instead think about freer monads as "implementation mix-ins." You
say "I want some state, so I will add a `State` capability." The crucial
difference is that this thing *isn't* just `s -> (s, a)`. It might run locally,
but it also might write to a database. Or it might issue `GET` and `POST` HTTP
requests. Who knows? Who cares?

Most of the people reading the code, most of the time, don't actually care what
are the semantics behind the state. Those semantics are implementation details,
interesting only to the people who care about the implementation. If you're
tracing a program flow, and *aren't* interested in the database side of things,
it's a lot nicer to not need to wade through a bunch of irrelevant database
code.

In short, freer monads let you separate the high-level "what am I trying to do"
from the low-level "how to actually do it."


## What Are Freer Monads?

> Organizations which design systems are constrained to produce designs which
> are copies of the communication structures of these organizations.
>
> -- Melvin Conway

Freer monads are a data representation of your program, which then gets
interpreted at finer-and-finer grained resolution until it's just code.

In other words, they enforce a clean boundary between "saying what you mean" and
"saying how to do it." They let you focus on writing business logic, and
relegate the implementation details to library code.

They give you composable, plug-and-play functionality for transforming a
high-level business logic spec into an actual implementation.

As an example of how this works on a real-life application, let's write a
program that fetches a CSV file from FTP, decrypts it, streams its contents to
an external pipeline, and tracks its stats in Redis.

```haskell
ingest
    :: ( Member (Input Record) r
       , Member (Output Record) r
       , Member (Output Stat) r
       )
    => Eff r ()
ingest = nextInput >>= \case
  Nothing     -> pure ()
  Just record -> do
    output record
    output ProcessedRecordStat
    ingest
```

Done! Pretty easy, hey?

"Now hold on a minute, Sandy! That program you wrote doesn't do what you said!
It doesn't fetch files from FTP, it doesn't decrypt them, and it doesn't do
anything with Redis."

That's right. It doesn't. What this does is exactly what the business people say
they want---it moves data from one place to somewhere else, and lets you know
about it. The rest are implementation details, and aren't relevant to anyone
except the particular engineers responsible for this piece of the system.
Engineers on *other teams in your organization* probably don't even care about
the implementation details.

Written like this it's easy for people to get a sense of what you're trying to
accomplish, without needing to know the nitty-gritty details connection
management, credential management, performance enhancements, error handling, or
database details. It concisely describes the goal, and leaves the irrelevant
bits out of sight and out of mind.

Of course; not *everyone* wants this high-level picture. The people responsible
for this service really and truly do care about how the thing actually works. At
least, at some level of abstraction. The people whose job it is to ingest data
probably care about the service's performance and error handling, but likely
don't have strong opinions on the semantics of fetching data, the encryption
schemes used, the database layout or the choice of the external streaming
pipeline. They probably don't even care that they're ingesting CSV
files---they'd just as happily consume real-time JSON requests.

The goal is to make it easy for people to analyze the pieces they understand and
are responsible for, and hide the noise of the underlying details to someone
else.

So, how to do we get from our high-level description to a real program? We
transform it into a slightly less-high-level program. For example, in order to
get our `Input` of `Record`s, we do actually need to parse a CSV file. You'll
notice that such a problem really doesn't care where the file comes from; it
just wants something to read.

So we write an interpretation of `Input Record` in terms of CSV files. This
suggests we have some sort of `FileProvider` capability, whose job it is to
actually get use the file in question.

```haskell
csvInput
    :: ( Member FileProvider r
       , FromCSVRow i
       )
    => FilePath
    -> Eff (Input i ': r) a
    -> Eff r a
csvInput file m = do
    contents <- getFile file
    let csvData = toList $ parseCSV contents
    handleRelayS csvData (const pure) bind m
  where
    --  bind :: [i] -> Input i x -> (i -> Eff r a) -> Eff r a
    bind (row : rows) NextInput k = k rows $ Just row
    bind rows@[]      NextInput k = k rows Nothing
```

`csvInput` takes a file name, reads that file in terms of some abstract
`FileProvider` capability, and then returns one row of the result every time
`nextInput` is called in the higher-level application.

In effect, we've described what it means to have an `Input` capability in terms
of what it means to have a `FileProvider` capability. Notice that this isn't the
only interpretation of `Input`---it could just as well be implemented by reading
from a streaming source, or by always giving back the same result, or by cycling
through a static list.

The point is that the people writing the service don't care where this data is
coming from. All they care is that they can read it and pipe it to the right
place. In fact, they might want to test that their service works by calling it
on a constant stream of data---so instead they can interpret it purely:

```haskell
pureInput
    :: [i]
    -> Eff (Input i ': r) a
    -> Eff r a
pureInput is = handleRelayS is (const pure) bind
  where
    --  bind :: [i] -> Input i x -> (x -> Eff r a) -> Eff r a
    bind (row : rows) NextInput k = k rows $ Just row
    bind rows@[]      NextInput k = k rows Nothing
```

(for bonus points, you can implement `csvInput` in terms of `pureInput`)

Ok, great! The next step towards a working program is to give an interpretation
of a `FileProvider`. We'll write two---one in terms of a lower level `FTP`
capability, and one in terms of regular everyday `IO`:

```haskell
ftpFileProvider
    :: Member FTP r
    => Eff (FileProvider ': r) a
    -> Eff r a
ftpFileProvider = handleRelay pure bind
  where
    bind (GetFile filename) k = ftpGet filename >>= k

localFileProvider
    :: Member IO r
    => Eff (FileProvider ': r) a
    -> Eff r a
localFileProvider = handleRelay pure bind
  where
    bind (GetFile filename) k =
      send (Data.Bytestring.readFile filename) >>= k
```

For testing, you might also want a mock filesystem---`pureFileProvider :: Map
FilePath ByteString -> _`.

Our program can now provide provide an `Input` capability via a `FileProvider`
capability, via `IO` directly or via an `FTP` capability. You get the picture.

Something we haven't yet handled is file decryption. It's worth noting that this
concern is largely orthogonal to `FileProvider`s; we'd like to be able to mix-in
the capability to deal with encrypted files regardless of what the actual
mechanism for files looks like.

For that, rather than using `handleRelay`, we can instead use `interpose`. While
`handleRelay` provides a capability in terms of *other* capabilities,
`interpose` allows us to provide a capability in terms of itself. Which means,
we can *intercept* calls to a capability without necessarily *handling* them.
Providing decrypted files is a good use case for this---we can intercept
requests for files, and silently decrypt them before giving them back.

```haskell
decryptFileProvider
    :: Member Encryption r
    => Eff (FileProvider ': r) a
    -> Eff (FileProvider ': r) a
decryptFileProvider = interpose pure bind
  where
    -- bind
    --     :: FileProvider x
    --     -> (x -> Eff (FileProvider ': r) a)
    --     -> Eff (FileProvider ': r) a
    bind (GetFile filename) k = do
      cyphertext <- getFile filename
      plaintext  <- decrypt cyphertext
      k plaintext
```

We've gained the ability to inject logic _around_ other interpretations!

Assuming we have an FTP implementation, the `Input` side of the coin is
done. Now to deal with the `Output`s of our ingestion program.









> TODO
> freer monads are better understood as implementation mixins


## Bad Arguments Against Freer Monads

There are several arguments against freer monad, some of which are good, but
most of which are terrible.


### Free Monads Have Bad Performance

*Free* monads suffer from $O(n^2)$ complexity [when used naively][codensity],
which is unfortunately what you get by default.  Freer monads are optimized via
a queue which provides constant-time construction of the default case.

[codensity]:

Yes, freer monads are today somewhere around 30x slower than the equivalent
`mtl` code. That's [roughly on par with Python][speed], but be honest, you've
deployed Python services in the past and they were fast enough. And besides, the
network speed already dominates your performance---you're IO-bound anyway.

If you are writing real-time services maybe this will be an issue, but you're
probably not. And if you are, optimizing Haskell is likely a skill you already
have.

[speed]: https://benchmarksgame-team.pages.debian.net/benchmarksgame/which-programs-are-fast.html

A subtle point to notice is that it's the *monadic* bits of the code that are
30x slower. Not "your program is 30x slower if you import
`Control.Monad.Freer`"---but simply that you will spend more time in binds than
you would in another monad. But your program isn't only monadic in `Eff`; it
also needs to compute expressions and wait for `IO` and all of that stuff.

In short: worry about writing good code first, and deal with performance if it
becomes an issue.


### Purescript Abandoned Eff

Purescript _had a thing called `Eff`_, *but it was not the same as this.* From
the `purescript-eff` [readme][purescript-eff]:

[purescript-eff]: https://github.com/purescript-deprecated/purescript-eff

> As of PureScript 0.12 the default type for handling effects is Effect from
> purescript-effect. This differs from Eff by removing the row of effect types.
> This decision was made as getting the effect rows to line up was sometimes
> quite tricky, without providing a great deal of benefit.
>
> There is also purescript-run now, which uses a similar effect row mechanic
> **but provides true algebraic effect handling.** [emphasis mine]

The `Eff` described in this document is equivalent to `purescript-run`.



## Reasonably Good Arguments Against Freer Monads

### `ContT` is Not an Algebraic Effect

I never really understood this one as stated---I've never actually used `ContT`
in a real monad stack. Have you?

But the sentiment behind this argument is better stated in human as "`Eff` is
unable to model resource bracketing." Which is to say, it's hard to make sure an
`Eff` program calls all of its finalizers.

The good news is that there's a solution if your allocation and cleanup code
only requires `IO`---you can just interpret your entire `Eff` monad directly
into [`ResourceT`][resourcet]:

[resourcet]:

```haskell
bracket
    :: Member (ResourceT IO) r
    => IO a
    -> (a -> IO ())
    -> (a -> Eff r b)
    -> Eff r b
bracket alloc dealloc m = do
  (key, a) <- send $ allocate alloc dealloc
  result   <- m a
  send $ release key
  pure result
```

Specialize `bracket` with your own first two parameters to taste.

More annoyingly, the lack of `ContT`-support means that it's hard to write
effects that imply asynchronicity. That's not to say it's impossible, merely
that it doesn't compose in the same nice way that synchronous effects do.

This is bad, but not disastrously so. You can spin up a thread pool elsewhere,
and add a capability that sends effects to it:

```haskell
data AsyncEff capabilities a where
  AsyncEff
      :: Members capabilities r
      => Eff r a
      -> AsyncEff capabilities ()


startAsyncTaskSlave
    :: Members capabilities r
    => (forall x. Eff r x -> IO x)
    -> IO (InChan (AsyncEff capabilities))
startThreadPool runEff = do
  (in, out) <- newChan 10
  void . async . forever $ do
    m <- readChan out
    async $ runEff m
  pure in


asyncEff
    :: Member IO r
    => InChan (AsyncEff capabilities)
    -> Eff (AsyncEff capabilities ': r) a
    -> Eff r a
asyncEff chan = handleRelay pure bind
  where
    bind eff k = send (writeChan chan eff) >>= k
```

Changing the interface to fill an `MVar` upon completion of the task and make it
available to the original `Eff` program is an exercise left to the reader.


### The Error Messages Are Bad / It's Too Complicated

This has historically been true. While `freer-simple` makes the situation
significantly better, there is definitely room for improvement on this front.

First things first, `Eff` eschews the functional dependencies that `mtl` has.
This means you can have multiple `Writer` effects in the same stack in `Eff`
(but not in `mtl`) at the cost of type-inference.

This is both a feature, and, I won't lie to you, _amazingly annoying at times._
It's a feature because lots of things *are* just `Writer` effects. It's annoying
as heck because *polymorphism makes it eat shit.*

For example, consider the following innocuous looking program:

```haskell
foo :: Member (Writer Int) r => Eff r ()
foo = tell 15
```

Seems fine, right? _Wrong._ Because `15` is actually `fromInteger 15 :: Num a =>
a`, this program will complain about not having a `Writer a` capability. You as
a human know what should happen here, but the compiler is stupid.

Thankfully the solution is simple, but it requires knowing what's wrong and how
to fix it.

```haskell
foo' :: Member (Writer Int) r => Eff r ()
foo' = tell @Int 15
```

If you're going to be doing a lot of work with polymorphic effects, a low-energy
solution is to just provide a locally-bound monomorphic type:

```haskell
foo'' :: Member (Writer Int) r => Eff r ()
foo'' = do
  let tellInt = tell @Int
  tellInt 1
  tellInt 2
  tellInt 3
```

All of this is much less user-friendly than it should be. However, in my
experience, people quickly learn how to debug problems like this. It was enough
to have an "Eff mentor" on our team, whose job it was was to promptly reply to
"I don't know why this doesn't work."


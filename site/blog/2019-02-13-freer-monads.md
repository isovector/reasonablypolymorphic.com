---
layout: post
title: "Freer Monads, More Better Programs"
date: 2019-02-13 11:40
comments: true
tags: freer-monads, extensible-effects
---

If you consider yourself a Haskell beginner, this post is not aimed at you!
You're going to want to understand [`DataKinds`][datakinds] and
[`RankNTypes`][rankn] in order to get things done. Feel free to read anyway, but
keep in mind that the technical solutions described here are tricky.

[datakinds]: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#datatype-promotion
[rankn]: https://downloads.haskell.org/~ghc/latest/docs/html/users_guide/glasgow_exts.html#arbitrary-rank-polymorphism

Every two weeks in the [functional programming slack][fpchat], we get into a big
argument about "the right way to structure programs." The debate goes around and
around in circles; names get called; feelings get hurt. We never get anywhere,
and the whole process starts again 14 days later. Frankly, it's exhausting.

[fpchat]: https://functionalprogramming.slack.com

As best I can tell, the community roughly fragments itself along four
lines---those who like [mtl][mtl], those who say "[just do everything in Reader
IO][rio]", those who like [the three layer cake][cake], and those who think
[free(r) monads][freer-simple] are worth their weight in gold.

[mtl]: https://github.com/haskell/mtl
[rio]: https://www.fpcomplete.com/blog/2017/06/readert-design-pattern
[cake]: https://www.parsonsmatt.org/2018/03/22/three_layer_haskell_cake.html
[freer-simple]: https://github.com/lexi-lambda/freer-simple

Being in the latter camp is frustrating, because everyone has strongly negative
opinions on freer monads, and as best I can tell, nobody seems to have ever
actually used them.

As one of the few people in the Haskell-sphere who has actually used freer
monads in both anger *and* production, I wanted to set the record straight. So
today, let's talk about freer monads---what they are, what they buy you, how
they work, and what wide-scale adoption could buy us. Yes, I'll also talk about
what their weaknesses are.


## Criminally Misunderstood

Freer monads are amazingly powerful. Much more so than I think anyone
realizes---including many of the *people who maintain the libraries.* There's a
lot of free, super-common, crazy-generic functionality that exists, but isn't
anywhere useful.

Freer monads are *so much more* than just a different way of expressing monad
transformers. They're a completely orthogonal means of composition that doesn't
really exist anywhere else in the Haskell ecosystem. By not using them, you are
condemning yourself to writing a significant amount more of significantly more
complicated code than you need to be.

Traditional monad stacks can be understood as "a small, established toolbox for
side effects." You say "I want some state, so I will add a `StateT`
transformer," with the understanding that *this is isomorphic to `s -> (s, a)`.*
That means it only ever does *local state.*

I'd suggest we instead think about freer monads as "implementation mix-ins," or
equivalently, as "compiler passes." Code written against freer monads is
exceptionally high-level and doesn't mix concerns. It's all "business logic",
where the implementation details are handled in layers, each one performed by a
pass that simplifies the representation.

These passes are type-safe, independent and composable. You can mix-and-match
which ones you want---which means testing is often just swapping in a test pass
somewhere near the bottom of the stack. By mocking out different layers, it's
easy to get 100% test coverage, without ever needing to write full-scale
integration tests.

The beauty of this system is that the testability itself also composes. If your
program runs properly under the test pass, and you can prove that both your test
and real pass are also correct, this correctness composes to the entire program.

Having an exceptionally high-level representation of your program's intent is
valuable in another way. Let's take a `State` capability as an example. This
thing might correspond to local state, or a database, or maybe even just
`GET`/`POST` HTTP requests. Who knows? But also, who *cares?*

Most of the people reading the code, most of the time, don't actually care what
are the semantics behind the state. Those semantics are implementation details,
interesting only to the people who care about the implementation. If you're
tracing a program flow, and *aren't* interested in the database side of things,
it's a lot nicer to not need to wade through a bunch of irrelevant database
code.

In short, freer monads let you separate the high-level "what am I trying to do"
from the low-level "how to actually do it."


## Understanding Freer Monads

The `Eff` monad is parameterized by a type-level list of *effects* (or
*capabilities* as I will also call them.) This list is kept polymorphic, and
constraints are enforced on it to ensure that certain effects are available.

For example, the type `StateT String (ReaderT Int IO) Bool` is analogous to `Eff
'[State String, Reader Int, IO] Bool`.

However, the type `(MonadState String m, MonadReader Int m, MonadIO m) => m
Bool` in the `mtl` style also has an analogue: `(Member (State String) r, Member
(Reader Int) r, Member IO r) => Eff r Bool`.

Freer monads are extensible in their effects---that means you can write your
own, and use them completely interchangeably with existing effects. It's trivial
to write a new effect, as they're just GADTs:

```haskell
data Teletype a where
  GetLine ::           Teletype String
  PutLine :: String -> Teletype ()
```

This is all it takes to define a new effect. We now have a `Teletype` effect,
and we can use it after a small amount of ([freely derivable][th]) boilerplate:

[th]: https://hackage.haskell.org/package/freer-simple-1.2.1.0/docs/Control-Monad-Freer-TH.html#v:makeEffect

```haskell
getLine :: Member Teletype r => Eff r String
getLine = send GetLine

putLine :: Member Teletype r => String -> Eff r ()
putLine = send . PutLine
```

Notice that the `a` in `Teletype a` describes *the type you get back from
calling this operation.*

Our new `Teletype` effect corresponds to a domain specific language that can
talk about reading and writing lines on a teletype. It's important to keep in
mind that *there is no meaning associated with this effect.* We get no
semantics, other than an implicit, unverified guarantee that "it probably does
what you expect."

However, this lack of pre-established semantics is a feature, rather than a bug.
The semantics are given after the fact by *interpretations* of the effects. One
interpretation of `Teletype` might be to perform it in `IO`, interacting
directly with the console. Another might be in the form of `POST`ing `putLine`s
to an HTTP server, and returning the results of a `GET` for `getLine`. Another
could just do everything purely in memory.

Freer monads are extensible not only in their effects, but also in their
interpretations. You can give new interpretations for existing effects, and for
your own.

`freer-simple` offers several combinators for constructing new effects, which
we'll explore in the example below.


## Solving Problems with Freer Monads

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
       , Member (Output [Record]) r
       , Member (Output Stat) r
       )
    => Eff r ()
ingest = nextInput >>= \case
  Nothing     -> pure ()
  Just record -> do
    output [record]
    output ProcessedRecordStat
    ingest
```

Done![^2] Pretty easy, hey?

[^2]: `Input` and `Output` are called `Reader` and `Writer` respectively in `freer-simple`. I decided to not use this terminology in order to prevent people from thinking that these are the same monads they're used to.

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
    handleRelayS csvData (const pure) bind m  -- discussed immediately after
  where
    --  bind :: [i] -> Input i x -> ([i] -> x -> Eff r a) -> Eff r a
    bind (row : rows) NextInput k = k rows $ Just row
    bind rows@[]      NextInput k = k rows Nothing
```

`csvInput` takes a file name, reads that file in terms of some abstract
`FileProvider` capability, and then returns one row of the result every time
`nextInput` is called in the higher-level application.

This function is implemented in terms of the [`handleRelayS`][handleRelayS] combinator. You can
think of `handleRelayS` as being parameterized on what `return` and `(>>=)` mean
for the effect being interpreted. In addition, it allows you to thread a piece
of state between binds and the final `return`.

[handleRelayS]: https://hackage.haskell.org/package/freer-simple-1.2.1.0/docs/Control-Monad-Freer-Internal.html#v:handleRelayS

Our implementation of `bind` is to return a new row of the CSV file for every
subsequent call to `nextInput` in the original program. We accomplish this by
returning the head of the list of rows, and then passing the tail as the next
piece of state.

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
    --  bind :: [i] -> Input i x -> ([i] -> x -> Eff r a) -> Eff r a
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
ftpFileProvider = interpret $ \(GetFile filename) ->
  ftpGet filename
```

```haskell
localFileProvider
    :: Member IO r
    => Eff (FileProvider ': r) a
    -> Eff r a
localFileProvider = interpret $ \(GetFile filename) ->
  send $ Data.Bytestring.readFile filename
```

Often you just want to reinterpret an effect in terms of some other effect you
already have (here, `FTP` and `IO`, respectively). In this case, it's sufficient
to just use the `interpret` combinator, which takes implements your
interpretation via a *natural transformation* (something of the form `forall x.
effect x -> Eff r x`.)

For testing, you might also want a mock filesystem---`pureFileProvider :: Map
FilePath ByteString -> _`.

Our program can now provide an `Input` capability via a `FileProvider`
capability, via `IO` directly or via an `FTP` capability. You get the picture.

Something we haven't yet handled is file decryption. It's worth noting that this
concern is largely orthogonal to `FileProvider`s; we'd like to be able to mix-in
the capability to deal with encrypted files regardless of what the actual
mechanism for files looks like.

For that, we're exposed to yet another combinator for writing interpretations;
`interpose`. This combinator allows us to interpret a capability in terms of
itself.  Which means, we can *intercept* calls to a capability without
necessarily *handling* them. Providing decrypted files is a good use case for
this---we can intercept requests for files, and silently decrypt them before
giving them back.

```haskell
decryptFileProvider
    :: Member Encryption r
    => Eff (FileProvider ': r) a
    -> Eff (FileProvider ': r) a
decryptFileProvider =
  interpose $ \(GetFile filename) -> do
    cyphertext <- getFile filename
    decrypt cyphertext
```

We've gained the ability to inject logic _around_ other interpretations!

Assuming we have an FTP implementation, the `Input` side of the coin is
done. Now to deal with the `Output`s of our ingestion program. Remember, we want
to put our records into some external streaming service. We can naively provide
an interpreter that `POST`s these records against our service.

```haskell
postOutput
    :: ( Member HTTP r
       , ToJSON i
       )
    => (i -> HttpRequest 'POST)
    -> Eff (Output i ': r) a
    -> Eff r a
postOutput mkReq = interpret $ \Output i ->
  postHttp $ mkReq i
```

Assuming we have another interpretation `HTTP ~> IO`, we're now good to go!

This works, but accounting comes back a few days later and complains---our
streaming bill is suddenly really big. Apparently we pay *per API call.* Uh oh.
The good news is that the API can handle up to 500 records per `POST`. So, we
can just write another interpret that batches writes before posting them.

```haskell
batch
    :: Int
    -> Eff (Output [i] ': r) a
    -> Eff (Output [i] ': r) a
batch size = interposeS (0, []) finalize bind
  where
    -- finalize :: (Int, [i]) -> a -> Eff (Writer [i] ': r) a
    finalize (_, acc) a = do
      output acc
      pure a

    -- bind
    --     :: (Int, [i])
    --     -> Output [i] x
    --     -> ((Int, [i]) -> x -> Eff (Writer [i] ': r) a)
    --     -> Eff (Writer [i] ': r) a
    bind (nacc, acc) (Output o) k = do
      let no     = length o
          total  = acc <> o
          ntotal = nacc + no
      if (ntotal >= size)
        then do
          let (emit, acc') = splitAt size total
          output emit
          k (ntotal - size, acc') ()
        else k (ntotal, total) ()
```

Cool. Now sticking a `batch 500` pass before `postOutput` will batch all of our
transactions sent to the API. Again, our business-logic doesn't change, because
it need to care about this implementation detail.

We could continue on, but at this point you've seen most of the machinery freer
monads give us. At the end of the day, `main` will end up looking like this:

```haskell
main :: IO ()
main = runM
     . runRedis
     . runFTP
     . runHTTP
     . runEncryption
     . redisOuput @Stat   mkRedisKey
     . postOutput @Record mkApiCall
     . batch      @Record 500
     . ftpFileProvider
     . decryptFileProvider
     . csvInput "file.csv"
     $ ingest
```

It composes nicely, and the compiler will yell at you if you forget to handle
any of required capabilities.

Behavior can be mixed in at will; some other common things you might want
include retry-with-backoff, service discovery, chaos-injection, etc.

Over time and scale, you'll realize that *most of your application code* is the
same crap over and over again---read configuration, connect to a database, deal
with retry, shuffle data from one buffer to another. It's often hard to see this
when it's written with a traditional monad stack, because traditional monad
stacks don't give you the tools to abstract it away.

As you get into the habit of building new effects and interpretations for those
effects, you'll see that new applications are often ready to ship after 25 lines
of business logic and another 25 lines of choosing the right interpretations for
it.


## Bad Arguments Against Freer Monads

There are several arguments against freer monad, some of which are good, but
most of which are terrible.


### Free Monads Have Bad Performance

*Free* monads suffer from $O(n^2)$ complexity [when used naively][codensity],
which is unfortunately what you get by default.  Freer monads are optimized via
a queue which provides constant-time construction of the default case.

[codensity]: https://www.stackage.org/haddock/lts-11.7/kan-extensions-5.1/Control-Monad-Codensity.html#t:Codensity

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

If it makes you feel better, [I recently got a 15% performance increase][perf]
by just more aggressively inlining some of the combinators. This suggests
there's a lot of low-hanging optimization wins for anyone willing to go through
the work to pluck it.

[perf]: https://github.com/lexi-lambda/freer-simple/pull/21

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

[resourcet]: https://www.stackage.org/haddock/lts-13.7/resourcet-1.2.2/Control-Monad-Trans-Resource.html#t:ResourceT

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
       -- ^ An interpretation stack from `Eff r` into `IO`
    -> IO (InChan (AsyncEff capabilities))
startThreadPool runEff = do
  (in, out) <- newChan 10
  void . async . forever $ do
    m <- readChan out
    void . async $ runEff m
  pure in


asyncEff
    :: Member IO r
    => InChan (AsyncEff capabilities)
    -> Eff (AsyncEff capabilities ': r) a
    -> Eff r a
asyncEff chan = interpret $ send . writeChan chan
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
to have an "Eff mentor" on our team, whose job it was to promptly reply to
"I don't know why this doesn't work."


### Jesus Help Me There Are A Lot of Unmaintained Free(r) Monad Packages

Tell me about it. Even as someone who is keenly interested in this stuff I have
a hard time keeping up with the situation.

Here's the skinny---I'd strongly recommend [`freer-simple`][freer-simple].
Failing that, if you *really, really, really* need the performance, take a look
at [`fused-effects`][fused-effects].

[fused-effects]: https://github.com/robrix/fused-effects

Ignore the other ones.[^1]

[^1]: If you're the maintainer of another effects package and want me to include it here, shoot me an email and make an argument!


## Conclusion

Freer monads are *fucking sick* and you'd be foolish to not at least consider
them for your next project.

Furthermore, if you're going to continue insisting on saying that \$technology
is better, I **strongly** encourage you to write up a similar argument stating
your case. My mind is open on this; if you make a strong argument, I'm more than
happy to denounce this article and jump on the \$technology train too.

It's worth keeping in mind that despite our small differences; we're all on the
same team here. We all love functional programming and want to do our best to
make it more popular. As best I can tell, the best strategy towards that aim is
to come up with a consensus on how to do things, and to stop the needless
infighting.

One love.


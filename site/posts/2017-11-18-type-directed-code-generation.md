---
layout: post
title: "Type-Directed Code Generation"
date: 2017-11-18 23:17
comments: true
tags: haskell, design, type trickery
---

> Update 2019-05-30:
>
> Formation finally got around to opensourcing the work done here.
>
> https://github.com/formationai/proto-lens-grpc

---

> aka "Type-Level Icing Sugar"


## Context

At work recently I've been working on a library to get idiomatic gRPC support in
our Haskell project. I'm quite proud of how it's come out, and thought it'd make
a good topic for a blog post. The approach demonstrates several type-level
techniques that in my opinion are under-documented and exceptionally useful in
using the type-system to enforce external contracts.

Thankfully the networking side of the library had already been done for me by
[Awake Security](https://github.com/awakesecurity/gRPC-haskell), but the
interface feels like a thin-wrapper on top of C bindings. I'm *very, very*
grateful that it exists, but I wouldn't expect myself to be able to use it in
anger without causing an uncaught type error somewhere along the line. I'm sure
I'm probably just using it wrong, but the library's higher-level bindings all
seemed to be targeted at Awake's implementation of protobuffers.

We wanted a version that would play nicely with
[proto-lens](https://github.com/google/proto-lens), which, at time of writing,
has no official support for describing RPC services via protobuffers. If you're
not familiar with proto-lens, it generates Haskell modules containing idiomatic
types and lenses for protobuffers, and can be used directly in the build chain.

So the task was to add support to proto-lens for generating interfaces to
RPC services defined in protobuffers.

My first approach was to generate the dumbest possible thing that could work --
the idea was to generate records containing fields of the shape `Request -> IO
Response`. Of course, with a network involved there is a non-negligible chance
of things going wrong, so this interface should expose some means of dealing
with errors. However, the protobuffer spec is agnostic about the actual RPC
backend used, and so it wasn't clear how to continue without assuming anything
about the particulars behind errors.

More worrisome, however, was that RPCs can be marked as streaming -- on the side
of the client, server, or both. This means, for example, that a method marked as
server-streaming has a different interface on either side of the network:

```haskell
serverSide :: Request -> (Response -> IO ()) -> IO ()
clientSide :: Request -> (IO (Maybe Response) -> IO r) -> IO r
```

This is problematic. Should we generate different records corresponding to
which side of the network we're dealing with? An early approach I had was to
parameterize the same record based on which side of the network, and use a type
family to get the correct signature:

```haskell
{-# LANGUAGE DataKinds #-}

data NetworkSide = Client | Server

data MyService side = MyService
  { runServerStreaming :: ServerStreamingType side Request Response
  }

type family ServerStreamingType (side :: NetworkSide) input output where
  ServerStreamingType Server input output =
      input -> (output -> IO ()) -> IO ()

  ServerStreamingType Client input output =
      forall r. input -> (IO (Maybe output) -> IO r) -> IO r
```

This seems like it would work, but in fact the existence of the `forall` on the
client-side is "illegally polymorphic" in GHC's eyes, and it will refuse to
compile such a thing. Giving it up would mean we wouldn't be able to return
arbitrarily-computed values on the client-side while streaming data from the
server. Users of the library might be able to get around it by invoking `IORef`s
or something, but it would be ugly and non-idiomatic.

So that, along with wanting to be backend-agnostic, made this approach a no-go.
Luckily, my brilliant coworker [Judah Jacobson](https://github.com/judah) (who
is coincidentally also the author of proto-lens), suggested we instead generate
metadata for RPC services in proto-lens, and let backend library code figure it
out from there.

With all of that context out of the way, we're ready to get into the actual meat
of the post. Finally.


## Generating Metadata

According to the
[spec](https://developers.google.com/protocol-buffers/docs/reference/proto3-spec),
a protobuffer service may contain zero or more RPC methods. Each method has a
request and response type, either of which might be marked as streaming.

While we could represent this metadata at the term-level, that won't do us any
favors in terms of getting type-safe bindings to this stuff. And so, we instead
turn to `TypeFamilies`, `DataKinds` and `GHC.TypeLits`.

For reasons that will become clear later, we chose to represent RPC services via
types, and methods in those services as symbols (type-level strings). The
relevant typeclasses look like this:

```haskell
class Service s where
  type ServiceName    s :: Symbol

class HasMethod s (m :: Symbol) where
  type MethodInput       s m :: *
  type MethodOutput      s m :: *
  type IsClientStreaming s m :: Bool
  type IsServerStreaming s m :: Bool
```

For example, the instances generated for the RPC service:

```
service MyService {
  rpc BiDiStreaming(stream Request) returns(stream Response);
}
```

would look like this:

```haskell
data MyService = MyService

instance Service MyService where
  type ServiceName    MyService = "myService"

instance HasMethod MyService "biDiStreaming" where
  type MethodInput       MyService "biDiStreaming" = Request
  type MethodOutput      MyService "biDiStreaming" = Response
  type IsClientStreaming MyService "biDiStreaming" = 'True
  type IsServerStreaming MyService "biDiStreaming" = 'True
```

You'll notice that these typeclasses perfectly encode all of the information we
had in the protobuffer definition. The idea is that with all of this metadata
available to them, specific backends can generate type-safe interfaces to
these RPCs. We'll walk through the implementation of the gRPC bindings together.


## The Client Side

The client side of things is relatively easy. We can the `HasMethod` instance
directly:

```haskell
runNonStreamingClient
    :: HasMethod s m
    => s
    -> Proxy m
    -> MethodInput s m
    -> IO (Either GRPCError (MethodOutput s m))
runNonStreamingClient =  -- call the underlying gRPC code

runServerStreamingClient
    :: HasMethod s m
    => s
    -> Proxy m
    -> MethodInput s m
    -> (IO (Either GRPCError (Maybe (MethodOutput s m)) -> IO r)
    -> IO r
runServerStreamingClient =  -- call the underlying gRPC code

-- etc
```

This is a great start! We've got the interface we wanted for the
server-streaming code, and our functions are smart enough to require the correct
request and response types.

However, there's already some type-unsafety here; namely that nothing stops us
from calling `runNonStreamingClient` on a streaming method, or other such silly
things.

Thankfully the fix is quite easy -- we can use type-level equality to force
callers to be attentive to the streaming-ness of the method:


```haskell
runNonStreamingClient
    :: ( HasMethod s m
       , IsClientStreaming s m ~ 'False
       , IsServerStreaming s m ~ 'False
       )
    => s
    -> Proxy m
    -> MethodInput s m
    -> IO (Either GRPCError (MethodOutput s m))

runServerStreamingClient
    :: ( HasMethod s m
       , IsClientStreaming s m ~ 'False
       , IsServerStreaming s m ~ 'True
       )
    => s
    -> Proxy m
    -> MethodInput s m
    -> (IO (Either GRPCError (Maybe (MethodOutput s m)) -> IO r)
    -> IO r

-- et al.
```

Would-be callers attempting to use the wrong function for their method will now
be warded off by the type-system, due to the equality constraints being
unable to be discharged. Success!

The actual usability of this code leaves much to be desired (it requires being
passed a proxy, and the type errors are absolutely *disgusting*), but we'll
circle back on improving it later. As it stands, this code is type-safe, and
that's good enough for us for the time being.


## The Server Side

### Method Discovery

Prepare yourself (but don't panic!): the server side of things is significantly
more involved.

In order to run a server, we're going to need to be able to handle any sort of
request that can be thrown at us. That means we'll need an arbitrary number of
handlers, depending on the service in question. An obvious thought would be to
generate a record we could consume that would contain handlers for every method,
but there's no obvious place to generate such a thing. Recall: proto-lens can't,
since such a type would be backend-specific, and so our only other strategy down
this path would be Template Haskell. Yuck.

Instead, recall that we have an instance of `HasMethod` for every method on
`Service s` -- maybe we could exploit that information somehow? Unfortunately,
without Template Haskell, there's no way to discover typeclass instances.

But that doesn't mean we're stumped. Remember that we control the code
generation, and so if the representation we have isn't powerful enough, we can
change it. And indeed, the representation we have isn't quite enough. We can go
from a `HasMethod s m` to its `Service s`, but not the other way. So let's
change that.

We change the `Service` class slightly:

```haskell
class Service s where
  type ServiceName    s :: Symbol
  type ServiceMethods s :: [Symbol]
```

If we ensure that the `ServiceMethods s` type family always contains an element
for every instance of `HasService`, we'll be able to use that info to discover
our instances. For example, our previous `MyService` will now get generated
thusly:

```haskell
data MyService = MyService

instance Service MyService where
  type ServiceName    MyService = "myService"
  type ServiceMethods MyService = '["biDiStreaming"]

instance HasMethod MyService "biDiStreaming" where
  type MethodInput       MyService "biDiStreaming" = Request
  type MethodOutput      MyService "biDiStreaming" = Response
  type IsClientStreaming MyService "biDiStreaming" = 'True
  type IsServerStreaming MyService "biDiStreaming" = 'True
```

and we would likewise add the `m` for any other `HasMethod MyService m`
instances if they existed.

This seems like we can now use `ServiceMethods s` to get a list of methods, and
then somehow type-level `map` over them to get the `HasMethod s m` constraints
we want.

And we almost can, except that we haven't told the type-system that
`ServiceMethods s` relates to `HasService s m` instances in this way. We can add
a superclass constraint to `Service` to do this:

```haskell
class HasAllMethods s (ServiceMethods s) => Service s where
  -- as before
```

But was is this `HasAllMethods` thing? It's a specialized type-level `map` which
turns our list of methods into a bunch of constraints proving we have `HasMethod
s m` for every `m` in that promoted list.

```haskell
class HasAllMethods s (xs :: [Symbol])

instance HasAllMethods s '[]
instance (HasMethod s x, HasAllMethods s xs) => HasAllMethods s (x ': xs)
```

We can think of `xs` here as the list of constraints we want. Obviously if we
don't want any constraints (the `'[]` case), we trivially have all of them. The
other case is induction: if we have a non-empty list of constraints we're
looking for, that's the same as looking for the tail of the list, and having the
constraint for the head of it.

Read through these instances a few times; make sure you understand the approach
before continuing, because we're going to keep using this technique in scarier
and scarier ways.

With this `HasAllMethods` superclass constraint, we can now convince ourselves
(and, more importantly, GHC), that we can go from a `Service s` constraint to
all of its `HasMethod s m` constraints. Cool!


## Typing the Server

We return to thinking about how to actually run a server. As we've discussed,
such a function will need to be able to handle every possible method, and,
unfortunately, we can't pack them into a convenient data structure.

Our actual implementation of such a thing might take a list of handlers. But
recall that each handler has different input and output types, as well as
different shapes depending on which bits of it are streaming. We can make this
approach work by
[existentializing](http://reasonablypolymorphic.com/existentialization/) away
all of the details.

While it works as far as the actual implementation of the underlying gRPC goes,
we're left with a great sense of uneasiness. We have no guarantees that we've
provided a handler for every method, and the very nature of existentialization
means we have absolutely no guarantees that any of these things are the right
ype.

Our only recourse is to somehow use our `Service s` constraint to put a prettier
facade in front of this ugly-if-necessary implementation detail.

The actual interface we'll eventually provide will, for example, for a service
with two methods, look like this:

```haskell
runServer :: HandlerForMethod1 -> HandlerForMethod2 -> IO ()
```

Of course, we can't know a priori how many methods there will be (or what type
their handlers should have, for that matter). We'll somehow need to extract this
information from `Service s` -- which is why we previously spent so much effort
on making the methods discoverable.

The technique we'll use is the same one you'll find yourself using again and
again when you're programming at the type-level. We'll make a typeclass with an
associated type family, and then provide a base case and an induction case.

```haskell
class HasServer s (xs :: [Symbol]) where
  type ServerType s xs :: *
```

We need to make the methods `xs` explicit as parameters in the typeclass, so
that we can reduce them. The base case is simple -- a server with no more
handlers is just an IO action:

```haskell
instance HasServer s '[] where
  type ServerType s '[] = IO ()
```

The induction case, however, is much more interesting:

```haskell
instance ( HasMethod s x
         , HasMethodHandler s x
         , HasServer s xs
         ) => HasServer s (x ': xs) where
  type ServerType s (x ': xs) = MethodHandler s x -> ServerType s xs
```

The idea is that as we pull methods `x` off our list of methods to handle, we
build a function type that takes a value of the correct type to handle method
`x`, which will take another method off the list until we're out of methods to
handle. This is exactly a type-level fold over a list.

The only remaining question is "what is this `MethodHandler` thing?" It's going
to have to be a type family that will give us back the correct type for the
handler under consideration. Such a type will need to dispatch on the streaming
variety as well as the request and response, so we'll define it as follows, and
go back and fix `HasServer` later.

```haskell
class HasMethodHandler input output (cs :: Bool) (ss :: Bool) where
  type MethodHandler input output cs ss :: *
```

`cs` and `ss` refer to whether we're looking for client-streaming and/or
server-streaming types, respectively.

Such a thing could be a type family, but isn't because we'll need its class-ness
later in order to actually provide an implementation of all of this stuff. We
provide the following instances:

```haskell
-- non-streaming
instance HasMethodHandler input output 'False 'False where
  type MethodHandler input output 'False 'False =
    input -> IO output

-- server-streaming
instance HasMethodHandler input output 'False 'True where
  type MethodHandler input output 'False 'True =
    input -> (output -> IO ()) -> IO ()

-- etc for client and bidi streaming
```

With `MethodHandler` now powerful enough to give us the types we want for
handlers, we can go back and fix `HasServer` so it will compile again:

```haskell
instance ( HasMethod s x
         , HasMethodHandler (MethodInput       s x)
                            (MethodOutput      s x)
                            (IsClientStreaming s x)
                            (IsServerStreaming s x)
         , HasServer s xs
         ) => HasServer s (x ': xs) where
  type ServerType s (x ': xs)
      = MethodHandler (MethodInput       s x)
                      (MethodOutput      s x)
                      (IsClientStreaming s x)
                      (IsServerStreaming s x)
     -> ServerType s xs
```

It's not pretty, but it works! We can convince ourselves of this by asking ghci:

```
ghci> :kind! ServerType MyService (ServiceMethods MyService)

(Request -> (Response -> IO ()) -> IO ()) -> IO () :: *
```

and, if we had other methods defined for `MyService`, they'd show up here with
the correct handler type, in the order they were listed in `ServiceMethods
MyService`.


## Implementing the Server

Our `ServerType` family now expands to a function type which takes a handler
value (of the correct type) for every method on our service. That turns out to
be more than half the battle -- all we need to do now is to provide a value of
this type.

The generation of such a value is going to need to proceed in perfect lockstep
with the generation of its type, so we add to the definition of `HasServer`:

```haskell
class HasServer s (xs :: [Symbol]) where
  type ServerType s xs :: *
  runServerImpl :: [AnyHandler] -> ServerType s xs
```

What is this `[AnyHandler]` thing, you might ask. It's an explicit accumulator
for existentialized handlers we've collected during the fold over `xs`. It'll
make sense when we look at the induction case.

For now, however, the base case is trivial as always:

```haskell
instance HasServer s '[] where
  type ServerType s '[] = IO ()
  runServerImpl handlers = runGRPCServer handlers
```

where `runGRPCServer` is the underlying server provided by Awake's library.

We move to the induction case:

```haskell
instance ( HasMethod s x
         , HasMethodHandler (MethodInput       s x)
                            (MethodOutput      s x)
                            (IsClientStreaming s x)
                            (IsServerStreaming s x)
         , HasServer s xs
         ) => HasServer s (x ': xs) where
  type ServerType s (x ': xs)
      = MethodHandler (MethodInput       s x)
                      (MethodOutput      s x)
                      (IsClientStreaming s x)
                      (IsServerStreaming s x)
     -> ServerType s xs
  runServerImpl handlers f = runServerImpl (existentialize f : handlers)
```

where `existentialize` is a new class method we add to `HasMethodHandler` We
will elide it here because it is just a function `MethodHandler i o cs mm ->
AnyHandler` and is not particularly interesting if you're familiar with
existentialization.

It's evident here what I meant by `handlers` being an explicit accumulator --
our recursion adds the parameters it receives into this list so that it can pass
them eventually to the base case.

There's a problem here, however. Reading through this implementation of
`runServerImpl`, you and I both know what the right-hand-side means,
unfortunately GHC isn't as clever as we are. If you try to compile it right now,
GHC will complain about the non-injectivity of `HasServer` as implied by the
call to `runServerImpl` (and also about `HasMethodHandler` and `existentialize`,
but for the exact same reason.)

The problem is that there's nothing constraining the type variables `s` and `xs`
on `runServerImpl`. I always find this error confusing (and I suspect everyone
does), because in my mind it's perfectly clear from the `HasServer s xs` in the
instance constraint. However, because `SeverType` is a type family without any
injectivity declarations, it means we can't learn `s` and `xs` from `ServerType
s xs`.

Let's see why. For a very simple example, let's look at the following type
family:

```haskell
type family NotInjective a where
  NotInjective Int  = ()
  NotInjective Bool = ()
```

Here we have `NotInjective Int ~ ()` and `NotInjective Bool ~ ()`, which means
even if we know `NotInjective a ~ ()` it doesn't mean that we know what `a` is
-- it could be either `Int` or `Bool`.

This is the exact problem we have with `runServerImpl`: even though we know what
type `runServerImpl` has (it must be `ServerType s xs`, so that the type on the
left-hand of the equality is the same as on the right), that doesn't mean we
know what `s` and `xs` are! The solution is to explicitly tell GHC via a type
signature or type application:

```haskell
instance ( HasMethod s x
         , HasMethodHandler (MethodInput       s x)
                            (MethodOutput      s x)
                            (IsClientStreaming s x)
                            (IsServerStreaming s x)
         , HasServer s xs
         ) => HasServer s (x ': xs) where
  type ServerType s (x ': xs)
      = MethodHandler (MethodInput       s x)
                      (MethodOutput      s x)
                      (IsClientStreaming s x)
                      (IsServerStreaming s x)
     -> ServerType s xs
  runServerImpl handlers f = runServerImpl @s @xs (existentialize f : handlers)
```

(For those of you playing along at home, you'll need to type-apply the monstrous
`MethodInput` and friends to the `existentialize` as well.)

And finally, we're done! We can slap a prettier interface in front of this
`runServerImpl` to fill in some of the implementation details for us:

```haskell
runServer
    :: forall s
     . ( Service s
       , HasServer s (ServiceMethods s)
       )
    => s
    -> ServerType s (ServiceMethods s)
runServer _ = runServerImpl @s @(ServiceMethods s) []
```

Sweet and typesafe! Yes!


## Client-side Usability

Sweet and typesafe all of this might be, but the user-friendliness on the
client-side leaves a lot to be desired. As promised, we'll address that now.


### Removing Proxies

Recall that the `runNonStreamingClient` function and its friends require a
`Proxy m` parameter in order to specify the method you want to call. However,
`m` has kind `Symbol`, and thankfully we have some new extensions in GHC for
turning `Symbol`s into values.

We can define a new type, isomorphic to `Proxy`, but which packs the fact that
it is a `KnownSymbol` (something we can turn into a `String` at runtime):

```haskell
data WrappedMethod (sym :: Symbol) where
  WrappedMethod :: KnownSymbol sym => WrappedMethod sym
```

We change our `run*Client` friends to take this `WrappedMethod m` instead of the
`Proxy m` they used to:

```haskell
runNonStreamingClient
    :: ( HasMethod s m
       , IsClientStreaming s m ~ 'False
       , IsServerStreaming s m ~ 'False
       )
    => s
    -> WrappedMethod m
    -> MethodInput s m
    -> IO (Either GRPCError (MethodOutput s m))
```

and, with this change in place, we're ready for the magic syntax I promised
earlier.


```haskell
import GHC.OverloadedLabel

instance ( KnownSymbol sym
         , sym ~ sym'
         ) => IsLabel sym (WrappedMethod sym') where
  fromLabel _ = WrappedMethod
```

This `sym ~ sym'` thing is known as the [constraint trick for
instances](http://chrisdone.com/posts/haskell-constraint-trick), and is
necessary here to convince GHC that this can be the only possible instance of
`IsLabel` that will give you back `WrappedMethod`s.

Now turning on the `{-# LANGUAGE OverloadedLabels #-}` pragma, we've changed the
syntax to call these client functions from the ugly:

```haskell
runBiDiStreamingClient MyService (Proxy @"biDiStreaming")
```

into the much nicer:

```haskell
runBiDiStreamingClient MyService #biDiStreaming
```


### Better "Wrong Streaming Variety" Errors

The next step in our journey to delightful usability is remembering that the
users of our library are only human, and at some point they are going to call
the wrong `run*Client` function on their method with a different variety of
streaming semantics.

At the moment, the errors they're going to get when they try that will be a few
stanza long, the most informative of which will be something along the lines of
`unable to match 'False with 'True`. Yes, it's technically correct, but it's
entirely useless.

Instead, we can use the `TypeError` machinery from `GHC.TypeLits` to make these
error messages actually helpful to our users. If you aren't familiar with it, if
GHC ever encounters a `TypeError` constraint it will die with a error message of
your choosing.

We will introduce the following type family:

```haskell
type family RunNonStreamingClient (cs :: Bool) (ss :: Bool) :: Constraint where
  RunNonStreamingClient 'False 'False = ()
  RunNonStreamingClient 'False 'True = TypeError
      ( Text "Called 'runNonStreamingClient' on a server-streaming method."
   :$$: Text "Perhaps you meant 'runServerStreamingClient'."
      )
  RunNonStreamingClient 'True 'False = TypeError
      ( Text "Called 'runNonStreamingClient' on a client-streaming method."
   :$$: Text "Perhaps you meant 'runClientStreamingClient'."
      )
  RunNonStreamingClient 'True 'True = TypeError
      ( Text "Called 'runNonStreamingClient' on a bidi-streaming method."
   :$$: Text "Perhaps you meant 'runBiDiStreamingClient'."
      )
```

The `:$$:` type operator stacks message vertically, while `:<>:` stacks it
horizontally.

We can change the constraints on `runNonStreamingClient`:

```haskell
runNonStreamingClient
    :: ( HasMethod s m
       , RunNonStreamingClient (IsClientStreaming s m)
                               (IsServerStreaming s m)
       )
    => s
    -> WrappedMethod m
    -> MethodInput s m
    -> IO (Either GRPCError (MethodOutput s m))
```

and similarly for our other client functions. Reduction of the resulting
boilerplate is left as an exercise to the reader.

With all of this work out of the way, we can test it:

```haskell
runNonStreamingClient MyService #biDiStreaming
```

```
Main.hs:45:13: error:
    • Called 'runNonStreamingClient' on a bidi-streaming method.
      Perhaps you meant 'runBiDiStreamingClient'.
    • In the expression: runNonStreamingClient MyService #bidi
```

Amazing!


### Better "Wrong Method" Errors

The other class of errors we expect our users to make is to attempt to call a
method that doesn't exist -- either because they made a typo, or are forgetful
of which methods exist on the service in question.

As it stands, users are likely to get about six stanzas of error messages, from
`No instance for (HasMethod s m)` to `Ambiguous type variable 'm0'`, and
other terrible things that leak our implementation details. Our first thought
might be to somehow emit a `TypeError` constraint if we *don't* have a
`HasMethod s m` instance, but I'm not convinced such a thing is possible.

But luckily, we can actually do better than any error messages we could produce
in that way. Since our service is driven by a value (in our example, the data
constructor `MyService`), by the time things go wrong we *do* have a `Service s`
instance in scope. Which means we can look up our `ServiceMethods s` and given
some helpful suggestions about what the user probably meant.

The first step is to implement a `ListContains` type family so we can determine
if the method we're looking for is actually a real method.

```haskell
type family ListContains (n :: k) (hs :: [k]) :: Bool where
  ListContains n '[]       = 'False
  ListContains n (n ': hs) = 'True
  ListContains n (x ': hs) = ListContains n hs
```

In the base case, we have no list to look through, so our needle is trivially
not in the haystack. If the head of the list is the thing we're looking for,
then it must be in the list. Otherwise, take off the head of the list and
continue looking. Simple really, right?

We can now use this thing to generate an error message in the case that the
method we're looking for is not in our list of methods:

```haskell
type family RequireHasMethod s (m :: Symbol) (found :: Bool) :: Constraint where
  RequireHasMethod s m 'False = TypeError
      ( Text "No method "
   :<>: ShowType m
   :<>: Text " available for service '"
   :<>: ShowType s
   :<>: Text "'."
   :$$: Text "Available methods are: "
   :<>: ShowType (ServiceMethods s)
      )
  RequireHasMethod s m 'True = ()
```

If `found ~ 'False`, then the method `m` we're looking for is not part of the
service `s`. We produce a nice error message informing the user about this
(using `ShowType` to expand the type variables).

We will provide a type alias to perform this lookup:

```haskell
type HasMethod' s m =
  ( RequireHasMethod s m (ListContains m (ServiceMethods s)
  , HasMethod s m
  )
```

Our new `HasMethod' s m` has the same shape as `HasMethod`, but will expand to
our custom type error if we're missing the method under scrutiny.

Replacing all of our old `HasMethod` constraints with `HasMethod'` works
fantastically:

```
Main.hs:54:15: error:
    • No method "missing" available for service 'MyService'.
      Available methods are: '["biDiStreaming"]
```

Damn near perfect! That list of methods is kind of ugly, though, so we can write
a quick pretty printer for showing promoted lists:

```haskell
type family ShowList (ls :: [k]) :: ErrorMessage where
  ShowList '[]  = Text ""
  ShowList '[x] = ShowType x
  ShowList (x ': xs) = ShowType x :<>: Text ", " :<>: ShowList xs
```

Replacing our final `ShowType` with `ShowList` in `RequireHasMethod` now gives
us error messages of the following:

```
Main.hs:54:15: error:
    • No method "missing" available for service 'MyService'.
      Available methods are: "biDiStreaming"
```

Absolutely gorgeous.


## Conclusion

This is where we stop. We've used type-level metadata to generate client- and
server-side bindings to an underlying library. Everything we've made is entirely
typesafe, and provides gorgeous, helpful error messages if the user does
anything wrong. We've found a practical use for many of these seemingly-obscure
type-level features, and learned a few things in the process.

In the words of my coworker [Renzo Carbonara](https://ren.zone/articles/opaleye-sot)[^1]:

[^1]: Whose article "Opaleye's sugar on top" was a strong inspiration on me, and
  subsequently on this post.

"It is up to us, as people who understand a problem at hand, to try and teach
the type system as much as we can about that problem. And when we don’t
understand the problem, talking to the type system about it will help us
understand. Remember, the type system is not magic, it is a logical reasoning
tool."

This resounds so strongly in my soul, and maybe it will in yours too. If so, I
encourage you to go forth and find uses for these techniques to improve the
experience and safety of your own libraries.


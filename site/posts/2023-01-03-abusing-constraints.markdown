---
layout: post
title: Abusing Constraints for Automatic Documentation
date: 2023-01-03 00:26
comments: true
tags: haskell
---

## Constraints

[At work I was recently tasked with figuring out what API calls our program
makes](https://github.com/wireapp/wire-server/pull/2950), and more
interestingly, which code-paths lead to those API calls. Determining this by
hand is tedious and error-prone, and worse, doesn't stay up to date with code
changes. Instead, let's see how we can use the type system to eliminate the
pain.

The existing code was organized around a class `HasAPI` that looks something
like this:

```haskell
type  HasAPI :: Service -> Symbol -> Constraint
class HasAPI srv name where
  type APICall srv name
  callAPI :: APICall srv name
```

Here, `HasAPI` is a type class with an associated type family `APICall` which
gives the type for making the call. For example, there might be an instance:

```haskell
instance HasAPI ShoutService "shout" where
  type APICall ShoutService "shout" = String -> IO String
  callAPI str = pure $ fmap toUpper str
```

This is a silly example --- the real codebase makes actual API calls --- but it
serves for demonstration.

Our goal is to document every codepath that makes any use of `callAPI`, in some
sense, "infecting" every path with some marker of that fact. This is a common
experience to Haskell programmers; in fact, `IO` has this same pattern of
infectiousness. Whenever you make a function perform IO, every type in the
callstack needs to document the fact it performs `IO`. This is the inspiration
we will take, except that changing types is extremely expensive. What if we
pushed a constraint around instead?

### Propagating Constraints

The trick is to define a new class, of the same shape as `HasAPI`:

```haskell
type  CallsAPI :: Service -> Symbol -> Constraint
class CallsAPI srv name
```

but crucially, we give `CallsAPI` *no instances.* On first blush, this seems
insane: why introduce a class with no methods and no instances? Having no
methods means it can't do anything useful. Having no instances means GHC can
never eliminate the constraint, and thus must propagate it upwards. This is the
infectiousness we want; any function which makes an API call must document that
fact in its type --- failure to do so will result in GHC failing to compile with
the message `No instance for (CallsAPI srv name)`.

The trick now is to ensure that `callsAPI` produces a `CallsAPI` constraint.
The easy way to do this is a little renaming to ensure existing polymorphic code
continues work:

```haskell
type  UnsafeHasAPI :: Service -> Symbol -> Constraint
class UnsafeHasAPI srv name where
  type APICall srv name
  unsafeCallAPI :: APICall srv name

type HasAPI :: Service -> Symbol -> Constraint
type HasAPI = (UnsafeHasAPI srv name, CallsAPI srv name)

callAPI
  :: forall srv name
   . HasAPI srv name
  => APICall srv name
callAPI = unsafeCallAPI
```

Any code written against the old `HasAPI` constraint will continue to work
(modulo the instance definitions,) but concrete calls to `callAPI` now result in
a dangling, unsatisfiable `CallsAPI` constraint. You'll need to go through the
codebase now, and document every transitive call to the API with matching
`CallsAPI` constraints. Thankfully, HLS can help with this task: it will
underline the missing cases, and suggest a code action that will automatically
add these constraints to the type. Rinse and repeat, until every code path is
documented.

Great success! We have automatically found every codepath that makes an API
call, and forced them to document that fact. Better yet, we have solved the
problem once and for all; our coworkers also must document any new API calls
they make, lest their code not compile. It seems like we're done!

Except for one fact: GHC will rudely refuse to compile our project, even if we
correctly track all of our API calls. The problem of course, is that all we have
managed to do is force `main` to collect every `CallsAPI` constraint. But GHC
will still complain `No instance for (CallsAPI srv name)`. Of course, you could
just give an orphan instance in the same module that defines `main`, which would
work, but this doesn't give you any sort of *external documentation.* It's nice
when you read the code, but it doesn't help the business people.


## Solving The Unsolvable

A better approach here is to selectively solve the `CallsAPI` constraints,
which we can do with some Haskell dark magic. The `Dict` type captures a
constraint, giving us a convenient way to manipulate constraints:

```haskell
type Dict :: Constraint -> Type
data Dict c where
  Dict :: c => Dict c
```

We can write an eliminator to bring the `c` from a `Dict c` into scope, which,
importantly, allows us to solve otherwise-unsolved constraints:

```haskell
(\\) :: (c => r) -> Dict c -> r
f \\ Dict = f
```

If we can get our hands on a `Dict (CallsAPI Srv Name)`, we can use `(\\)`
to convince GHC to compile our program.

GHC is happy to give us dictionaries for constraints it knows about:

```haskell
showIntDict :: Dict (Show Int)
showIntDict = Dict
```

but unfortunately, refuses to give us dictionaries for unsolved constraints:

```haskell
callsAPIDict :: forall srv name. Dict (CallsAPI srv name)
callsAPIDict = Dict

-- Error: No instance for (CallsAPI srv name)
```

It seems like we're just as stuck, but we have a trick up our sleeve. The first
step is to define another class with an instance in scope. GHC will happily give
us a dictionary for such a thing:

```haskell
class Trivial
instance Trivial

trivialDict :: Dict Trivial
trivialDict = Dict
```

and now for something naughty:

```haskell
callsAPIDict :: forall srv name. Dict (CallsAPI srv name)
callsAPIDict = unsafeCoerce trivialDict
```

Behind the scenes, GHC compiles classes into records, instances into values of
these records, and replaces wanted constraints with function arguments taking
those records. By ensuring that `Trivial` and `CallsAPI` are both empty classes,
with no methods or super-classes, we can be certain the generated records for
these classes will be identical, and thus that it is OK to coerce one into the
other.

Armed with `withDict` and `callsAPIDict`, we can play the part of the constraint
solver and satisfy constraints ourself. GHC will happily compile the following
example:

```haskell
ex :: HasAPI ShoutService "shout" => IO String
ex = callAPI @ShoutService @"shout" "hello world"

-- Look ma, no HasAPI constraint!
test :: IO String
test = ex \\ callsAPIDict @ShoutService @"shout"
```

So that's the rough technique. But how do we actually use it in anger?


### Automatically Documenting the Server

Our actual use case at work is to add these API calls to our swagger
documentation. Swagger is this automatically generated manifest of an API
surface; we want to document the fact that some API calls might call other ones.
Our server is one big servant application, and servant is extensible. So the
real technique is to build a servant combinator that eliminates `HasAPI`
constraints when you document them in the API definition.

Getting into the nitty gritty bits of servant is beyond the scope of this post,
but we can sketch the idea. Servant APIs use the type-level `(:>)` operator to
combine information about an endpoint. For example, we might expose another
service:

```haskell
type ServantAPI = "api" :>
  "echo"
      :> ReqBody '[JSON] String
      :> Get '[JSON] String
```

This definition states that we have a REST server with a single route,
`api/echo` which responds to `POST` requests, returning a JSON-encoded string,
which takes a JSON-encoded string as the request body.

A servant server for `ServantAPI` would have type `Server ServantAPI`, where
`Server` is a type family given by `HasServer`. Evaluating the type family
results in `String -> Handler String`, so in order to implement this server, we
would need to provide a function of that type.

Let's implement our server endpoint:

```haskell
echo
    :: CallsAPI ShoutService "shout"
    => String
    -> Handler String
echo str = liftIO $ callAPI @ShoutService @"shout" str
```

Unfortunately, due to our earlier work, we can't eliminate the `CallsAPI`
constraint, and thus we can't actually use `echo` as the handler for our
endpoint.

It's important to note that servant's DSL is extensible, and we can add our own
machinery here. The first step is to build a type that we can use in servant:

```haskell
type MakesAPICall :: Service -> Symbol -> Type
data MakesAPICall srv name
```

We can now build a second version of `ServantAPI`:

```haskell
type ServantAPI = "api" :>
  "echo"
      :> MakesAPICall ShoutService "shout"
      :> ReqBody '[JSON] String
      :> Get '[JSON] String
```

In order to actually run our endpoint, we need to give an instance of
`HasServer` for our new `MakesAPICall` combinator:

```haskell
instance HasServer api ctx
      => HasServer (MakesAPICall srv name :> api) ctx
         where
  type ServerT (MakesAPICall srv name :> api) m =
    Dict (CallsFed srv name) -> ServerT api m
  route _ ctx f =
    route (Proxy @api) ctx $ fmap ($ callsAPIDict @srv @name) f
```

The `ServerT` instance here adds a `Dict (CallsFed srv name)` to the type of
the handler required to satisfy this endpoint, while `route` automatically fills
in the dictionary whenever the handler needs to be run. In an ideal world,
we could give our `ServerT` instance as:

```haskell
  type ServerT (MakesAPICall srv name :> api) m =
    CallsFed srv name => ServerT api m
```

but GHC doesn't let us use quantified types on the right-hand sides of type
families, so this is unfortunately a no-go. Playing games with `Dict` instead is
the best approach I've found here, but I'd love to hear if anyone has a better
idea.

We still can't use `echo` as a handler, but we can use `makesCall echo` as one,
where `makesCall` is given as:

```haskell
makesCall :: (c => r) -> Dict c -> r
makesCall = (\\)
```

Servers that document their API calls via `MakesAPICall` and which wrap their
handlers with `makesCall` can now eliminate `CallsFed` constraints. Since this
is the only way of eliminating `CallsFed` constraints, we can be sure that every
API call is correctly documented in the servant DSL!

The final step here is to add an instance of `HasSwagger (MakesAPICall srv name
:> api)`, but the details are gory and devoid of educational value. Suffice it
to say that this instance was written, and now we have automatically generated
JSON documentation describing which server endpoints make which other API calls.
This documentation is guaranteed to be correct, because updating it is the only
way to convince GHC to compile your code.


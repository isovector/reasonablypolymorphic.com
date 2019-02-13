---
layout: post
title: Same Same But Different
date: TO_BE_DETERMINED
comments: true
tags: foo, bar
---

I've just returned from [ZuriHac 2018][zurihac], a conglomeration of nerds
possibly unsurpassed by any event in history thus far. It was three days chocked
full of Haskell hacking, interesting discussions, Ed Kmett pulling superhuman
stunts of lecturing about category theory, and more Nix-aficionados than a
mother could love. Shout-outs to Simpleflips, and to the organizers who pulled
off such an amazing conference!

[zurihac]:

I came in armed with the plan to convince GHC that `a` and `Identity a` are the
same thing, and can thus be used interchangeably. Everyone I talked to was
convinced it was a Bad Idea™, but I'm not one to let bad ideas get in the way of
a good time.

Having played a little bit with constraint solving via typechecker plugins in
[constraints-emerge][emerge], I "knew" that that path was a no-go. As a result,
I sunk my teeth into [Equality proofs and deferred type errors: A compiler
pearl][defer-type-errors] which describes generating fake coercions that fail at
runtime in order to implement `-fdefer-type-errors`. It seemed like a good
starting point.

[emerge]:
[defer-type-errors]:

That being said, I was all too aware that my goal was something that would
*never ever* be implemented upstream in the compiler, and so I had to tread
carefully in GHC territory. Any changes to the compiler would need to be small
and well-argued, and "it sounded like a giggle" isn't the best argument in the
world. Having any chance whatsoever of this being successful was going to need
to live in userland, which meant GHC plugins.

The equality `a ~ Identity a` is certainly insoluble (unable to be solved) in
Haskell, *and* is an occurs check. So GHC's `isInsolubleOccursCheck` function
seemed like it might be a good place to start. I changed the case that
scrutinized type constructors to always return `False` (in effect, disabling
occurs checks throughout the entire compiler) and hacked up a quick plugin that
would explode whenever it was asked to solve something. I passed in the
function:

```haskell
fromIdentity :: Identity a -> a
fromIdentity = id
```

To my immense pleasure, the plugin exploded asking for a wanted insoluble
`CIrredCan` constraint proving `Identity a ~ a`. As it happens, this had nothing
to do with my change, and in-fact is functionality that exists in GHC head
(although [people][csongor] [way][mpickering] [smarter][nomeata] [than
me][agundry] think it's an upstream bug.) So much the better -- my plugin would
require no changes to GHC. Which meant nobody could stop me now.

[csongor]:
[mpickering]:
[nomeata]:
[agundry]:

So anyway, as soon as you have your hands on a [`Ct`][ct], you can generate an
[`EvTerm`][evterm] which corresponds to the dictionary witnessing a proof of
constraint you're trying to prove. And just because it's insoluble doesn't mean
we can't solve it. The solution is to provide an unsafe `Coercion` from `a` to
`Identity a`, and since these things are representationally equal anyway, we
should be fine.

[ct]:
[evterm]:

And believe it or not, this stuff actually worked. My `fromIdentity` function
successfully compiled, and didn't even crash at runtime. Pretty cool. Encouraged
by my brilliance, I tried the next example:

```haskell
showIdentity :: Show a => Identity a -> String
showIdentity = show

main :: IO ()
main = putStrLn $ showIdentity "hello"
```

and was rewarded with the following lovely error:

```
    • Ambiguous type variable ‘a0’ arising from a use of ‘showIdentity’
      prevents the constraint ‘(Show a0)’ from being solved.
```

As it happens, I was being asked to solve both `Show a` and `String ~ Identity
a`. By solving only the latter, I was leaving the `Show a` constraint floating,
with nothing to unify `a` against. The solution is to *emit* a new wanted `a ~
String` constraint, which causes GHC to attempt to unify the two.

In the general case, it's not entirely clear which things we want to unify. I
came up with a strategy that makes sense in my head, but I haven't spent any
time actually justifying its correctness:

1. Given an insoluble constraint of the form `a ~ b`
2. Construct `a'` and `b'` by stripping off as many `Identity` constructors as
   you can.
3. If `a'` and `b'` could possibly unify, emit the wanted constraint.
   Otherwise fail.

The "could possibly unify" algorithm is naive:

1. Check if either `a'` or `b'` is a type variable. If so, return `True`.
2. Otherwise, determine whether `a' ~ b'`.

With this final piece in place, my plugin was finished and ready to start
kicking ass. I showed it to [Adam Gundry][agundry] who besides being
exceptionally helpful, immediately used it to show that it rendered the
typesystem unsound:

```haskell
import Data.Type.Equality


witness :: Bool :~: Identity Bool
witness = Refl

type family UnsafeCoerce a where
  UnsafeCoerce (Identity a) = Void
  UnsafeCoerce a            = a

illegal
  :: (a :~: b)
  -> (UnsafeCoerce a :~: UnsafeCoerce b)
illegal Refl = Refl

cast :: (a :~: b) -> a -> b
cast Refl a = a

unsafeCoerce :: Bool -> Void
unsafeCoerce = cast (illegal witness)
```

Whoopsies! Being able to produce a `Void` is certainly bad news. I spent the
next two days trying to fix this. The problem is that `:~:` describes a
*nominal* equality, while all we truly have is a *representational* one.
Generally this error is caught by the role checker, but my plugin is in fact
providing nominal equalities. Real terror ensues.

A better solution would be to insert `coerce :: Coerceble a b => a -> b` calls
into the AST whenever we hit an insoluble `a ~ Identity a` constraint, but
unfortunately type-checker plugins don't have enough power to do this.
Alternatively we could inspect the roles of the relevant types to see if none of
them are nominal -- but again, we don't have the POWER.

My stance on this unsoundness is "well just don't do that!" Which is to say that
it's vanishingly unlikely that you'll hit it without trying, and so *just don't
try, ya dingus.* Sure, it makes me nervous too, but hey -- where's the fun in
life without a little risk?

And so that's where we stood, until I decided to write some tests.

Surprisingly, monomorphising things can actually break this approach! Consider
the following version of `fromIdentity`:

```haskell
fromIdentity :: Identity String -> String
fromIdentity = id
```

While this seems like it should work just as well as the polymorphic case, it
doesn't. Recall that `String` is a type synonym for `[Char]`, which means our
type is actually:

```haskell
fromIdentity :: Identity [Char] -> [Char]
fromIdentity = id
```

Here's where things get hairy. Haskell realizes both `Identity [Char]` and
`[Char]` are of the form `f a`, and it helpfully decomposes the equality
`Identity [Char] ~ [Char]` into two insoluble constraints:

* `Identity ~ []`
* `Char ~ [Char]`

While it's certainly possible to detect this case, it's less clear what to
actually do about it. The `Identity ~ []` constraint seems like it's possibly
soluble given our terrible terrible black magic, but `Char ~ [Char]`


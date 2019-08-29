---
host: Jonathan Lorimer
github-user: JonathanLorimer
city: Toronto
country: Canada
project: Weft
project-url: "https://github.com/JonathanLorimer/weft"
arrival-date: 2019-08-06
departure-date: 2019-08-09
---

Back at Jonathan's, in a second push attempting to get `weft` finished. We had a
long list of things to do, and we powered through almost all of them. We pulled
a few 15 hour days, aggressively programming as hard as we could. Things were
looking promising to releasing the library --- just hours before Jon was going
to present it at the local Haskell meetup.

But that morning, I'd decided to do a big refactor, using `higgledy` to
magically hide all of our HKD machinery. The approach is actually quite
involved: instead of forcing your users to use a type family `TypeFam a`,
you instead wrap it with a newtype `newtype ToTypeFam a = ToTypeFam (TypeFam
a)`, and then `HKD` over _that_. The result is gross, but it works.

God am I ever excited for unsaturated type families.

Anyway, such a refactor was an exceptionally breaking change. Literally every
module we had assumed your code was written in the direct-HKD style. A few extra
typeclass instances helped:

Assuming you have `class GSomething (rep :: * -> *)`, with instances for
`GHC.Generics`, we found that if you separate the structural bits (`M1`, `:*:`,
`:+:`, eg.) from the interesting pieces (`K1`), everything becomes much easier.
We introduced a second typeclass for the `K1` contents, and then implemented the
structural bit in terms of it:

```haskell
class GSomethingTerm (t :: *)

instance GSomethingTerm t => GSomething (K1 _1 t) where
  gSomething = K1 gSomethingTerm
```

This separation allows you to easily inject the `higgledy`-style HKD logic into
a more traditional approach. You need to add two additional cases of
`GSomethingTerm`. The first is:

```haskell
instance GSomethingTerm (Magic a) => GSomethingTerm (ToTypeFam a) where
  gSomethingTerm = ToTypeFam gSomethingTerm
```

which expands your type family's instance. The second is:

```haskell
instance GSomething (M1 _1 _2 _3) => GSomethingTerm (M1 _1 _2 _3 _4) where
  gSomethingTerm = gSomething
```

which ties the recursive knot, connecting the `GHC.Generics`-based
representation of `higgledy` back into the original generics instances you wrote
for the traditional HKD style.

It's crazy, but amazingly, it works. I don't even want to think about how much
work we're making the compiler do in Weft.

Enough shop talk. Jonathan also took me to the Toronto Haskell meetup which he
organizes. I gave a beginner-level talk about the value of types, stressing Matt
Parsons' old adage that *if your business logic bugs aren't type errors, you
should make them be.*


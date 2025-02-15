---
layout: post
title: Bidirectional Instance Contexts
date: 2025-02-15 02:15
comments: true
tags: haskell, constraints, typeclasses
---

Just a quick one today, but I wanted to point out a little trick you can do with
Haskell's typeclass inference.

Imagine we have some little class, the details of which matter not in the least:

```haskell
type Foo :: Type -> Constraint
class Foo a where
  ...
```

We can give some instances of this type:

```haskell
instance Foo Int where ...
instance Foo Bool where ...
instance Foo () where ...
```

Regular, everyday stuff. But the instances for type constructors are more
interesting, because they come with an instance context:

```haskell
instance (Foo a, Foo b) => Foo (a, b) where ...
```

Then, of course, if we know both `Foo a` and `Foo b`, we can infer `Foo (a, b)`.
To make this fact overwhelmingly explicit, we can reify the usual
constraint-solving logic by using the `Dict` type, and thus the following
program will typecheck:

```haskell
import Data.Constraint

forwards
  :: Dict (Foo a)
  -> Dict (Foo b)
  -> Dict (Foo (a, b))
forwards Dict Dict = Dict
```

Perhaps tipped off by the name here, the gentle reader is asked to notice the
asymmetry here, since the converse program will not typecheck:

```haskell
backwards
  :: Dict (Foo (a, b))
  -> (Dict (Foo a), Dict (Foo b))
backwards Dict = (Dict, Dict)
```

But why should it not typecheck?[^shut-up] Recall from the relevant instance
definition that these instances must, in fact, exist:

[^shut-up]: Rhetorical question. I don't want to hear about orphans or overlapping instances or whatever.

```haskell
instance (Foo a, Foo b) => Foo (a, b)
```

As a testament to *just* how good GHC is, we can support this bidirectionality
via a minor tweak to the definition of class and its instances.

The trick is to add an associated type family to `Foo`, and to *use it as
a superclass constraint:*

```haskell
type Foo :: Type -> Constraint
class Evidence a => Foo a where
  type Evidence a :: Constraint
  type Evidence a = ()
  ...
```

Because we've given a default implementation of the type family, our existing
simple instances work as before:

```haskell
instance Foo Int where ...
instance Foo Bool where ...
instance Foo () where ...
```

with the only change required coming from the type constructor instances:

```haskell
instance (Foo a, Foo b) => Foo (a, b) where
  type Evidence (a, b) = (Foo a, Foo b)
  ...
```

or, if we you want to be cute about it:

```haskell
instance Evidence (a, b) => Foo (a, b) where
  type Evidence (a, b) = (Foo a, Foo b)
  ...
```

By sticking `Evidence` into the superclass constraint, GHC knows that this
dictionary is always available when you've got a `Foo` dictionary around. And
our earlier `backwards` program now typechecks as expected.

[This is all available in a play
session](https://play.haskell.org/saved/YjCfxwNy) if you'd like to fool around
with it.


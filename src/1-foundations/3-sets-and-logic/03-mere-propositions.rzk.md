# Mere propositions

This is a literate Rzk file:

```rzk
#lang rzk-1
```

This module assumes function extensionality:

```rzk
#assume funext : FunExt
```

!!! note "Definition 3.3.1"

    A type $P$ is a __mere proposition__ if for all $x, y : P$ we have $x = y$.

```rzk
#define isProp
  ( A : U)
  : U
  := (x : A) → (y : A) → x = y
```

## Examples

```rzk
#define isProp-Unit
  : isProp Unit
  := \ unit unit → refl
```

```rzk
#define isProp-function uses (funext)
  ( A : U)
  ( B : A → U)
  ( isProp-B : (a : A) → isProp (B a))
  : isProp ((a : A) → B a)
  := \ f g → map-funext funext A B f g (\ a → isProp-B a (f a) (g a))
```

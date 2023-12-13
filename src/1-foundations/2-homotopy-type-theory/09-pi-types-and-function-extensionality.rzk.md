# 2.9 $\Pi$-types and the function extensionality axiom

This is a literate Rzk file:

```rzk
#lang rzk-1
```

```rzk title="HoTT Book, Definition 2.9.2"
#define happly
  ( A : U)
  ( B : A → U)
  ( f g : (a : A) → B a)
  : ( f = g) → homotopy A B f g
  :=
  path-ind ((a : A) → B a)
  ( \ f' g' _ → homotopy A B f' g')
  ( \ f' _ → refl)
  f g
```

```rzk title="HoTT Book, Axiom 2.9.3"
#define FunExt
  : U
  :=
    ( A : U)
  → ( B : A → U)
  → ( f : (a : A) → B a)
  → ( g : (a : A) → B a)
  → isequiv
    ( f = g)
    ( homotopy A B f g)
    ( happly A B f g)
```

```rzk
#assume funext : FunExt
```

```rzk
#define map-funext uses (funext)
  ( A : U)
  ( B : A → U)
  ( f g : (a : A) → B a)
  : homotopy A B f g → f = g
  := first (second (funext A B f g))
```

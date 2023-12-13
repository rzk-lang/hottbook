# 3.1 Sets and $n$-types

This is a literate Rzk file:

```rzk
#lang rzk-1
```

This module assumes function extensionality:

```rzk
#assume funext : FunExt
```

In general, types behave like spaces or higher groupoids, but there is a subclass of types that behave more like sets in a traditional sense.
We expect a type to be a set, if there is no higher homotopical information.

!!! note "Definition 3.1.1."
    A type $A$ is a **set** if for all $x, y : A$ and all $p, q : x = y$, we have $p = q$.

```rzk
#def isSet
  ( A : U)
  : U
  :=
    ( x : A)
  → ( y : A)
  → ( p : x = y)
  → ( q : x = y)
  → ( p = q)
```

## Some examples

Many of the proofs below appeal to the injectivity of equivalences:

```rzk
#define injective-equivalence
  ( A B : U)
  ( ( f , isequiv-f) : equivalence A B)
  ( x y : A)
  : ( f x = f y)
  → ( x = y)
  :=
  \ fx-eq-fy →
    3-path-concat A
    ( x)
    ( first (second isequiv-f) (f x))
    ( first (second isequiv-f) (f y))
    ( y)
    ( path-sym A
      ( first (second isequiv-f) (f x))
      ( x)
      ( second (second isequiv-f) x))
    ( ap B A
      ( first (second isequiv-f))
      ( f x)
      ( f y)
      fx-eq-fy)
    ( second (second isequiv-f) y)
```

### Unit type is a set

!!! example "Example 3.1.2."
    The type $\mathbb{1}$ is a set.

```rzk
#def isSet-Unit
  : isSet Unit
  :=
  \ x y p q →
    injective-equivalence
    ( x = y)
    ( Unit)
    ( paths-in-unit-equiv-unit x y)
    ( p)
    ( q)
    ( refl)
```

### Products of sets are sets

!!! example "Example 3.1.5."
    If $A$ and $B$ are sets, then so is $A \times B$.

```rzk
#def isSet-prod
  ( A B : U)
  ( isSet-A : isSet A)
  ( isSet-B : isSet B)
  : isSet (prod A B)
  :=
  \ (a₁ , b₁) (a₂ , b₂) p q →
    injective-equivalence
    ( ( a₁ , b₁) = (a₂ , b₂))
    ( prod (a₁ = a₂) (b₁ = b₂))
    ( paths-in-prod-equiv-prod-of-paths A B a₁ a₂ b₁ b₂)
    ( p)
    ( q)
    ( prod-of-paths-to-path-in-prod
      ( a₁ = a₂)
      ( b₁ = b₂)
      ( ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) p)
      ( ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) q)
      ( ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) p)
      ( ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) q)
      ( ( isSet-A a₁ a₂
          ( ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) p)
          ( ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) q)
        , isSet-B b₁ b₂
          ( ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) p)
          ( ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) q)))
    )
```

### Function types into sets form sets

!!! example "Example 3.1.6"

    If $A$ is _any_ type and $B : A \to \mathcal{U}$ is such that each $B(x)$ is a set, then the type $\prod_{(x:A)} B(x)$ is a set.

```rzk
#define weak-isSet-function
  ( A B : U)
  ( isSet-B : isSet B)
  ( f g : A → B)
  ( p q : homotopy A (\ _ → B) f g)
  : homotopy A (\ x → f x = g x) p q
  := \ x → isSet-B (f x) (g x) (p x) (q x)

#define weak-isSet-function₁
  ( A B : U)
  ( isSet-B : isSet B)
  ( f g : A → B)
  ( p q : f = g)
  : homotopy A (\ x → f x = g x)
    ( happly A (\ _ → B) f g p)
    ( happly A (\ _ → B) f g q)
  :=
  weak-isSet-function A B isSet-B f g
  ( happly A (\ _ → B) f g p)
  ( happly A (\ _ → B) f g q)

#define weak-isSet-function₂ uses (funext)
  ( A B : U)
  ( isSet-B : isSet B)
  ( f g : A → B)
  ( p q : f = g)
  : happly A (\ _ → B) f g p
  = happly A (\ _ → B) f g q
  :=
  map-funext funext A (\ x → f x = g x)
  ( happly A (\ _ → B) f g p)
  ( happly A (\ _ → B) f g q)
  ( weak-isSet-function₁ A B isSet-B f g p q)

#define isSet-function uses (funext)
  ( A B : U)
  ( isSet-B : isSet B)
  : isSet (A → B)
  :=
  \ f g p q →
    injective-equivalence
    ( f = g)
    ( homotopy A (\ _ → B) f g)
    ( happly A (\ _ → B) f g
    , funext A (\ _ → B) f g)
    ( p)
    ( q)
    ( weak-isSet-function₂ A B isSet-B f g p q)
```

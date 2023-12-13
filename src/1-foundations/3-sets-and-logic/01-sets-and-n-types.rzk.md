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

### Unit type is a set

!!! example "Example 3.1.2."
    The type $\mathbb{1}$ is a set.

```rzk
#def isSet-Unit
  : isSet Unit
  := \ x y p q → 3-path-concat
        ( x = y)
        -- p = f_inv (f(p)) = f_inv (f(q)) = q
        p
        ( ( first (second (second (paths-in-unit-equiv-unit x y)))) ((first (paths-in-unit-equiv-unit x y)) p))
        ( ( first (second (second (paths-in-unit-equiv-unit x y)))) ((first (paths-in-unit-equiv-unit x y)) q))
        q
        -- p = f_inv (f(p)) : use the proof embedded in the equivalence
        ( path-sym (x = y) (((first (second (second (paths-in-unit-equiv-unit x y)))) ((first (paths-in-unit-equiv-unit x y)) p))) p
            ( ( second (second (second (paths-in-unit-equiv-unit x y)))) p))
        -- f_inv (f(p)) = f_inv (f(q)) : use the fact that f(p) and f(q) are of type Unit and therefore there is equality between them
        ( ap
            Unit (x = y)
            ( first (second (second (paths-in-unit-equiv-unit x y))))
            ( ( first (paths-in-unit-equiv-unit x y)) p)
            ( ( first (paths-in-unit-equiv-unit x y)) q)
            refl)
        -- f_inv (f(q)) = q : use the proof embedded in the equivalence
        ( ( second (second (second (paths-in-unit-equiv-unit x y)))) q)
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
  := \ (a₁ , b₁) (a₂ , b₂) p q → 3-path-concat
    ( ( a₁ , b₁) = (a₂ , b₂))
    p
    ( prod-of-paths-to-path-in-prod A B a₁ a₂ b₁ b₂ (path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂) p))
    ( prod-of-paths-to-path-in-prod A B a₁ a₂ b₁ b₂ (path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂) q))
    q
    ( path-sym ((a₁ , b₁) = (a₂ , b₂))
      ( prod-of-paths-to-path-in-prod A B a₁ a₂ b₁ b₂ (path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂) p))
      p
      ( second (second (prod-path-qinv A B a₁ a₂ b₁ b₂)) p))
    ( ap (prod (a₁ = a₂) (b₁ = b₂)) ((a₁ , b₁) = (a₂ , b₂))
      ( \ x → (prod-of-paths-to-path-in-prod A B a₁ a₂ b₁ b₂ x))
      ( path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂) p)
      ( path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂) q)
      -- proof that (pa, pb) = (qa, qb)
      ( prod-of-paths-to-path-in-prod (a₁ = a₂) (b₁ = b₂)
        ( ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) p)
        ( ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) q)
        ( ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) p)
        ( ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) q)
        ( ( isSet-A a₁ a₂ (ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) p) (ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) q)
      , isSet-B b₁ b₂ (ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) p) (ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) q)))
      )
    )
    ( second (second (prod-path-qinv A B a₁ a₂ b₁ b₂)) q)
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

#define weak-isSet-function₃ uses (funext)
  ( A B : U)
  ( isSet-B : isSet B)
  ( f g : A → B)
  ( p q : f = g)
  : map-funext funext A (\ _ → B) f g (happly A (\ _ → B) f g p)
  = map-funext funext A (\ _ → B) f g (happly A (\ _ → B) f g q)
  :=
  ap
  ( homotopy A (\ _ → B) f g)
  ( f = g)
  ( map-funext funext A (\ _ → B) f g)
  ( happly A (\ _ → B) f g p)
  ( happly A (\ _ → B) f g q)
  ( weak-isSet-function₂ A B isSet-B f g p q)

#define funext-happly-eq-id uses (funext)
  ( A B : U)
  ( isSet-B : isSet B)
  ( f g : A → B)
  ( p : f = g)
  : map-funext funext A (\ _ → B) f g (happly A (\ _ → B) f g p)
  = p
  := second (second (funext A (\ _ → B) f g)) p

#define path-concat3
  ( A : U)
  ( x y z w : A)
  : ( x = y) → (y = z) → (z = w) → (x = w)
  :=
  \ p q r →
    path-concat A x z w
      ( path-concat A x y z p q)
      r

#define isSet-function uses (funext)
  ( A B : U)
  ( isSet-B : isSet B)
  : isSet (A → B)
  :=
  \ f g p q →
    path-concat3 (f = g)

      p
      ( map-funext funext A (\ _ → B) f g (happly A (\ _ → B) f g p))
      ( map-funext funext A (\ _ → B) f g (happly A (\ _ → B) f g q))
      q

      ( path-sym (f = g)
        ( map-funext funext A (\ _ → B) f g (happly A (\ _ → B) f g p))
        p
        ( funext-happly-eq-id A B isSet-B f g p))
      ( weak-isSet-function₃ A B isSet-B f g p q)
      ( funext-happly-eq-id A B isSet-B f g q)
```

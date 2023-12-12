# 3.1 Sets and $n$-types

This is a literate Rzk file:

```rzk
#lang rzk-1
```

In general, types behave like spaces or higher groupoids, but there is a subclass of types that behave more like sets in a traditional sense.
We expect a type to be a set, if there is no higher homotopical information.

!!! note "Definition 3.1.1."
    A type $A$ is a **set** if for all $x, y : A$ and all $p, q : x = y$, we have $p = q$.

```rzk
#def is-set
    ( A : U)
  : U
  := (x : A) → (y : A) → (p : x = y) → (q : x = y) → (p = q)
```

!!! note "Example 3.1.2."
    The type $\mathbb{1}$ is a set.

```rzk
#def is-set-Unit
  : is-set Unit
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

!!! note "Example 3.1.5."
    If $A$ and $B$ are sets, then so is $A \times B$.

```rzk
#def is-set-prod
  ( A B : U)
  ( is-set-A : is-set A)
  ( is-set-B : is-set B)
  : is-set (prod A B)
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
        ( ( is-set-A a₁ a₂ (ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) p) (ap (prod A B) A (pr₁ A B) (a₁ , b₁) (a₂ , b₂) q)
      , is-set-B b₁ b₂ (ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) p) (ap (prod A B) B (pr₂ A B) (a₁ , b₁) (a₂ , b₂) q)))
      )
    )
    ( second (second (prod-path-qinv A B a₁ a₂ b₁ b₂)) q)
```

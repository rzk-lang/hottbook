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
```

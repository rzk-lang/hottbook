# 2.8 The unit type

This is a literate Rzk file:

```rzk
#lang rzk-1
```

For `#!rzk Unit` type, uniqueness principle is built-in. That is, for any `#!rzk x, y : Unit`, we have `#!rzk refl : x = y`

!!! note "Theorem 2.8.1."

    For any $x, y : \mathbb{1}$, we have $(x = y) \simeq \mathbb{1}$.

```rzk
#def paths-in-unit-equiv-unit
    ( x y : Unit)
  : equivalence (x = y) Unit
    -- provide a function - a constant map to unit
  :=
  ( \ (p : x = y) → unit
  , ( -- provide right inverse - a constant map to refl_{unit}
      ( \ (u : Unit) → refl_{unit}
      , -- prove that composition is homotopical to id_Unit
        \ (u : Unit) → refl)
    , -- provide left inverse - a constant map to refl_{unit}
      ( \ (u : Unit) → refl_{unit}
      , -- prove that composition is homotopical to id_{x = y}; use path induction on p
        path-ind Unit
        ( \ x' y' p' → refl_{unit} = p')
        ( \ x' → refl)
        x y)))
```

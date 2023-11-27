# 2.8 The unit type

This is a literate Rzk file:

```rzk
#lang rzk-1
```

!!! note "Lemma. Any two elements of $\mathbb{1}$ are equal"
    For any $x,y:\mathbb{1}$, we have $x = y$.

```rzk
#def units-eq
    (x y : Unit)
    : x = y
    := path-concat Unit x unit y (Unit-uniq x) (path-sym Unit y unit (Unit-uniq y))
```

!!! note "Theorem 2.8.1."
    For any $x,y:\mathbb{1}$, we have $(x=y) \simeq \mathbb{1}$.

```rzk
#def paths-in-unit-equiv-unit
    (x y : Unit)
    : equivalence (x = y) Unit
    -- provide a function - a constant map to unit
    := ( \ (p : x = y) → unit, (
        -- provide right inverse - a constant map to an inhabitant of x = y
        (\ (u : Unit) → units-eq x y,
        -- prove that composition is homotopical to id_Unit, via the proof that any inhabitant of unit is equal to unit
            \ (u : Unit) → path-sym Unit u unit (Unit-uniq u)),
        -- provide left same inverse (choose same as right inverse)
        (\ (u : Unit) → units-eq x y, 
        -- prove that composition is homotopical to id_{x = y}, in other words, that
        -- concatenation of paths (x = unit) and (unit = y) is equal to p; use path induction on p to show that
        -- concatenation of paths (x = unit) and (unit = x) is equal to refl, with the "concat with inverse is refl" theorem
            \ (p : x = y) → path-ind 
                Unit
                ( \ x' y' p' → units-eq x' y' = p')
                ( \ x' → inverse-r Unit x' unit (Unit-uniq x'))
                x y p
            )
        ))
```


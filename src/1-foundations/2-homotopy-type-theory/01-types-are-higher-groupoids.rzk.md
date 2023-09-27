# 2.1 Types are higher groupoids

This is a literate Rzk file:

```rzk
#lang rzk-1
```

Groupoids are categories in which all morphisms are isomorphisms.
Alternativerly, groupoids can be viewed as a generalization of groups, where not all pairs of elements can be composed
(but the group laws for the operation hold).

## Path symmetry
!!! lemma "Lemma 2.1.1."
    For every type $A$ and every $x, y : A$ there is a function $(x = y) \to (y = x)$`
    denoted $p \mapsto p^{-1}$, such that $refl_x^{-1} \equiv refl_x$ for each $x : A$. We call $p^{-1}$ the inverse of $p$.

```rzk
#def path-sym
  (A : U)
  (x y : A)
  : (x = y) → (y = x)
  := path-ind 
    A 
    (\ x' y' _ → y' = x') 
    (\ z → refl) 
    x y
```

## Path concatenation
!!! lemma "Lemma 2.1.2."
    For every type $A$ and every $x, y, z : A$ there is a function $(x = y) \to (y = z) \to (x = z)$,
    written $p \mapsto q \mapsto p \cdot q$, such that $refl_x \cdot refl_x \equiv refl_x$ for any $x : A$. 
    We call $p \cdot q$ the concatenation or composite of $p$ and $q$.

```rzk
#def path-concat
  (A : U)
  (x y z : A)
  : (x = y) → (y = z) → (x = z)
  := \ p → path-ind 
      A 
      (\ x' y' p' → ((y' = z) → (x' = z)))
      (\ x' → \ r → r)
      x y p
```


## Coherence laws
!!! lemma "Lemma 2.1.4."
    Suppose $A : U$, that $x, y, z, w : A$ and that $p : x = y$ and $q : y = z$ and $r : z = w$. We
    have the following:

    1. $p = p \cdot refl$ and $p=refl \cdot p$.
    2. $p^{-1} \cdot p = refl$ and $p \cdot p^{-1} = refl$. 
    3. $(p^{-1})^{-1} = p$.
    4. $p \cdot (q \cdot r) = (p \cdot q) \cdot r$.

1. Composition with `refl`
```rzk
#def concat-refl
  (A : U)
  (x y : A)
  (p : x = y)
  : p = path-concat A x y y p refl
  := path-ind 
    A
    (\ x' y' p' → p' = path-concat A x' y' y' p' refl)
    -- ? : refl = path-concat A x x x refl refl ==
    (\ _ → refl)
    x y p

#def refl-concat
  (A : U)
  (x y : A)
  (p : x = y)
  : p = path-concat A x x y refl p
  := path-ind 
    A
    (\ x' y' p' → p' = path-concat A x' x' y' refl p')
    -- ? : p = path-concat A x x x refl refl
    (\ _ → refl)
    x y p
```

2. Composition with inverse
```rzk    
#def inverse-l
  (A : U)
  (x y : A)
  (p : x = y)
  : path-concat A y x y (path-sym A x y p) p  = refl
  := path-ind
    A
    (\ x' y' p' → path-concat A y' x' y' (path-sym A x' y' p') p'  = refl)
    (\ _ → refl)
    x y p
 
#def inverse-r
  (A : U)
  (x y : A)
  (p : x = y)
  : path-concat A x y x p (path-sym A x y p) = refl
  := path-ind A
     (\ x' y' p' → path-concat A x' y' x' p' (path-sym A x' y' p') = refl )
     (\ _ → refl)
      x y p
```

3. Inverse of inverse
```rzk
#def inverse-twice
  (A : U)
  (x y : A)
  (p : x = y)
  : path-sym A y x (path-sym A x y p) = p
  := path-ind A
     (\ x' y' p' → path-sym A y' x' (path-sym A x' y' p') = p')
     (\ _ → refl)
      x y p
```

4. Associativity of concatenation
```rzk
#def concat-assoc
  (A : U)
  (x y z w : A)
  (p : x = y)
  (q : y = z)
  (r : z = w)
  : path-concat A x y w p (path-concat A y z w q r) = 
      path-concat A x z w (path-concat A x y z p q) r 
  := (path-ind 
        A
        (\ x' y' p' → (z' : A) → (q' : y' = z') → (w' : A) → (r' : z' = w') →
          path-concat A x' y' w' p' (path-concat A y' z' w' q' r') = 
            path-concat A x' z' w' (path-concat A x' y' z' p' q') r' )
        -- ? : (z' : A) → (q' : y' = z') → (w' : A) → (r' : z' = w') →
          -- path-concat A x' x' w' refl (path-concat A x' z' w' q' r') = 
          -- path-concat A x' z' w' (path-concat A x' x' z' refl q') r' ) ===
          -- (z' : A) → (q' : y' = z') → (w' : A) → (r' : z' = w') →
          -- path-concat A x' z' w' q' r' = path-concat A x' z' w' q' r' )
        (\ x' z' q' w' r' → refl)
        x y p) z q w r
```
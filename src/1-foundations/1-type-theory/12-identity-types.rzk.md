# 1.11 Identity types

This is a literate Rzk file:

```rzk
#lang rzk-1
```

Induction on identity type is defined with built-in `idJ` operator:

```rzk
#def path-ind
  ( A : U)
  ( C : (x : A) → (y : A) → (x = y) → U)
  ( d : (x : A) → C x x refl)
  : ( x : A) → (y : A) → (p : x = y) → C x y p
  := \ x y p → idJ(A , x , C x , d x , y , p)
```

Indiscernability of identicals:

```rzk
#def indiscernability-of-identicals
  ( A : U)
  ( C : A → U)
  : ( x : A) → (y : A) → (p : x = y) → (C x) → (C y)
  := path-ind
    A
    ( \ x y p → ((C x) → (C y)))
    ( \ x → \ cx → cx)
```

Based path induction directly corresponds to the `idJ` operator:

```rzk
#def based-path-ind
  ( A : U)
  ( a : A)   
  ( C : (x : A) → (a = x) → U)
  ( ca : C a refl)
  : ( x : A) → (p : a = x) → (C x p)
  := \ x p → idJ(A , a , C , ca , x , p)
```


Based path induction can be defined with the (usual) path induction:

```rzk
#def based-path-ind'
  ( A : U)
  : ( a : A)
  → ( C : (x : A) → (a = x) → U)
  → ( ca : C a refl)
  → ( x : A)
  → ( p : a = x)
  → ( C x p)
  := \ a C ca x p → 
  path-ind 
    A
    ( \ a' x' p' → (C' : ((x'' : A) → (a' = x'') → U)) → (C' a' refl) → (C' x' p'))
    ( \ a' → \ C' ca' → ca')
    a x p C ca
```

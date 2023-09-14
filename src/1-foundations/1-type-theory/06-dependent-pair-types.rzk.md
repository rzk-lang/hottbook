# 1.6 Dependent pair types

This is a literate Rzk file:

```rzk
#lang rzk-1
```
!!! warning "TODO"
    Add proper descriptions and check for missing definitions

```rzk
#def pr₁-Σ
  (A : U)
  (B : A -> U)
  : (Σ (x : A), B x) -> A
  := \p -> first p

#def pr₂-Σ
  (A : U)
  (B : A -> U)
  : (p : Σ (x : A), B x) -> (B (first p))
  := \p -> second p
```
Recursor for $\Sigma$-types. They are called like this:

$$
\mathsf{rec}_{\Sigma_{x : A}B(x)} ((C: U), (g: (x : A) \rightarrow B (x) \rightarrow C), (p: \Sigma_{x : A} B(x)))
$$

```rzk
#def rec-Σ
  (A : U)
  (B : A -> U)
  (C : U)
  : (g : (x : A) -> B x -> C) -> (p : Σ (x : A), B x) -> C
  := \ g (a, b) -> g a b
```

```rzk
#def ind-Σ
  (A : U)
  (B : A -> U)
  (C : (Σ (x : A), B x) -> U)
  : (g : (x : A) -> (y : B x) -> C (x, y)) -> (p : Σ (x : A), B x) -> C p
  := \ g (a, b) -> g a b
```

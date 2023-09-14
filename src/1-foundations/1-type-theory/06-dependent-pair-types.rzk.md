# 1.6 Dependent pair types

This is a literate Rzk file:

```rzk
#lang rzk-1
```
TODO

```rzk
#def pr₁-sigma
  (A : U)
  (B : A -> U)
  : (Sigma (x : A), (B x)) -> A
  := \p -> first p

#def pr₂-sigma
  (A : U)
  (B : A -> U)
  : (p : Sigma (x : A), (B x)) -> (B (first p))
  := \p -> second p
```
Recursor for sigma types. They are called like this:

$$
\mathsf{rec}_{\Sigma_{x : A}B(x)} ((C: U), (g: (x : A) \rightarrow B (x) \rightarrow C), (p: \Sigma_{x : A} B(x)))
$$

```rzk
#def rec-sigma
  (A : U)
  (B : A -> U)
  (C : U)
  : (g : (x : A) -> B x -> C) -> (p : Sigma (x : A), (B x)) -> C
  := \ g (a, b) -> g a b
```

```rzk
#def ind-sigma
  (A : U)
  (B : A -> U)
  (C : (Sigma (x : A), (B x)) -> U)
  : (g : (x : A) -> (y : B x) -> C (x, y)) -> (p : Sigma (x : A), (B x)) -> C p
  := \ g (a, b) -> g a b
```

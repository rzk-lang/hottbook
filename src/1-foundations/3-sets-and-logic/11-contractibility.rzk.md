# Contractibility

This is a literate Rzk file:

```rzk
#lang rzk-1
```

!!! note "Definition 3.11.1"

    A type $A$ is __contractible__, or a __singleton__,
    if there is $a : A$, called the __center of contraction__,
    such that $a = x$ for all $x : A$.
    We denote the specified path $a = x$ by $\mathsf{contr}_{x}$.

```rzk
#define isContr
  ( A : U)
  : U
  := Σ (a : A) , (x : A) → a = x

#define center
  ( A : U)
  : isContr A → A
  := \ (a , _) → a

#define contr
  ( A : U)
  ( isContr-A : isContr A)
  ( x : A)
  : center A isContr-A = x
  := second isContr-A x
```

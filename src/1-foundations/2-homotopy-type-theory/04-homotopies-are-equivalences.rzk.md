# 2.4 Homotopies are equivalences

This is a literate Rzk file:

```rzk
#lang rzk-1
```

## Homotopies between functions
!!! lemma "Definition 2.4.1."
    Let $f, g : \Pi_{(x:A)} P(x)$ be two sections of a type family $P : A \to U$. A homotopy from $f$ to $g$ is a dependent function of type

    $$(f \sim g) :\equiv \Pi_{(x:A)} (f(x) = g(x)).$$

```rzk
#def homotopy
    (A : U)
    (P : A → U)
    (f g : (x : A) → P x)
    : U
    := (x : A) → f x = g x
```

## Homotopies as equivalences
!!! lemma "Lemma 2.4.2."
    Homotopy is an equivalence relation on each dependent function type $\Pi_{(x:A) P(x)}$. That is, we have elements of the types

    $$\Pi_{f:\Pi_{(x:A)} P(x)} (f \sim f)$$

    $$\Pi_{f,g:\Pi_{(x:A)} P(x)} (f \sim g) \to (g \sim f)$$

    $$\Pi_{f,g,h:\Pi_{(x:A)} P(x)} (f \sim g) \to (g \sim h) \to (f \sim h)$$

1. Reflexivity:
```rzk
#def homotopy-refl
    (A : U)
    (P : A → U)
    (f : (x : A) → P x)
    : homotopy A P f f
    := \ x → refl
```

2. Symmetry:
```rzk
#def homotopy-sym:
    (A : U)
    (P : A → U)
    (f g : (x : A) → P x)
    : homotopy A P f g → homotopy A P g f
    := \ hom → \ x → path-sym (P x) (f x) (g x) (hom x)
```

3. Transitivity:
```rzk
#def homotopy-trans
    (A : U)
    (P : A → U)
    (f g h : (x : A) → P x)
    : homotopy A P f g → homotopy A P g h → homotopy A P f h
    := \ hom-fg → \ hom-gh → \ x → path-concat (P x) (f x) (g x) (h x) (hom-fg x) (hom-gh x)
```

## Naturality
!!! lemma "Lemma 2.4.3."
    Suppose $H : f \sim g$ is a homotopy between functions $f, g: A \to B$ and let $p : x =_A y$. Then we have

    $$H(x) \cdot g(p) = f(p) \cdot H(y).$$
!!! note
    When dealing with paths, authors write $f(p)$ to mean $ap_f(p)$

```rzk
#def hom-naturality
    (A B : U)
    (f g : A → B)
    (H : homotopy A (\ _ → B) f g)
    (x y : A)
    (p : x = y)
    : path-concat B (f x) (g x) (g y) (H x) (ap A B g x y p)
        = path-concat B (f x) (f y) (g y) (ap A B f x y p) (H y)
    := path-ind
        A
        (\ x' y' p' → path-concat B (f x') (g x') (g y') (H x') (ap A B g x' y' p')
            = path-concat B (f x') (f y') (g y') (ap A B f x' y' p') (H y')
        )
        -- ? : path-concat B (f x') (g x') (g x') (H x') (ap A B g x' x' refl) =
        --       path-concat B (f x') (f x') (g x') (ap A B f x' x' refl) (H x') ===
        --     path-concat B (f x') (g x') (g x') (H x') refl =
        --       path-concat B (f x') (f x') (g x') refl (H x')
        -- Both sides of the equality are equal to (H x'), we can use transitivity
        (\ x' → path-concat -- lhs = rhs
            (f x' = g x')
            (path-concat B (f x') (g x') (g x') (H x') refl) -- lhs
            (H x')
            (path-concat B (f x') (f x') (g x') refl (H x')) -- rhs
            (path-sym -- lhs = H x'
                (f x' = g x')
                (H x')
                (path-concat B (f x') (g x') (g x') (H x') refl)
                (concat-refl B (f x') (g x') (H x')) -- H x' = lhs
            )
            (refl-concat B (f x') (g x') (H x')) -- H x' = rhs
        )
        x y p
```

!!! lemma "Corollary 2.4.4."
    Let $H : f \sim id_A$ be a homotopy, with $f : A \to A$. Then, for any $x : A$ we have

    $$H(f(x)) = f(H(x)).$$

    Here $f(x)$ denotes the ordinary application of $f$ to $x$, while $f(H(x))$ denotes $ap_f(H(x))$.

```rzk
-- #def homotopy-id-swap
--     (A : U)
--     (f : A → A)
--     (H : homotopy A (\ _ → A) f (id A))
--     (x : A)
--     : H (f x) = ap A A f (f x) (id A x) (H x)
--     :=
```

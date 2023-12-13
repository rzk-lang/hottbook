# 2.6 Cartesian product types

This is a literate Rzk file:

```rzk
#lang rzk-1
```

For any elements $x, y : A \times B$ and a path $p : x =_{A \times B} y$, by functoriality we can extract paths $\mathsf{pr}_1(p) : \mathsf{pr}_1(x) =_A \mathsf{pr}_1(y)$ and $\mathsf{pr}_2(p) : \mathsf{pr}_2(x) =_B \mathsf{pr}_2(y)$.

```rzk
#def path-in-prod-to-prod-of-paths
  ( A B : U)
  ( x y : prod A B)
  : ( x = y)
  → prod
    ( pr₁ A B x = pr₁ A B y)
    ( pr₂ A B x = pr₂ A B y)
  :=
  \ p →
    ( ap (prod A B) A (pr₁ A B) x y p
    , ap (prod A B) B (pr₂ A B) x y p)
```


!!! note "Theorem 2.6.2. Paths in a product space are pairs of paths"

    The function

    $$(x =_{A \times B} y) → (\mathsf{pr}_1(x) =_A \mathsf{pr}_1(y)) \times (\mathsf{pr}_2(x) =_B \mathsf{pr}_2(y)).$$

    is an equivalence

```rzk
#def prod-of-paths-to-path-in-prod
  ( A B : U)
  ( a₁ a₂ : A)
  ( b₁ b₂ : B)
  : prod (a₁ = a₂) (b₁ = b₂)
  → ( a₁ , b₁) = (a₂ , b₂)
  :=
  \ (pa , pb) →
    path-ind A
    ( \ x y p → (x , b₁) = (y , b₂))
    ( \ x →
        path-ind B
        ( \ x' y' _p' → (x , x') = (x , y'))
        ( \ _x' → refl)
        ( b₁)
        ( b₂)
        ( pb))
    ( a₁)
    ( a₂)
    ( pa)
```


```rzk
#def prod-path-qinv
  ( A B : U)
  ( a₁ a₂ : A)
  ( b₁ b₂ : B)
  : qinv
    ( ( a₁ , b₁) = (a₂ , b₂))
    ( prod (a₁ = a₂) (b₁ = b₂))
    ( path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂))
  :=
  ( prod-of-paths-to-path-in-prod A B a₁ a₂ b₁ b₂
  , ( \ (pa , pb) →
        path-ind A
        ( \ x y p →
          path-in-prod-to-prod-of-paths A B (x , b₁) (y , b₂)
          ( prod-of-paths-to-path-in-prod A B x y b₁ b₂
            ( p , pb))
        = ( p , pb))
        ( \ x →
            path-ind B
            ( \ x' y' p' →
                path-in-prod-to-prod-of-paths A B (x , x') (x , y')
                ( prod-of-paths-to-path-in-prod A B x x x' y'
                  ( refl , p'))
              = ( refl , p'))
            ( \ x' → refl)
            ( b₁)
            ( b₂)
            ( pb)
        )
        ( a₁)
        ( a₂)
        ( pa)
      , \ pab →
          path-ind (prod A B)
          ( \ (a₁' , b₁') (a₂' , b₂') pab' →
              prod-of-paths-to-path-in-prod A B a₁' a₂' b₁' b₂'
              ( path-in-prod-to-prod-of-paths A B (a₁' , b₁') (a₂' , b₂')
                ( pab'))
            = pab')
          ( \ x → refl)
          ( a₁ , b₁)
          ( a₂ , b₂)
          ( pab)
      )
  )
```

```rzk
#def paths-in-prod-equiv-prod-of-paths
  ( A B : U)
  ( a₁ a₂ : A)
  ( b₁ b₂ : B)
  : equivalence
    ( ( a₁ , b₁) = (a₂ , b₂))
    ( prod (a₁ = a₂) (b₁ = b₂))
  :=
  ( path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂)
  , qinv-to-isequiv
    ( ( a₁ , b₁) = (a₂ , b₂))
    ( prod (a₁ = a₂) (b₁ = b₂))
    ( path-in-prod-to-prod-of-paths A B (a₁ , b₁) (a₂ , b₂))
    ( prod-path-qinv A B a₁ a₂ b₁ b₂))
```

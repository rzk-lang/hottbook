# 2.4 Homotopies and equivalences

This is a literate Rzk file:

```rzk
#lang rzk-1
```

## Homotopies between functions

!!! note "Definition 2.4.1."
    Let $f, g : \prod_{(x:A)} P(x)$ be two sections of a type family $P : A \to U$.
    A homotopy from $f$ to $g$ is a dependent function of type

    $$(f \sim g) :\equiv \prod_{(x:A)} (f(x) = g(x)).$$

```rzk
#def homotopy
  ( A : U)
  ( P : A → U)
  ( f g : (x : A) → P x)
  : U
  := (x : A) → f x = g x
```

## Homotopies are equivalence relations

!!! note "Lemma 2.4.2."

    Homotopy is an equivalence relation on each dependent function type $\prod_{(x:A)} P(x)$.
    That is, we have elements of the types

    $$\prod_{f : \prod_{(x:A)} P(x)} (f \sim f)$$

    $$\prod_{f, g : \prod_{(x:A)} P(x)} (f \sim g) \to (g \sim f)$$

    $$\prod_{f, g, h : \prod_{(x:A)} P(x)} (f \sim g) \to (g \sim h) \to (f \sim h)$$

### Reflexivity

```rzk
#def homotopy-refl
  ( A : U)
  ( P : A → U)
  ( f : (x : A) → P x)
  : homotopy A P f f
  := \ x → refl
```

### Symmetry

```rzk
#def homotopy-sym
  ( A : U)
  ( P : A → U)
  ( f g : (x : A) → P x)
  : homotopy A P f g → homotopy A P g f
  :=
  \ hom x →
    path-sym (P x) (f x) (g x) (hom x)
```

### Transitivity

```rzk
#def homotopy-trans
    ( A : U)
    ( P : A → U)
    ( f g h : (x : A) → P x)
  : homotopy A P f g
  → homotopy A P g h
  → homotopy A P f h
  :=
  \ hom-fg hom-gh x →
    path-concat (P x) (f x) (g x) (h x) (hom-fg x) (hom-gh x)
```

## Naturality

!!! note "Lemma 2.4.3."

    Suppose $H : f \sim g$ is a homotopy between functions $f, g: A \to B$ and let $p : x =_A y$. Then we have

    $$H(x) \cdot g(p) = f(p) \cdot H(y).$$

!!! tip
    When dealing with paths, authors write $f(p)$ to mean $ap_f(p)$.

```rzk
#def hom-naturality
  ( A B : U)
  ( f g : A → B)
  ( H : homotopy A (\ _ → B) f g)
  : ( x : A)
  → ( y : A)
  → ( p : x = y)
  → path-concat B (f x) (g x) (g y) (H x) (ap A B g x y p)
  = path-concat B (f x) (f y) (g y) (ap A B f x y p) (H y)
  :=
  path-ind A
  ( \ x' y' p' →
      path-concat B (f x') (g x') (g y') (H x') (ap A B g x' y' p')
    = path-concat B (f x') (f y') (g y') (ap A B f x' y' p') (H y'))
  ( \ x' → path-sym -- H x' ∙ refl = H x'
            ( f x' = g x')
            ( H x')
            ( path-concat B (f x') (g x') (g x') (H x') refl)
            ( concat-refl B (f x') (g x') (H x')) -- H x' = H x' ∙ refl
        )
```

!!! note "Corollary 2.4.4."

    Let $H : f \sim id_A$ be a homotopy, with $f : A \to A$. Then, for any $x : A$ we have

    $$H(f(x)) = f(H(x)).$$

    Here $f(x)$ denotes the ordinary application of $f$ to $x$, while $f(H(x))$ denotes $ap_f(H(x))$.

Proof [`#!rzk homotopy-id-swap`](#define:homotopy-id-swap) is given in the end of the file.

## Quasi-Inverses

The traditional notion of isomorphism is poorly behaved for proof-relevant mathematics. Thus, it is given the name of quasi-inverse.

!!! note "Definition 2.4.6."

    For a function $f : A → B$,
    a __quasi-inverse__ of $f$ is a triple $(g, \alpha, \beta)$ consisting of
    a function $g : B → A$
    and homotopies $\alpha : f \circ g \sim id_B$
    and $\beta : g \circ f \sim id_A$.

```rzk
#def qinv
  ( A B : U)
  ( f : A → B)
  : U
  :=
  Σ ( g : B → A)
  , prod
    ( homotopy B (\ _ → B) (compose B A B f g) (id B))
    ( homotopy A (\ _ → A) (compose A B A g f) (id A))
```

### Examples

!!! example "Example 2.4.7. Identity quasi-inverse"

    The identity function $id_A : A \to A$ has a quasi-inverse given by $id_A$ itself,
    together with homotopies defined by $\alpha(y) :\equiv \mathsf{refl}_y$ and $\beta(x) :\equiv \mathsf{refl}_x$.

```rzk
#def qinv-id
  ( A : U)
  : qinv A A (id A)
  :=
  ( id A
  , ( \ y → refl_{y}
    , \ x → refl_{x}))
```

!!! example "Example 2.4.8. Quasi-inverse for path concatenation"

    For any $p : x =_A y$ and $z : A$,
    the functions $(p \cdot –) : (y =_A z) \to (x =_A z)$
    and $(– \cdot p) : (z =_A x) \to (z =_A y)$
    have quasi-inverses given by $(p^{−1} \cdot –)$ and $(– \cdot p^{−1})$, respectively.

#### Quasi-inverse has a quasi-inverse

```rzk
#define inverse-from-qinv
  ( A B : U)
  ( f : A → B)
  : qinv A B f → (B → A)
  := \ (g , _) → g

#define qinv-inverse-from-qinv
  ( A B : U)
  ( f : A → B)
  : ( qinv-f : qinv A B f)
  → qinv B A (inverse-from-qinv A B f qinv-f)
  := \ (g , (α , β)) → (f , (β , α))
```

#### Quasi-inverse of the concatenation from the right side

!!! tip "Change of variables in the code"

    Note the change of variables: $p \mapsto q, x \mapsto y, y \mapsto z, z \mapsto x$. That is, the code corrsesponds to the statement that for any $q : y =_A z$ and $x : A$, the function $(– \cdot q) : (x =_A y) \to (x =_A z)$ have quasi-inverse given by $(– \cdot q^{−1})$, respectively.

```rzk title="Definition of right concatenation as a function, and its inverse"
#def right-concat
  ( A : U)
  ( x y z : A)
  ( q : y = z)
  : ( x = y) → (x = z)
  := \ p → path-concat A x y z p q

#def right-concat-inv
  ( A : U)
  ( x y z : A)
  ( q : y = z)
  : ( x = z) → (x = y)
  := right-concat A x z y (path-sym A y z q)
```

```rzk title="Proofs that both compositions are homotopical to identity"
#def right-concat-right-inv-remove-refl
  ( A : U)
  ( x y z : A)
  ( p : x = y)
  : ( q : y = z)
  → right-concat-inv A x y z q (right-concat A x y z q p) -- (p ∙ q) ∙ q⁻¹
  = p
  :=
  path-ind A
  ( \ x' y' p' →
      ( q : y' = z) → right-concat-inv A x' y' z q (right-concat A x' y' z q p') = p')
  ( \ x' → inverse-r A x' z)
  ( x)
  ( y)
  ( p)

#def right-concat-left-inv-remove-refl
  ( A : U)
  ( x y z : A)
  ( r : x = z)
  : ( q : y = z)
  → right-concat A x y z q (right-concat-inv A x y z q r) -- (r ∙ q⁻¹) ∙ q
  = r
  :=
  path-ind A
  ( \ x' z' r' →
      ( q : y = z') → right-concat A x' y z' q (right-concat-inv A x' y z' q r') = r')
  ( \ x' → inverse-l A y x')
  ( x)
  ( z)
  ( r)
```

```rzk title="Proof for quasi-inverse of right concatenation"
#def right-concat-inv-is-qinv-for-right-concat
  ( A : U)
  ( x y z : A)
  ( q : y = z)
  : qinv (x = y) (x = z) (right-concat A x y z q)
  :=
  ( right-concat-inv A x y z q
  , ( \ (r : x = z) → right-concat-left-inv-remove-refl  A x y z r q
    , \ (p : x = y) → right-concat-right-inv-remove-refl A x y z p q))
```


## Equivalences

An improved notion, [`isequiv`](#define:isequiv), has the following properties:

1. For each $f : A \to B$ there is a function $\mathsf{qinv}(f) \to \mathsf{isequiv}(f)$
2. Similarly, for each $f$ we have $\mathsf{isequiv}(f) \to \mathsf{qinv}(f)$; thus the two are logically equivalent.
3. For any two inhabitants $e_1, e_2 : \mathsf{isequiv}(f)$, we have $e_1 = e_2$.

One of numerous, but equivalent ways to define `isequiv`:

!!! note "Definition 2.4.10."

    $$\mathsf{isequiv}(f) :\equiv \left(\sum_{(g:B \to A)} (f \circ g \sim id_B)\right) \times \left(\sum_{(h:B \to A)} (h \circ f \sim id_A)\right).$$

```rzk
#def isequiv
  ( A B : U)
  ( f : A → B)
  : U
  :=
  prod
  ( Σ ( g : B → A) , homotopy B (\ _ → B) (compose B A B f g) (id B))
  ( Σ ( h : B → A) , homotopy A (\ _ → A) (compose A B A h f) (id A))
```

### Proof of Property 1

For the $\mathsf{qinv}(f) \to \mathsf{isequiv}(f)$ direction, $g$ can play the role of both $g$ and $h$, i.e. we take $(g, \alpha, \beta)$ to $(g, \alpha, g, \beta)$.

```rzk
#def qinv-to-isequiv
  ( A B : U)
  ( f : A → B)
  : qinv A B f → isequiv A B f
  := \ (g , (α , β)) → ((g , α) , (g , β))
```

### Proof of Property 2

For the other direction, we are given $(g, \alpha, h, \beta)$. Notice that $h \circ f \circ g \sim_{\alpha} h$ and $h \circ f \circ g \sim_{\beta} g$. Let $\gamma$ be the composite homotopy

    $$g \sim_{\beta^{-1}} h \circ f \circ g \sim_{\alpha} h,$$

    meaning $\gamma(x) :\equiv \beta(g(x))^{-1} \cdot h(\alpha(x))$. Now define $\beta'(x) :\equiv \gamma(f(x)) \cdot \beta(x)$. Then $(g, \alpha, \beta) : \mathsf{qinv}(f)'$.

```rzk
#def isequiv-to-qinv
  ( A B : U)
  ( f : A → B)
  : isequiv A B f → qinv A B f
  :=
  \ ((g , α) , (h , β)) →
    ( g
      , ( α
        , \ x →
            -- g (f x) = h (f (g (f x))) = h (f x) = x
            path-concat A -- g (f x) = id x
            ( compose A B A g f x)
            ( compose A B A h f x)
            ( id A x)
            ( path-concat A -- g (f x) = h (f x)
              ( g (f x))
              ( h (f (g (f x))))
              ( h (f x))
              ( path-sym A -- g (f x) = (h . f . g) (f x)
                ( compose A B A h f (g (f x)))
                ( id A (g (f x)))
                ( β (g (f x))))
              ( ap B A h -- (h . f . g) (f x) = h (f x)
                ( compose B A B f g (f x))
                ( id B (f x))
                ( α (f x))))
            ( β x))) -- h (f x) = id x
```

### Proof of Property 3

Proof of the third property requires identifying the identity types of cartesian products and dependent pair types,
which are discussed in Sections [2.6](06-cartesian-product-types.rzk.md) and [2.7](07-sigma-types.rzk.md).

## Equivalence of types

!!! lemma "Definition 2.4.11."
    An equivalence from type $A$ to type $B$ is defined to be a function $f : A \to B$ together with an inhabitant of $\mathsf{isequiv}(f)$.

    $$(A \simeq B) :\equiv \sum_{(f:A \to B)} \mathsf{isequiv}(f).$$

!!! lemma "Note"
    If we have a function $f : A \to B$ and we know that $e : \mathsf{isequiv}(f)$, we may write $f : A \simeq B$, rather than $(f, e)$.

```rzk
#def equivalence
  ( A B : U)
  : U
  := Σ (f : A → B) , isequiv A B f
```

## Type equivalences are equivalence relations

!!! lemma "Lemma 2.4.12."

    Type equivalence is an equivalence relation on $U$. More specifically:

    1. For any $A$, the identity function $id_A$ is an equivalence; hence $A \simeq A$.
    2. For any $f : A \simeq B$, we have an equivalence $f^{-1} : B \simeq A$.
    3. For any $f : A \simeq B$ and $g : B \simeq C$, we have $g \circ f : A \simeq C$.

### Reflexivity

```rzk
#def equivalence-refl
  ( A : U)
  : equivalence A A
  :=
  ( id A
  , ( ( id A , \ x → refl)
    , ( id A , \ x → refl)))
```

### Symmetry

```rzk
#def inverse-from-equivalence
  ( A B : U)
  : equivalence A B → (B → A)
  :=
  \ (f , isequiv-f) →
    inverse-from-qinv A B f (isequiv-to-qinv A B f isequiv-f)

#def isequiv-inverse-from-equivalence
  ( A B : U)
  : ( f : equivalence A B)
  → isequiv B A (inverse-from-equivalence A B f)
  :=
  \ (f , isequiv-f) →
    qinv-to-isequiv B A
    ( inverse-from-equivalence A B (f , isequiv-f))
    ( qinv-inverse-from-qinv A B f (isequiv-to-qinv A B f isequiv-f))

#def equivalence-sym
  ( A B : U)
  : equivalence A B → equivalence B A
  :=
  \ f →
    ( inverse-from-equivalence A B f
    , isequiv-inverse-from-equivalence A B f)
```

### Transitivity

```
#define qinv-trans
  ( A B C : U)
  ( f : A → B)
  ( g : B → C)
  : qinv A B f → qinv B C g → qinv A C (compose A B C g f)
  :=
  \ (f⁻¹ , (α-f , β-f)) (g⁻¹ , (α-g , β-g)) →
    ( compose C B A f⁻¹ g⁻¹
    , ( \ c →
          path-concat C
          ( g (f (f⁻¹ (g⁻¹ c))))
          ( g (g⁻¹ c))
          ( c)
          ( ap B C g
            ( f (f⁻¹ (g⁻¹ c)))
            ( g⁻¹ c)
            ( α-f (g⁻¹ c)))
          ( α-g c)
      , \ a →
          path-concat A
          ( f⁻¹ (g⁻¹ (g (f a))))
          ( f⁻¹ (f a))
          (a)
          ( ap B A f⁻¹
            (g⁻¹ (g (f a)))
            (f a)
            ( α-f (g⁻¹ c)))
          ( α-g c)))

#def equivalence-trans
  ( A B C : U)
  : equivalence A B → equivalence B C → equivalence A C
  :=
  \ (f , isequiv-f) (g , isequiv-g) →
    ( \ ((f⁻¹ , (α-f , β-f)) : (qinv A B f)) ((g⁻¹ , (α-g , β-g)) : (qinv B C g)) →
        ( compose A B C g f
        , qinv-to-isequiv A C (compose A B C g f)
            ( compose C B A f⁻¹ g⁻¹
            , ( \ c → path-concat C -- g f f⁻¹ g⁻¹ c = g g⁻¹ c = c
                ( g (f (f⁻¹ (g⁻¹ (c)))))
                ( g (g⁻¹ (c)))
                ( c)
                ( ap B C g (f (f⁻¹ (g⁻¹ (c)))) (g⁻¹ (c)) (α-f (g⁻¹ (c))))
                ( α-g c)
              , \ a → path-concat A -- f⁻¹ g⁻¹ g f a = f⁻¹ f a = a
                ( f⁻¹ (g⁻¹ (g (f (a)))))
                ( f⁻¹ (f (a)))
                ( a)
                ( ap B A f⁻¹ (g⁻¹ (g (f (a)))) (f (a)) (β-g (f (a))))
                ( β-f a)))))
  ( isequiv-to-qinv A B f isequiv-f)
  ( isequiv-to-qinv B C g isequiv-g)
```

## Proof of Corollary 2.4.4

``` title="Proof for corollary 2.4.4. Homotopy with id"
lemma 2.4.3 :  H(x) • g  (p)   = f (p)   • H y

Substitutions:
x → f x
y → x
g → id
p → H x

Result of application of lemma with the corresponding values:
H(f x) • id (H x) = f (H x) • H x


By right-concatenating (H x)⁻¹ to the both sides, we have
H(f x) = H(f x) • id (H x) • (H x)⁻¹ = f (H x) • H x • (H x)⁻¹ = f (H x)
```


```rzk
#def homotopy-id-swap
     ( A : U)
     ( f : A → A)
     ( H : homotopy A (\ _ → A) f (id A))
     ( x : A)
  : H (f x) = ap A A f (f x) (id A x) (H x)
  := 3-path-concat
          ( f (f x) = (f x)) -- type of points
          -- 1st point: H (f x)
          ( H (f x))
          -- 2nd point: (H (f x) • (H x)) • (H x)⁻¹
          ( path-concat A (f (f x)) x (f x) (path-concat A (f (f x)) (f x) x (H (f x)) (H x)) (path-sym A (f x) x (H x)))
          -- 3rd point:  (f (H x) • (H x)) • (H x)⁻¹
          ( path-concat A (f (f x)) x (f x) (path-concat A (f (f x)) (f x) x (ap A A f (f x) x (H x)) (H x)) (path-sym A (f x) x (H x)))
          -- 4th point: f (H x)
          ( ap A A f (f x) x (H x))
          -- proof that H (f x) = (H (f x) • H x) • (H x)⁻¹
          ( path-sym
               ( f (f x) = f x)
               ( path-concat A (f (f x)) x (f x) (path-concat A (f (f x)) (f x) x (H (f x)) (H x)) (path-sym A (f x) x (H x)))
               ( H (f x))
               ( right-concat-right-inv-remove-refl A (f (f x)) (f x) x (H (f x)) (H x)))
          -- proof that (H (f x) • H x) • (H x)⁻¹ = (f (H x) • (H x)) • (H x)⁻¹
          ( ap
               ( f (f x) = x) -- (type of domain)
               ( f (f x) = f x) -- (type of codomain)
               ( \ p' → path-concat A (f (f x)) x (f x) p' (path-sym A (f x) x (H x)))
               -- function-to-apply: whiskering by (Hx)⁻¹, a.k.a. cancel out H x
               ( path-concat A (f (f x)) (f x) x (H (f x)) (H x)) -- left point in path below
               ( path-concat A (f (f x)) (f x) x (ap A A f (f x) x (H x)) (H x)) -- right point in path below
               ( path-concat
                    ( f (f x) = x)
                    -- (H (f x) • H x)
                    ( path-concat A (f (f x)) ((\ (z : A) → z) (f x)) ((\ (z : A) → z) x) (H (f x)) (H x))
                    -- (H (f x) • id (H x))
                    ( path-concat A (f (f x)) ((\ (z : A) → z) (f x)) ((\ (z : A) → z) x) (H (f x)) (ap A A (\ (z : A) → z) (f x) x (H x)))
                    -- f (H x) • (H x)
                    ( path-concat A (f (f x)) (f x) ((\ (z : A) → z) x) (ap A A f (f x) x (H x)) (H x))
                    -- (H (f x) • H x) = (H (f x) • id (H x))
                    ( ap
                         ( f x = x) -- domain
                         ( ( f (f x)) = x) -- codomain
                         ( \ p' → path-concat A (f (f x)) ((\ (z : A) → z) (f x)) ((\ (z : A) → z) x) (H (f x)) p') -- action of concatenation
                         ( H x) -- left point in path
                         ( ap A A (\ z → z) (f x) x (H x)) -- right point in path
                         ( path-sym (f x = x) (ap A A (\ z → z) (f x) x (H x)) (H x) (ap-id A (f x) x (H x))))
                    -- (H (f x) • id (H x)) = f (H x) • (H x)
                    ( hom-naturality A A f (\ z → z) H (f x) x (H x))))
          -- proof that (f (H x) • (H x)) • (H x)⁻¹ = f (H x)
          ( right-concat-right-inv-remove-refl A (f (f x)) (f x) x (ap A A f (f x) (id A x) (H x)) (H x))
```

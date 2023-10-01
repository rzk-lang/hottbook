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

## Homotopies are equivalence relations
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

Proof is given in the end of the file.
```rzk
-- #def homotopy-id-swap
--     (A : U)
--     (f : A → A)
--     (H : homotopy A (\ _ → A) f (id A))
--     (x : A)
--     : H (f x) = ap A A f (f x) (id A x) (H x)
--     :=
```

## Quasi-Inverses
The traditional notion of isomorphism is poorly behaved for proof-relevant mathematics. Thus, it is given the name of quasi-inverse.
!!! lemma "Definition 2.4.6."
    For a function $f : A → B$, a quasi-inverse of $f$ is a triple $(g, \alpha, \beta)$ consisting of a function $g : B → A$ and homotopies $\alpha : f \circ g \sim id_B$ and $\beta : g \circ f \sim id_A$.

```rzk
#def qinv
    (A B : U)
    (f : A → B)
    : U
    := Σ (g : B → A),
        prod
                        (homotopy B (\ _ → B) (compose B A B f g) (id B))
                        (homotopy A (\ _ → A) (compose A B A g f) (id A))
```

### Examples
!!! note "Example 2.4.7. Identity quasi-inverse"
     The identity function $id_A : A \to A$ has a quasi-inverse given by $id_A$ itself, together with homotopies defined by $\alpha(y) :\equiv \mathsf{refl}_y$ and $\beta(x) :\equiv \mathsf{refl}_x$.

```rzk
#def qinv-id
     (A : U)
     : qinv A A (id A)
     := (id A, 
          (\ x → refl, 
          \ x → refl))
```

!!! note "Example 2.4.8. Quasi-inverse for path concatenation"
     For any $p : x =_A y$ and $z : A$, the functions $(p \cdot –) : (y =_A z) \to (x =_A z)$ and $(– \cdot p) : (z =_A x) \to (z =_A y)$ have quasi-inverses given by $(p^{−1} \cdot –)$ and $(– \cdot p^{−1})$, respectively.

**Quasi-inverse of the concatenation from the right side.**

!!! note "Change of variables in the code"
     Note the change of variables: $p \mapsto q, x \mapsto y, y \mapsto z, z \mapsto x$. That is, the code corrsesponds to the statement that for any $q : y =_A z$ and $x : A$, the function $(– \cdot q) : (x =_A y) \to (x =_A z)$ have quasi-inverse given by $(– \cdot q^{−1})$, respectively.


```rzk title="Definition of right concatenation as a function, and its inverse"
#def right-concat
     (A : U)
     (x y z : A)
     (q : y = z)
     : (x = y) → (x = z)
     := \ p → path-concat A x y z p q


#def right-concat-inv
     (A : U)
     (x y z : A)
     (q : y = z)
     : (x = z) → (x = y)
     := right-concat A x z y (path-sym A y z q)

```

```rzk title="Proofs that both compositions are homotopical to identity"
#def right-concat-right-inv-remove-refl
     (A : U)
     (x y z : A)
     (p : x = y)
     (q : y = z)
     : (compose (x = y) (x = z) (x = y) (right-concat-inv A x y z q) (right-concat A x y z q)) p = p
     := 3-path-concat
          (x = y) -- type of things that are connected my paths
          -- 1st point: (p • q) • q⁻¹
          (compose (x = y) (x = z) (x = y) (right-concat-inv A x y z q) (right-concat A x y z q) p)
          -- 2nd point: p • (q • q⁻¹)
          (path-concat A x y y p (path-concat A y z y q (path-sym A y z q)))
          -- 3rd point: p • refl
          (path-concat A x y y p refl)
          -- 4th point: p
          p
          -- 1st proof: (p • q) • q⁻¹ = p • (q • q⁻¹)
          (concat-assoc-2 A x y z y
               p
               q
               (path-sym A y z q)
          )
          -- 2nd proof: p • (q • q⁻¹) = p • refl
          (ap
               (y = y)
               (x = y)
               (\ p' → (path-concat A x y y p p'))
               (path-concat A y z y q (path-sym A y z q))
               refl
               (inverse-r A y z q)
          )
          -- 3rd proof: p • refl = p
          (path-sym (x = y) p (path-concat A x y y p refl) (concat-refl A x y p))


#def right-concat-left-inv-remove-refl
     (A : U)
     (x y z : A)
     (r : x = z)
     (q : y = z)
     : (compose (x = z) (x = y) (x = z) (right-concat A x y z q) (right-concat-inv A x y z q)) r = r
     := 3-path-concat
          (x = z) -- type of things that are connected my paths
          -- 1st point: (r • q⁻¹) • q
          (compose (x = z) (x = y) (x = z) (right-concat A x y z q) (right-concat-inv A x y z q) r)
          -- 2nd point: r • (q⁻¹ • q)
          (path-concat A x z z r (path-concat A z y z (path-sym A y z q) q))
          -- 3rd point: r • refl
          (path-concat A x z z r refl)
          -- 4th point: p
          r
          -- 1st proof: (r • q⁻¹) • q = r • (q⁻¹ • q)
          (concat-assoc-2 A x z y z
               r
               (path-sym A y z q)
               q
          )
          -- 2nd proof: r • (q⁻¹ • q) = r • refl
          (ap
               (z = z)
               (x = z)
               (\ p' → (path-concat A x z z r p'))
               (path-concat A z y z (path-sym A y z q) q)
               refl
               (inverse-l A y z q)
          )
          -- 3rd proof: r • refl = r
          (path-sym (x = z) r (path-concat A x z z r refl) (concat-refl A x z r))
```     

```rzk title="Proof for quasi-inverse of right concatenation"
#def right-concat-inv-is-qinv-for-right-concat
     (A : U)
     (x y z : A)
     (q : y = z)
     : qinv (x = y) (x = z) (right-concat A x y z q)
     := (right-concat-inv A x y z q,
          (
               \ (r : x = z) → right-concat-left-inv-remove-refl  A x y z r q,
               \ (p : x = y) → right-concat-right-inv-remove-refl A x y z p q
          ))
```


## Equivalences
An improved notion, `isequiv`, has the following properties:

1. For each $f : A \to B$ there is a function $qinv(f) \to isequiv(f)$
2. Similarly, for each $f$ we have $isequiv(f) \to qinv(f)$; thus the two are logically equivalent.
3. For any two inhabitants $e_1, e_2 : isequiv(f)$, we have $e_1 = e_2$.

One of numerous, but equivalent ways to define `isequiv`:
!!! lemma "Definition 2.4.10."
    $$isequiv(f) :\equiv (\Sigma_{(g:B \to A)} (f \circ g \sim id_B)) \times (\Sigma_{(h:B \to A)} (h \circ f \sim id_A)).$$

```rzk
#def isequiv
    (A B : U)
    (f : A → B)
    : U
    := prod
        (Σ (g : B → A), homotopy B (\ _ → B) (compose B A B f g) (id B))
        (Σ (h : B → A), homotopy A (\ _ → A) (compose A B A h f) (id A))
```

1. For the $qinv(f) \to isequiv(f)$ direction, $g$ can play the role of both $g$ and $h$, i.e. we take $(g, \alpha, \beta)$ to $(g, \alpha, g, \beta)$.

```rzk
#def qinv-to-isequiv
    (A B : U)
    (f : A → B)
    : (qinv A B f) → (isequiv A B f)
    := \ (g, (α, β)) → ((g, α), (g, β))
```

2. For the other direction, we are given $(g, \alpha, h, \beta)$. Notice that $h \circ f \circ g \sim_{\alpha} h$ and $h \circ f \circ g \sim_{\beta} g$. Let $\gamma$ be the composite homotopy

$$g \sim_{\beta^{-1}} h \circ f \circ g \sim_{\alpha} h,$$

meaning $\gamma(x) :\equiv \beta(g(x))^{-1} \cdot h(\alpha(x))$. Now define $\beta'(x) :\equiv \gamma(f(x)) \cdot \beta(x)$. Then $(g, \alpha, \beta) : qinv(f)'$.

```rzk
#def isequiv-to-qinv
    (A B : U)
    (f : A → B)
    : (isequiv A B f) → (qinv A B f)
    := \ ((g, α), (h, β)) →
        (g,
            (α,
                \ x → path-concat -- g (f x) = id x
                    A
                    (compose A B A g f x)
                    (compose A B A h f x)
                    (id A x)
                    (path-concat -- g (f x) = h (f x)
                        A
                        (g (f x))
                        (h (f (g (f x))))
                        (h (f x))
                        (path-sym -- g (f x) = (h . f . g) (f x)
                            A
                            (compose A B A h f (g (f x)))
                            (id A (g (f x)))
                            (β (g (f x)))
                        )
                        (ap -- (h . f . g) (f x) = h (f x)
                            B
                            A
                            h
                            (compose B A B f g (f x))
                            (id B (f x))
                            (α (f x))
                        )
                    )
                    (β x) -- h (f x) = id x
            )
        )
```

3. Proof of the third property requires identifying the identity types of cartesian products and dependent pair types, which are discussed in Sections 2.6 and 2.7.

## Equivalence of types
!!! lemma "Definition 2.4.11."
    An equivalence from type $A$ to type $B$ is defined to be a function $f : A \to B$ together with an inhabitant of $isequiv(f)$.

    $$(A \simeq B) :\equiv \Sigma_{(f:A \to B)} isequiv(f).$$

!!! lemma "Note"
    If we have a function $f : A \to B$ and we know that $e : isequiv(f)$, we may write $f : A \simeq B$, rather than $(f, e)$.

```rzk
#def equivalence
    (A B : U)
    : U
    := Σ (f : A → B), isequiv A B f
```

## Type equivalences are equivalence relations
!!! lemma "Lemma 2.4.12."
    Type equivalence is an equivalence relation on $U$. More specifically:

    1. For any $A$, the identity function $id_A$ is an equivalence; hence $A \simeq A$.
    2. For any $f : A \simeq B$, we have an equivalence $f^{-1} : B \simeq A$.
    3. For any $f : A \simeq B$ and $g : B \simeq C$, we have $g \circ f : A \simeq C$.

1. Reflexivity
```rzk
#def equivalence-refl
    (A : U)
    : equivalence A A
    := (id A, ((id A, \ x → refl), (id A, \ x → refl)))
```

2. Symmetry
```rzk
#def equivalence-sym
    (A B : U)
    : equivalence A B → equivalence B A
    := \ (f, isequiv-f) →
        ( first (isequiv-to-qinv A B f isequiv-f)
        , qinv-to-isequiv
            B
            A
            (first (isequiv-to-qinv A B f isequiv-f))
            ( f
            , ( second (second (isequiv-to-qinv A B f isequiv-f))
              , first (second (isequiv-to-qinv A B f isequiv-f))
              )
            )
        )
```

3. Transitivity
```rzk
-- #def equivalence-trans
--     (A B C : U)
--     : equivalence A B → equivalence B C → equivalence A C
--     := \ (f, isequiv-f) (g, isequiv-g) →
```



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
     (A : U)
     (f : A → A)
     (H : homotopy A (\ _ → A) f (id A))
     (x : A)
     : H (f x) = ap A A f (f x) (id A x) (H x)
     := 3-path-concat
          (f (f x) = (f x)) -- type of points
          -- 1st point: H (f x)
          (H (f x))
          -- 2nd point: (H (f x) • (H x)) • (H x)⁻¹
          (path-concat A (f (f x)) x (f x) (path-concat A (f (f x)) (f x) x (H (f x)) (H x)) (path-sym A (f x) x (H x)))
          -- 3rd point:  (f (H x) • (H x)) • (H x)⁻¹ 
          (path-concat A (f (f x)) x (f x) (path-concat A (f (f x)) (f x) x (ap A A f (f x) x (H x)) (H x)) (path-sym A (f x) x (H x)))
          -- 4th point: f (H x)
          (ap A A f (f x) x (H x))
          -- proof that H (f x) = (H (f x) • H x) • (H x)⁻¹
          (path-sym
               (f (f x) = f x) 
               (path-concat A (f (f x)) x (f x) (path-concat A (f (f x)) (f x) x (H (f x)) (H x)) (path-sym A (f x) x (H x)))
               (H (f x))
               (right-concat-right-inv-remove-refl A (f (f x)) (f x) x (H (f x)) (H x)))
          -- proof that (H (f x) • H x) • (H x)⁻¹ = (f (H x) • (H x)) • (H x)⁻¹
          (ap 
               (f (f x) = x) -- (type of domain) 
               (f (f x) = f x) -- (type of codomain) 
               (\ p' → path-concat A (f (f x)) x (f x) p' (path-sym A (f x) x (H x)))
               -- function-to-apply: whiskering by (Hx)⁻¹, a.k.a. cancel out H x
               (path-concat A (f (f x)) (f x) x (H (f x)) (H x)) -- left point in path below
               (path-concat A (f (f x)) (f x) x (ap A A f (f x) x (H x)) (H x)) -- right point in path below
               (path-concat
                    (f (f x) = x)
                    -- (H (f x) • H x)
                    (path-concat A (f (f x)) ((\ (z : A) → z) (f x)) ((\ (z : A) → z) x) (H (f x)) (H x))
                    -- (H (f x) • id (H x))
                    (path-concat A (f (f x)) ((\ (z : A) → z) (f x)) ((\ (z : A) → z) x) (H (f x)) (ap A A (\ (z : A) → z) (f x) x (H x)))
                    -- f (H x) • (H x)
                    (path-concat A (f (f x)) (f x) ((\ (z : A) → z) x) (ap A A f (f x) x (H x)) (H x))
                    -- (H (f x) • H x) = (H (f x) • id (H x))
                    (ap
                         (f x = x) -- domain
                         ((f (f x)) = x) -- codomain
                         (\p' → path-concat A (f (f x)) ((\ (z : A) → z) (f x)) ((\ (z : A) → z) x) (H (f x)) p') -- action of concatenation
                         ( H x ) -- left point in path
                         (ap A A (\ z → z) (f x) x (H x)) -- right point in path
                         (path-sym (f x = x) (ap A A (\ z → z) (f x) x (H x)) (H x) (ap-id A (f x) x (H x))))
                    -- (H (f x) • id (H x)) = f (H x) • (H x)
                    (hom-naturality A A f (\ z → z) H (f x) x (H x))))
          -- proof that (f (H x) • (H x)) • (H x)⁻¹ = f (H x)
          (right-concat-right-inv-remove-refl A (f (f x)) (f x) x (ap A A f (f x) (id A x) (H x)) (H x))
```
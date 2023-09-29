# 2.3 Type families are fibrations

This is a literate Rzk file:

```rzk
#lang rzk-1
```

## Transport, path lifting, and dependent map
!!! note "Lemma 2.3.1. Transport"
    Suppose that $P$ is a type family over $A$ and that $p : x =_A y$. Then there is a function $p_\ast : P(x) → P(y)$.

```rzk  
#def transport
    (A : U)
    (P : A → U)
    (x y : A)
    (p : x = y)
    : P x → P y
    := path-ind
        A
        (\ x' y' p' → P x' → P y')
        -- ? : P x' → P x'
        (\ x' → \ px → px)
        x y p
```

!!! note "Lemma 2.3.2. Path lifting property"
    Let $P : A \to U$ be a type family over $A$ and assume we have $u : P(x)$ for some $x : A$. Then for any $p : x = y$, we have
    $\mathsf{lift}(u, p) : (x, u) = (y, p_\ast(u))$ in $\Sigma_{(x:A)} P(x)$, such that $\mathsf{pr}_1(\mathsf{lift}(u, p)) = p$    .

```rzk  
#def lift
    (A : U)
    (P : A → U)
    (x : A)
    (u : P x)
    (y : A)
    (p : x = y)
    : (x, u) =_{Σ (z : A), P z} (y, (transport A P x y p u))
    := path-ind
        A
        (\ x' y' p' → (u' : P x') → (x', u') =_{Σ (z : A), P z} (y', (transport A P x' y' p' u')))
        -- ? : (u' : P x') → (x', u') = (x', (transport A P x' x' refl u')))
        -- (u' : P x') → (x', u') = (x', ((\px → px) u'))
        -- u' → (x, u) = (x, u)
        (\ x' u' → refl)
        x y p u
```


!!! note "Lemma 2.3.4. Dependent map"
    Suppose $f : \Pi_{(x:A)} P(x)$; then we have a map $\mathsf{apd}_f : \Pi_{p:x=y} (p_\ast(f(x)) =_{P(y)} f(y))$.

```rzk  
#def apd
    (A : U)
    (P : A → U)
    (f : (z : A) → P z)
    (x y : A)
    (p : x = y)
    : transport A P x y p (f x) = f y
    := path-ind
        A
        (\ x' y' p' → transport A P x' y' p' (f x') = f y')
        -- ? : transport A P x x refl (f x) = f x
        -- path-ind A C (\ x' → \ px → px) x x refl) (f x) = (f x)
        -- (\ px → px) (f x) = (f x)
        (\ x' → refl)
        x y p 
```

## Dependent and non-dependent maps
!!! note "Lemma 2.3.5. Transport in a constant type family"
    If $P : A \to U$ is defined by $P(x) :\equiv B$ for a fixed $B : U$, then for any $x,y : A$ and $p : x = y$ and $b : B$ we have a path
    $\mathsf{transportconst}^B_p (b) : \mathsf{transport}^P(p, b) = b$.
```rzk  
#def transportconst
    (A B : U)
    (b : B)
    (x y : A)
    (p : x = y)
    : transport A (\ _ → B) x y p b = b
    := path-ind
        A
        (\ x' y' p' → transport A (\ _ → B) x' y' p' b = b)
        -- ? : transport A (\ _ → B) x' x' refl b = b
        -- (\ px → px) b = b
        (\ x' → refl)
        x y p 
```


!!! note "Functions 2.3.6 and 2.3.7"
    Inverse equivalences that relate $\mathsf{ap}_f(p)$ and $\mathsf{apd}_f(p)$:

    - $(f(x) = f(y)) \to (p_\ast(f(x)) = f(y))$, and

    - $(p_\ast(f(x)) = f(y)) \to (f(x) = f(y))$

```
given
transportconst A B (f x) x y p  : transport A (\ _ → B) x y p (f x) = f x
and a hypothesis                : f x = f y

find                            : transport A (\ _ → B) x y p (f x) = f y
```

```rzk  
#def ap2apd
    (A B : U)
    (x y : A)
    (p : x = y)
    (f : A → B)
    : (f x = f y) → (transport A (\ _ → B) x y p (f x) = f y) 
    := \ fp → path-concat B (transport A (\ _ → B) x y p (f x)) (f x) (f y) 
        (transportconst A B (f x) x y p) 
        fp
```

```
given
transportconst A B (f x) x y p  : transport A (\ _ → B) x y p (f x) = f x
and a hypothesis                : transport A (\ _ → B) x y p (f x) = f y

find                            : f x = f y
```

```rzk  
#def apd2ap
    (A B : U)
    (x y : A)
    (p : x = y)
    (f : A → B)
    : (transport A (\ _ → B) x y p (f x) = f y) → (f x = f y) 
    := \ fpd → path-concat B (f x) (transport A (\ _ → B) x y p (f x)) (f y) 
        (path-sym B (transport A (\ _ → B) x y p (f x)) (f x) (transportconst A B (f x) x y p))
        fpd
```



!!! note "Lemma 2.3.8. $\mathsf{ap}$ and $\mathsf{apd}$ in a constant type family"
    For $f : A \to B$ and $p : x =_A y$, we have
    $\mathsf{apd}_f(p) = \mathsf{transportconst}_p^B(f(x)) \cdot \mathsf{ap}_f(p)$


```rzk  
#def apd-ap
    (A B : U)
    (x y : A)
    (p : x = y)
    (f : A → B)
    : apd A (\ _ → B) f x y p = path-concat B (transport A (\ _ → B) x y p (f x)) (f x) (f y) 
        (transportconst A B (f x) x y p) (ap A B f x y p)
    := path-ind 
        A
        (\ x' y' p' → apd A (\ _ → B) f x' y' p' = path-concat B (transport A (\ _ → B) x' y' p' (f x')) (f x') (f y') 
            (transportconst A B (f x') x' y' p') (ap A B f x' y' p'))
        -- ? : apd A (\ _ → B) f x' x' refl = path-concat B (transport A (\ _ → B) x' x' refl (f x')) (f x') (f x') 
        --    (transportconst A B (f x') x' x' refl) (ap A B f x' x' refl) ===
        -- refl = path-concat B (f x') (f x') (f x') refl refl
        (\ _ → refl)
        x y p
```

## Properties of transport
!!! note "Lemma 2.3.9. Transport along a concatenation of paths"
    Given $P : A \to U$ with $p : x =_A y$ and $q : y =_A z$ while $u:P(x)$, we have $q_\ast(p_\ast(u)) = (p \cdot q)_\ast(u)$.

```rzk  
#def transport-concat
    (A : U)
    (P : A → U)
    (x y z : A)
    (p : x = y)
    (q : y = z)
    (u : P x)
    : transport A P y z q (transport A P x y p u) = transport A P x z (path-concat A x y z p q) u
    := (path-ind 
        A
        (\ x' y' p' → (z' : A) → (q' : y' = z') → (u' : P x') → transport A P y' z' q' (transport A P x' y' p' u') = transport A P x' z' (path-concat A x' y' z' p' q') u')
        -- ? : (z' : A) → (q' : y' = z') → (u' : P x') → transport A P x' z' q' (transport A P x' x' refl u) = transport A P x' z' (path-concat A x' x' z' refl q') u
        -- \ (z' : A) → (q' : y' = z') → (u' : P x') → transport A P x' z' q' u = transport A P x' z' q' u
        (\ x' z' q' u' → refl)
        x y p) z q u
```


!!! note "Lemma 2.3.10. Transport along a path obtained by $\mathsf{ap}_f$" 
    For a function $f : A \to B$ and a type family $P : B \to U$, and any $p : x =_A y$ and $u : P(f(x))$, we have
    $\mathsf{transport} ^{P \circ f}(p,u) = \mathsf{transport}^P(\mathsf{ap}_f(p),u)$.

```rzk  
#def transport-ap
    (A B : U)
    (P : B → U)
    (f : A → B)
    (x y : A)
    (p : x = y)
    (u : P (f x))
    : transport A (\ z → P (f z)) x y p u = transport B P (f x) (f y) (ap A B f x y p) u
    := (path-ind 
        A
        (\ x' y' p' → (u' : P (f x')) → transport A (\ z → P (f z)) x' y' p' u' = transport B P (f x') (f y') (ap A B f x' y' p') u')
        -- ? :  (u : P x') → transport A (\ z → P (f z)) x' x' refl = transport B P (f x') (f x') (ap A B f x' x' refl)
        -- (u : P x') → id u = transport B P (f x') (f x') refl u
        -- (u : P x') → id u = id u
        (\ x' u' → refl)
        x y p) u
```

!!! note "Lemma 2.3.11. Function from fiber to fiber and transport in different type families can be rearranged"
    For $P, Q : A \to U$ and a family of functions $f : \Pi_{(x:A)} P(x) \to Q(x)$, 
    and any $p : x =_A y$ and $u : P(x)$, we have $\mathsf{transport}^Q(p, f_x(u)) = f_y(\mathsf{transport}^P(p, u))$.

```rzk  
#def transport-f
    (A : U)
    (P Q : A → U)
    (f : (x : A) → (P x) → (Q x))
    (x y : A)
    (p : x = y)
    (u : P x)
    : transport A Q x y p (f x u) = f y (transport A P x y p u)
    := (path-ind 
        A
        (\ x' y' p' → (u' : P x') → transport A Q x' y' p' (f x' u') = f y' (transport A P x' y' p' u'))
        -- ? :  (u : P x') → transport A Q x' x' refl (f x' u') = f x' (transport A P x' x' refl u'))
        -- (u : P x') → id (f x' u') = f x' (id u'))
        -- (u : P x') → (f x' u') = (f x' u')
        (\ x' u' → refl)
        x y p) u
```
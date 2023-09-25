# 2.2 Functions are functors

This is a literate Rzk file:

```rzk
#lang rzk-1
```

## Action on paths

!!! lemma "Lemma 2.2.1"
    Suppose that $f : A → B$ is a function. 
    Then for any $x, y : A$ there is an operation  $\mathsf{ap}_f : (x =_A y) \to (f(x) =_B f(y))$.
    Moreover, for each $x : A$ we have $\mathsf{ap}_f (\mathsf{refl}_x) ≡ \mathsf{refl}_{h(x)}$.


```rzk
#def ap
    (A B : U)
    (f : A → B)
	(x y : A)
	(p : x = y)
    : f x = f y
    := path-ind
        A
        (\ x' y' p' → f x' = f y')
        (\x' → refl)
        x y p
```



## Functor laws

!!! lemma "Lemma 2.2.2"
    For functions $f : A → B$ and $g : B → C$ and paths $p : x =_A y$ and $q : y =_A z$, we have:
    
    1. $\mathsf{ap}_f(p \cdot q) = \mathsf{ap}_f(p)\cdot \mathsf{ap}_f(q)$
    2. $\mathsf{ap}_f (p^{−1}) = \mathsf{ap}_f (p)^{−1}$ 
    3. $\mathsf{ap}_g(\mathsf{ap}_f(p)) = \mathsf{ap}_{g \circ f} (p)$
    4. $\mathsf{ap}_{id_A}(p)=p$


1. $\mathsf{ap}$ disctributes over path concatetation.
```rzk      
#def ap-concat
    (A B : U)
    (f : A → B)
	(x y z : A)
	(p : x = y)
    (q : y = z)
    : ap A B f x z (path-concat A x y z p q) = 
        path-concat B (f x) (f y) (f z) (ap A B f x y p) (ap A B f y z q)
    := (path-ind
            A
            (\ x' y' p' → (z' : A) → (q' : y' = z') → ap A B f x' z' (path-concat A x' y' z' p' q') =
                    path-concat B (f x') (f y') (f z') (ap A B f x' y' p') (ap A B f y' z' q'))
            -- ? : (z' : A) → (q' : x' = z') → ap A B f x' z' (path-concat A x' x' z' refl q') =
            --      path-concat B (f x') (f x') (f z') (ap A B f x' x' refl) (ap A B f x' z' q')) ===
            -- (z' : A) → (q' : x' = z') → ap A B f x' z' q' = (ap A B f x' z' q'))
            (\x' z' q' → refl)
            x y p) z q
```
 
2. Action of path and path inversion can be reordered.
```rzk
#def ap-inverse
    (A B : U)
    (f : A → B)
	(x y : A)
	(p : x = y)
    : ap A B f y x (path-sym A x y p) =
		path-sym B (f x) (f y) (ap A B f x y p)
    := path-ind
        A
        (\ x' y' p' → ap A B f y' x' (path-sym A x' y' p') = path-sym B (f x') (f y') (ap A B f x' y' p'))
        -- ? : ap A B f x' x' (path-sym A x' x' refl) = path-sym B (f x') (f y') (ap A B f x' x' refl) ===
        -- ap A B f x' x' refl = path-sym B (f x') (f y') refl == 
        -- refl = refl
        (\ x' → refl)
        x y p
```
 
3. Sequential application of functions and application of functions composed.
```rzk      
#def ap-twice
    (A B C : U)
    (f : A → B)
    (g : B → C)
	(x y : A)
	(p : x = y)
    : ap B C g (f x) (f y) (ap A B f x y p) =
		ap A C (\ a → g (f a)) x y p
    := path-ind
        A
        (\ x' y' p' → ap B C g (f x') (f y') (ap A B f x' y' p') = ap A C (\ a → g(f a)) x' y' p')
        -- ?: ap B C g (f x') (f x') (ap A B f x' x' refl) = ap A C (\ a → g(f a)) x' x' refl ===
        -- ap B C g (f x') (f x') refl = refl
        -- refl = refl
        (\ x' → refl)
        x y p
```

4. Identity leaves the path unchanged.
```rzk  
#def ap-id
    (A : U)
    (x y : A)
    (p : x = y)
    : ap A A (\ a → a) x y p = p
    := path-ind
        A
        (\ x' y' p' → ap A A (\ a → a) x' y' p' = p')
        -- ? : ap A A (\ a → a) x' x' refl = refl
        (\ x' → refl)
        x y p
```
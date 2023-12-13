# IU HoTT Seminar 2023-12-06

```rzk
#lang rzk-1
```

# Sets and logic in HoTT


```rzk title="HoTT Book, Definition 2.4.10"
#define is-equiv
  ( A B : U)
  ( f : A → B)
  : U
  :=
  prod
    ( Σ ( g : B → A) , (y : B) → f (g y) = y)
    ( Σ ( g : B → A) , (x : A) → g (f x) = x)
```

```rzk title="HoTT Book, Definition 2.9.2"
#define happly
  ( A : U)
  ( B : A → U)
  ( f g : (a : A) → B a)
  : ( f = g) → homotopy A B f g
  :=
  path-ind ((a : A) → B a)
  ( \ f' g' _ → homotopy A B f' g')
  ( \ f' _ → refl)
  f g
```


```rzk title="HoTT Book, Axiom 2.9.3"
#define FunExt
  : U
  :=
    ( A : U)
  → ( B : A → U)
  → ( f : (a : A) → B a)
  → ( g : (a : A) → B a)
  → is-equiv
    ( f = g)
    ( homotopy A B f g)
    ( happly A B f g)
```

```rzk
#assume funext' : FunExt
```

```rzk
#define funext uses (funext')
  ( A : U)
  ( B : A → U)
  ( f g : (a : A) → B a)
  : homotopy A B f g → f = g
  := first (second (funext' A B f g))
```

```rzk
#define weak-is-set-function
  ( A B : U)
  ( is-set-B : is-set B)
  ( f g : A → B)
  ( p q : homotopy A (\ _ → B) f g)
  : homotopy A (\ x → f x = g x) p q
  := \ x → is-set-B (f x) (g x) (p x) (q x)

#define weak-is-set-function₁
  ( A B : U)
  ( is-set-B : is-set B)
  ( f g : A → B)
  ( p q : f = g)
  : homotopy A (\ x → f x = g x)
    ( happly A (\ _ → B) f g p)
    ( happly A (\ _ → B) f g q)
  :=
  weak-is-set-function A B is-set-B f g
  ( happly A (\ _ → B) f g p)
  ( happly A (\ _ → B) f g q)

#define weak-is-set-function₂ uses (funext')
  ( A B : U)
  ( is-set-B : is-set B)
  ( f g : A → B)
  ( p q : f = g)
  : happly A (\ _ → B) f g p
  = happly A (\ _ → B) f g q
  :=
  funext A (\ x → f x = g x)
  ( happly A (\ _ → B) f g p)
  ( happly A (\ _ → B) f g q)
  ( weak-is-set-function₁ A B is-set-B f g p q)

#define weak-is-set-function₃ uses (funext')
  ( A B : U)
  ( is-set-B : is-set B)
  ( f g : A → B)
  ( p q : f = g)
  : funext A (\ _ → B) f g (happly A (\ _ → B) f g p)
  = funext A (\ _ → B) f g (happly A (\ _ → B) f g q)
  :=
  ap
  ( homotopy A (\ _ → B) f g)
  ( f = g)
  ( funext A (\ _ → B) f g)
  ( happly A (\ _ → B) f g p)
  ( happly A (\ _ → B) f g q)
  ( weak-is-set-function₂ A B is-set-B f g p q)

#define funext-happly-eq-id uses (funext')
  ( A B : U)
  ( is-set-B : is-set B)
  ( f g : A → B)
  ( p : f = g)
  : funext A (\ _ → B) f g (happly A (\ _ → B) f g p)
  = p
  := second (second (funext' A (\ _ → B) f g)) p

#define path-concat3
  ( A : U)
  ( x y z w : A)
  : ( x = y) → (y = z) → (z = w) → (x = w)
  :=
  \ p q r →
    path-concat A x z w
      ( path-concat A x y z p q)
      r

#define is-set-function uses (funext')
  ( A B : U)
  ( is-set-B : is-set B)
  : is-set (A → B)
  :=
  \ f g p q →
    path-concat3 (f = g)

      p
      ( funext A (\ _ → B) f g (happly A (\ _ → B) f g p))
      ( funext A (\ _ → B) f g (happly A (\ _ → B) f g q))
      q

      ( path-sym (f = g)
        ( funext A (\ _ → B) f g (happly A (\ _ → B) f g p))
        p
        ( funext-happly-eq-id A B is-set-B f g p))
      ( weak-is-set-function₃ A B is-set-B f g p q)
      ( funext-happly-eq-id A B is-set-B f g q)
```

## Logic

```rzk
#define is-prop
  ( A : U)
  : U
  := (x : A) → (y : A) → x = y
```

```rzk
#define is-contr
  ( A : U)
  : U
  := Σ (a : A) , (x : A) → a = x
```

```rzk
#define is-prop-Unit
  : is-prop Unit
  := \ unit unit → refl

#define is-prop-function uses (funext')
  ( A : U)
  ( B : A → U)
  ( is-prop-B : (a : A) → is-prop (B a))
  : is-prop ((a : A) → B a)
  := \ f g → funext A B f g (\ a → is-prop-B a (f a) (g a))

-- #define is-set-if-is-prop
--   (A : U)
--   (is-prop-A : is-prop A)
--   : is-set A
--   :=
--   \ x y p q →
--     path-ind (x = y)
--     (\ x' y' p' → x=x' p' y'=y = q)
--     (\ x' → refl)
--     x y p

-- #define is-prop-is-prop
--   (A : U)
--   : is-prop ((a : A) → (b : A) → a = b)
--   :=
```

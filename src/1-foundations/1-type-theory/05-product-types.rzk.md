# 1.5 Product types

This is a literate Rzk file:

```rzk
#lang rzk-1
```

Rzk has built-in support for dependent pairs,
so we define product types here in terms of those.

```rzk
#define prod (A B : U)
  : U
  := Σ (_ : A), B
```

To construct a pair, we can now simply use tuple syntax for
$\Sigma$-types: `#!rzk (a, b)`.

To use a pair, we can use pattern matching or introduce projections:

```rzk
#define pr₁
  (A B : U)
  : prod A B → A
  := \ (a, _b) → a

#define pr₂
  (A B : U)
  : prod A B → B
  := \ (_a, b) → b
```

The recursor for product types can be defined as follows:

```rzk
#define prod-rec
  (A B : U)
  : (C : U) → (A → B → C) → prod A B → C
  := \ C f (a, b) → f a b
```

Then instead of defining functions such as pr1 and pr2 directly by a defining equation, we could
define

```rzk
#define pr₁-via-recursor
  (A B : U)
  : prod A B → A
  := prod-rec A B A (\ a _b → a)

#define pr₂-via-recursor
  (A B : U)
  : prod A B → B
  := prod-rec A B B (\ _a b → b)
```

To be able to define dependent functions over the product type,
we have to generalize the recursor:

```rzk
#define prod-ind
  (A B : U)
  : (C : prod A B → U) → ((x : A) → (y : B) → C (x, y)) → (x : prod A B) → C x
  := \ C f (x, y) → f x y
```

For example, in this way we can prove the propositional uniqueness principle, which says that
every element of `#!rzk A × B` is equal to a pair. Specifically, we can construct a function

```rzk
#define prod-uniq
  (A B : U)
  : (x : prod A B) → (pr₁ A B x, pr₂ A B x) =_{prod A B} x
  := \ (a, b) → refl_{(a, b)}
```

## Unit type

Rzk has a built-in `#!rzk Unit` type which behaves slightly differently from
the unit type in the HoTT Book. In particular, in Rzk, uniqueness principle
for the unit type is built in, making some proofs easier than in the book.

Still, following the book, here is the recursor for the unit type:

```rzk
#define Unit-rec
  : (C : U) → C → Unit → C
  := \ _C c _unit → c
```

And, similarly, the induction principle for the unit type:

```rzk
#define Unit-ind
  : (C : Unit → U) → C unit → (x : Unit) → C x
  := \ _C c unit → c
```

Induction enables us to prove the propositional uniqueness principle for `#!rzk Unit`,
which asserts that its only inhabitant is `#!rzk unit`:

```rzk
#define Unit-uniq
  : (x : Unit) → x = unit
  := Unit-ind (\ x → x = unit) refl_{unit}
```

As mentioned above, this uniqueness principle is built into Rzk
(making any value of type `#!rzk Unit` definitionally equal to `#!rzk unit`),
allowing to use `#!rzk refl` immediately:

```rzk
#define Unit-uniq'
  : (x : Unit) → x = unit
  := \ _ → refl
```

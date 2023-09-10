# Exercises for Section 1

!!! warning

    At the moment `rzk typecheck` does not check indented blocks,
    so solutions in this section (which are nested in admonitions)
    are not checked.

This is a literate Rzk file:

```rzk
#lang rzk-1
```

## Exercise 1.1

> Given functions $f : A \to B$ and $g : B \to C$, define their composite $g \circ f : A \to C$.
> Show that we have $h \circ (g \circ f) \equiv (h \circ g) \circ f$.

First, the definition of the composition operation:

$$
g \circ f :\equiv \lambda (x: A) . g(f(x))
$$

Then, we demonstrate associativity by evaluating both sides of the equality and reaching the same result:

$$
    \begin{align*}
        h \circ (g \circ f) & \equiv \lambda x. h((g\circ f)(x)) \\
                            & \equiv \lambda x. h(g(f(x)))
    \end{align*}
$$

$$
    \begin{align*}
        (h \circ g) \circ f & \equiv \lambda x. (h\circ g)(f(x)) \\
                            & \equiv \lambda x. (\lambda y . h(g(y)))(f(x)) \\
                            & \equiv \lambda x. h(g(f(x)))
    \end{align*}
$$

??? abstract "Solution"

    ```rzk title="Solution to Exercise 1.1"
    #define compose
      (A B C : U)
      (f : A -> B)
      (g : B -> C)
      : A -> C
      := \ x -> g (f x)

    #define composition-associativity
      (A B C D : U)
      (f : A -> B)
      (g : B -> C)
      (h : C -> D)
      (x : A)
      : compose A C D (compose A B C f g) h = compose A B D f (compose B C D g h)
      := refl
    ```

## Exercise 1.2

> Derive the recursion principle for products $rec_{A\times B}$ using only the projections, and verify that the definitional equalities are valid. Do the same for $\Sigma$-types.

The recursion principle for products has the type:

$$ rec_{A\times B} : \Pi_{C:U}(A \to B \to C) \to A \times B \to C $$

It can be defined using projection as such:

$$ rec_{A\times B}(C, g, x) :\equiv g(pr_1(x))(pr_2(x)) $$

To verify that the definitional equality is valid... // TODO

Similarly, for $\Sigma$-types, the recursion principle has the type:

$$ rec_{\Sigma_{x:A}B(x)} : \Pi_{C:U}(\Pi_{x:A} B(x) \to C) \to (\Sigma_{x:A} B(x)) \to C $$

and can be defined using the projection functions <!--($pr_1 :(\Sigma_{x:A} B(x)) \to A$ and $pr_2 : \Pi_{p:\Sigma_{x:A}B(x)}B(pr_1(p))$)--> as such:

$$ rec_{\Sigma_{x:A}B(x)}(C, g, x) :\equiv g(pr_1(x))(pr_2(x)) $$

To verify that the definitional equality is valid... // TODO

In rzk, these can be expressed as follows:

??? abstract "Solution"

    ```rzk
    #define rec_AxB
      (A B C : U)
      (g : A -> B -> C)
      (x : ∑ (x_1 : A), B)
      : C
      := g(first x)(second x)

    #define rec_sigma
      (A : U)
      (B : A -> U)
      (C : U)
      (g : (x : A) -> B x -> C)
      (x : ∑ (x_1 : A), B x_1)
      : C
      := g(first x)(second x)
    ```

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

Given functions $f : A \to B$ and $g : B \to C$,
define their composite $g \circ f : A \to C$.
Show that we have $h \circ (g \circ f) \equiv (h \circ g) \circ f$.

??? abstract "Solution"

    ```rzk title="Solution to Exercise 1.1"
    #define compose
      (A B C : U)
      (g : B → C)
      (f : A → B)
      : A → C
      := \ x → g (f x)
    ```

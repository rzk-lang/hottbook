# Example formalisation module

```rzk
#lang rzk-1
```

Here is an identity function:

```rzk
#define identity
    ( A : U)
    : A → A
    := \ x → x
```

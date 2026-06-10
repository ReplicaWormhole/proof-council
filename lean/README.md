# Erdos539 Lean formalization

This Lake project contains a Lean 4 formalization of the Erdős Problem 539
case study discussed in the write-up.

The project uses Lean 4.29.1 and mathlib 4.29.1, as pinned in
`lean-toolchain` and `lakefile.lean`.

The root module is:

```lean
import Erdos539.Main
```

Module guide:

- `Erdos539.Basic`: finite positive-difference and ordinary-difference sets.
- `Erdos539.DifferenceLower`: lower bounds for ordinary difference sets.
- `Erdos539.NumberBridge` and `Erdos539.NumberLower`: bridge between finite
  integer sets and the positive-projection formulation.
- `Erdos539.Base`: the two-dimensional base strip construction.
- `Erdos539.Suspension`: the separated suspension step.
- `Erdos539.Iteration`: iterated constructions and fixed-depth upper bounds.
- `Erdos539.Main`: the collected lower/upper logarithmic exponent estimates.

To build:

```bash
cd lean
lake exe cache get
lake build
```

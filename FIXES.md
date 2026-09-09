# Changes made to the Atlas sources

Every edit to the nine `Atlas/FC/` files is listed here. The originals are at
`facebookresearch/atlas-lean` @ `prepare-atlas-v2` (`223d8bc`), and each
`Solution.lean` carries a provenance banner naming the file it came from.

## Mechanical, applied to all nine

**Namespace rename `X` → `Atlas.X`.** Each Atlas file opens the *same* namespace as
the formal-conjectures file it targets (`namespace Green25` in both, `namespace
OeisA22030` in both, and so on). A comparator has to import both and tell the two
copies of each definition apart, which is impossible while they share a namespace.
The rename touches only the `namespace` and `end` lines; no file contained a
self-qualified reference, so nothing else needed adjusting.

`Erdos138_dvd_two_pow_solution.lean` had no closing `end` (the namespace ran to
end-of-file); one was added.

## Mathlib drift repairs

These are the changes needed to make the files compile against the Mathlib pinned by
formal-conjectures (`v4.33.1`). Each is tactic-level; none changes a statement or
closes a mathematical gap.

### Green25

`Solution.lean`, in `complemented_digit_partition`'s injectivity step. Original:

```lean
simpa [f, encodeVector] using congrArg (fun n => n - 1) hbc
```

`encodeVector v = (finFunctionFinEquiv v : ℕ) + 1`, so the proof strips the `+ 1`
with `congrArg (· - 1)` and relies on `simp` cancelling `x + 1 - 1`. It no longer
does, and the goal is left as

```
⊢ ∑ i, ↑(flipVector Q r v b i) * Q ^ ↑i + 1 - 1 = … + 1 - 1
```

against an expected equality without the `+ 1 - 1`. Replaced with an explicit
restatement plus `omega`:

```lean
have hbc' : (finFunctionFinEquiv (flipVector Q r v b) : ℕ) + 1
    = (finFunctionFinEquiv (flipVector Q r v c) : ℕ) + 1 := hbc
omega
```

This was the *only* error in the file — the mathematics is untouched.

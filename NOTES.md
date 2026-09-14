# Changes from the Atlas sources

Every `AtlasFCSolutions/<Problem>.lean` is built from the corresponding file under `Atlas/FC/` in
[facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean) at `prepare-atlas-v2`
(`223d8bc`). Nothing below changes a formal-conjectures statement.

## Why the Atlas files could not be used as they are

Each Atlas file opens the *same namespace* as the formal-conjectures file it targets and carries its
*own copy* of the definitions the statement is about (the sequence `a`, `Property25`, `XWord`, the
AME block, ...). Such a file can compile while proving a true statement about the wrong `a`. Here
those copies are deleted, and the formal-conjectures problem file is imported instead, so every
definition in every statement is formal-conjectures' own.

## Applied to all nine

- `import FormalConjecturesUtil` → `import FormalConjectures.<the problem file>`.
- Namespace `X` → `AtlasFCSolutions.X`, preceded by `open X` (formal-conjectures' namespace).
- The local copies of formal-conjectures' definitions are deleted:

  | file | deleted |
  | --- | --- |
  | `Erdos138` | `monoAP_guarantee_set`, `monoAPNumber`, `W` |
  | `Erdos337` | — |
  | `Green25` | `Property25`, `bestUpper` |
  | `OeisA108081` | `a`, `Word`, `l`, `r`, `XWord`, `xN` |
  | `OeisA211417` | `a` |
  | `OeisA22030` | `a` |
  | `Oqp35` | `Config` … `IsConstantConfig` and its instance (the whole vendored AME block) |
  | `Wotw100` | — |
  | `Wotw314` | `largestInducedPathSize` |

- `@[category research open, …]` (formal-conjectures metadata) is dropped from the final theorems.

## Final theorems whose shape differs from the Atlas file

- **Erdos138, Oqp35.** formal-conjectures states `answer(sorry) ↔ P`. Atlas proves `P`. The final
  theorem is formal-conjectures' statement with the answer filled in, `answer(True) ↔ P`, proved
  from `P`.
- **Green25.** formal-conjectures states `let ans := (answer(sorry) : ℕ → ℕ); … ∧ ¬ ∀ᶠ N, Property25 (ans N) N`.
  Atlas proved `∃ ans, … ∧ ∀ᶠ N, ¬ Property25 (ans N) N` with `ans N = O(N / (log N)²)`, by
  instantiating `complemented_digit_partition Q m r` at `r = 4 + 4t`. That lemma holds for every
  `r ≤ m`, and its sumset budget is linear in `r` against a denominator of order `Q = 2^(4m)`, so
  this file instantiates it at `r = m` instead. The Atlas construction at `r = 4 + 4t` and the Atlas
  theorem are removed; only the shared digit-partition and tiling lemmas are kept. The resulting
  answer `strongAnswer` satisfies `strongAnswer N = O(N / exp(√(log N) / 16))`
  (`strongAnswer_rate`), which is `o(N / (log N)^k)` for every `k`. The final theorem is
  formal-conjectures' statement verbatim with `answer(strongAnswer)`; its third conjunct
  `¬ ∀ᶠ N, Property25 …` follows from the stronger `∀ᶠ N, ¬ Property25 …`.

## OeisA108081: dot notation

The Atlas file proves lemmas `XWord.foo` about its own `XWord` and uses them as `hw.foo`. For
`hw : OeisA108081.XWord w`, dot notation looks in `OeisA108081.XWord`, so each such lemma is followed
by `alias _root_.OeisA108081.XWord.foo := XWord.foo`.

## Repairs for Mathlib drift

These were needed to compile the Atlas files against the Mathlib that formal-conjectures pins
(`v4.33.1`) and are carried over unchanged. None changes a statement.

- **Green25** — `simpa [f, encodeVector] using congrArg (· - 1) hbc` no longer cancels `x + 1 - 1`;
  replaced by an explicit `+ 1` equation and `omega`.
- **Wotw100** — `Finset.filter_card_add_filter_neg_card_eq_card` renamed
  `Finset.card_filter_add_card_filter_not` (2 sites).
- **OeisA108081** — `Relation.ReflTransGen.lift` now returns a relation inequality, so call sites
  supply both endpoints (`lift f h _ _ hw`) and `Function.onFun` joins two `simpa` sets (6 sites);
  `Finset.mem_antidiagonal` no longer unifies at one call site, replaced by `simpa using hij`.
- **Erdos138** — 15 tactic-level repairs: `simp` no longer normalising `algebraMap (ZMod 2) K 0/1`;
  `rw` steps that stopped matching because pattern and target differ only in a decidability
  instance (folded into `simp`, or closed with `exact`); an alpha-equivalent leftover goal (`rfl`);
  `minpoly.natDegree_le` argument renamed `K` → `A`; `LinearMap.BilinForm.Nondegenerate` is now a
  conjunction (`.1`); `omega` for a `1 ≤ a` / `0 < a` bridge; a no-op `dsimp` removed;
  `map_smul, smul_eq_mul` added to a `simp` set.
- **Oqp35** — the cast into `ZMod 5` no longer distributes over nested `ite`s, so a bridging lemma
  `q5GraphNat_cast` is proved by `decide` (not `native_decide`, which would add
  `Lean.ofReduceBool`); `Matrix.submatrix_apply` no longer fires through `Matrix.of`, replaced by
  `simp only [Matrix.submatrix, Matrix.of_apply]`; in `graphPhase_add`, summands are normalised
  by a `ring` lemma before `simp_rw`.

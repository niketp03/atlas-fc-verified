# atlas-fc-solutions

Nine problems from [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures),
each solved in a single Lean file, all compiling in one Lake project.

The proofs come from [facebookresearch/atlas-lean](https://github.com/facebookresearch/atlas-lean)
(`Atlas/FC/`, branch `prepare-atlas-v2`, commit `223d8bc`).

## How to see that each file solves the right problem

Every file follows the same pattern:

1. **It imports the formal-conjectures problem file**, e.g. `import FormalConjectures.OEIS.«22030»`.
2. **It declares none of the definitions the statement uses.** It `open`s formal-conjectures'
   namespace and uses formal-conjectures' own `a`, `W`, `Property25`, `XWord`, `ExistsAME`, ….
   The Atlas originals each carried a private copy of these; those copies are deleted (listed in
   `NOTES.md`).
3. **The last theorem has the formal-conjectures theorem's name and its statement**, in namespace
   `AtlasFCSolutions.<Problem>`, followed by `#print axioms`.

So to check a file: open it next to the formal-conjectures file linked in its header, and compare the
last theorem with formal-conjectures' theorem of the same name.

## The problems

formal-conjectures is pinned at [`990d209a`](https://github.com/google-deepmind/formal-conjectures/tree/990d209a1ffbe75e59e11267242675931f524824).

| File | formal-conjectures theorem | formal-conjectures file | Statement |
| --- | --- | --- | --- |
| [`Erdos138.lean`](AtlasFCSolutions/Erdos138.lean) | `Erdos138.erdos_138.variants.dvd_two_pow` | `ErdosProblems/138.lean` | `answer(sorry)` → `answer(True)` |
| [`Erdos337.lean`](AtlasFCSolutions/Erdos337.lean) | `Erdos337.erdos_337.variants.ruzsa_turjanyi` | `ErdosProblems/337.lean` | identical |
| [`Green25.lean`](AtlasFCSolutions/Green25.lean) | `Green25.green_25.upper` | `GreensOpenProblems/25.lean` | `answer(sorry)` → `answer(strongAnswer)` |
| [`OeisA108081.lean`](AtlasFCSolutions/OeisA108081.lean) | `OeisA108081.count_words_in_x_is_a_shifted` | `OEIS/108081.lean` | identical |
| [`OeisA211417.lean`](AtlasFCSolutions/OeisA211417.lean) | `OeisA211417.supercongruence` | `OEIS/211417.lean` | identical |
| [`OeisA22030.lean`](AtlasFCSolutions/OeisA22030.lean) | `OeisA22030.conjecture` | `OEIS/22030.lean` | identical |
| [`Oqp35.lean`](AtlasFCSolutions/Oqp35.lean) | `OpenQuantumProblem35.ame_9_10_open` | `OpenQuantumProblems/35.lean` | `answer(sorry)` → `answer(True)` |
| [`Wotw100.lean`](AtlasFCSolutions/Wotw100.lean) | `WrittenOnTheWallII.GraphConjecture100.conjecture100` | `WrittenOnTheWallII/GraphConjecture100.lean` | identical |
| [`Wotw314.lean`](AtlasFCSolutions/Wotw314.lean) | `WrittenOnTheWallII.GraphConjecture314.conjecture314` | `WrittenOnTheWallII/GraphConjecture314.lean` | identical |

"identical" means the statement text matches formal-conjectures character for character, under the
same `open`s and `variable`s. The three others differ only in the `answer(…)` slot, which
formal-conjectures leaves as `sorry` for the solver to fill:

- **Erdos138** and **Oqp35** are yes/no questions stated as `answer(sorry) ↔ P`. The proof proves
  `P`, so the answer is `True`.
- **Green25** asks for a function `ans : ℕ → ℕ` with `ans N = o(N / log N)` for which the property
  eventually fails. The answer is the explicit `strongAnswer N = #(strongPartition25 N).parts`.
  The file also proves the rate it achieves, `strongAnswer_rate`:
  `strongAnswer N = O(N / exp(√(log N) / 16))`, hence `o(N / (log N)^k)` for every fixed `k`.

## Build result

`lake build` completes with exit code 0 and no errors. Every solution depends only on the standard
axioms: no `sorryAx`, and no `Lean.ofReduceBool` (nothing uses `native_decide`).

| Theorem | Axioms |
| --- | --- |
| `AtlasFCSolutions.Erdos138.erdos_138.variants.dvd_two_pow` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.Erdos337.erdos_337.variants.ruzsa_turjanyi` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.Green25.green_25.upper` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.Green25.strongAnswer_rate` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.OeisA108081.count_words_in_x_is_a_shifted` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.OeisA211417.supercongruence` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.OeisA22030.conjecture` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.Oqp35.ame_9_10_open` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.Wotw100.conjecture100` | `propext, Classical.choice, Quot.sound` |
| `AtlasFCSolutions.Wotw314.conjecture314` | `propext, Classical.choice, Quot.sound` |

## Building

```bash
lake exe cache get   # Mathlib oleans
lake build
```

Toolchain `leanprover/lean4:v4.33.1`, the one formal-conjectures pins. `lake build` also compiles the
formal-conjectures modules these files import. The `#print axioms` output appears as `info:` lines
in the build log.

## Licence

The proofs are derivative works of `Atlas/FC/` in facebookresearch/atlas-lean (Apache 2.0,
© Meta Platforms, Inc.). Each file keeps the original copyright header. The licence is reproduced
verbatim in `LICENSE`, including the use restriction upstream prepends to Apache 2.0. `NOTES.md` lists
every change from the Atlas sources.

This repository is not affiliated with or endorsed by Meta or Google DeepMind.

# atlas-fc-verified

The nine `Atlas/FC/` Lean files from [`facebookresearch/atlas-lean`][atlas]
(branch `prepare-atlas-v2`, commit `223d8bc`), made to compile, each paired with a
**comparator** that checks the proof actually discharges the statement
[`google-deepmind/formal-conjectures`][fc] records.

Local repository — nothing here is pushed anywhere.

[atlas]: https://github.com/facebookresearch/atlas-lean
[fc]: https://github.com/google-deepmind/formal-conjectures

## Why this exists

As committed, the Atlas files cannot be built: the repository root carries no
`lakefile.toml` and no `lean-toolchain`, and every file imports
`FormalConjecturesUtil`, which lives only in formal-conjectures. So the claim
"these prove nine open problems" had never been checked by a compiler.

There is also a subtler problem that a build alone would not catch. **Every Atlas
file reuses the exact namespace of the formal-conjectures file it targets** — the
Atlas Green 25 file opens `namespace Green25`, and so does FC's `25.lean`. Each
Atlas file therefore carries its *own* copy of the definitions the statement is
about (the sequence `a`, the predicate `IsAME`, `Property25`, …). A file can
compile perfectly while proving a true statement about the wrong `a`.

The comparators exist to close that gap.

## Layout

```
AtlasVerified/<Problem>/
    Solution.lean     the Atlas proof, namespace-renamed, with drift repairs
    Comparator.lean   the check against formal-conjectures
```

| Directory | Atlas namespace → | FC target |
| --- | --- | --- |
| `Erdos138` | `Atlas.Erdos138` | `ErdosProblems/138.lean` `erdos_138.variants.dvd_two_pow` |
| `Erdos337` | `Atlas.Erdos337` | `ErdosProblems/337.lean` `erdos_337.variants.ruzsa_turjanyi` |
| `Green25` | `Atlas.Green25` | `GreensOpenProblems/25.lean` `green_25.upper` |
| `OeisA108081` | `Atlas.OeisA108081` | `OEIS/108081.lean` `count_words_in_x_is_a_shifted` |
| `OeisA211417` | `Atlas.OeisA211417` | `OEIS/211417.lean` `supercongruence` |
| `OeisA22030` | `Atlas.OeisA22030` | `OEIS/22030.lean` `conjecture` |
| `Oqp35` | `Atlas.OpenQuantumProblem35` | `OpenQuantumProblems/35.lean` `ame_9_10_open` |
| `Wotw100` | `Atlas.WrittenOnTheWallII.GraphConjecture100` | `WrittenOnTheWallII/GraphConjecture100.lean` |
| `Wotw314` | `Atlas.WrittenOnTheWallII.GraphConjecture314` | `WrittenOnTheWallII/GraphConjecture314.lean` |

## What a comparator checks

Each `Comparator.lean` does three things.

**1. Definitional identity.** For every definition both files declare:

```lean
example : Atlas.OeisA22030.a = OeisA22030.a := rfl
```

`rfl` is definitional equality — stronger than a textual diff. It survives
reformatting and fails if either side drifted.

**2. Statement closure.** The formal-conjectures theorem is restated *in
formal-conjectures' own vocabulary* and closed by the Atlas term:

```lean
theorem fc_statement_is_proved (n : ℕ) (hn : 4 ≤ n) :
    OeisA22030.a n = 4 * OeisA22030.a (n - 1) - … :=
  Atlas.OeisA22030.conjecture n hn
```

This is the load-bearing check. If any shared definition differed, it would not
typecheck. Where FC uses its `answer(sorry)` slot, the comparator says explicitly
what the answer is instantiated to and why.

**3. Axiom audit.** `#print axioms` on each `fc_statement_is_proved`, so a
`sorryAx` cannot hide. This is the fifth check `formal-conjectures`' own
`PROOFS.md` requires before a `formal_proof` claim, and the one that cannot be
done without a build.

See `STATUS.md` for results and `FIXES.md` for every change made to the Atlas
sources.

## Building

The proofs need Mathlib and formal-conjectures. Rather than make this a standalone
Lake package — which would re-clone Mathlib and rebuild everything — the build
copies `AtlasVerified/` into an existing formal-conjectures checkout that already
has ~7.2 GB of oleans built, and builds there.

```bash
./scripts/build_all.sh            # sync + build everything, print a per-file error count
./scripts/build_all.sh /tmp/logs Green25.Comparator    # one module
```

`scripts/lakeenv.sh` holds the paths and the two environment variables this
machine needs (`MATHLIB_CACHE_FROM=master`, because the legacy cache container
returns `ResourceNotFound`; and `CURL_CA_BUNDLE`, because Mathlib's bundled static
curl cannot find the system CA store).

A symlink into the checkout does **not** work — lake hangs indefinitely on a
symlinked directory in the package root — so `sync.sh` makes a real copy. The repo
stays the source of truth; edit here, then build.

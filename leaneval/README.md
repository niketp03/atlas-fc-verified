# lean-eval comparator workspaces

The nine problems as [`leanprover/lean-eval`][le] benchmark problems, so that the
Atlas proofs are checked by lean-eval's **comparator** rather than by the
hand-written `AtlasVerified/*/Comparator.lean` files.

[le]: https://github.com/leanprover/lean-eval

## What comparator adds over the hand-written comparators

`Solution.lean` in a generated workspace is a bridge that restates the trusted
`Challenge.lean` theorem and closes it with `Submission.<name>` — structurally
the same idea as `fc_statement_is_proved`. What is new is the checking:
comparator runs the workspace under a sandbox (`landrun`), exports the built
olean with `lean4export`, and replays the proof through **nanoda**, a kernel
implemented independently of Lean's, as well as Lean's own. An axiom audit by
`#print axioms` cannot do that.

There is also a structural gain. In a workspace there is exactly *one* copy of
each definition the statement is about — the trusted one in `ChallengeDeps`. The
Atlas file's own copy is deleted when porting the proof. So the failure mode the
root README is built around ("a file can compile perfectly while proving a true
statement about the wrong `a`") cannot arise inside a workspace.

## What it does not check

A lean-eval workspace depends on **Mathlib alone**. It cannot import
formal-conjectures, and it cannot import `FormalConjecturesForMathlib` either.
So each `Challenge.lean` carries a *vendored copy* of FC's statement and of
whatever vocabulary that statement needs.

That relocates the gap rather than closing it. Comparator proves

> the Atlas proof discharges **our copy** of the statement,

not

> the Atlas proof discharges **formal-conjectures'** statement.

Nothing here checks the vendored copy against FC. The `AtlasVerified/*/Comparator.lean`
files are what close that second link, against the real FC definitions by `rfl`.
Treat the two as complementary: comparator is the stronger check of the proof,
the FC comparators are the only check of the statement.

Every vendored definition is recorded in its module docstring with the FC file
it came from.

## Statement-shape deviations

Four FC targets are stated as `answer(sorry) ↔ P` or `let ans := answer(sorry)`.
`answer(…)` is formal-conjectures machinery and does not exist outside it, and a
Challenge has to be a closed proposition.

| problem | FC shape | Challenge shape |
| --- | --- | --- |
| `erdos_138_dvd_two_pow` | `answer(sorry) ↔ P` | `P` |
| `oqp35_ame_9_10` | `answer(sorry) ↔ ExistsAME 9 10` | `ExistsAME 9 10` |
| `green_25_upper` | `let ans := answer(sorry)` | `∃ ans, …` |

The first two match the instantiation the hand-written comparators already
record. The third is **weaker** than FC's idiom: FC's `AGENTS.md` says a
tautological term inside `answer()` is not a mathematical solution, and an
existential is exactly that weakening. The construction does produce an explicit
function — see `Green25Improved/` — but this Challenge does not force it.

## Toolchain

lean-eval pins Lean `v4.33.0` and Mathlib `6f1ef4e5`; formal-conjectures pins
`v4.33.1` and Mathlib `0df444a3`. The two Mathlib revisions are 34 commits
apart. The Atlas proofs ported across that gap without modification — the only
output was linter warnings that a few `omega` and `push_cast` steps are now
redundant.

`scripts/setup-tools.sh` installs the four external tools at the commits pinned
in lean-eval's `SECURITY.md`. `landrun` needs Go, `nanoda` needs Rust.

## Layout

```
LeanEval/FormalConjectures/   the nine trusted statements, vendored, @[eval_problem]
manifests/problems/           one manifest per problem
submissions/<id>/             our Submission.lean + Submission/Helpers.lean
scripts/overlay.sh            copy the above into a lean-eval checkout
scripts/setup-tools.sh        install landrun, lean4export, comparator, nanoda
```

`Challenge.lean`, `Solution.lean` and the rest of a workspace are *generated* by
`lake exe lean-eval generate`, so they are not committed. One `Challenge.lean`
is kept under `submissions/oeis_a22030_conjecture/` for reference.

## Status

| problem | statement typechecks | proof ported | comparator + nanoda |
| --- | --- | --- | --- |
| `oeis_a22030_conjecture` | yes | yes | **accepted** |
| `wotw314_conjecture` | yes | not yet | — |
| `erdos_337_ruzsa_turjanyi` | yes | not yet | — |
| `wotw100_conjecture100` | yes | not yet | — |
| `oeis_a211417_supercongruence` | yes | not yet | — |
| `oeis_a108081_count_words` | yes | not yet | — |
| `erdos_138_dvd_two_pow` | yes | not yet | — |
| `green_25_upper` | yes | not yet | — |
| `oqp35_ame_9_10` | yes | not yet | — |

All nine statements build clean against Mathlib `6f1ef4e5` (exit 0, nine `sorry`
warnings, one per statement). One problem is verified end to end:

```
Running nanoda kernel on solution
Nanoda kernel accepts the solution
Running Lean default kernel on solution.
Lean default kernel accepts the solution
Your solution is okay!
```

The remaining eight need their Atlas proofs ported into `Submission.lean`, which
means deleting each file's own copies of the now-trusted definitions:

| problem | Atlas lines | duplicates to strip |
| --- | --- | --- |
| `erdos_337_ruzsa_turjanyi` | 278 | none |
| `wotw100_conjecture100` | 343 | none |
| `wotw314_conjecture` | 880 | `largestInducedPathSize` |
| `oeis_a211417_supercongruence` | 938 | `a` |
| `green_25_upper` | 1001 | `Property25`, `bestUpper` |
| `erdos_138_dvd_two_pow` | 1070 | `monoAP_guarantee_set`, `monoAPNumber`, `W` |
| `oqp35_ame_9_10` | 1436 | the AME definition block |
| `oeis_a108081_count_words` | 3810 | `a`, `Word`, `l`, `r`, `XWord`, `xN` |

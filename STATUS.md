# Status

Last full build: 2026-09-09, `lake build` exit 0, **zero errors across all 18 modules**.

Toolchain: `leanprover/lean4:v4.33.1`, Mathlib as pinned by formal-conjectures
(`v4.33.1`). Regenerate with `./scripts/build_all.sh`, then `./scripts/status.sh`.

## Result

| Problem | Solution | Comparator | `fc_statement_is_proved` axioms |
| --- | --- | --- | --- |
| Erdos138 | ok | ok | `propext, Classical.choice, Quot.sound` |
| Erdos337 | ok | ok | `propext, Classical.choice, Quot.sound` |
| Green25 | ok | ok | `propext, Classical.choice, Quot.sound` |
| OeisA108081 | ok | ok | `propext, Classical.choice, Quot.sound` |
| OeisA211417 | ok | ok | `propext, Classical.choice, Quot.sound` |
| OeisA22030 | ok | ok | `propext, Classical.choice, Quot.sound` |
| Oqp35 | ok | ok | `propext, Classical.choice, Quot.sound` |
| Wotw100 | ok | ok | `propext, Classical.choice, Quot.sound` |
| Wotw314 | ok | ok | `propext, Classical.choice, Quot.sound` |

All nine compile, and each comparator's `fc_statement_is_proved` — the
formal-conjectures statement restated in formal-conjectures' own vocabulary and closed
by the Atlas term — depends on **only the three standard axioms**. No `sorryAx`, and no
`Lean.ofReduceBool` (nothing here uses `native_decide`; see `FIXES.md` on Oqp35).

## What this does and does not establish

**Does.** Each Atlas proof really discharges the proposition formal-conjectures records,
not a lookalike. That is not implied by the files compiling: every Atlas file reuses the
exact namespace of its FC target and so carries its *own* copy of the definitions the
statement is about, and a file can compile perfectly while proving a true statement
about the wrong `a`. The comparators pin those definitions — by `rfl` where the two
sides are definitionally equal, and by proof where they are not (see below) — and then
close the FC statement with the Atlas term.

**Does not.** This says nothing about whether the underlying mathematics is *interesting*
or whether the statements faithfully capture the informal problems. Two statement-level
caveats are recorded in the comparators themselves:

- **Erdos138** and **Oqp35** target FC theorems of the form `answer(sorry) ↔ P`. The
  Atlas files prove `P` outright, so the answer is instantiated to `True`. That is a
  faithful reading — proving `P` is exactly the content — but it is an instantiation
  choice, and it is stated explicitly in each comparator.
- **Green25** deviates from FC's `let ans := answer(sorry)` by using
  `∃ candidateAnswer`, which is weaker in FC's idiom. Its comparator states the Atlas
  shape and says so. (Separately, the bound this construction reaches can be improved
  from `N/(log N)²` to `N·exp(−c√(log N))`; that work lives outside this repo.)

## Checks that needed a proof rather than `rfl`

Three definitions could not be equated by `rfl`, for reasons that are worth recording
because each is a place a weaker comparator would have silently passed or silently
failed:

- **OeisA22030's `a`** — textually identical recursive definitions, but each compiles to
  its own recursor, so `rfl` will not reduce one to the other. Proved pointwise by the
  same recursion the definition uses.
- **OeisA108081's `xN`** — defined via the inductive predicate `XWord`, which each file
  declares separately. Two `inductive` declarations are distinct constants however
  identical their constructors. Proved `Atlas.XWord w ↔ XWord w` by induction in both
  directions. This is the check that actually matters here: it establishes that the
  Atlas file's notion of an X-word really is FC's.
- **Wotw314's `largestInducedPathSize`** and **Oqp35's thirteen definitions** are
  polymorphic; stated unapplied, the implicit type/index arguments are undetermined.
  Stated applied instead.

## Repair effort

35 errors on the first build, cleared over 8 rounds; 24 repairs in total, none of which
changes a statement. `FIXES.md` lists every one. The recurring causes were Mathlib API
churn — `Relation.ReflTransGen.lift` now returning a relation inequality (6 sites),
`BilinForm.Nondegenerate` becoming a conjunction, `Finset.mem_antidiagonal` becoming a
class field, two renamed lemmas — and a cluster of `rw`/`simp` steps that stopped
matching because pattern and target differ only in a decidability instance the
pretty-printer hides. Those last ones needed `exact`, which checks definitional
equality, rather than syntactic matching.

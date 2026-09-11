# Green 25 — an improvement on the Atlas construction

The Atlas Green 25 file reaches a part count of `N / (log N)²`. The same
construction, instantiated differently, reaches `N / exp(√(log N)/16)` — below
*every* polylogarithmic rate `N / (log N)^k`.

`complemented_digit_partition Q m r` holds for **every** `r ≤ m`. The Atlas file
instantiates it at `r = 4 + 4t`, which is exactly the value making the part count
`B / (log₂ B)²` — the choice is driven by the target, not by the construction. The
sumset budget is *linear* in `r` against a denominator of order `Q = 2^(4m)`, so `r`
can be taken to its structural maximum `r = m` at no cost.

## Files

| file | contents |
| --- | --- |
| `Green25Work.lean` | the base construction; eight declarations un-`private`d so a second module can reach them |
| `Green25Strong.lean` | the `r = m` instantiation; proves `green_25.variants.upper_exp_sqrt_log` with a named answer function `strongAnswer` |
| `Green25Ladder.lean` | `strongUpper =o[atTop] N/(log N)^k` for every `k`; corollaries against `bestUpper` and the Atlas `N/(log N)²`; and `fc_green_25_upper_answered` |
| `Green25Compare.lean` | `rfl` identity of `Property25` / `bestUpper` / `improvedUpper` across namespaces; the FC-typed statement closed by the work term; a non-vacuity check; `#print axioms` |
| `formal-conjectures.patch` | the change to the formal-conjectures checkout these modules need |

## Why this is the stronger result

`Green25Ladder.fc_green_25_upper_answered` is the body of FC's `green_25.upper`
**verbatim**, with the single change that `answer(sorry)` is replaced by
`strongAnswer`. In particular it keeps FC's own weaker third conjunct
`¬ ∀ᶠ N, Property25 …` rather than the stronger `∀ᶠ N, ¬ Property25 …` the Atlas
file states, and it uses FC's `bestUpper` and `Property25`, not the work file's
copies. So it answers `green_25.upper` on FC's terms.

`Green25Compare.witness_partition_exists` rules out the cheap reading: because
`Property25 k N` has `1 ≤ k` and `k ≤ N` as its first two clauses, `¬ Property25`
could in principle be satisfied by an out-of-range `k`. That check shows the size
constraints do hold on the eventual set, so the failure comes from the third
clause, and extracts the witnessing partition.

## These modules need a patched formal-conjectures

They are `FormalConjectures`-namespace modules that extend FC's `25.lean`, so they
live inside the FC library rather than beside `AtlasVerified/`.
`formal-conjectures.patch` adds `improvedUpper` and the
`green_25.variants.upper_exp_sqrt_log` statement to FC's own `25.lean` (plus the
`AtlasVerified` `lean_lib` stanza to `lakefile.toml`). `scripts/sync.sh` applies it.
Without the patch these modules do not compile, and `Green25Compare`'s `rfl` check
against FC's `improvedUpper` has nothing to check against.

## Build result

Verified 2026-09-10, `lake build` exit 0, zero errors:

| declaration | axioms |
| --- | --- |
| `Green25Atlas.strongAnswer_isBigO` | `propext, Classical.choice, Quot.sound` |
| `Green25Atlas.green_25.variants.upper_exp_sqrt_log` | `propext, Classical.choice, Quot.sound` |
| `Green25Ladder.strongUpper_isLittleO_polylog` (every `k`) | `propext, Classical.choice, Quot.sound` |
| `Green25Ladder.strongUpper_isLittleO_bestUpper` | `propext, Classical.choice, Quot.sound` |
| `Green25Ladder.strongUpper_isLittleO_logSq` | `propext, Classical.choice, Quot.sound` |
| **`Green25Ladder.fc_green_25_upper_answered`** | `propext, Classical.choice, Quot.sound` |
| `Green25Compare.fc_statement_is_proved` | `propext, Classical.choice, Quot.sound` |
| `Green25Compare.witness_partition_exists` | `propext, Classical.choice, Quot.sound` |
| `Green25.green_25.variants.upper_exp_sqrt_log` (FC's statement copy) | + `sorryAx`, as expected |

`sorryAx` appears only on FC's own statement copy, which is deliberately unproved.

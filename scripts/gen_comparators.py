#!/usr/bin/env python3
"""Write AtlasVerified/<D>/Comparator.lean for each problem.

Each comparator does two things:
  1. `rfl` identity checks on every definition the Atlas file and the
     formal-conjectures file both define. These are definitional, so they survive
     reformatting and fail if either side drifted.
  2. Restates the formal-conjectures theorem *in formal-conjectures' own
     vocabulary* and closes it with the Atlas term. This is the load-bearing check:
     if any shared definition differed, this would not typecheck.
Then `#print axioms`, so a `sorryAx` cannot hide.
"""
import os
DST = "/scratch/nnp5656/projects/atlas-fc-verified/AtlasVerified"

HEADER = """/-
Comparator for %(title)s.

Atlas file : `Atlas/FC/%(afile)s`  (namespace `Atlas.%(ns)s`)
FC file    : `%(fcfile)s`  (namespace `%(ns)s`)
FC theorem : `%(ns)s.%(thm)s`

%(note)s
-/

import AtlasVerified.%(d)s.Solution
import %(fcmod)s

%(opens)s
namespace AtlasCompare.%(d)s

"""

FOOT = "\nend AtlasCompare.%(d)s\n\n%(prints)s\n"

SPEC = [
dict(d="Erdos138", ns="Erdos138", afile="Erdos138_dvd_two_pow_solution.lean",
 fcfile="FormalConjectures/ErdosProblems/138.lean",
 fcmod="FormalConjectures.ErdosProblems.«138»", thm="erdos_138.variants.dvd_two_pow",
 title="Erdos 138 (`erdos_138.variants.dvd_two_pow`)",
 opens="open Nat Filter\n",
 common=["W", "monoAPNumber", "monoAP_guarantee_set"],
 note="""Note on the `answer()` slot. FC states `answer(sorry) ↔ Tendsto …`, i.e. the
answer is a *proposition* to be determined. The Atlas file proves the right-hand side
outright (`W k / 2 ^ k → ∞`), so the answer is `True`, and we discharge FC's iff with
that instantiation. Filling `answer()` with `True` is exactly the content of proving
the right-hand side, so this is a faithful reading rather than a dodge.""",
 body="""/-! ## Check 1 — the shared definitions agree definitionally. -/

%(idchecks)s
/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term.

`answer(sorry)` is instantiated to `True`; see the note above. -/

theorem fc_statement_is_proved :
    True ↔ atTop.Tendsto (fun k => ((Erdos138.W k : ℚ) / (2 ^ k))) atTop :=
  ⟨fun _ => Atlas.Erdos138.erdos_138.variants.dvd_two_pow, fun _ => trivial⟩
"""),

dict(d="Erdos337", ns="Erdos337", afile="Erdos337_ruzsa_turjanyi_solution.lean",
 fcfile="FormalConjectures/ErdosProblems/337.lean",
 fcmod="FormalConjectures.ErdosProblems.«337»", thm="erdos_337.variants.ruzsa_turjanyi",
 title="Erdos 337 (`erdos_337.variants.ruzsa_turjanyi`)",
 opens="open Filter Set Asymptotics\nopen scoped Pointwise\n",
 common=[],
 note="""The Atlas statement is byte-for-byte identical to FC's, and neither side
introduces auxiliary definitions that enter the statement — every notion in it
(`Set.IsAsymptoticAddBasis`, `ncard`, `=o`) comes from Mathlib or
FormalConjecturesForMathlib. So Check 2 alone is decisive here.""",
 body="""/-! ## Check — FC's statement, verbatim, closed by the Atlas term. -/

theorem fc_statement_is_proved :
    ∀ A : Set ℕ, A.IsAsymptoticAddBasis →
      (fun N : ℕ ↦ ((A ∩ Icc 1 N).ncard : ℝ)) =o[atTop] (fun N : ℕ ↦ (N : ℝ)) →
      Tendsto (fun N : ℕ ↦
          (((A + A) ∩ Icc 1 (2 * N)).ncard : ℝ) / ((A ∩ Icc 1 N).ncard : ℝ))
        atTop atTop :=
  Atlas.Erdos337.erdos_337.variants.ruzsa_turjanyi
"""),

dict(d="OeisA22030", ns="OeisA22030", afile="OeisA22030_conjecture.lean",
 fcfile="FormalConjectures/OEIS/22030.lean",
 fcmod="FormalConjectures.OEIS.«22030»", thm="conjecture",
 title="OEIS A022030 (`conjecture`)",
 opens="", common=["a"],
 note="""Both files define the sequence `a` independently. Check 1 is therefore
load-bearing: without it the Atlas proof could be about a different sequence.""",
 body="""/-! ## Check 1 — the two definitions of the sequence agree definitionally. -/

%(idchecks)s
/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved (n : ℕ) (hn : 4 ≤ n) :
    OeisA22030.a n
      = 4 * OeisA22030.a (n - 1) - OeisA22030.a (n - 3) + OeisA22030.a (n - 4) :=
  Atlas.OeisA22030.conjecture n hn
"""),

dict(d="OeisA211417", ns="OeisA211417", afile="OeisA211417_supercongruence_solution.lean",
 fcfile="FormalConjectures/OEIS/211417.lean",
 fcmod="FormalConjectures.OEIS.«211417»", thm="supercongruence",
 title="OEIS A211417 (`supercongruence`)",
 opens="open Nat Int Finset\n", common=["a"],
 note="""Both files define the factorial-ratio sequence `a` independently, so Check 1
is load-bearing.""",
 body="""/-! ## Check 1 — the two definitions of the sequence agree definitionally. -/

%(idchecks)s
/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved (p k : ℕ) (hp : p.Prime) (hp5 : 5 ≤ p) (hk : 0 < k) :
    (p : ℤ) ^ (3 * k) ∣ ((OeisA211417.a (p ^ k) : ℤ) - (OeisA211417.a (p ^ (k - 1)) : ℤ)) :=
  Atlas.OeisA211417.supercongruence p k hp hp5 hk
"""),

dict(d="OeisA108081", ns="OeisA108081", afile="OeisA108081_count_words_in_x_is_a_shifted.lean",
 fcfile="FormalConjectures/OEIS/108081.lean",
 fcmod="FormalConjectures.OEIS.«108081»", thm="count_words_in_x_is_a_shifted",
 title="OEIS A108081 (`count_words_in_x_is_a_shifted`)",
 opens="open Nat\n", common=["Word", "a", "l", "r", "xN"],
 note="""Five definitions are shared, including the word-set `xN` the statement counts
and the sequence `a` it is compared against. Check 1 pins all of them.""",
 body="""/-! ## Check 1 — every shared definition agrees definitionally. -/

%(idchecks)s
/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved (n : ℕ) :
    n ≥ 1 → Set.ncard (OeisA108081.xN n) = OeisA108081.a (n - 1) :=
  Atlas.OeisA108081.count_words_in_x_is_a_shifted n
"""),

dict(d="Oqp35", ns="OpenQuantumProblem35", afile="OpenQuantumProblem35_ame_9_10_open_solution.lean",
 fcfile="FormalConjectures/OpenQuantumProblems/35.lean",
 fcmod="FormalConjectures.OpenQuantumProblems.«35»", thm="ame_9_10_open",
 title="Open Quantum Problem 35 (`ame_9_10_open`) — AME(9,10)",
 opens="open scoped BigOperators\n",
 common=["Config","StateVector","mkStateVector","IsNormalized","permuteConfig",
         "permuteState","IsConstantConfig","combineFirst","reducedDensityFirst",
         "maximallyMixed","HasMaximallyMixedFirstReduction","IsAME","ExistsAME"],
 note="""This is the substantive one: thirteen definitions are shared, and the whole
meaning of the claim rests on them (what a state vector is, what `IsAME` means, what
`ExistsAME` quantifies over). Check 1 pins every one.

Note on the `answer()` slot. FC states `answer(sorry) ↔ ExistsAME 9 10`. The Atlas file
proves `ExistsAME 9 10` outright, so the answer is `True`.""",
 body="""/-! ## Check 1 — every shared definition agrees definitionally. -/

%(idchecks)s
/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term.

`answer(sorry)` is instantiated to `True`; see the note above. -/

theorem fc_statement_is_proved : True ↔ OpenQuantumProblem35.ExistsAME 9 10 :=
  ⟨fun _ => Atlas.OpenQuantumProblem35.ame_9_10_open, fun _ => trivial⟩
"""),

dict(d="Wotw100", ns="WrittenOnTheWallII.GraphConjecture100",
 afile="WrittenOnTheWallII_GraphConjecture100_conjecture100.lean",
 fcfile="FormalConjectures/WrittenOnTheWallII/GraphConjecture100.lean",
 fcmod="FormalConjectures.WrittenOnTheWallII.GraphConjecture100", thm="conjecture100",
 title="Written on the Wall II, Graph Conjecture 100",
 opens="open SimpleGraph\n\nvariable {α : Type*} [Fintype α] [DecidableEq α] [Nontrivial α]\n",
 common=[],
 note="""The Atlas statement is byte-for-byte identical to FC's, and every notion in it
(`indepNum`, `indepNeighborsCard`, `degreeL2Norm`) comes from
FormalConjecturesForMathlib rather than being redefined locally. Check 2 is decisive.""",
 body="""/-! ## Check — FC's statement, verbatim, closed by the Atlas term. -/

theorem fc_statement_is_proved (G : SimpleGraph α) [DecidableRel G.Adj] (h : G.Connected) :
    let maxL := (Finset.univ.image (indepNeighborsCard G)).max' (by simp)
    (G.indepNum : ℝ) ≤ ⌈((maxL : ℝ) + (1 / 2) * (degreeL2Norm Gᶜ : ℝ)) / 2⌉ :=
  Atlas.WrittenOnTheWallII.GraphConjecture100.conjecture100 G h
"""),

dict(d="Wotw314", ns="WrittenOnTheWallII.GraphConjecture314",
 afile="WrittenOnTheWallII_GraphConjecture314_conjecture314.lean",
 fcfile="FormalConjectures/WrittenOnTheWallII/GraphConjecture314.lean",
 fcmod="FormalConjectures.WrittenOnTheWallII.GraphConjecture314", thm="conjecture314",
 title="Written on the Wall II, Graph Conjecture 314",
 opens="open SimpleGraph\n\nvariable {α : Type*} [Fintype α] [DecidableEq α]\n",
 common=["largestInducedPathSize"],
 note="""`largestInducedPathSize` appears in the hypotheses of the statement and is
defined on both sides, so Check 1 is load-bearing: a weaker notion of induced path
length would weaken the hypothesis and so strengthen the theorem spuriously.""",
 body="""/-! ## Check 1 — the shared definition agrees definitionally. -/

%(idchecks)s
/-! ## Check 2 — FC's statement, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved [Nontrivial α] (G : SimpleGraph α) [DecidableRel G.Adj]
    (hG : G.Connected)
    (hTriFree : ∀ a b c : α, G.Adj a b → G.Adj b c → G.Adj c a → False)
    (hPath : WrittenOnTheWallII.GraphConjecture314.largestInducedPathSize G ≤ 4) :
    IsWellTotallyDominated G :=
  Atlas.WrittenOnTheWallII.GraphConjecture314.conjecture314 G hG hTriFree hPath
"""),

dict(d="Green25", ns="Green25", afile="Green25_upper_solution.lean",
 fcfile="FormalConjectures/GreensOpenProblems/25.lean",
 fcmod="FormalConjectures.GreensOpenProblems.«25»", thm="green_25.upper",
 title="Green's Open Problem 25 (`green_25.upper`)",
 opens="open Asymptotics Filter Finset\n", common=["Property25", "bestUpper"],
 note="""Two deviations from FC's statement, in opposite directions.

  * FC writes `let ans := answer(sorry)`; Atlas writes `∃ candidateAnswer`. Replacing a
    determination by an existential is *weaker* in FC's idiom — see `AGENTS.md`, "a
    tautological term inside `answer()` is not a mathematical solution". The construction
    does produce an explicit function, so this is presentational; `Improved.lean` in this
    directory names it and discharges FC's statement verbatim.
  * FC's third conjunct is `¬ ∀ᶠ N, Property25 …`; Atlas proves `∀ᶠ N, ¬ Property25 …`,
    which is *stronger*.

Check 2 below states the Atlas shape in FC's vocabulary. The verbatim FC statement is
discharged in `Improved.lean`.""",
 body="""/-! ## Check 1 — the shared definitions agree definitionally. -/

%(idchecks)s
/-! ## Check 2 — the Atlas shape, in FC's own vocabulary, closed by the Atlas term. -/

theorem fc_statement_is_proved :
    ∃ candidateAnswer : ℕ → ℕ,
      let ans := (candidateAnswer : ℕ → ℕ)
      (∀ᶠ N in atTop, 1 ≤ ans N ∧ ans N ≤ N) ∧
      (fun N => (ans N : ℝ)) =o[atTop] Green25.bestUpper ∧
      ∀ᶠ N in atTop, ¬ Green25.Property25 (ans N) N :=
  Atlas.Green25.green_25.upper
"""),
]

for s in SPEC:
    idchecks = "".join(
        "example : Atlas.%s.%s = %s.%s := rfl\n" % (s["ns"], c, s["ns"], c)
        for c in s["common"])
    if idchecks: idchecks += "\n"
    body = s["body"] % dict(idchecks=idchecks) if "%(idchecks)s" in s["body"] else s["body"]
    prints = "#print axioms AtlasCompare.%s.fc_statement_is_proved" % s["d"]
    txt = HEADER % dict(title=s["title"], afile=s["afile"], ns=s["ns"],
                        fcfile=s["fcfile"], thm=s["thm"], note=s["note"],
                        d=s["d"], fcmod=s["fcmod"], opens=s["opens"])
    txt += body + FOOT % dict(d=s["d"], prints=prints)
    p = os.path.join(DST, s["d"], "Comparator.lean")
    open(p, "w").write(txt)
    print("wrote %-12s (%d shared defs)" % (s["d"], len(s["common"])))

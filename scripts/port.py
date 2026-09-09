#!/usr/bin/env python3
"""Port the nine Atlas/FC solution files into AtlasVerified/<Dir>/Solution.lean.

The only edit is the namespace: every Atlas file uses exactly the same namespace as
the formal-conjectures file it targets, so a comparator that imports both could not
tell them apart. We prefix the Atlas copy with `Atlas.`.
"""
import os, re, shutil

SRC = "/scratch/nnp5656/projects/fc/atlas-lean/Atlas/FC"
DST = "/scratch/nnp5656/projects/atlas-fc-verified/AtlasVerified"

# dir, atlas filename, namespace, FC module, FC theorem
SPEC = [
 ("Erdos138","Erdos138_dvd_two_pow_solution.lean","Erdos138",
  "FormalConjectures.ErdosProblems.«138»","erdos_138.variants.dvd_two_pow"),
 ("Erdos337","Erdos337_ruzsa_turjanyi_solution.lean","Erdos337",
  "FormalConjectures.ErdosProblems.«337»","erdos_337.variants.ruzsa_turjanyi"),
 ("Green25","Green25_upper_solution.lean","Green25",
  "FormalConjectures.GreensOpenProblems.«25»","green_25.upper"),
 ("OeisA108081","OeisA108081_count_words_in_x_is_a_shifted.lean","OeisA108081",
  "FormalConjectures.OEIS.«108081»","count_words_in_x_is_a_shifted"),
 ("OeisA211417","OeisA211417_supercongruence_solution.lean","OeisA211417",
  "FormalConjectures.OEIS.«211417»","supercongruence"),
 ("OeisA22030","OeisA22030_conjecture.lean","OeisA22030",
  "FormalConjectures.OEIS.«22030»","conjecture"),
 ("Oqp35","OpenQuantumProblem35_ame_9_10_open_solution.lean","OpenQuantumProblem35",
  "FormalConjectures.OpenQuantumProblems.«35»","ame_9_10_open"),
 ("Wotw100","WrittenOnTheWallII_GraphConjecture100_conjecture100.lean",
  "WrittenOnTheWallII.GraphConjecture100",
  "FormalConjectures.WrittenOnTheWallII.GraphConjecture100","conjecture100"),
 ("Wotw314","WrittenOnTheWallII_GraphConjecture314_conjecture314.lean",
  "WrittenOnTheWallII.GraphConjecture314",
  "FormalConjectures.WrittenOnTheWallII.GraphConjecture314","conjecture314"),
]

for d, fn, ns, fcmod, thm in SPEC:
    src = os.path.join(SRC, fn)
    outdir = os.path.join(DST, d)
    os.makedirs(outdir, exist_ok=True)
    s = open(src).read()
    n_ns = len(re.findall(r"(?m)^namespace %s\s*$" % re.escape(ns), s))
    assert n_ns == 1, (fn, "namespace count", n_ns)
    s = re.sub(r"(?m)^namespace %s\s*$" % re.escape(ns), "namespace Atlas." + ns, s)
    s = re.sub(r"(?m)^end %s\s*$" % re.escape(ns), "end Atlas." + ns, s)
    if not re.search(r"(?m)^end Atlas\.%s\s*$" % re.escape(ns), s):
        s = s.rstrip() + "\n\nend Atlas." + ns + "\n"
    banner = (
      "/-\nProvenance: verbatim copy of `Atlas/FC/%s` from\n"
      "facebookresearch/atlas-lean @ prepare-atlas-v2 (223d8bc), with two mechanical\n"
      "changes only:\n"
      "  * namespace `%s` renamed to `Atlas.%s`, because the Atlas file reuses the\n"
      "    exact namespace of the formal-conjectures file it targets and the\n"
      "    comparator has to import both;\n"
      "  * any Mathlib-drift repairs recorded in FIXES.md for this problem.\n"
      "Target: `%s` in `%s`.\n-/\n\n" % (fn, ns, ns, thm, fcmod))
    # insert banner after the licence header (first closing -/)
    i = s.find("-/")
    s = s[:i+2] + "\n\n" + banner + s[i+2:].lstrip("\n")
    open(os.path.join(outdir, "Solution.lean"), "w").write(s)
    print("%-12s -> %s/Solution.lean  (%d lines)" % (ns, d, s.count("\n")))

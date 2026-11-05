import B.Main

/-!
# B axiom check — the verification protocol's kernel replay surrogate.

Expected axioms for every entry below: `propext`, `Classical.choice`, `Quot.sound` only
(no `sorryAx`, no extra axioms).

**Invocation** (the lane's `lake env lean` form needs the shim here): B's lib and A0's
lib both own `Frontier.*` modules, and the module resolver binds a name to the first
LEAN_PATH entry containing its parent directory — so bare `lake env lean` cannot see
both halves of `Frontier.*`.  `.axiomshim/Frontier/` merges every `Frontier.*` olean
(A0 + B's RAM trio) into one directory; put it first:

    lake env sh -c 'LEAN_PATH="$PWD/.axiomshim:$LEAN_PATH" lean B/AxiomCheck.lean'

(Rebuild `.axiomshim` after a clean: symlink every `.olean` under
`../A0/.lake/build/lib/lean/Frontier` and `.lake/build/lib/lean/Frontier` into
`.axiomshim/Frontier`, preserving subpaths.)

**B status (honest):** no `sorry` anywhere in the package; the B5–B8 fragment texts and
their spec proofs are *hypotheses* (`EntrySpec`/`BaseSpec`/`FPSpec`/`LevelRealizes`),
so the entries below are axiom-clean and conditional only on those pinned obligations.
-/

-- glue texts, fully proved
#print axioms Frontier.DMSY.cmpLen_runs
#print axioms Frontier.DMSY.exportBody_runs
#print axioms Frontier.DMSY.export_runs

-- representation and the output bridge (key lemma 2's seam)
#print axioms Frontier.DMSY.outRep_solves

-- realization and the key lemmas
#print axioms Frontier.DMSY.realizes_of_assembly
#print axioms Frontier.DMSY.runsWithin_bounds_cost
#print axioms Frontier.DMSY.runsWithin_of_runsB
#print axioms Frontier.DMSY.runsWithin_of_realizes
#print axioms Frontier.DMSY.exact_of_realizes
#print axioms Frontier.DMSY.exact_solves
#print axioms Frontier.DMSY.dmsy_runsWithin
#print axioms Frontier.DMSY.dmsy_exact
#print axioms Frontier.DMSY.dmsy_solves

-- name disjointness at assembly (key lemma 3)
#print axioms Frontier.DMSY.assembly_names_disjoint
#print axioms Frontier.DMSY.regs_pairwise_disjoint
#print axioms Frontier.DMSY.arrs_pairwise_disjoint
#print axioms Frontier.DMSY.regs_ne_arrs

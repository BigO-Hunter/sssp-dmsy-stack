# A4 Axiom Audit — SORRY Seam Report

**Date:** 2026-11-05
**Build:** full `lake build` of A4 green — 2028 jobs, exit 0. Log: `/private/tmp/sssp_a4_glm_recovery.log`.

## Principal theorems

`Frontier.DMSY.a4_joint`, `lemma37Star`, `theoremT`, `a4_contract` depend on `sorryAx`.
The dependency is localized to exactly two source lines:

- `A4/A4/Main.lean:65`
- `A4/A4/Main.lean:80`

This is the CORRECTED_PROOF §8.1 joint-chain seam — a documented, intentional
placeholder (see `A4/A4/AxiomCheck.lean:177`).

## Everything else is clean

- Audited scope: 155 declarations across 15 modules, plus explicit probes of
  `coneClosure_of_run`, `coneClosure_of_callPre_run`, `reachable_dst`.
- All clean: axiom base is exactly `[propext, Classical.choice, Quot.sound]`.
- The `import cone` module was verified clean and is **not** the cause of the
  sorryAx dependencies.

## Conclusion

The only sorry in the A4 stack is the two-line §8.1 joint-chain seam in
`Main.lean`. No hidden axioms, no unexpected `Classical.choice`-beyond-standard,
no sorry leakage from imported modules.

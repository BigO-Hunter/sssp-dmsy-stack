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

---

## §8.1 status after a closure attempt (2026-11-08) — both seams remain

**Re-verified from a fresh clone**, pin `leanprover/lean4:v4.34.1` + mathlib
`d13f23b7` (the repo's own `lean-toolchain`/`lakefile.toml`): `lake build` exit 0
over A0–A4; `lake env lean A4/AxiomCheck.lean` audits 89 declarations — 82 at
`[propext, Classical.choice, Quot.sound]`, 1 (`pullCap_add_fpCap_le_memCap`) at
`[propext, Quot.sound]`, and 6 on `sorryAx`: `a4_joint`, `lemma37Star`,
`theoremT`, `a4_contract`, `top_full_facts`, `top_exact_at` (the last two consume
`a4_joint`). `grep '\bsorry\b'` over A0–A4 finds no other `sorry`/`admit`. So the
source confinement claim above still holds exactly.

### The two seam statements

- `Main.lean:65` — `a4_joint : @JointChain G s t`, i.e.
  `∀ e out, Reach t e → Lemma37Hyp t e → Run t e out → Lemma37Concl (Full t) e out ∧ NoPrem e out`.
- `Main.lean:80` — `theoremT : @TheoremT G s (@Reach G s t) (@Run G s t)`, i.e.
  `∀ e out, Reach t e → Run t e out → ∀ x val, ¬ out.Premature x val`.

### Seam 2 (`theoremT`) — attempted, mechanically reduced, blocked at one goal

Probed in a scratch module against the built library (discarded; not a root):

1. The `l = 0` half is **free**: a base return's `mints = []` (`Semantics.baseOut`), so
   `∀ x val, ¬ (baseOut bout).Premature x val` closes immediately.
2. The `recur` half closes **given** `LabelFloorHyp t`: `run_mintFloor` gives
   `out.B' ≤ m.val` for every final mint, contradicting `val < out.B'`.
3. The unconditional `recur` half stops at exactly one goal — `⊢ LoopBInv stf.bp stf`
   (via `PremLabelKey.prem_empty_recur`). The only producer of `LoopBInv` is
   `LoopBInv.iloop_bInv`, whose premise is `ChildLabelFloor st fo'` at every step.

`ChildLabelFloor st fo'` reads: a residual group member **not** settled by the child
has child-returned label `≥ fo'.B'`. That is precisely Lemma 3.7\*(2b)/(2c) at the
child, i.e. the child's `Lemma37Concl` — the same object `a4_joint` must produce. And
at a leaf it is *equivalent* to `NoAbandonedBelow` (`MintPreFloor.childLabelFloor_base_iff`,
`mintPreFloor_base_iff`), which `CallPre + baseRun_lemma31` do not force
(`MintPreFloor.base_leaf_counterexample` is a formalized leaf where it fails). So seam 2
is **not independent** of seam 1: it is the `NoPrem` half of the same joint induction,
and `Reach` alone does not even supply `Lemma37Hyp` (`JointAssembly.lemma37Hyp_of_reach`
needs the step-uniform `ChildStep` and `StepSplit` premises).

### Seam 1 (`a4_joint`) — the return side is the whole obstuction

`Lemma37Concl` has six clauses at the return, and each already carries a named,
falsifiable-or-unreachable residual in this tree rather than an open proof:

| clause | unit that reduces it | residual it names |
|---|---|---|
| `frontier`, `progress`, `uSubset` | `A4.BpMonotonicity`, `A4.DrainedClauses` | per-step `ChildStep` / loop `B'` chain |
| `identity` (2c) | `A4.IdentityCover` | `Yclear`, or `LowKeyAccurate + BelowLabelFloor` |
| `containS`/`containR` (3) | `A4.NoLoose` §3 | full execution + `CandSettled` |
| `bound` (2b) | `A4.LemmaV`, `A4.PremLabelKey` | `LoopBInv` (`ChildLabelFloor` again) |
| `settleComplete` | `A4.JointAssembly.istepTrace_childStep` | `ChildFloor` (`A4.BelowSeparator`) |
| `fullImmune`, `premInD`, `premShape` | **proved** (`Structural.full_no_prem`, etc.) | — |

Per `A4.CustodyInduction` §4/§6 and `A4.JointAssembly`'s closing note, closing them all
is the joint first-violation induction of `research/CORRECTED_PROOF.md` §8.1 — the audit's
hand proof ("the main body of the Lean work"), which nothing in this artifact re-proves.

### Status line

`sorryAx` remains confined to `A4/A4/Main.lean:65` and `:80`. Both are the §8.1 joint
chain, not two independent gaps: seam 2 reduces to seam 1's `bound` clause, and neither is
closeable from this artifact's own lemmas without importing the audit's induction or adding
antecedents strong enough to restate the theorem. Leaving the named `sorry`s is the honest
state; a closer must supply the joint induction (or `NoAbandonedBelow`-strength leaf linkage
from the parent's `pullRun`/`expand`/`FPContract` residual groups).

*Construction (DMSY, arXiv:2602.07868v1) is the original authors'; the durable copy, build
harness, axiom audit and this closure attempt are ours.*

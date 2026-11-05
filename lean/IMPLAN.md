# IMPLAN — Corrected Duan–Mao–Shu–Yin directed SSSP in the Frontier model

Target: a single uniform `Frontier.RAM.Program` implementing the corrected DMSY algorithm
(BMSSP = Alg. 3, base case = Alg. 4 **with the V5 cap**, FindPivots, MergeSort), proved
`Program.Exact` (→ `State.Solves` = `IsSSSP`) and `Program.RunsWithin` under the lane's
`Bound a b a' b' c'` (sparse clause for `m ≤ n·F n`, polynomial fallback otherwise),
following the C-HD precedent (`bigospeedrun/c-hd-proof@98c53acc`, 289 frozen Lean files).

## 1. Reuse inventory (import, do not rebuild)

| Asset (c-hd-proof) | Reuse for DMSY |
|---|---|
| `Frontier.Spec` — `Graph`, `dist`, `IsSSSP`, `isSSSP_of_relaxed_of_realized`, Frontier framework (`IsFrontier.step`, `.split`, `complete_of_min`, `Utilde`) | correctness endpoint + §2.5 framework, **verbatim** |
| `Frontier.CostModel` — `Stmt`/`exec`, `Program`, `Exact`, `RunsWithin`, `initState` | machine + goal shape |
| `Frontier.RAMLogic` — `Runs` rules (incl. `runs_while_var`) | every RAM-code proof |
| `Frontier.CostCharging` / `CostAggregate` / `CostSkeleton` / `CostFinal` — `CallForest`, `CallCounters.Valid`, `total_cost_le`, term menu `tpar/kpar/Lpar` | **parametric** in `(t,k,Lmax,M0)`; re-instantiate for DMSY parameters, then CostFinal-style bridge |
| `Frontier.CHD.MergeSort.sortRange_spec` (40·(b−a+1)·(log₂+1), permutation + sorted + write sets) | MergeSort subroutine **as-is** (generic in `le`) |
| `Frontier.CHD.IHeap`/`IHeapLab` (indexed heap), `RamLevel` (row lists, group table), `LabRAM`/`LabTab` (label tables) | base case + FindPivots data structures, same pattern |
| CHD dispatcher + verified Bellman–Ford fallback (`O((n+1)(m+1))`), name-disjointness via `decide +kernel` at a 1-vertex dummy | D1/D2 modules |
| Verification protocol: `lake build`, kernel replay, `#print axioms`, FROZEN sha256 manifest | unchanged |

What is **not** reusable: CHD's FindPivots-HD (permanent edge deletion FH.9, leaves, lazy-D pull)
and its base case — the corrected DMSY subroutines are simpler; reuse their *contract shapes*
(`CallPre`, `FPContract`, `PullSpec` in `CHD.Basic`) but write the semantics fresh.

## 2. Module structure (namespace `Frontier.DMSY`; each bullet splits into 3–8 compile units)

```
A0 Interface      labels-as-keys (walk-order `WLab`, `ext`, Sound/Complete), CallPre,
                  FPContract, PullSpec — port of CHD.Basic minus deletion/leaf idioms
A1 BaseCase       Alg. 4 semantics with the **V5 cap** + correctness + per-call cost
A2 FindPivots     Alg. 2 (tree building, member cap k) + FPContract proof
A3 Pull           D-structure (DMSY Lemma 3.4): insert/merge/deleteSet + PullSpec + cost
A4 BMSSP          Alg. 3 recursion (relational big-step), corrected Lemmas 3.7/3.8 (S2.1),
                  termination (level measure), top-level exactness (isSSSP_of_complete)
B1–B4 RAM data    label table · indexed heap · D blocks · MergeSort (import CHD's)
B5–B8 RAM code    base-case text · FindPivots text · level body (spine) · recursion driver,
                  each with `Runs` specs + exact write sets (`Unchanged`) + name lists
C1 CallForest     instantiate for the DMSY call tree (nested bounds, sibling-disjoint U)
C2 Counters       `CallCounters.Valid`: jump windows (Line 24), Wr own-vertices, Q-witness,
                  re-selection edges, merge total M0 = O(n·L + m)
C3 PerCall        per-call cost inequalities (base cap V5, FindPivots ≤ c·k·t, pull cost)
C4 Bridge         CostFinal-style: Valid → total ≤ K · T_dmsy(n,m)  [sparse clause]
D1 Fallback       Bellman–Ford O((n+1)(m+1)) exact fallback
D2 Dispatch       threshold F: run DMSY when m ≤ n·F n else fallback
D3 Program        `dmsyProgram : Program` + closed name facts (`decide +kernel`)
D4 Bound          `dmsy_exact_within` + `Bound a b a' b' c'` theorem
```

## 3. Key lemmas

1. **Framework** (have): `IsFrontier.step`, `.split`, `.complete_of_min`, `isSSSP_of_relaxed_of_realized`.
2. **PullSpec** (Lemma 3.4): pulled set = keys `< x`, rest preserved, `x ≤ B`, nonempty pull — with cost `O(merged blocks)`. *Hardest data-structure work.*
3. **FPContract**: labels only decrease + stay walks; `⟨W, ⋃Pⱼ⟩` frontier; P₁…P_p,Q partition S; completed region ⊆ Ũ(B,S).
4. **Base case + V5 cap**: settled vertices complete under the frontier invariant; work ≤ V5 per call (cap enforced by the program; above the cap the call is truncated as per the correction spec — *pin the V5 constant from the lane's correction list*).
5. **BMSSP S2.1** (= corrected Lemmas 3.7/3.8): post-state has U ⊇ Ũ(B,S) complete below returned bound x ≤ B; children nested (`B_child ≤ B_parent`), sibling `U`s disjoint; depth ≤ Lmax = 2·Lpar − 1.
6. **Termination**: recursion depth decreases by the level/B measure (`runs_while_var` style).
7. **Accounting** (have in CostCharging): `sum_card_le_of_witness` (Q-charge), `window_unique` (each edge in one Line-24 window), `bichromatic_ge` (re-selection), `level_card_sum_le`.
8. **Merge total** ≤ c·(n·Lpar + m); **base total** ≤ c·V5·|V|·(Lmax+1).
9. **Exactness bridge**: all-complete labels → `State.Solves` (reach/dist arrays) via `labelLen_dis`.
10. **Assembly**: `dmsy_exact_within : dmsyProgram.Exact ∧ ∀ G s, RunsWithin G s (K·T_dmsy G.n G.m)`; dispatcher+fallback ⇒ `Bound a b a' b' c'`.

## 4. Effort estimate

Calibration: C-HD = 289 frozen files, 2,548 build jobs, 266-module closure, ~10 agents
(L1–L6 + B-L2/B-L3/B-L4 work packages), months of wall-clock; its cost skeleton was
deliberately algorithm-parametric, and DMSY is the *simpler* algorithm (no permanent edge
deletion, no leaves, no lazy-D), but Lemma 3.9-style accounting is the same size.

- **~200–280 Lean files, 4–6 MB**, 8 work packages (A0–A4, B, C, D).
- With 8–10 parallel agents: **~2–3 months elapsed**. Solo cadence: not realistic.
- Splits: A (abstract semantics+correctness, incl. PullSpec) ≈ 40%; B (RAM realization +
  write-set hygiene) ≈ 35%; C+D (cost + assembly) ≈ 25%.
- Risk hotspots: (1) PullSpec cost at RAM level; (2) `CallCounters.Valid` re-selection /
  Q-witness bookkeeping; (3) name-disjointness fan-out at assembly (CHD needed ~15 `decide`
  facts at a dummy instance); (4) the V5 cap constant + its truncation branch — must be pinned
  before A1 is written.
- Build/verification: copy CHD protocol (pinned Mathlib, full build, fresh-copy rebuild,
  kernel replay of the final closure, axiom audit).

*Skipped: exact `Bound a b a' b' c'` shape and the V5 constant were not in the studied sources —
take both from the lane's correction spec before starting A1/D4. Did not measure Mathlib
elaboration cost per file (C-HD's split pattern suggests keeping units <100 KB).*

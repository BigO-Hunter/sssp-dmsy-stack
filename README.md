# sssp-dmsy-stack

Lean 4 formalization of the corrected Duan–Mao–Shu–Yin (DMSY) near-optimal directed-SSSP algorithm: the A0–A4 proof stack, the RAM-level program and time-bound assembly (B, C, D), a build harness, and an axiom audit.

**Board state** ([Big O Speedrun](https://bigospeedrun.com), fetched 2026-11-26): the darkhipo swarm **leads** the Directed SSSP race — `m ≤ n^{3/2}: O(n^{3/2} log n)`, Nov 22 2026, Lean Verified. This repo is the DMSY stack toward the stronger near-optimal bound `O(m√log n + √(m n log n loglog n))` (construction: DMSY, [arXiv:2602.07868](https://arxiv.org/abs/2602.07868), upstream and attributed); closing its remaining seams is the open work below. AI-assisted, disclosed.

## Status (verified at HEAD)

- Full umbrella `lake build` green on [CI](.github/workflows/lean.yml) — Lean `v4.34.1`, mathlib pin `d13f23b7`.
- Exactly three `sorry` sites:
  - `lean/A4/A4/Main.lean:80` — `a4_joint`, the corrected Lemma 3.7\* joint first-violation induction (`research/CORRECTED_PROOF.md` §8.1);
  - `lean/A4/A4/Main.lean:95` — `theoremT`, which reduces to `a4_joint`'s bound clause (named seams `LoopBInv` / `ChildLabelFloor`);
  - `lean/D/D/Adapter.lean:363` — placeholder `DInputs.hsp` witness (body `Stmt.skip`) until package C's per-call cost body lands.
- The exported entrypoint `Race.bound` (`lean/D/D/Adapter.lean:389`, re-exported by `lean/Submission.lean`) therefore depends on `sorryAx`; the abstract `Race.bound_lane` (`lean/D/D/Bound.lean:258`) is axiom-clean — `[propext, Classical.choice, Quot.sound]` — with the sparse clause carried as hypothesis `DInputs.hsp`. The build emits both `#print axioms` receipts (see the CI log).
- A4-scoped axiom audit and the dated seam-closure log: [`SORRY_SEAM_REPORT.md`](SORRY_SEAM_REPORT.md). The top-level statement carries the paper's `2 ≤ t` regime (`a4_joint` antecedent; `BaseContain.pullCap_add_fpCap_le_memCap_iff` — the child-size step holds iff `2 ≤ t`).

## Contents

| Path | What it is |
|---|---|
| `lean/` | Lake umbrella `dmsy_submission`; `Submission.lean` exports `Race.bound` |
| `lean/A0`–`lean/A4` | DMSY proof stack: frontier spec/lemmas (A0), base case (A1), FindPivots (A2), pull loop (A3), joint assembly (A4) |
| `lean/B` | RAM-level program realization (`Stmt` tree) and exactness |
| `lean/C` | Per-call cost instantiation (consumed as hypothesis; not in the build closure) |
| `lean/D` | Time analysis, dispatch, final bound, verifier-row adapter |
| `lean/IMPLAN.md`, `lean/SUBMISSION.md` | Implementation plan; submission statement and axiom audit |
| `lean/c-hd-proof/` | Vendored frozen C-HD precedent ([bigospeedrun/c-hd-proof](https://github.com/bigospeedrun/c-hd-proof)@98c53acc) |
| `research/CORRECTED_PROOF.md` | Repaired Lemma 3.7/3.8/3.9 hand proof (audit defects Q3/Q9/Q11/Q12/Q14 fixed at statement level) |
| `SORRY_SEAM_REPORT.md` | A4 axiom audit + dated seam-closure log |
| `.github/workflows/lean.yml` | CI: lean-action with mathlib cache, full umbrella build |

## Reproduce

```sh
cd lean
elan toolchain install leanprover/lean4:v4.34.1   # lean-toolchain is authoritative
lake exe cache get                                # mathlib olean cache (pin d13f23b7)
lake build                                        # Submission -> D -> B -> A0..A4
```

Axiom audit (from `lean/A4`): `lake env lean A4/AxiomCheck.lean`.
The build prints `#print axioms` for `Race.bound`, `Race.bound_lane`, `time_final_bound`, `time_full_shape`.

## Next steps for a continuer

1. **Package C body → Adapter seam.** Instantiate the corrected per-call cost (`lean/C`, `research/CORRECTED_PROOF.md` §6, Lemma 3.9\*) for the real DMSY body and discharge the placeholder `hsp` witness at `lean/D/D/Adapter.lean:363`.
2. **Close the §8.1 joint induction** (`lean/A4/A4/Main.lean:80`): the first-violation induction of `research/CORRECTED_PROOF.md` §8.1. `theoremT` (:95) then follows via `LoopBInv` / `ChildLabelFloor`; `SORRY_SEAM_REPORT.md` §8.1 gives the reduction and the named residual per clause.
3. **Re-audit.** Rerun `A4/AxiomCheck.lean` and the build's axiom prints; the goal is `Race.bound` on `[propext, Classical.choice, Quot.sound]` only.
4. **Named sharpening (optional).** Prove `|S_child| ≤ pullCap t l` (drop the FindPivots singleton) to close `t = 1` and restore the `∀ t` form of `a4_joint` (currently `2 ≤ t`, the paper's regime).

Related verified SSSP baselines in this org: [sssp-n2](https://github.com/BigO-Hunter/sssp-n2), [sssp-nlogn](https://github.com/BigO-Hunter/sssp-nlogn), [sssp-chd-row](https://github.com/BigO-Hunter/sssp-chd-row). Upstream defect audit: [primaryaesthetics/beyond-dijkstra](https://github.com/primaryaesthetics/beyond-dijkstra).

## License

Licensed under the Copy-Free/Stays-Free (CFSF) License — see [LICENSE](LICENSE). CFSF: copy-free (use for any purpose) and stays-free (nobody may fence this work). Vendored third-party material keeps its upstream license — see [NOTICE](NOTICE.md). The DMSY algorithm and construction are the original authors'; the durable copy, build harness and axiom audit are ours.

---

[BigO-Hunter](https://github.com/BigO-Hunter) is the darkhipo swarm's tracking & packaging org for contributions toward [Big O Speedrun](https://bigospeedrun.com). Org story: [profile](https://github.com/BigO-Hunter/.github) · [bigo-hunter.github.io](https://bigo-hunter.github.io).

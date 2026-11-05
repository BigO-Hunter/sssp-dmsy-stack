import Frontier.DMSY.Lemma37
import Frontier.CostModel

/-!
# Frontier.DMSY.Interfaces — work-package interface signatures (A1–A4, then B/C/D)

Work package **A0 (interface)**.  The exact proof obligations each downstream package
(IMPLAN.md §2) must discharge, as Prop-valued signatures.  Every judgment named here is
*defined* by the package that owns it; A0 pins only its type.  No axioms, no `sorry`.

| Package | Owns | Must produce |
|---|---|---|
| A1 BaseCase | `baseRun : BaseIn → BaseOut → Prop` (Alg. 4 semantics with (E1)) | `A1Contract` |
| A2 FindPivots | `fpRun : FPIn → FPOut → Prop` (Alg. 2, member cap k) | `A2Contract` |
| A3 Pull | `pullRun` (D-structure: insert/merge/deleteSet/pull) | `A3Contract` |
| A4 BMSSP | `Run/Reach/Full` (Alg. 3 relational big-step, (E0)–(E3)) | `A4Contract`, `TopExact` |
| C3 PerCall | per-call cost inequalities | `C3Contract` (shape) |
| D3/D4 Program/Bound | `dmsyProgram : RAM.Program` | `DMSYExact`, `DMSYWithin` |
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD
open RAM

variable {G : Graph} {s : Fin G.n}

/-! ## A1 — BaseCase (Algorithm 4 semantics with the V5 cap) -/

/-- **A1 signature.** `baseRun e out` is the cost-indexed relational semantics of Algorithm 4
(with (E1) the V5 cap and (E3) event semantics) on input `e` returning `out`. -/
def A1Contract (ReachBase : BaseIn G s → Prop)
    (baseRun : BaseIn G s → BaseOut G s → Prop) : Prop :=
  Lemma31Star ReachBase baseRun

/-! ## A2 — FindPivots (Algorithm 2, tree building, member cap `k`) -/

/-- **A2 signature.** `fpRun i o` is the semantics of FindPivots on input `i` returning `o`.
Its proof obligation is exactly `FPContract` (labels only decrease and stay walks; `⟨W, ⋃P_j⟩`
frontier for `Ũ(B, S)`; `P_1 … P_p, Q` partition `S`; completed region `⊆ Ũ(B, S)`) plus the
member cap `|⋃P_j| ≤ i.k`; sizes/trees/Q-charging belong to C2/C3. -/
def A2Contract (fpRun : FPIn G s → FPOut G s → Prop) : Prop :=
  ∀ (i : FPIn G s) (o : FPOut G s), fpRun i o →
    FPContract i.B i.S i.d o.d' o.p o.P o.Q o.W ∧
      (Finset.biUnion Finset.univ o.P).card ≤ i.k

/-! ## A3 — Pull (DMSY Lemma 3.4: the D-structure) -/

/-- **A3 signature.** `pullRun cap D Bd S' x D'` is the semantics of one `Pull(D, Bd)` returning
separator `x`, pulled set `S'` and remainder `D'`, size-capped at `cap` (Lemma 3.4's pull-size
clause `|S'| ≤ M = t·2^((l−1)t)` = `pullCap t l` at a level-`l` call — the hypothesis the A4
recursion consumes to apply its induction hypothesis to children). -/
def A3Contract (pullRun : ℕ → DS G s → WLab G s → Finset (Fin G.n) → WLab G s → DS G s → Prop) :
    Prop :=
  ∀ (cap : ℕ) (D : DS G s) (Bd : WLab G s) (S' : Finset (Fin G.n)) (x : WLab G s) (D' : DS G s),
    pullRun cap D Bd S' x D' → PullSpec cap D Bd S' x D'

/-! ## A4 — BMSSP (Algorithm 3 recursion, relational big-step) -/

/-- **A4 signature.** The corrected engine satisfies Lemma 3.7* and Theorem T. -/
def A4Contract (t : ℕ) (Reach : CallEntry G s → Prop)
    (Run : CallEntry G s → CallOut G s → Prop)
    (Full : CallEntry G s → CallOut G s → Prop) : Prop :=
  Lemma37Star t Reach Run Full ∧ TheoremT Reach Run

/-- **A4 top-level exactness.** The run `BMSSP*(⊤, {s}, l_top)` from `initLabels` returns
labels complete for every vertex; `isSSSP_of_complete` + `labelLen_dis` (Basic) then give
`G.IsSSSP s (fun v => labelLen (d v))`. -/
def TopExact (t : ℕ) : Prop :=
  ∀ (G : Graph) (s : Fin G.n)
    (Reach : CallEntry G s → Prop) (Run : CallEntry G s → CallOut G s → Prop),
    Reach ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ →
      ∃ out : CallOut G s,
        Run ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ out ∧
          ∀ v, Complete out.d' v

/-! ## D3/D4 — the uniform program and the lane's `Bound` theorem -/

/-- **D3 signature.** The corrected DMSY algorithm as one uniform deep-embedded program:
`dmsyProgram : RAM.Program` (a finite `Stmt` tree over the unit-cost RAM + comparison-addition
machine of `Frontier.CostModel`, with the subroutine texts of B5–B8 in its procedure table).
Defined in D3; the type is pinned here. -/
abbrev DMSYProgram := Program

/-- **D4 signature (exactness).** `dmsyProgram.Exact`: on every graph and source the program
terminates without getting stuck and outputs exact shortest-path distances. -/
def DMSYExact (P : DMSYProgram) : Prop := P.Exact

/-- **D4 signature (time).** `RunsWithin` by the DMSY bound `K · T_dmsy(n, m)` (sparse clause
`m ≤ n·F n`, polynomial fallback otherwise — the lane's `Bound a b a' b' c'`). -/
def DMSYWithin (P : DMSYProgram) (K : ℝ) (T : ℕ → ℕ → ℝ) : Prop :=
  ∀ (G : Graph) (s : Fin G.n), P.RunsWithin G s (K * T G.n G.m)

end DMSY
end Frontier

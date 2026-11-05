import C.Counters

/-!
# C3 — PerCall: the per-call cost inequalities of the corrected engine

Work package **C (cost instantiation)**, IMPLAN §2 C3 (the task's key lemma 1).  The corrected
DMSY engine's per-call cost contract, in the shape of **corrected Lemma 3.9\***
(CORRECTED_PROOF §6) — not the C-HD `cost_le` shape: the corrected DMSY subroutines are
simpler (no permanent edge deletion FH.9, no leaves, no lazy-`D` pull; IMPLAN §1), so the
per-call vertex term is `(|U| + T_X)·(l + log t)·log t` with **no `k` factor** — the C-HD
`(k+1)·(|U| + |Fo|)` term provably cannot reach `T_dmsy` (it is `≥ n·log n` at `L = ⌈log n/t⌉`
for every `k ≥ 2`, while `T_dmsy(n,n) = Θ(n·√(log n·log log n))`), which is why the DMSY
accounting is re-instantiated rather than re-used verbatim.

Per call `X` (children excluded), `T_X = C.dup X`:

    cost X ≤ c·(|U X| + T_X)·(l + log t)·log t      -- vertex term (FindPivots + sweeps)
           + c·t·(|J X| + |Cr X|)                  -- Line-24 jumps + re-selection edges
           + c·t·δ·(|U X| + T_X)                   -- merge/pull/line-33 volumes (δ factor)
           + c·l·(|U X| + T_X)                     -- the l/t share: Q-charge per partial call
           + c·t·δ·T_X                             -- duplicate surcharge (re-settlement)

and the named step obligations below pin the sub-contracts the seam is discharged from:

* **base cap V5** (`basePerCall`): a leaf's work is bounded by its settled mass under the (E1)
  V5 cap (`Engine.v5Cap`, A1's Algorithm-4 contract) — `c·(lg+1)·(|U X| + |Eout X|)`;
* **FindPivots ≤ c·k·t** (`fp_le`): A2's `fpRun` with the member cap `k = fpCap t` (the
  tighter S4.1 form `c(k)·min(|Ũ|, 4k|S|) + c(k)·k|Q_X| + |S|` implies it at the fold);
* **pull cost** (`pull_le`): A3's `pullRun` = `O(merged blocks)` per BM.10/BM.14 (Lemma 3.4's
  cost clause, `PullSpec`'s docstring: "cost clauses are package C3's cost contract").
-/

namespace Frontier
namespace DMSY

open Finset

set_option linter.unusedSectionVars false

variable {ι V E α : Type*} [Fintype ι] [Fintype V] [Fintype E]
  [DecidableEq ι] [DecidableEq V] [DecidableEq E] [LinearOrder α]

/-- **C3.**  The corrected per-call cost contract (Lemma 3.9\* shape) for one execution's
counters.  `lgT = log₂(t+1)` and `lTop` are the engine's bookkeeping constants (A0 `Engine`:
`lTop t n = ⌈log₂ n / t⌉`); `δ` is the out-degree cap after degree reduction. -/
structure DmsyPerCall (C : DmsyCounters ι V E α) (t k c δ lTop lgT : ℕ) : Prop where
  /-- the corrected Lemma 3.9\* per-call inequality (children excluded) -/
  perCall : ∀ X, C.cost X ≤
      c * ((C.F.U X).card + C.dup X) * ((lTop + lgT) * lgT)
        + c * t * ((C.J X).card + (C.Cr X).card)
        + c * t * δ * ((C.F.U X).card + C.dup X)
        + c * lTop * ((C.F.U X).card + C.dup X)
        + c * t * δ * C.dup X
  /-- **base cap V5**: a base call costs `≤ c·(lg+1)·(|U X| + |Eout X|)` with
  `lg = log₂(t+1) + log₂(δ+1) + 1` (A1's V5-capped Algorithm 4; IMPLAN key lemma 8:
  base total `≤ c·V5·|V|·(Lmax+1)`) -/
  basePerCall : ∀ X, C.base X = true →
      C.cost X ≤ c * (lgT + Nat.log 2 (δ + 1) + 2) * ((C.F.U X).card + (C.Eout X).card)
  /-- **FindPivots ≤ c·k·t** per invocation (A2 `fpRun`, member cap `k = fpCap t`) -/
  fp_le : ∀ X, C.fpCost X ≤ c * k * t
  /-- **pull cost** `O(merged blocks)` ≤ `c·t·δ` per pull (A3 `pullRun`, BM.10/BM.14) -/
  pull_le : ∀ X, C.pullCost X ≤ c * t * δ

end DMSY
end Frontier

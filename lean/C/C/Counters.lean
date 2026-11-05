import C.CallForest
import A4.Size

/-!
# C2 — Counters: the DMSY instantiation of `CallCounters` bookkeeping

Work package **C (cost instantiation)**, IMPLAN §2 C2.  The corrected engine's per-call
counters (CORRECTED_PROOF §6, Lemma 3.9\*'s T-numbers) over the C1 call forest:

* `J X` — **jump windows** (Line 24): edges whose candidate value was inserted at `X` from a
  child's settlement, in the window `[B_child, B_X)` (engine: BM.20 gate, (E2));
* `Wr X` — `W'`-sweep relaxations (BM.27–28), starting at vertices whose deepest call is `X`;
* `Cr X` — **re-selection edges** (BM.23): crossing edges of `E(U_X) ⧵ ⋃ᵢ E(Uᵢ)` (the T5 charge);
* `Q X` — FindPivots **failed-search roots** (A2), with the per-vertex in-edge **witness**
  (DMSY26 Lemma 3.9: the latest inserting relaxation into `v` before `X`);
* `dup X` — the **duplicate excess** charged to `X` (Lemma 3.8\*(c); A4's `dupExcess` at the
  top, bounded by `LemmaR`), `mergeCost X` — the `𝒟`-merge cost (Lemma 3.8\*(b), `M0`);
* `fpCost`/`pullCost`/`cost` — the per-call cost indices of C3.

Unlike the C-HD counters there are **no** foreign leaves (`Fo`), **no** deletions (`Del`) and
**no** kind-(β) edges (`Be`): the corrected DMSY engine carries no FIX-STALE deletion (BM.15/29
are the B1 variant's) and no leaves — `Del = Be = Fo = ∅` is definitional here.

`DmsyValid` is the C2 obligation battery — each field is a seam with its engine source; the
counting lemmas below (`sum_J_le`, `sum_Cr_le`, `sum_U_le`) are **proved** from the abstract
`CostCharging` charging lemmas (`window_unique`, `cross_unique`, `level_card_sum_le`) — this is
the algorithm-parametric payoff the reuse inventory points at.
-/

namespace Frontier
namespace DMSY

open Finset Frontier.CostCharging

set_option linter.unusedSectionVars false

variable {ι V E α : Type*} [Fintype ι] [Fintype V] [Fintype E]
  [DecidableEq ι] [DecidableEq V] [DecidableEq E] [LinearOrder α]

/-- The counters of one corrected-DMSY execution over its C1 call forest. -/
structure DmsyCounters (ι V E α : Type*) [LinearOrder α] where
  F : CallForest ι V α
  src : E → V
  dst : E → V
  val : E → α
  full : ι → Bool
  base : ι → Bool
  S : ι → Finset V
  J : ι → Finset E
  Wr : ι → Finset E
  Cr : ι → Finset E
  Q : ι → Finset V
  p : ι → ℕ
  dup : ι → ℕ
  mergeCost : ι → ℕ
  fpCost : ι → ℕ
  pullCost : ι → ℕ
  cost : ι → ℕ

namespace DmsyCounters

variable (C : DmsyCounters ι V E α)

/-- `v` belongs to `U X` but to no child of `X` (its deepest call is `X`). -/
def Own (X : ι) (v : V) : Prop := v ∈ C.F.U X ∧ ∀ Y, C.F.parent Y = some X → v ∉ C.F.U Y

/-- Out-edges of `U X`. -/
def Eout (X : ι) : Finset E := univ.filter (fun e => C.src e ∈ C.F.U X)

/-- **C2 obligation battery** (each field is a seam with its engine source).  Parameters: `t`
the engine parameter (A0 `Engine`), `k` the FindPivots member cap (`fpCap t`, A2), `c` the
per-operation constant of A0's operation table, `Lmax` the maximal depth, `M0` the merge
total (Lemma 3.8\*(b): `O(n·L + m)`), `δ` the out-degree cap after degree reduction, `T` the
run's total duplicate excess (Lemma 3.8\*(c)/`LemmaR`). -/
structure DmsyValid (t k c Lmax M0 δ T : ℕ)
    (inE : V → Finset E) (wit : ι → V → E) (src : V) : Prop where
  two_le_k : 2 ≤ k
  k_le_t : k ≤ t
  depth_le : ∀ X, C.F.depth X ≤ Lmax
  /-- Line 24 jumps lie in the window of `X`: `B_child ≤ val e < B_X`, `u` settled by the child
  (engine: the BM.20 (E2) gate; charged once per edge by `window_unique`, Obs. 3.5). -/
  jump_window : ∀ X, ∀ e ∈ C.J X, ∃ Y, C.F.parent Y = some X ∧ C.src e ∈ C.F.U Y ∧
      C.F.B Y ≤ C.val e ∧ C.val e < C.F.B X
  /-- `W'` relaxations start at vertices whose deepest call is `X` (BM.26's call-local filter;
  this is why `W'` can re-settle — the duplicate excess of Lemma 3.8\*(c)). -/
  wr_own : ∀ X, ∀ e ∈ C.Wr X, C.Own X (C.src e)
  /-- Re-selection edges cross at `X`: both ends in `U X`, no child contains both (the T5
  charge to `E(U_X) ⧵ ⋃ᵢ E(Uᵢ)`; injected once by `cross_unique`). -/
  cr_cross : ∀ X, ∀ e ∈ C.Cr X, C.src e ∈ C.F.U X ∧ C.dst e ∈ C.F.U X ∧
      ∀ Y, C.F.parent Y = some X → ¬ (C.src e ∈ C.F.U Y ∧ C.dst e ∈ C.F.U Y)
  /-- partial calls have small frontiers and pivots (`|S| ≤ |U|/t`, Lemma 3.7\* (2b)) -/
  partial_S : ∀ X, C.full X = false → t * (C.S X).card ≤ (C.F.U X).card
  partial_p : ∀ X, C.full X = false → C.p X ≤ (C.S X).card
  /-- full calls: `S ⊆ U`, pivots `≤ |U|/(k-1)` (tree/PT pieces have `≥ k-1` edges, S4.4) -/
  full_S : ∀ X, C.full X = true → C.S X ⊆ C.F.U X
  full_p : ∀ X, C.full X = true → C.p X * (k - 1) ≤ (C.F.U X).card
  Q_sub : ∀ X, C.Q X ⊆ C.S X
  /-- `Q`-witnesses of full calls: in-edges (for `v ≠ src`), injective per vertex (Lemma 3.9:
  the edge of the latest inserting relaxation into `v` before `X` starts) -/
  wit_mem : ∀ X, C.full X = true → ∀ v ∈ C.Q X, v ≠ src → wit X v ∈ inE v
  wit_inj : ∀ v X X', C.full X = true → C.full X' = true → v ∈ C.Q X → v ∈ C.Q X' →
      wit X v = wit X' v → X = X'
  /-- the source lies in `Q` of at most one full call (the O22(C) carve-out) -/
  src_once : ∀ X X', C.full X = true → C.full X' = true → src ∈ C.Q X → src ∈ C.Q X' → X = X'
  inE_card : ∑ v, (inE v).card ≤ Fintype.card E
  /-- merge total: `M0 = O(n·Lpar + m)` (Lemma 3.8\*(b), the DS' lemma) -/
  merge_total : ∑ X, C.mergeCost X ≤ M0
  /-- total duplicate excess `T` (Lemma 3.8\*(c); `T = 0` on full executions / V8–V10, and
  `≤ LemmaR`'s bound on the unmarked V5 engine) -/
  dup_total : ∑ X, C.dup X ≤ T
  /-- base calls have no sub-calls -/
  base_leaf : ∀ X Y, C.base X = true → C.F.parent Y ≠ some X

variable {C} {t k c Lmax M0 δ T : ℕ} {inE : V → Finset E} {wit : ι → V → E} {src : V}

/-- **Jumps: each edge is a jump of at most one call** (proved — `window_unique`). -/
theorem sum_J_le (h : C.DmsyValid t k c Lmax M0 δ T inE wit src) :
    ∑ X, (C.J X).card ≤ Fintype.card E := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨Y, hY, hu, hw1, hw2⟩ := h.jump_window X e he
    obtain ⟨Y', hY', hu', hw1', hw2'⟩ := h.jump_window X' e he'
    exact C.F.window_unique hY hY' hu hu' hne ⟨hw1, hw2⟩ ⟨hw1', hw2'⟩

/-- **Re-selection edges: each edge crosses at most one call** (proved — `cross_unique`). -/
theorem sum_Cr_le (h : C.DmsyValid t k c Lmax M0 δ T inE wit src) :
    ∑ X, (C.Cr X).card ≤ Fintype.card E := by
  classical
  rw [← Finset.card_biUnion]
  · exact Finset.card_le_univ _
  · intro X _ X' _ hne
    rw [Function.onFun, Finset.disjoint_left]
    intro e he he'
    obtain ⟨ha, hb, hc⟩ := h.cr_cross X e he
    obtain ⟨ha', hb', hc'⟩ := h.cr_cross X' e he'
    exact hne (C.F.cross_unique ha hb ha' hb' hc hc')

/-- Summing a per-call quantity bounded levelwise by `A` over depths `0..Lmax`. -/
theorem sum_le_levels (h : C.DmsyValid t k c Lmax M0 δ T inE wit src) (g : ι → ℕ) (A : ℕ)
    (hlev : ∀ j, ∑ X ∈ univ.filter (fun X => C.F.depth X = j), g X ≤ A) :
    ∑ X, g X ≤ (Lmax + 1) * A := by
  classical
  have hmaps : ∀ X ∈ (univ : Finset ι), C.F.depth X ∈ Finset.range (Lmax + 1) := by
    intro X _; simp only [Finset.mem_range]; have := h.depth_le X; omega
  have hsplit : ∑ X, g X = ∑ j ∈ Finset.range (Lmax + 1),
      ∑ X ∈ univ.filter (fun X => C.F.depth X = j), g X :=
    (Finset.sum_fiberwise_of_maps_to hmaps g).symm
  rw [hsplit]
  calc ∑ j ∈ Finset.range (Lmax + 1), ∑ X ∈ univ.filter (fun X => C.F.depth X = j), g X
      ≤ ∑ _j ∈ Finset.range (Lmax + 1), A := Finset.sum_le_sum fun j _ => hlev j
    _ = (Lmax + 1) * A := by simp

/-- **Level sums** (proved — `level_card_sum_le`): `Σ|U X| ≤ (Lmax+1)·|V|`. -/
theorem sum_U_le (h : C.DmsyValid t k c Lmax M0 δ T inE wit src) :
    ∑ X, (C.F.U X).card ≤ (Lmax + 1) * Fintype.card V :=
  sum_le_levels h _ _ fun j => C.F.level_card_sum_le j

end DmsyCounters

/-! ## Link to A4's duplicate excess -/

/-- The C2 `dup` counter's semantics at a return: A4's `dupExcess` of the (E3) log is the log
length minus the settled finset of C1 (definitional). -/
theorem dupExcess_eq {G : Graph} {s : Fin G.n} (out : CallOut G s) :
    dupExcess out.evts = out.evts.length - (settledFin out).card :=
  rfl

end DMSY
end Frontier

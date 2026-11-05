import A4.Semantics
import Frontier.CostCharging

/-!
# C1 — CallForest: the DMSY call-tree instantiation of the cost skeleton

Work package **C (cost instantiation)**, task key lemma setup (IMPLAN §2 C1).  The C-HD cost
theory (`Frontier.CostCharging`) is **algorithm-parametric**: `CallForest` is an abstract
recursion forest of calls with nested bounds and sibling-disjoint vertex sets, and its
counting lemmas (`window_unique`, `cross_unique`, `level_card_sum_le`, `sum_card_le_of_witness`)
are exactly the DMSY26 §3.4/§3.6 bookkeeping.  This module instantiates it for the *corrected*
DMSY engine (A4's `Run`/`ILoop`/`ChildOf` on engine deltas (E0)–(E3)):

* `settledFin` — `U X`, the settled vertices of `X`'s return log ((E3): `U` is the settlement
  **log**; the finset is the log projected to vertices, duplicates erased);
* `DmsyTree` — the call-occurrence data with engine linkage and the forest laws;
* `mkForest` — the abstract `CallForest` instance; every CostCharging lemma then applies.

**Proofs here (engine-local):** `istep_B_le` (a child's entry bound is `≤` the parent's — the
BM.10 pull separator `x ≤ Bd` of A0's `PullSpec.bound`, via `A3.a3_contract`), and the two
`ILoop` log-growth lemmas (`iloop_evts_mono`, `iloop_child_evts_sub`: a child's return log is a
sublist of the parent's final log, because the loop accumulates `st.evts ++ fo'.evts` and the
tail only appends `W'` events).

**The C1 seam** (the `DmsyTree` law fields): `U_sub` follows from `iloop_child_evts_sub` once
`childOf` exposes the parent's `Run` decomposition (run-witness uniqueness seam); `B_le`
follows from `istep_B_le` through the same seam; `siblings_disjoint` is **Lemma 3.8\*(c)**
with duplicate excess `T_X = 0` — true on full executions and on the V8/V10 settled-bit
engine (CORRECTED_PROOF §6).  On the unmarked V5 engine sibling logs may overlap by exactly
the duplicate excess; that overlap is what C2's `dup` counter and C4's re-settlement surcharge
carry (key lemma 3).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD
open Frontier.CostCharging

variable {G : Graph} {s : Fin G.n}

/-! ## The settled vertex set of a return -/

/-- `U X` of the abstract forest: the settled vertices of the (E3) return log, as a finset. -/
def settledFin (out : CallOut G s) : Finset (Fin G.n) :=
  (out.evts.map (·.v)).toFinset

theorem mem_settledFin {out : CallOut G s} {v : Fin G.n} :
    v ∈ settledFin out ↔ ∃ ev ∈ out.evts, ev.v = v := by
  simp only [settledFin, List.mem_toFinset, List.mem_map]

theorem settledFin_sub_of_sublist {out out' : CallOut G s} (h : List.Sublist out.evts out'.evts) :
    settledFin out ⊆ settledFin out' := by
  intro v hv
  obtain ⟨ev, hev, rfl⟩ := mem_settledFin.mp hv
  exact mem_settledFin.mpr ⟨ev, h.mem hev, rfl⟩

/-! ## Engine-local growth laws (proved) -/

/-- One loop iteration's next state logs the child's return events after the running log. -/
theorem istep_evts {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    st'.evts = st.evts ++ fo'.evts := by
  rcases h with ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hD2, hsweep,
    hresid, hJ, hsel, hst'⟩
  subst hst'
  rfl

/-- **Nested bounds (proved half).**  The recursive call entry of `IStep` has bound `Bi ≤ B`:
BM.10's pull separator, `PullSpec.bound` of A0 (`x ≤ Bd`), discharged by `A3.a3_contract`. -/
theorem istep_B_le {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    c.B ≤ B := by
  rcases h with ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hD2, hsweep,
    hresid, hJ, hsel, hst'⟩
  rw [hc]
  exact (a3_contract (pullCap t l) st.D B Si Bi D1 hpull).bound

/-- The loop log only grows. -/
theorem iloop_evts_mono {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st stf : RState G s p}
    {qs : List (CallEntry G s × CallOut G s)} (h : ILoop t B l st qs stf) :
    List.Sublist st.evts stf.evts := by
  induction h with
  | exit _ => exact List.Sublist.refl _
  | step hne hg hstep hrest ih =>
    rw [istep_evts hstep] at ih
    exact (List.sublist_append_left _ _).trans ih

/-- Each child's return log is a sublist of the parent's final loop log. -/
theorem iloop_child_evts_sub {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st stf : RState G s p}
    {qs : List (CallEntry G s × CallOut G s)} (h : ILoop t B l st qs stf) :
    ∀ q ∈ qs, List.Sublist q.2.evts stf.evts := by
  induction h with
  | exit _ => intro q hq; simp at hq
  | step hne hg hstep hrest ih =>
    intro q' hq'
    rcases List.mem_cons.mp hq' with hqq | hqt
    · subst hqq
      exact List.Sublist.trans (List.sublist_append_right _ _)
        (istep_evts hstep ▸ iloop_evts_mono hrest)
    · exact ih q' hqt

/-! ## The DMSY call tree and its abstract forest -/

/-- **C1 instance data.**  A finite call-occurrence index over one corrected-DMSY execution:
each occurrence carries its `Run` (A4) and its entry/return records; `parent` is the direct
sub-call relation (`ChildOf`).  `U`/`B` of the abstract forest are *defined* from the engine
records (`settledFin (out X)`, `(entry X).B`); the five forest laws are the C1 seam (see the
module docstring). -/
structure DmsyTree (G : Graph) (s : Fin G.n) (ι : Type) (t : ℕ) where
  parent : ι → Option ι
  depth : ι → ℕ
  entry : ι → CallEntry G s
  out : ι → CallOut G s
  run : ∀ X, Run t (entry X) (out X)
  childOf : ∀ {X Y}, parent X = some Y → ChildOf t (entry Y) (entry X)
  depth_parent : ∀ X Y, parent X = some Y → depth X = depth Y + 1
  depth_root : ∀ X, parent X = none → depth X = 0
  U_sub : ∀ X Y, parent X = some Y → settledFin (out X) ⊆ settledFin (out Y)
  B_le : ∀ X Y, parent X = some Y → (entry X).B ≤ (entry Y).B
  siblings_disjoint : ∀ X X' Y, parent X = some Y → parent X' = some Y → X ≠ X' →
      Disjoint (settledFin (out X)) (settledFin (out X'))
  roots_disjoint : ∀ X X', parent X = none → parent X' = none → X ≠ X' →
      Disjoint (settledFin (out X)) (settledFin (out X'))

/-- **C1.**  The abstract `CostCharging.CallForest` of a DMSY execution.  Every counting
lemma of the parametric cost theory (`window_unique`, `cross_unique`, `level_card_sum_le`)
applies to this instance. -/
def DmsyTree.forest {G : Graph} {s : Fin G.n} {ι : Type} {t : ℕ} (T : DmsyTree G s ι t) :
    CallForest ι (Fin G.n) (WLab G s) where
  parent := T.parent
  depth := T.depth
  U := fun X => settledFin (T.out X)
  B := fun X => (T.entry X).B
  depth_parent := T.depth_parent
  depth_root := T.depth_root
  U_sub := T.U_sub
  B_le := T.B_le
  siblings_disjoint := T.siblings_disjoint
  roots_disjoint := T.roots_disjoint

/-- Level sums for the DMSY forest (free from `level_card_sum_le`): the settled sets of one
level are pairwise disjoint (`T_X = 0` reading), so their sizes sum to at most `|V|`. -/
theorem dmsy_level_card_sum_le {ι : Type} {t : ℕ} [Fintype ι]
    (T : DmsyTree G s ι t) (j : ℕ) :
    ∑ X ∈ (Finset.univ.filter (fun X : ι => T.forest.depth X = j)),
      (T.forest.U X).card ≤ G.n := by
  have h := T.forest.level_card_sum_le j
  rwa [Fintype.card_fin] at h

end DMSY
end Frontier

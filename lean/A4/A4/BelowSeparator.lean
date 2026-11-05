import A4.SettleSweep
import A4.LoopFrontier

/-!
# Frontier.DMSY.BelowSeparator — the below-separator discharge (the refusal floor)

`A4.SettleSweep.childStep_of` left one hypothesis to the joint chain:

```
hbelow : ∀ e, G.src e ∈ settledSet fo'.evts → ext (st'.d (G.src e)) e < c.B →
  Complete st'.d (G.dst e)
```

This file discharges it from an explicit, minimal child induction hypothesis `ChildFloor`
(stated at the child's own boundary, never the unstructured final theorem), the actual
`IStep` equations, and the canonical-label/walk facts.

The chain: the `IStep` equations pin `st'.d` to the sweep image of `fo'.d'` and `c.B` to the
pull separator `Bi`; a settled source keeps its child label through the sweep (`Complete.of_le`
+ `WalkInv.sound` + `sweepEvts_le`), so the below-separator candidate is the child's own
candidate, and the child's floor supplies `Complete fo'.d' (G.dst e)`; the sweep never raises a
label, and label soundness (every label is at least the canonical label `dis`) restores
completeness at the post labels.  The refusal-floor walk fact `dis_le_cand_of_settled` — the
head's canonical label sits at or below any candidate out of a complete, finitely-labelled
source — is exported separately: it is what makes `ChildFloor`'s second clause achievable at
the child (the candidate is below `c.B`, the walk `path src ++ [e]` visits the child's seed
set through the settled source, and the child's frontier/identity clauses with the carve-out
empty settle such heads complete).

Status: `ChildFloor` is the one genuinely inductive premise (the recursion's fixed point of
the same below-separator clause; the base case delivers it from A1's ungated sweep).  No
`sorry`/`admit`/new axioms.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The refusal-floor walk fact -/

/-- **The refusal-floor walk fact.**  The candidate out of a complete, reachable source
dominates the head's canonical label: `d src` is the canonical walk `path src`, so the
candidate is the walk `path src ++ [e]`, and `dis` is at most every walk.  This is the fact
that puts a below-separator candidate's head inside `Ũ(c.B, c.S)` (its canonical path visits
the child's seed set through the settled source) — the input half of the child-side
refusal-floor argument (`A1.utilde_of_relax`'s setting). -/
theorem dis_le_cand_of_settled {d : Labels G s} {u : Fin G.n}
    (hcomp : Complete d u) (hreach : G.Reachable s u) {e : Fin G.m} (hsrc : G.src e = u) :
    dis (s := s) (G.dst e) ≤ ext (d u) e := by
  have hcand : ext (d u) e
      = ((toW (path (s := s) u ++ [e]) : WalkOrd G s) : WLab G s) := by
    rw [hcomp, dis_of_reachable hreach]
    exact ext_coe (path (s := s) u) e
  rw [hcand]
  exact dis_le_walk (walk_ext (path_isMinWalk hreach).1 e hsrc)

/-! ## The child's floor — the one genuinely inductive premise -/

/-- **The child's floor** — the single genuinely-inductive premise of the below-separator
discharge, stated at the child's own boundary (`c`, `fo'`), never as the unstructured final
theorem.  The child's joint chain (`a4_joint`'s `Lemma37Concl` at the child call) delivers
both clauses: (1) is clause (2a)'s settlement completeness; (2) is the refusal floor — below
the child's separator `c.B`, an edge out of a child-settled vertex finds the head complete at
the child's return labels.  The recursion's fixed point: the parent needs (2) of the child for
exactly the clause the child obtains from its own children (plus the squeeze of (1) with the
frontier/identity clauses); the base case delivers it from A1's ungated sweep. -/
def ChildFloor (c : CallEntry G s) (fo' : CallOut G s) : Prop :=
  (∀ ev ∈ fo'.evts, Complete fo'.d' ev.v) ∧
    ∀ e, G.src e ∈ settledSet fo'.evts → ext (fo'.d' (G.src e)) e < c.B →
      Complete fo'.d' (G.dst e)

/-! ## The discharge -/

/-- **`hbelow`, discharged.**  The parent-post-label completeness hypothesis of
`A4.SettleSweep.childStep_of` follows from the child's floor, the `IStep` equations
(`st'.d = d3` is the sweep image of `fo'.d'`; `c.B = Bi`), and the canonical-label facts:
a settled source keeps its child label through the sweep (`Complete.of_le` + label
soundness + `sweepEvts_le`), the child's floor supplies `Complete fo'.d' (G.dst e)` below
the separator, and the sweep never raises a label while soundness holds labels at or above
`dis` — so completeness survives to `st'.d`. -/
theorem hbelow_of_floor (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hwalk : WalkInv fo'.d') (hfloor : ChildFloor c fo') :
    ∀ e, G.src e ∈ settledSet fo'.evts → ext (st'.d (G.src e)) e < c.B →
      Complete st'.d (G.dst e) := by
  obtain ⟨Si, Bi, D1, _resid, _J, _sel, D2, d3, _D3, _hpull, hc, _hmerge, hsweep, _hresid,
    _hJ, _hsel, hst'⟩ := h
  obtain ⟨hsettle, hbelow⟩ := hfloor
  have hst'd : st'.d = d3 := by rw [hst']
  have hcB : c.B = Bi := by rw [hc]
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := congrArg Prod.fst hsweep
  have hwalk3 : WalkInv d3 := by
    rw [hd3]; exact sweepEvts_walk B Bi fo'.evts fo'.d' D2 hwalk
  rw [hst'd]
  intro e hu hlt
  rw [hcB] at hlt
  have hsrc : Complete fo'.d' (G.src e) := by
    obtain ⟨ev, hev, hv⟩ := hu
    rw [← hv]; exact hsettle ev hev
  have hsrc3 : Complete d3 (G.src e) :=
    Complete.of_le hsrc (WalkInv.sound hwalk3)
      (by rw [hd3]; exact sweepEvts_le B Bi fo'.evts fo'.d' D2 (G.src e))
  have hdu : d3 (G.src e) = fo'.d' (G.src e) := hsrc3.trans hsrc.symm
  have hlt' : ext (fo'.d' (G.src e)) e < c.B := by
    rw [hcB]; rwa [← hdu]
  exact Complete.of_le (hbelow e hu hlt') (WalkInv.sound hwalk3)
    (by rw [hd3]; exact sweepEvts_le B Bi fo'.evts fo'.d' D2 (G.dst e))

/-! ## The strengthened `ChildStep` discharge -/

/-- **Strengthened `ChildStep` discharge.**  The per-iteration fact
`A4.LoopFrontier.ChildStep B st st' fo'` (= mono ∧ walk ∧ `SettleSweep`) from the child's
run-derived monotonicity and walk (`hmono`/`hwalk` — themselves available from the child's
`Run` via `child_mono_walk_of_run`) and the single genuinely-inductive premise `ChildFloor`:
`hbelow`'s parent-post-label form is `hbelow_of_floor`; `SettleSweep`'s relaxation then
follows in `A4.SettleSweep.settleSweep_relax` (above the separator from the sweep's own
acceptance, below it from completeness). -/
theorem childStep_of_floor (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hmono : ∀ v, fo'.d' v ≤ st.d v) (hwalk : WalkInv fo'.d')
    (hfloor : ChildFloor c fo') :
    ChildStep B st st' fo' :=
  ⟨hmono, hwalk, settleSweep_complete t B l h hfloor.1 hwalk,
    settleSweep_relax t B l h hfloor.1 hwalk (hbelow_of_floor t B l h hwalk hfloor)⟩

/-! ## The strengthened loop-frontier closure -/

/-- **Strengthened loop-frontier closure.**  `A4.LoopFrontier.lInv_iloop` with the per-step
`ChildStep` premise replaced by what the recursion actually supplies: at every iteration, the
child's run-derived monotonicity/walk and the child's floor `ChildFloor c fo'`.  The
genuinely-inductive premise exposed at the loop level is pointwise in the step — no history,
no final theorem. -/
theorem lInv_iloop_floor (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      LInv B S st →
      (∀ (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
         IStep t B l st₁ st₂ c fo' →
           (∀ v, fo'.d' v ≤ st₁.d v) ∧ WalkInv fo'.d' ∧ ChildFloor c fo') →
      LInv B S stf := by
  intro p st stf qs h
  induction h with
  | exit _ => exact fun hinv _ => hinv
  | step _hne _hg hstep hrest ih =>
      rename_i st st' st'' q qs'
      intro hinv hfloors
      obtain ⟨hmono, hwalk, hfloor⟩ := hfloors st st' q.1 q.2 hstep
      exact ih (lInv_istep t B l S hstep (childStep_of_floor t B l hstep hmono hwalk hfloor)
        hinv)
        (fun st₁ st₂ c fo' hstep => hfloors st₁ st₂ c fo' hstep)

end DMSY
end Frontier

import A4.BpMonotonicity
import A4.LowKeyClosure
import A4.JointAssembly

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.DrainedClauses — the return-side clauses at a **drained** return

Work package **A4**.  `A4.ReturnClauses` reduced clause (2a) `progress` to the loop-exit invariant
`LoopProg` **plus** `BpChain` (the running-bound monotonicity), and `A4.BpMonotonicity` /
`A4.ValueBpChain` showed that `BpChain` is the return side's genuinely inductive premise: `IStep`
alone never forces `st.bp ≤ st'.bp` (`istep_does_not_force_mono`), and neither the value floor at
keys nor the group label floor bridges to the label the child reads (`valueForm_fails`).  This file
records the case where **none of that is needed**: a return whose loop exited with `𝒟` drained.

## What changes when the loop drains (BM.24a / FIX-EMPTY)

`tailBP B st = B` whenever `DS.IsEmpty st.D` (`tailBP_of_isEmpty`).  So at a drained return the
returned bound is the *call's own* bound `B`, not the last child's `B'`, and every settlement of
every iteration already sits below `B` — because each child's bound is `≤` its own pull separator
`≤ B` (`run_le_bound` at the child, `PullSpec`/`pullRun`'s `x ≤ Bd` at the pull).  The chain
`BpChain` therefore drops out of `progress` entirely, and the replacement invariant
`LoopProgB` — "every loop settlement is below the call bound `B`" — is threaded by a single
`iloop_U_mem` split, with no monotonicity premise anywhere.

* `istep_Bprime_le_B` — the per-step arithmetic (`fo'.B' ≤ c.B ≤ B`) that feeds the threading.
* `LoopProgB`, `mkInit_progB`, `iloop_progB` — the invariant and its loop closure.
* `tail_progress_drained`, `callOut_tail_progress_of_drained` — clause (2a) `progress` at a
  drained return, **`BpChain`-free**.
* `istep_bp_le_of_drained` — the one place `BpChain` survives: a *drained* child has
  `fo'.B' = c.B`, so the step is monotone **provided** the entry state keeps no sub-`bp` key
  (`Ge st.bp st.D`).  That premise is the Q12 residue, not a label floor.

## The residue this does and does not remove

Removed for drained returns (i.e. for `Full t e out`, the case `TopFull` delivers at the top
entry): the audit's item 5 (`BpChain`, "unproved even at sketch grade") and the `LiveFloor`
seed-floor chain (`A4.BpMonotonicity` §2, `A4.LiveFloor`'s distance counterexample).

**Not** removed, and named exactly:

1. **`ChildFloor`'s refusal floor** (`A4.BelowSeparator`): the child's post-separator
   completeness half `∀ e, G.src e ∈ settledSet fo'.evts → ext (fo'.d' (G.src e)) e < c.B →
   Complete fo'.d' (G.dst e)`.  Its first clause *is* the child's `Lemma37Concl.settleComplete`
   (IH); the second is not a `Lemma37Concl` field, so the joint induction must carry it as a
   strengthened hypothesis (`SettleSweep`/`ChildStep`, hence `LInv` and clause (1), consume it).
2. **`StepSplit`** (`A4.JointAssembly`): the loop's frontier-coverage half `hcover` and the
   seed-cone half `j6 : (c.S : Set _) ⊆ Utilde B S`.  `uSubset` needs `j6`; `childOf_frontier`
   needs both.  Neither follows from `IStep` (the pull separator and the group filter are A2/A3's).
3. **The identity cover** `Ũ(B', S) ⊆ U ∪ K` (`A4.LowKeyClosure.ExitJoint`, and equivalently
   clause (1)'s `IsFrontier out.d' … out.U (DS.keys out.D)`): untouched by draining — `out.D` is
   the *tail's* store, which re-enters `W'` seeds and sweep candidates after the loop empties it,
   so a drained loop does not make the returned key set empty.
4. **`TopFull`** (`A4.Main`): drainedness is delivered at the top entry by the (E3) guard's
   full-execution delivery, which is a judgment (`eventCap` counts events, duplicates included),
   not a theorem — so everything here is *available* at a `Full` return but the top-level
   assembly still takes `TopFull` as an antecedent.

No `sorry`/`admit`, no new axiom.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The per-step bound arithmetic -/

/-- **A child's returned bound is below the call bound.**  `fo'.B' ≤ c.B` is the child's bound law
(`run_le_bound`), `c.B` is the pull separator, and the pull separator is `≤ Bd = B`
(`pullRun`'s third conjunct).  This is the fact that lets `LoopProgB` be stated against `B`
instead of against `st.bp`. -/
theorem istep_Bprime_le_B {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hble : fo'.B' ≤ c.B) : fo'.B' ≤ B := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _hmerge, _hsweep, _hresid, _hJ,
    _hsel, _hst'⟩ := h
  rw [hc] at hble
  exact hble.trans hpull.2.2.1

/-! ## 2. The drained progress invariant: every loop settlement is below `B` -/

/-- **`LoopProgB`**: every settlement of the loop's accumulated log sits below the **call** bound
`B`.  This is `A4.ReturnClauses.LoopProg` with `st.bp` replaced by `B` — the replacement that makes
`BpChain` unnecessary at a drained return, because there `tailBP B st = B` (`tailBP_of_isEmpty`). -/
def LoopProgB (B : WLab G s) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x ∈ settledSet st.evts, dis (s := s) x < B

/-- The initial state settles nothing, so `LoopProgB` holds there for free. -/
theorem mkInit_progB (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n) :
    LoopProgB e.B (mkInit e fo piv) := by
  intro x hx
  simp [mkInit, settledSet] at hx

/-- **The loop threads `LoopProgB`.**  One split on `iloop_U_mem`: a settlement of the exit log is
either the entry state's (nothing, at `mkInit`) or one of the children's, and each child's
settlements are below `B` by the child's own `progress` clause composed with
`istep_Bprime_le_B`.  No `BpChain`, no seed floor, no label floor. -/
theorem iloop_progB (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, ∀ x ∈ settledSet q.2.evts, dis (s := s) x < B) →
      LoopProgB B st → LoopProgB (G := G) (s := s) B stf := by
  intro p st stf qs hloop hchild hinv x hx
  rcases iloop_U_mem t B l hloop x hx with h0 | ⟨q, hq, hqx⟩
  · exact hinv x h0
  · exact hchild q hq x hqx

/-! ## 3. Clause (2a) `progress` at a drained return — without `BpChain` -/

/-- **(2a) `progress` at a drained return.**  With `𝒟` drained the returned bound is `B`
(BM.24a / FIX-EMPTY), the boundary half of `U` is below `B` by `wPrime`'s own filter, and the log
half is `LoopProgB`.  This is `A4.ReturnClauses.tail_progress` with its `LoopProg`+`BpChain`
premise pair replaced by `LoopProgB` alone. -/
theorem tail_progress_drained (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hempty : DS.IsEmpty st.D) (hprog : LoopProgB B st)
    (hsound : Sound st.d) :
    ∀ x ∈ (callOut (tail B S W st)).U, dis (s := s) x < (callOut (tail B S W st)).B' := by
  intro x hx
  rw [tailOut_B', tailBP_of_isEmpty B st hempty]
  rcases tailOut_U_mem.mp hx with h | h
  · exact hprog x h
  · have h' : x ∈ wPrime (tailBP B st) W st.evts st.d := by rwa [tailWp_reads_state] at h
    have hp := progress_wPrime (bp := tailBP B st) hsound h'
    rwa [tailBP_of_isEmpty B st hempty] at hp

/-- Every child of a loop returns below the **call** bound `B`: its own bound law
(`run_le_bound`, `hble`) composed with `istep_Bprime_le_B` at the iteration that made it. -/
theorem iloop_children_bound (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, q.2.B' ≤ q.1.B) → ∀ q ∈ qs, q.2.B' ≤ B := by
  intro p st stf qs hloop
  induction hloop with
  | exit _ => intro _ q hq; exact absurd hq List.not_mem_nil
  | step hne hg hstep hrest ih =>
    intro hble q hq
    rcases List.mem_cons.mp hq with heq | hq'
    · subst heq
      exact istep_Bprime_le_B hstep (hble _ List.mem_cons_self)
    · exact ih (fun q' hq' => hble q' (List.mem_cons_of_mem _ hq')) q hq'

/-- **Clause (2a) `progress` of `Lemma37Concl` at a drained return**, assembled from the loop: the
child premise is each child's own `Lemma37Concl.progress` (the joint induction's IH), transported
to `B` by `iloop_children_bound`. -/
theorem callOut_tail_progress_of_drained (t : ℕ) (B : WLab G s) (l : ℕ)
    (S W : Finset (Fin G.n)) {p : ℕ} {st stf : RState G s p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t B l st qs stf) (hempty : DS.IsEmpty stf.D)
    (hble : ∀ q ∈ qs, q.2.B' ≤ q.1.B)
    (hchild : ∀ q ∈ qs, ∀ x ∈ settledSet q.2.evts, dis (s := s) x < q.2.B')
    (hinit : LoopProgB B st) (hsound : Sound stf.d) :
    ∀ x ∈ (callOut (tail B S W stf)).U, dis (s := s) x < (callOut (tail B S W stf)).B' :=
  tail_progress_drained B S W stf hempty
    (iloop_progB t B l hloop
      (fun q hq x hx =>
        (hchild q hq x hx).trans_le (iloop_children_bound t B l hloop hble q hq))
      hinit)
    hsound

/-! ## 4. The one place `BpChain` survives: a drained child with no sub-`bp` key -/

/-- **A drained child makes the step monotone, given a value floor at the entry store.**  With
`fo'.B' = c.B` the step's new running bound is the pull separator `Bi`, and the pull's
availability conjunct (`(DS.IsEmpty D ∨ ∃ y v, D y = some v ∧ v < x)`) plus the value floor
`Ge st.bp st.D` puts `st.bp` below it.  The value floor is the Q12 residue
(`A4.MintPreFloor`): a sub-`bp` key that is a recorded mint is not excluded. -/
theorem istep_bp_le_of_drained {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hne : ∃ y, st.D y ≠ none) (hdrain : fo'.B' = c.B) (hge : Ge st.bp st.D) :
    st.bp ≤ st'.bp := by
  rw [istep_bp h, hdrain]
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _hmerge, _hsweep, _hresid, _hJ,
    _hsel, _hst'⟩ := h
  rw [hc]
  show st.bp ≤ Bi
  obtain ⟨y0, hy0⟩ := hne
  rcases hpull.2.2.2.2.1 with hemp | ⟨y, v, hy, hlt⟩
  · exact absurd (hemp y0) hy0
  · exact (hge y v hy).trans hlt.le

end DMSY
end Frontier

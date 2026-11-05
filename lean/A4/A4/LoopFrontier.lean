import A4.Structural

/-!
# Frontier.DMSY.LoopFrontier — the Algorithm-3 loop frontier invariant

`A4.ReachInv` isolated the one operational invariant still needed by `a4_joint`/`theoremT`: a
`StepFrontier` witness (parent loop-state frontier + coverage + (J6)) at every iteration.  This
file attacks that invariant *directly*: it defines the loop frontier invariant `LInv`, proves it
initialises from FindPivots, is preserved across one `IStep` (via the framework's `IsFrontier.step`),
and closes over `ILoop` — producing the child's frontier (`istep_child_frontier`) rather than
taking it as input.

The one fact the semantics does not pin down — the post-sweep state settles every child
settlement complete **and** relaxes every out-edge of a settled vertex below `B` — is kept as a
single per-iteration hypothesis `SettleSweep` (below), never as an axiom.  It is the joint
chain's clause-(2a) + refusal-floor content, the "single next missing fact".

The frontier's `X`/`Y` are existentially carried (`LInv`), and the exact `IStep` transition
`⟨X, Y⟩ ↦ ⟨X ∪ Z, (Y \ Z) ∪ Relaxed …⟩` is exhibited in `lInv_istep`'s body.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The post-sweep obligation (the one genuinely-missing per-iteration fact) -/

/-- After one iteration's merge-and-sweep, the child's settlements are complete at the post labels,
and every out-edge of a settled vertex with candidate below `B` has been relaxed.  This is the
joint chain's clause-(2a) (`settleComplete` at post labels) plus the refusal-floor (`hrelax`);
it is *not* derivable from `IStep` alone. -/
def SettleSweep (B : WLab G s) {p : ℕ} (st' : RState G s p) (fo' : CallOut G s) : Prop :=
  (∀ z ∈ settledSet fo'.evts, Complete st'.d z) ∧
    (∀ e, G.src e ∈ settledSet fo'.evts →
      ext (st'.d (G.src e)) e < B → st'.d (G.dst e) ≤ ext (st'.d (G.src e)) e)

/-- The full per-iteration child-step fact: label monotonicity, walk labels, and `SettleSweep`.
Monotonicity and walk are derivable from the child's `Run` (`child_mono_walk_of_run`); only
`SettleSweep` is left to the joint chain. -/
def ChildStep (B : WLab G s) {p : ℕ} (st₁ st₂ : RState G s p) (fo' : CallOut G s) : Prop :=
  (∀ v, fo'.d' v ≤ st₁.d v) ∧ WalkInv fo'.d' ∧ SettleSweep B st₂ fo'

/-- Monotonicity and walk of a child's return follow from the child's `Run` and the walk of its
entry labels (`run_le`/`run_walk`); only `SettleSweep` remains. -/
theorem child_mono_walk_of_run (t : ℕ) {c : CallEntry G s} {fo' : CallOut G s}
    (hrun : Run t c fo') (hwalk : WalkInv c.d) : (∀ v, fo'.d' v ≤ c.d v) ∧ WalkInv fo'.d' :=
  ⟨fun v => run_le t hrun v, run_walk t hrun hwalk⟩

/-! ## The loop frontier invariant -/

/-- `LInv B S st`: the loop state `st` carries a frontier `⟨X, Y⟩` for `Ũ(B, S)` at walk labels
(`X`/`Y` existential — the `IStep` transition is exhibited in `lInv_istep`). -/
def LInv (B : WLab G s) (S : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  WalkInv st.d ∧ ∃ X Y : Set (Fin G.n), IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y

/-- **Initialisation**: `mkInit` carries the FindPivots frontier `⟨W, ⋃ P_j⟩` for `Ũ(e.B, e.S)`
(`fpRun_frontier_persist` + `FPContract.walk`). -/
theorem lInv_init {t : ℕ} {e : CallEntry G s} {fo : FPOut G s} {piv : Fin fo.p → Fin G.n}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) :
    LInv e.B e.S (mkInit e fo piv) := by
  have hfront : IsFrontier (mkInit e fo piv).d (Utilde e.B (e.S : Set (Fin G.n)))
      (fo.W : Set (Fin G.n)) {x | ∃ j, x ∈ (mkInit e fo piv).pl j} := by
    simpa [mkInit] using (fpRun_frontier_persist hfp)
  have hwalk : WalkInv (mkInit e fo piv).d := by
    simpa [mkInit] using (fpRun_contract ⟨e.B, e.S, fpCap t, e.d⟩ fo hfp).1.walk
  exact ⟨hwalk, (fo.W : Set (Fin G.n)), {x | ∃ j, x ∈ (mkInit e fo piv).pl j}, hfront⟩

/-- **Preservation across one `IStep`.**  The framework step `IsFrontier.step` takes the settled
set `Z = settledSet fo'.evts` and the `SettleSweep` fact, and hands the next frontier
`⟨X ∪ Z, (Y \ Z) ∪ Relaxed st'.d B Z⟩`. -/
theorem lInv_istep (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hcs : ChildStep B st st' fo') (hinv : LInv B S st) :
    LInv B S st' := by
  rcases hinv with ⟨_hwalk, X, Y, hfront⟩
  have hwalk' : WalkInv st'.d := istep_walk t B l h hcs.2.1
  have hle : ∀ v, st'.d v ≤ st.d v := fun v => istep_le_of_child t B l h hcs.1 v
  have hU : ∀ v ∈ Utilde B (S : Set (Fin G.n)), dis (s := s) v < B := fun v hv => hv.1
  have hfront' : IsFrontier st'.d (Utilde B (S : Set (Fin G.n)))
      (X ∪ settledSet fo'.evts)
      ((Y \ settledSet fo'.evts) ∪ Relaxed st'.d B (settledSet fo'.evts)) :=
    IsFrontier.step hfront hU (WalkInv.sound hwalk') hle hcs.2.2.1 hcs.2.2.2
  exact ⟨hwalk', X ∪ settledSet fo'.evts,
    (Y \ settledSet fo'.evts) ∪ Relaxed st'.d B (settledSet fo'.evts), hfront'⟩

/-- **Closure over `ILoop`.**  `LInv` is preserved by the whole loop, given a `ChildStep` for
every `IStep` in it. -/
theorem lInv_iloop (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      LInv B S st →
      (∀ (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
         IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo') →
      LInv B S stf := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hinv _ => hinv
  | step hne hg hstep hrest ih =>
      rename_i st st' st'' q qs'
      intro hinv hcs
      exact ih (lInv_istep t B l S hstep (hcs st st' q.1 q.2 hstep) hinv) hcs

/-! ## Producing the child frontier (the `StepFrontier` witness) -/

/-- **Child frontier from the loop invariant**: at an `IStep` whose child is `c`, the parent
frontier `⟨X, Y⟩` (a component of `LInv`) plus coverage and (J6) give the child's frontier
`⟨∅, c.S⟩` for `Ũ(c.B, c.S)` — the `StepFrontier`→`child_frontier_of_step` chain of
`A4.ReachInv`, restated against `LInv`'s explicit frontier. -/
theorem child_frontier_of_lInv (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (X Y : Set (Fin G.n)) (hfront : IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y)
    (hcover : ∀ y ∈ Y, st.d y < c.B → y ∈ c.S)
    (hj6 : (c.S : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))) :
    IsFrontier c.d (Utilde c.B (c.S : Set (Fin G.n))) ∅ (c.S : Set (Fin G.n)) :=
  istep_child_frontier t B l h hfront hcover hj6

end DMSY
end Frontier

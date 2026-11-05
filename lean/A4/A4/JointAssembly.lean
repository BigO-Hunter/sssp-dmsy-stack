import A4.BelowSeparator
import A4.ReachInv
import A4.OriginTrace

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.JointAssembly — the entry-side assembly of the joint chain

This file connects the three landed layers across the recursion **without** assuming
`a4_joint` or `RunTraceCert`, and pins exactly how far that gets the two `Main` seams.

What it assembles (all new, all unconditional except for two explicitly-typed premises):

* `iloopTrace_child_run` — every child call of an *instrumented* loop is a genuine `Run`
  (`ILoopTrace.step`'s certified `hchild`, erased by `runTrace_run`).  The instrumented
  recursion therefore supplies the children's `Run`s that `ChildOf` hides existentially.
* `istepTrace_childStep` — one iteration's `ChildStep` from the step's own child `RunTrace`,
  the loop's walk labels and the typed `ChildFloor`: `BelowSeparator.childStep_of_floor`
  applied to `child_mono_walk_of_run`'s monotonicity/walk.
* `step_witness_bundle` — the per-step interface: level drop, entry-label inheritance, the
  typed mint origin (`OriginCert`, from `LastWriter`/`OriginTrace`) and `ChildStep`, in one
  conjunction.  This is what the joint induction consumes at each iteration.
* `iloop_child_frontier` — **every** child of a loop (not just the first) carries the frontier
  `⟨∅, c.S⟩` for `Ũ(c.B, c.S)`: `LInv` is threaded through the loop and `istep_child_frontier`
  fires at each iteration.  Previously only the initial frontier was reachable.
* `childOf_frontier`, `reachInv_of_reach`, `lemma37Hyp_of_reach` — the closure over `Reach`
  that `A4.ReachHyp` asked for: a `Reach`-strengthening carrying `IsFrontier`, hence
  `Lemma37Hyp` at every reachable non-base entry — the exact premise `a4_joint` takes.

What it does **not** do, and why (see the closing section): nothing here produces a
`Lemma37Concl` clause at a *return*.  `ChildFloor` + `OriginCert` are entry-side and
value-origin facts; the return-side clauses (`progress`, `identity`, `containS`/`containR`,
`bound`) and `NoPrem`'s mint bound are separate theorems.  So neither `a4_joint` nor
`theoremT` is discharged — the residual premises are named at the end.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The instrumented loop's children -/

/-- **Every child of an instrumented loop is a genuine `Run`.**  `ILoopTrace.step` certifies
each child with its own `RunTrace` at the threaded trace index; erasure (`runTrace_run`) drops
the trace.  This is the instrumented counterpart of `Run.recur`'s `hchildren`, and it is what
makes `ChildOf`'s existentially-hidden child runs unnecessary at the loop level. -/
theorem iloopTrace_child_run (t : ℕ) :
    ∀ {B : WLab G s} {l i : ℕ} {p : ℕ} {st stf : RState G s p}
      {qs : List (CallEntry G s × CallOut G s)} {tr : Trace G s},
      ILoopTrace t B l i st qs stf tr → ∀ q ∈ qs, Run t q.1 q.2 := by
  intro B l i p st stf qs tr h
  refine ILoopTrace.rec
    (motive_1 := fun _B _l _i _p _st qs _stf _tr _ => ∀ q ∈ qs, Run t q.1 q.2)
    (motive_2 := fun _B _l _e _out _tr _ => True) ?exit ?step ?base ?recur h
  case exit =>
    intro _B _l _i _p _st _h q hq
    exact absurd hq List.not_mem_nil
  case step =>
    intro _B _l _i _p _st _st' _st'' _q _qs _trStep _trChild _trRest _hne _hg _hstep hchild
      _hrest _ih_child ih_rest q' hq'
    rcases List.mem_cons.mp hq' with rfl | hq''
    · exact runTrace_run t hchild
    · exact ih_rest q' hq''
  case base => intro _B _l _e _bout _hl _hb; trivial
  case recur => intro _B _l _e _p _fo _piv _st0 _stf _qs _trLoop _hl _hfp _hpiv _hst0 _hloop _ih; trivial

/-! ## One iteration's `ChildStep`, from the child's own certified run -/

/-- **`ChildStep` at one iteration.**  The child's `RunTrace` (carried by the instrumented loop)
erases to a `Run`, whose monotonicity and walk (`child_mono_walk_of_run`) — with the child's
entry walk inherited from the loop state (`c.d = st.d`) — feed `childStep_of_floor`.  So the
single genuinely-inductive premise at a step is `ChildFloor`, exactly as `BelowSeparator` says. -/
theorem istepTrace_childStep (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    {trStep trChild : Trace G s} (h : IStepTrace t B l i st st' c fo' trStep trChild)
    (hchild : RunTrace t B l c fo' trChild) (hwalk : WalkInv st.d) (hfloor : ChildFloor c fo') :
    ChildStep B st st' fo' := by
  have hentry : c.d = st.d := istepTrace_child_d t B l i h
  have hcd : WalkInv c.d := by rw [hentry]; exact hwalk
  obtain ⟨hmono, hwalk'⟩ := child_mono_walk_of_run t (runTrace_run t hchild) hcd
  have hmono' : ∀ v, fo'.d' v ≤ st.d v := by
    intro v; rw [← hentry]; exact hmono v
  exact childStep_of_floor t B l (istepTrace_istep t B l i h) hmono' hwalk' hfloor

/-- **The per-step interface** the joint induction consumes: level drop, entry-label
inheritance, the typed mint origin, and `ChildStep` — one conjunction, no `Lemma37Concl`, no
`RunTraceCert`.  The mint disjunct is `LastWriter`/`OriginTrace`'s typed origin: the current
sweep wrote the value (`LastTarget`), or the value is the child's return bearing
`OriginCert.child`, **unconditionally** (no descent assumed). -/
theorem step_witness_bundle (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    {trStep trChild : Trace G s} (h : IStepTrace t B l i st st' c fo' trStep trChild)
    (hchild : RunTrace t B l c fo' trChild) (hwalk : WalkInv st.d) (hfloor : ChildFloor c fo') :
    c.l = l - 1 ∧ c.d = st.d ∧
      (∀ m ∈ st'.mints,
        (∃ r, LastTarget m.x trStep r ∧ r.vv = m.val) ∨
          (m.val = fo'.d' m.x ∧ OriginCert G s m.x m.val)) ∧
      ChildStep B st st' fo' :=
  ⟨istepTrace_child_l t B l i h, istepTrace_child_d t B l i h,
    istepTrace_mint_origin t B l i h, istepTrace_childStep t B l i h hchild hwalk hfloor⟩

/-! ## The per-step split premise -/

/-- **`StepSplit`** — the per-step frontier split, the one operational premise this assembly
still takes: for the frontier the loop state actually carries (some `X`, the state's `Y`), a
below-`c.B` member of `Y` lies in the child's seed set, and the child's seeds lie in `Ũ(B, S)`.
These are `LoopFrontier.child_frontier_of_lInv`'s `hcover`/`hj6` inputs, stated over an
existentially-given frontier so they compose with `LInv`.  Not derivable from `IStep` alone
(the `pullRun` spec is A2/A3's); not assumed as an axiom. -/
def StepSplit (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) : Prop :=
  ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
    IStep t B l st st' c fo' → ∀ Y : Set (Fin G.n),
      (∃ X : Set (Fin G.n), IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y) →
      (∀ y ∈ Y, st.d y < c.B → y ∈ c.S) ∧
        (c.S : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))

/-! ## Every child of a loop carries its frontier -/

/-- **Every iteration's child carries `⟨∅, c.S⟩`.**  `LInv` is threaded through the loop
(`lInv_istep`), so `istep_child_frontier` fires at *each* iteration, not only the first.  This
is the piece `A4.LoopFrontier` could not state: it produced the loop's final frontier only. -/
theorem iloop_child_frontier (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      LInv B S st →
      (∀ (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
         IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo') →
      StepSplit t B l S →
      ∀ q ∈ qs,
        IsFrontier q.1.d (Utilde q.1.B (q.1.S : Set (Fin G.n))) ∅ (q.1.S : Set (Fin G.n)) := by
  intro p st stf qs h
  refine ILoop.rec
    (motive := fun st qs stf _ =>
      LInv B S st →
      (∀ (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
         IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo') →
      StepSplit t B l S →
      ∀ q ∈ qs,
        IsFrontier q.1.d (Utilde q.1.B (q.1.S : Set (Fin G.n))) ∅ (q.1.S : Set (Fin G.n)))
    ?_ ?_ h
  case refine_1 =>
    intro st h _hinv _hcs _hsplit q hq
    exact absurd hq List.not_mem_nil
  case refine_2 =>
    intro st st' st'' q qs hne hg hstep hrest ih hinv hcs hsplit q' hq'
    rcases List.mem_cons.mp hq' with heq | hq''
    · rw [heq] at *
      obtain ⟨_hw, X, Y, hfront⟩ := hinv
      obtain ⟨hcover, hj6⟩ := hsplit st st' q.1 q.2 hstep Y ⟨X, hfront⟩
      exact child_frontier_of_lInv t B l S hstep X Y hfront hcover hj6
    · exact ih (lInv_istep t B l S hstep (hcs st st' q.1 q.2 hstep) hinv) hcs hsplit q' hq''

/-- **A child's frontier from `ChildOf`.**  `ChildOf` hides the parent loop, its pre-state and
the step; `lInv_init` supplies `LInv` at `mkInit`, and `iloop_child_frontier` walks to the
child's own iteration.  This is exactly the `hfrontier` input of `reachInv_child` /
`lemma37Hyp_child`. -/
theorem childOf_frontier (t : ℕ) {e c : CallEntry G s} (hcd : ChildOf t e c)
    (hcs : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st₁ st₂ : RState G s p)
      (c : CallEntry G s) (fo' : CallOut G s), IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo')
    (hsplit : ∀ (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)), StepSplit t B l S) :
    IsFrontier c.d (Utilde c.B (c.S : Set (Fin G.n))) ∅ (c.S : Set (Fin G.n)) := by
  obtain ⟨_out, _p, fo, piv, st0, stf, qs, _hrun, _hout, _hl, hfp, _hpiv, hst0, hloop, _hch,
    q, hq, hqc⟩ := hcd
  have hinv : LInv e.B e.S st0 := by
    rw [hst0]; exact lInv_init hfp
  have h := iloop_child_frontier t e.B e.l e.S hloop hinv (hcs e.B e.l) (hsplit e.B e.l e.S) q hq
  rwa [hqc] at h

/-! ## Closure over `Reach`: the premise `a4_joint` takes -/

/-- **`ReachInv` at every reachable non-base entry.**  Induction on `Reach`: the top entry is
`reachInv_top`; a child gets its frontier from `childOf_frontier` and its size/level from
`reachInv_child`.  The parent's own `ReachInv` is needed only for the level (`c.l = e.l - 1`
with `0 < c.l` forces `0 < e.l`), so the induction stays at the strengthened statement and does
not smuggle in `a4_joint`. -/
theorem reachInv_of_reach (t : ℕ) (ht : 2 ≤ t)
    (hcs : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st₁ st₂ : RState G s p)
      (c : CallEntry G s) (fo' : CallOut G s), IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo')
    (hsplit : ∀ (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)), StepSplit t B l S) :
    ∀ {e : CallEntry G s}, Reach t e → 0 < e.l → ReachInv t e := by
  intro e hre
  refine Reach.rec (motive := fun e _ => 0 < e.l → ReachInv t e) ?_ ?_ hre
  · intro hpos; exact reachInv_top t ht hpos
  · intro e0 c0 he hc ih hpos
    have hcd : ChildOf t e0 c0 := hc
    obtain ⟨_out, _p, _fo, _piv, _st0, _stf, qs, _hrun, _hout, _hl, _hfp, _hpiv, _hst0,
      hloop, _hch, q, hq, hqc⟩ := hcd
    have hlev : c0.l = e0.l - 1 := by
      rw [← hqc]
      exact reachInv_iloop_children_level t e0.B e0.l hloop q hq
    have hepos : 0 < e0.l := by omega
    exact reachInv_child t (ih hepos) hc ht hpos (childOf_frontier t hc hcs hsplit)

/-- **`Lemma37Hyp` at every reachable non-base entry** — verbatim the premise `a4_joint`
(`JointChain`) takes.  So the *entry side* of the joint chain is now assembled; what is left in
`a4_joint` is the return side (see the closing note). -/
theorem lemma37Hyp_of_reach (t : ℕ) (ht : 2 ≤ t)
    (hcs : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st₁ st₂ : RState G s p)
      (c : CallEntry G s) (fo' : CallOut G s), IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo')
    (hsplit : ∀ (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)), StepSplit t B l S) :
    ∀ {e : CallEntry G s}, Reach t e → 0 < e.l → Lemma37Hyp t e :=
  fun {e} hre hpos => reachInv_lemma37Hyp (reachInv_of_reach t ht hcs hsplit hre hpos)

/-! ## What this does and does not give the two `Main` seams

`a4_joint` (`JointChain t`) needs `Lemma37Concl (Full t) e out ∧ NoPrem e out` at every
reachable run's **return**.  Everything above is *entry-side*: it converts `Reach` into
`Lemma37Hyp`, and `ChildFloor` into per-step `ChildStep` (settlement completeness + the
refusal-floor relaxation of `SettleSweep`).  The clauses at `out = callOut (tail e.B e.S fo.W stf)`
are untouched:

* `progress`/`uSubset` — the tail's `B'` (`tailBP`) against `out.U = settledSet out.evts`;
* `identity` `out.U = Ũ(B',S) ∖ carveKeys` — the frontier squeeze (`IsFrontier.below`/`complete_of_empty`);
* `containS`/`containR` — `DS` custody (`A4.Rep`, `A4.WDrop`);
* `bound` — needs `NoPrem`'s converse at the final re-selection.

`theoremT` needs `out.B' ≤ m.val` for every `m ∈ out.mints`, i.e. a **value bound**, while
`OriginCert` types the *origin* of `m.val` (`LastTarget` / `OriginCert.child` / `iter`) and says
nothing about its size.  Concretely: `out.B' = tailBP e.B stf = stf.bp` when `stf.D` is
nonempty, and `stf.bp` is the **last child's** `B'`, so Theorem T is the loop invariant
"the last child's bound dominates the leftover pivot members' labels" — a return-side fact, not
an origin fact.  `Full` returns are already covered (`improvementProvenance_of_full` /
`full_no_prem`); the gap is the non-full case.

The *descent* gap flagged in `A4.OriginTrace` is likewise untouched here and is not repairable
at the certificate level: `OriginCert.child` is unconditional, so the only missing link is the
descent through a child whose own run logs nothing — `BaseInherited` is satisfiable only if the
base run accepts nothing, so base children need A1's `baseRun` acceptance-trace instrumentation,
and deeper children need A2's `fpRun` trace from FindPivots labels to entry labels.  Neither is
assumed here.
-/

end DMSY
end Frontier

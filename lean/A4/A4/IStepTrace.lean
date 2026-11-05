import A4.SweepTrace

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.IStepTrace — the instrumented `IStep`/`ILoop`/`Run`

Work package **A4 (BMSSP recursion)**, the lift of `SweepTrace` through the Algorithm-3 spine.
`IStepTrace` mirrors `A4.Semantics.IStep` exactly except that the child-settlement sweep uses
`sweepEvtsT`, so the step additionally carries `trStep` (the accepted-relaxation trace of that
sweep) and `trChild` (the child call's own acceptance history).  The **child index** `i` is
threaded alongside the level: `IStepTrace`'s step is the `i`-th child call of the parent loop
and `ILoopTrace`'s step counter carries it (`hrest` recurses at `i + 1`).  `i` is carried for
the origin certificates of `A4.OriginTrace` (`OriginCert.child i` / `OriginCert.iter i`); the
step's own semantics does not read it.

The recursion itself is instrumented: `ILoopTrace` and `RunTrace` are declared **mutually**,
and `ILoopTrace.step` requires the child call's own `RunTrace` derivation *directly*, with the
derivation's trace index **equal to the threaded `trChild`** — `hchild : RunTrace t B l q.1
q.2 trChild`.  The child's certified acceptance history is thus exactly the history threaded
into the loop's aggregate (the soundness tie; a nested `∃` formulation is rejected by the
kernel — nested inductive occurrences cannot carry the declaration's parameters — so the tie
rides on a direct mutual occurrence instead).  Mutual declarations must share their parameter
telescope, so only `t` is a parameter and the bound/level/counter (`B`, `l`, `i`) are indices —
that is also what lets `RunTrace.recur` instantiate the loop at the *call's* own `e.B`/`e.l`
(recursive mutual occurrences must be applied to the parameters verbatim, so per-call `B`/`l`
may not be parameters).  The children's `Run`s are recovered by erasure (`runTrace_run`, strong
induction on the level — a child sits at `l - 1`, `iloopTrace_children_l`).

Erasure is exact: `istepTrace_istep`, `iloopTrace_iloop`, `runTrace_run` recover the original
`IStep`/`ILoop`/`Run` by dropping the trace.

The mint value is pinned to the sweep's final label: `istepTrace_mints_label` proves that a
line-29 mint records `d3 (sel j)` — the label of the mint key *after* the gated sweep — so
`m.val = st'.d m.x`.  Whether that label was produced by a relaxation *in this sweep* (hence
visible in `trStep`) rather than inherited from the child is separated by
`A4.WriterTrace.istepTrace_mint_writer`, and the inherited case is typed by
`A4.OriginTrace.istepTrace_mint_origin` (`OriginCert.child`).  What no trace here can show is
the descent *below* a child's own logged history: A2's `fpRun` and A1's `baseRun` log no
acceptance trace, so a label's passage from FindPivots or base-run labels to the call's entry
labels is unwitnessed — instrumenting those two runs is the exact remaining field.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The instrumented iteration -/

open Classical in
/-- One Algorithm-3 loop iteration, instrumented: identical witnesses to `IStep`, but the
child-settlement sweep is `sweepEvtsT`, exposing `trStep` (its accepted relaxations) and
carrying `trChild` (the child call's acceptance history) plus the child's index `i` in the
parent loop. -/
def IStepTrace (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ} (st st' : RState G s p)
    (c : CallEntry G s) (fo' : CallOut G s) (trStep : Trace G s) (trChild : Trace G s) : Prop :=
  ∃ (Si : Finset (Fin G.n)) (Bi : WLab G s) (D1 : DS G s)
    (resid : Fin p → Finset (Fin G.n)) (J : Finset (Fin p)) (sel : Fin p → Fin G.n)
    (D2 : DS G s) (d3 : Labels G s) (D3 : DS G s),
    pullRun (pullCap t l) st.D B Si Bi D1 ∧
    c = ⟨Bi, expand st.d st.pl st.piv Si Bi, l - 1, st.d⟩ ∧
    D2 = DS.deleteSet (DS.merge D1 fo'.D) (settledFinset fo') ∧
    (d3, D3, trStep) = sweepEvtsT B Bi fo'.evts fo'.d' D2 ∧
    (∀ j, resid j = (st.pl j).filter (fun x => x ∉ settledSet fo'.evts)) ∧
    J = (Finset.univ.filter fun j => st.piv j ∈ settledSet fo'.evts ∧ (resid j).Nonempty) ∧
    (∀ j, j ∈ J → sel j ∈ resid j ∧ ∀ y ∈ resid j, d3 (sel j) ≤ d3 y) ∧
    st' = { d := d3,
            D := J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3,
            evts := st.evts ++ fo'.evts,
            bp := fo'.B',
            pl := resid,
            piv := fun j => if j ∈ J then sel j else st.piv j,
            mints := J.toList.map (fun j => Mint.mk (sel j) (d3 (sel j))) }

/-- **Erasure**: dropping the trace recovers `IStep`, with the same `d3`/`D3`/`st'`. -/
theorem istepTrace_istep (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) : IStep t B l st st' c fo' := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  refine ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, ?_, hresid, hJ, hsel, hst'⟩
  exact Prod.ext
    ((congrArg Prod.fst hsweep).trans (sweepEvtsT_fst B Bi fo'.evts fo'.d' D2))
    ((congrArg (fun x : Labels G s × DS G s × List (RelaxStep G s) => x.2.1) hsweep).trans
      (sweepEvtsT_snd B Bi fo'.evts fo'.d' D2))

/-- A line-29 mint records the sweep's final label of its key: `m.val = st'.d m.x = d3 (sel j)`.
This is what the provenance chain must trace back to a ground — but it names only the *value*,
not which acceptance (if any) in `trStep` produced it. -/
theorem istepTrace_mints_label (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) :
    ∀ m ∈ st'.mints, st'.d m.x = m.val := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, _hpull, _hc, _hmerge, _hsweep, _hresid, _hJ,
    _hsel, hst'⟩ := h
  subst hst'
  intro m hm
  obtain ⟨j, _hj, hjm⟩ := List.mem_map.mp hm
  subst m
  rfl

/-! ## The child-call linkage -/

/-- The instrumented step's child call sits one level below the loop. -/
theorem istepTrace_child_l (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) : c.l = l - 1 := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, _hpull, hc, _hmerge, _hsweep, _hresid, _hJ,
    _hsel, _hst'⟩ := h
  rw [hc]

/-- The instrumented step's child call inherits the prior iteration state's labels as its entry
labels — the `OriginCert.iter` link (`A4.OriginTrace`). -/
theorem istepTrace_child_d (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) : c.d = st.d := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, _hpull, hc, _hmerge, _hsweep, _hresid, _hJ,
    _hsel, _hst'⟩ := h
  rw [hc]

/-! ## The instrumented loop and run (mutually instrumented recursion) -/

/-- The tail's `W'` boundary sweep, instrumented: the same `seedIns`/`wPrime`/`wPrimeEvts`
arguments as `Semantics.tail`, with `sweepEvtsT` exposing its trace. -/
noncomputable def tailTrace (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    Trace G s :=
  let si := seedIns (tailBP B st) B S st.d st.D
  (sweepEvtsT B (tailBP B st) (wPrimeEvts (wPrime (tailBP B st) W st.evts si.1)) si.1 si.2).2.2

-- `ILoop` plus the concatenated acceptance history: each iteration contributes
-- `trChild ++ trStep` — the child call's own history then this step's gated sweep — and the
-- step counter `i` names the child's index in the loop.  The child's history is certified:
-- `hchild` is the child's own `RunTrace` derivation **with trace exactly `trChild`**.
mutual
inductive ILoopTrace (t : ℕ) :
    (B : WLab G s) → (l : ℕ) → (i : ℕ) → ∀ {p : ℕ}, RState G s p →
      List (CallEntry G s × CallOut G s) → RState G s p → Trace G s → Prop
  | exit {B : WLab G s} {l i : ℕ} {p : ℕ} {st : RState G s p}
      (h : DS.IsEmpty st.D ∨ eventCap t l < st.evts.length) :
      ILoopTrace t B l i st [] st []
  | step {B : WLab G s} {l i : ℕ} {p : ℕ} {st st' st'' : RState G s p}
      {q : CallEntry G s × CallOut G s} {qs : List (CallEntry G s × CallOut G s)}
      {trStep trChild trRest : Trace G s}
      (hne : ¬ DS.IsEmpty st.D) (hg : st.evts.length ≤ eventCap t l)
      (hstep : IStepTrace t B l i st st' q.1 q.2 trStep trChild)
      (hchild : RunTrace t B l q.1 q.2 trChild)
      (hrest : ILoopTrace t B l (i + 1) st' qs st'' trRest) :
      ILoopTrace t B l i st (q :: qs) st'' (trChild ++ trStep ++ trRest)

/-- The instrumented `Run`: the same spine as `Run`, but the recur case threads the loop's
acceptance history and the tail sweep's history (`trLoop ++ tailTrace`), and every loop child
call carries its own certified `RunTrace` derivation (through `ILoopTrace.step`'s `hchild`). -/
inductive RunTrace (t : ℕ) :
    (B : WLab G s) → (l : ℕ) → CallEntry G s → CallOut G s → Trace G s → Prop
  | base {B : WLab G s} {l : ℕ} {e : CallEntry G s} {bout : BaseOut G s} (hl : e.l = 0)
      (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
      RunTrace t B l e (baseOut bout) []
  | recur {B : WLab G s} {l : ℕ} {e : CallEntry G s} {p : ℕ} {fo : FPOut G s}
      {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
      {qs : List (CallEntry G s × CallOut G s)} {trLoop : Trace G s}
      (hl : 0 < e.l) (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
      (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
      (hst0 : st0 = mkInit e fo piv)
      (hloop : ILoopTrace t e.B e.l 0 st0 qs stf trLoop) :
      RunTrace t B l e (callOut (tail e.B e.S fo.W stf))
        (trLoop ++ tailTrace e.B e.S fo.W stf)
end

/-! ## Erasure of the instrumented loop -/

/-- **Erasure**: dropping the trace recovers `ILoop`.  (Mutual inductives need the explicit
recursor; the `RunTrace` motive is trivial here.) -/
theorem iloopTrace_iloop (t : ℕ) :
    ∀ {B : WLab G s} {l i : ℕ} {p : ℕ} {st stf : RState G s p}
        {qs : List (CallEntry G s × CallOut G s)} {tr : Trace G s},
      ILoopTrace t B l i st qs stf tr → ILoop t B l st qs stf := by
  intro B l i p st stf qs tr h
  refine ILoopTrace.rec
    (motive_1 := fun B l i _p st _qs stf _tr _ => ILoop t B l st _qs stf)
    (motive_2 := fun _B _l _e _out _tr _ => True) ?exit ?step ?base ?recur h
  case exit =>
    intro _B _l _i _p _st h'
    exact ILoop.exit h'
  case step =>
    intro B l i _p _st _st' _st'' _q _qs _trStep _trChild _trRest hne hg hstep _hchild _hrest
      _ih_child ih_rest
    exact ILoop.step hne hg (istepTrace_istep t B l i hstep) ih_rest
  case base => intro _B _l _e _bout _hl _hb; trivial
  case recur => intro _B _l _e _p _fo _piv _st0 _stf _qs _trLoop _hl _hfp _hpiv _hst0 _hloop _ih; trivial

/-- Every child call of an instrumented loop sits one level below the loop. -/
theorem iloopTrace_children_l (t : ℕ) :
    ∀ {B : WLab G s} {l i : ℕ} {p : ℕ} {st stf : RState G s p}
        {qs : List (CallEntry G s × CallOut G s)} {tr : Trace G s},
      ILoopTrace t B l i st qs stf tr → ∀ q ∈ qs, q.1.l = l - 1 := by
  intro B l i p st stf qs tr h
  refine ILoopTrace.rec
    (motive_1 := fun _B l _i _p _st qs _stf _tr _ => ∀ q ∈ qs, q.1.l = l - 1)
    (motive_2 := fun _B _l _e _out _tr _ => True) ?exit ?step ?base ?recur h
  case exit =>
    intro _B _l _i _p _st _h q hq
    exact absurd hq List.not_mem_nil
  case step =>
    intro _B l _i _p _st _st' _st'' _q _qs _trStep _trChild _trRest _hne _hg hstep _hchild
      _hrest _ih_child ih_rest q' hq'
    rcases List.mem_cons.mp hq' with rfl | hq''
    · exact istepTrace_child_l t _B l _i hstep
    · exact ih_rest q' hq''
  case base => intro _B _l _e _bout _hl _hb; trivial
  case recur => intro _B _l _e _p _fo _piv _st0 _stf _qs _trLoop _hl _hfp _hpiv _hst0 _hloop _ih; trivial

/-! ## Erasure of the instrumented `Run` -/

/-- A level-0 `RunTrace` derivation is a base run: the recur case is contradictory at level 0
(`0 < e.l` with `e.l = 0`). -/
theorem runTrace_run_of_level_zero (t : ℕ) {B : WLab G s} {l : ℕ} :
    ∀ {e : CallEntry G s} {out : CallOut G s} {tr : Trace G s},
      e.l = 0 → RunTrace t B l e out tr → Run t e out := by
  intro e out tr hle h
  revert hle
  cases h with
  | base hl hb => intro _; exact Run.base hl hb
  | recur hl _hfp _hpiv _hst0 _hloop => intro h0; omega

/-- **Erasure**: dropping the trace recovers `Run`.  Every loop child carries its own `RunTrace`
derivation (`ILoopTrace.step`'s `hchild`, tied to the threaded `trChild`); a child sits at
level `l - 1` (`istepTrace_child_l`), so the children erase by strong induction on the level.
The loop is walked with the mutual recursor; the walk motive carries an *eraser callback* for
levels below the walk's own level, because the step minors are generic in `l`. -/
theorem runTrace_run (t : ℕ) {B : WLab G s} {l : ℕ} :
    ∀ {e : CallEntry G s} {out : CallOut G s} {tr : Trace G s},
      RunTrace t B l e out tr → Run t e out := by
  have key : ∀ n : ℕ, ∀ {B : WLab G s} {l : ℕ} {e : CallEntry G s} {out : CallOut G s}
      {tr : Trace G s},
      e.l = n → RunTrace t B l e out tr → Run t e out := by
    intro n
    induction n using Nat.strongRecOn with
    | ind m ih =>
        intro B l e out tr hle h
        revert hle
        cases h with
        | base hl hb => intro _; exact Run.base hl hb
        | @recur B l e p fo piv st0 stf qs trLoop hl hfp hpiv hst0 hloop =>
            intro hle
            subst hle
            refine Run.recur (p := p) (fo := fo) (piv := piv) (st0 := st0) (stf := stf)
              (qs := qs) hl hfp hpiv hst0 (iloopTrace_iloop t hloop) ?_
            intro q hq
            refine ILoopTrace.rec
              (motive_1 := fun _B l _i _p _st qs' _stf _tr _ => ∀ q' ∈ qs',
                (∀ k, k < l → ∀ {e' : CallEntry G s} {out' : CallOut G s} {tr' : Trace G s},
                  e'.l = k → RunTrace t _B l e' out' tr' → Run t e' out') → Run t q'.1 q'.2)
              (motive_2 := fun _B _l _e' _out' _tr' _ => True) ?exit ?step ?base ?recur hloop
                q hq (fun k hk e' out' tr' he' hrun => (ih k hk) he' hrun)
            case exit =>
              intro _B l _i _p _st _h q' hq' _
              exact absurd hq' List.not_mem_nil
            case step =>
              intro B l i _p _st _st' _st'' _q _qs _trStep _trChild _trRest _hne _hg hstep hchild
                _hrest _ih_child ih_rest q' hq' H
              rcases List.mem_cons.mp hq' with rfl | hq''
              · have hql := istepTrace_child_l t B l i hstep
                rcases Nat.eq_zero_or_pos l with h0 | hp
                · have hql0 : q'.1.l = 0 := by omega
                  exact runTrace_run_of_level_zero t hql0 hchild
                · exact H (l - 1) (by omega) hql hchild
              · exact ih_rest q' hq'' H
            case base => intro _B _l _e' _bout _hl _hb; trivial
            case recur =>
              intro _B _l _e' _p _fo _piv _st0 _stf _qs _trLoop _hl _hfp _hpiv _hst0 _hloop _ih
              trivial
  intro e out tr h
  exact key e.l rfl h

end DMSY
end Frontier

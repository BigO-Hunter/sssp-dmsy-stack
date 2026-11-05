import A4.IStepTrace

set_option linter.unnecessarySimpa false

/-!
# Frontier.DMSY.WriterTrace — the per-vertex last-writer layer

Work package **A4 (BMSSP recursion)**, the precise missing object named by `IStepTrace`: a
per-vertex **last-writer witness**.  `IStepTrace.istepTrace_mints_label` pins `m.val = d3 (sel j)`
but does not say *which* acceptance produced `d3 (sel j)`.  This file answers that:

* `WriterEvent` — an indexed acceptance `(idx, RelaxStep)`, the operational unit of a write.
* `Origin` — the three ways a label can arrive without being written by a relaxation in the sweep
  at hand: initialization, a child return, or an earlier loop iteration.
* `LastWriter G s x val` — a certificate that `val` at `x` was last written by a `RelaxStep`
  (its `relax` case), or is an origin label (its `origin` case).  **Ties stay valid writer
  events**: `relaxGate` accepts `cand ≤ d (G.dst e)`, so a tie re-acceptance emits a `RelaxStep`
  whose `vv` equals the unchanged label.

The operational content is the pair of sweep lemmas: `sweepEvtsT_unchanged` (no emitted step
targets `x` ⟹ the label is inherited) and `sweepEvtsT_inherited_or_written` (else the label is
some emitted step's `vv`).  Combined with `istepTrace_mints_label` they give
`istepTrace_mint_writer`: a mint's value is either written by the current sweep's trace (a
`relax` certificate) or inherited from the child return (`Origin.child`).

This is **operational evidence extraction**, not a ground conclusion: `Origin.child`/`.iter`
name *where the label came from*, not that the walk reaches a settled or seed vertex — that
classification is the separate ground-split theorem, out of scope here.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Writer events, origins, and certificates -/

/-- An indexed acceptance/writer event: the `idx`-th accepted relaxation. -/
structure WriterEvent (G : Graph) (s : Fin G.n) where
  idx : ℕ
  step : RelaxStep G s

/-- The origin of a label not written by any relaxation in the sweep at hand. -/
inductive Origin (G : Graph) (s : Fin G.n) where
  | init
  | child (i : ℕ)
  | iter (i : ℕ)
  deriving DecidableEq

/-- A last-writer certificate for the label `val` at vertex `x`: written by relaxation `r` (ties
included, since `relaxGate` re-accepts via `≤`), or an origin label. -/
inductive LastWriter (G : Graph) (s : Fin G.n) : Fin G.n → WLab G s → Prop where
  | relax (i : ℕ) (r : RelaxStep G s) : LastWriter G s r.v r.vv
  | origin (o : Origin G s) (x : Fin G.n) (val : WLab G s) : LastWriter G s x val

/-! ## Single-edge writer facts -/

/-- A single gated relaxation either leaves `x` untouched or writes it (the emitted step's `vv` is
the written label). -/
theorem relaxGateT_inherited_or_written (B lo : WLab G s) (d : Labels G s) (D : DS G s)
    (e : Fin G.m) :
    ∀ x, (relaxGateT B lo d D e).1 x = d x ∨
      ∃ r ∈ (relaxGateT B lo d D e).2.2, r.v = x ∧ r.vv = (relaxGateT B lo d D e).1 x := by
  intro x
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · by_cases hxd : x = G.dst e
    · right
      refine ⟨⟨e, G.src e, G.dst e, d (G.src e), ext (d (G.src e)) e, rfl, rfl,
          ne_top_of_ext_lt_top (lt_of_lt_of_le hc.2.1 le_top), rfl⟩, by simp [relaxGateT, hc], ?_, ?_⟩
      · simpa [hxd]
      · simpa [relaxGateT, hc, hxd]
    · left
      simpa [relaxGateT, hc, hxd]
  · left
    simpa [relaxGateT, hc]

/-- A single gated relaxation that does not target `x` leaves its label unchanged. -/
theorem relaxGateT_unchanged (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) :
    ∀ x, (∀ r ∈ (relaxGateT B lo d D e).2.2, r.v ≠ x) → (relaxGateT B lo d D e).1 x = d x := by
  intro x hx
  rcases relaxGateT_inherited_or_written B lo d D e x with h | h
  · exact h
  · obtain ⟨r, hr, hrv, hvv⟩ := h
    exact absurd hrv (hx r hr)

/-! ## The sweep lemmas (the operational core) -/

/-- A vertex sweep leaves a label unchanged when no accepted step targets it. -/
theorem sweepGateT_unchanged (B lo : WLab G s) (u : Fin G.n) :
    ∀ es d D x, (∀ r ∈ (sweepGateT B lo u es d D).2.2, r.v ≠ x) →
      (sweepGateT B lo u es d D).1 x = d x := by
  intro es
  induction es with
  | nil => intro d D x hx; rfl
  | cons e es ih =>
      intro d D x hx
      simp only [sweepGateT]
      let r := relaxGateT B lo d D e
      have hxr : ∀ r' ∈ (if G.src e = u then r.2.2 else []), r'.v ≠ x := by
        intro r' hr'
        exact hx r' (List.mem_append.mpr (Or.inl hr'))
      have hxrest : ∀ r' ∈ (sweepGateT B lo u es (if G.src e = u then r.1 else d)
          (if G.src e = u then r.2.1 else D)).2.2, r'.v ≠ x := by
        intro r' hr'
        exact hx r' (List.mem_append.mpr (Or.inr hr'))
      have hrest := ih (if G.src e = u then r.1 else d) (if G.src e = u then r.2.1 else D)
        x hxrest
      -- hrest : (sweepGateT ... es ...).1 x = (if G.src e = u then r.1 else d) x
      by_cases hsrc : G.src e = u
      · simp [hsrc] at hrest ⊢
        -- hrest : (sweepGateT ...).1 x = r.1 x ; goal : (sweepGateT ...).1 x = d x
        have hu := relaxGateT_unchanged B lo d D e x (by
          intro r' hr'
          exact hxr r' (by simpa [hsrc] using hr'))
        rw [hrest, hu]
      · simp [hsrc] at hrest ⊢
        exact hrest

/-- A vertex sweep's label at `x` is either inherited or written by an accepted step. -/
theorem sweepGateT_inherited_or_written (B lo : WLab G s) (u : Fin G.n) :
    ∀ es d D x, (sweepGateT B lo u es d D).1 x = d x ∨
      ∃ r ∈ (sweepGateT B lo u es d D).2.2, r.v = x ∧ r.vv = (sweepGateT B lo u es d D).1 x := by
  intro es
  induction es with
  | nil => intro d D x; left; rfl
  | cons e es ih =>
      intro d D x
      by_cases hsrc : G.src e = u
      · -- e is out of u, processed first
        rcases ih (relaxGateT B lo d D e).1 (relaxGateT B lo d D e).2.1 x with h | h
        · -- inherited through the rest of the edges
          rcases relaxGateT_inherited_or_written B lo d D e x with he | he
          · left
            simpa [sweepGateT, hsrc, h, he]
          · right
            obtain ⟨r', hr', hx, hvv⟩ := he
            refine ⟨r', ?_, hx, ?_⟩
            · simpa [sweepGateT, hsrc] using (List.mem_append.mpr (Or.inl hr'))
            · simpa [sweepGateT, hsrc, h, hvv]
        · -- written in the rest of the edges
          right
          obtain ⟨r', hr', hx, hvv⟩ := h
          refine ⟨r', ?_, hx, ?_⟩
          · simpa [sweepGateT, hsrc] using (List.mem_append.mpr (Or.inr hr'))
          · simpa [sweepGateT, hsrc, hvv]
      · -- e is not out of u, skipped
        simpa [sweepGateT, hsrc] using ih d D x

/-- The event-list sweep: unchanged labels. -/
theorem sweepEvtsT_unchanged (B lo : WLab G s) :
    ∀ evts d D x, (∀ r ∈ (sweepEvtsT B lo evts d D).2.2, r.v ≠ x) →
      (sweepEvtsT B lo evts d D).1 x = d x := by
  intro evts
  induction evts with
  | nil => intro d D x hx; rfl
  | cons ev evts ih =>
      intro d D x hx
      simp only [sweepEvtsT]
      let a := sweepGateT B lo ev.v (List.finRange G.m) d D
      have hxa : ∀ r ∈ a.2.2, r.v ≠ x := by
        intro r hr
        exact hx r (List.mem_append.mpr (Or.inl hr))
      have hxrest : ∀ r ∈ (sweepEvtsT B lo evts a.1 a.2.1).2.2, r.v ≠ x := by
        intro r hr
        exact hx r (List.mem_append.mpr (Or.inr hr))
      have hrest := ih a.1 a.2.1 x hxrest
      have ha := sweepGateT_unchanged B lo ev.v (List.finRange G.m) d D x hxa
      rw [hrest, ha]

/-- The event-list sweep: a label is inherited or written by an accepted step. -/
theorem sweepEvtsT_inherited_or_written (B lo : WLab G s) :
    ∀ evts d D x, (sweepEvtsT B lo evts d D).1 x = d x ∨
      ∃ r ∈ (sweepEvtsT B lo evts d D).2.2, r.v = x ∧ r.vv = (sweepEvtsT B lo evts d D).1 x := by
  intro evts
  induction evts with
  | nil => intro d D x; left; rfl
  | cons ev evts ih =>
      intro d D x
      rcases ih (sweepGateT B lo ev.v (List.finRange G.m) d D).1
          (sweepGateT B lo ev.v (List.finRange G.m) d D).2.1 x with h | h
      · -- inherited through the rest
        rcases sweepGateT_inherited_or_written B lo ev.v (List.finRange G.m) d D x with ha | ha
        · left; simpa [sweepEvtsT, ha, h]
        · right
          obtain ⟨r', hr', hx, hvv⟩ := ha
          refine ⟨r', List.mem_append.mpr (Or.inl hr'), hx, ?_⟩
          simpa [sweepEvtsT, h, hvv]
      · -- written in the rest
        right
        obtain ⟨r', hr', hx, hvv⟩ := h
        refine ⟨r', List.mem_append.mpr (Or.inr hr'), hx, ?_⟩
        simpa [sweepEvtsT, hvv]

/-! ## The mint connection -/

/-- A mint's value is either written by the current sweep's trace (`LastWriter.relax`) or
inherited from the child return (`Origin.child`).  This uses `istepTrace_mints_label`
(`m.val = d3 (sel j)`) and the sweep lemmas; it does **not** classify the child label as settled
or seed — that is the separate ground-split step. -/
theorem istepTrace_mint_writer (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) :
    ∀ m ∈ st'.mints, (∃ r ∈ trStep, r.v = m.x ∧ r.vv = m.val) ∨ m.val = fo'.d' m.x := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, _hpull, _hc, _hmerge, hsweep, _hresid, _hJ,
    _hsel, hst'⟩ := h
  subst hst'
  intro m hm
  have hml : d3 m.x = m.val := by
    obtain ⟨j, _hj, hjm⟩ := List.mem_map.mp hm
    rw [← hjm]
  have h3 : d3 = (sweepEvtsT B Bi fo'.evts fo'.d' D2).1 := congrArg Prod.fst hsweep
  have htr : trStep = (sweepEvtsT B Bi fo'.evts fo'.d' D2).2.2 :=
    congrArg (fun x : Labels G s × DS G s × List (RelaxStep G s) => x.2.2) hsweep
  have hsw := sweepEvtsT_inherited_or_written B Bi fo'.evts fo'.d' D2 m.x
  rw [← h3, ← htr] at hsw
  rcases hsw with hsl | hsr
  · right
    rw [← hml, hsl]
  · left
    obtain ⟨r, hr, hx, hvv⟩ := hsr
    refine ⟨r, hr, hx, hvv.trans hml⟩

end DMSY
end Frontier

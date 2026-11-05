import A4.WriterTrace

set_option linter.unnecessarySimpa false

/-!
# Frontier.DMSY.LastWriter — `LastTarget` and last-writer correctness

Work package **A4 (BMSSP recursion)**, the refinement named at the end of `WriterTrace`: the
`relax` certificate there names *a* writer, but the recursive provenance needs the **last** writer.
This file supplies it.

* `LastTarget x tr r` — `r` is the last step of `tr` (reading left-to-right) that targets `x`,
  defined recursively: the head is last when no later step targets `x`, else recurse into the tail.
* `lastTarget_mem` / `lastTarget_exists` / `lastTarget_unique` — every written vertex has a last
  target, unique as an event.
* `relaxGateT_emit_val` / `relaxGateT_lastTarget_val` / `sweepGateT_lastTarget_val` /
  `sweepEvtsT_lastTarget_val` — the last target's written value equals the sweep's final label at
  that vertex (ties included: a tie re-acceptance still has `r.vv = d' x = d x`).
* `istepTrace_mint_lastTarget` — the mint value is either the last target's `vv` (written by this
  sweep) or inherited from the child return.
* `OriginCert` — the exact typed evidence the `child`/`iter` origin cases need.  **Constructed**
  in `A4.OriginTrace`: the recursion now carries child `RunTrace` derivations
  (`ILoopTrace.step`'s `hchild`, tied to the threaded `trChild`), and `OriginCert.child` is
  built from the step's own data; `OriginCert.iter` refines it from the prior iteration state
  under the child-inheritance premise (derived there for base-level children via
  `BaseInherited`).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Last target -/

/-- `r` is the last step of `tr` (reading left-to-right) that targets `x`. -/
inductive LastTarget (x : Fin G.n) : Trace G s → RelaxStep G s → Prop where
  | here (r : RelaxStep G s) (rest : Trace G s) (hx : r.v = x)
      (hno : ∀ r' ∈ rest, r'.v ≠ x) : LastTarget x (r :: rest) r
  | later (r : RelaxStep G s) (rest : Trace G s) (r' : RelaxStep G s)
      (hl : LastTarget x rest r') : LastTarget x (r :: rest) r'

namespace LastTarget

/-- A last target is in the trace and targets `x`. -/
theorem mem {x : Fin G.n} {tr : Trace G s} {r : RelaxStep G s} (h : LastTarget x tr r) :
    r ∈ tr ∧ r.v = x := by
  induction h with
  | here r rest hx _hno => exact ⟨List.mem_cons_self, hx⟩
  | later r rest r' _hl ih => exact ⟨List.mem_cons_of_mem r ih.1, ih.2⟩

end LastTarget

/-- Every vertex that some step targets has a last target. -/
theorem lastTarget_exists {x : Fin G.n} : ∀ tr : Trace G s,
    (∃ r ∈ tr, r.v = x) → ∃ r, LastTarget x tr r := by
  intro tr
  induction tr with
  | nil => intro h; rcases h with ⟨r, hr, _⟩; exact absurd hr List.not_mem_nil
  | cons r rest ih =>
      intro h
      by_cases hrest : ∃ r' ∈ rest, r'.v = x
      · rcases ih hrest with ⟨r', hl⟩
        exact ⟨r', LastTarget.later r rest r' hl⟩
      · refine ⟨r, LastTarget.here r rest ?_ ?_⟩
        · rcases h with ⟨r'', hr'', hx''⟩
          rcases List.mem_cons.mp hr'' with hr | hr
          · rw [hr] at hx''; exact hx''
          · exact (hrest ⟨r'', hr, hx''⟩).elim
        · intro r' hr' hx'; exact hrest ⟨r', hr', hx'⟩

/-- A last target is unique as an event. -/
theorem lastTarget_unique {x : Fin G.n} {tr : Trace G s} {r₁ r₂ : RelaxStep G s}
    (h₁ : LastTarget x tr r₁) (h₂ : LastTarget x tr r₂) : r₁ = r₂ := by
  induction h₁ generalizing r₂ with
  | here r rest hx hno =>
      cases h₂ with
      | here _ rest₂ hx₂ hno₂ => rfl
      | later _ rest₂ _ hl₂ =>
          exact (hno r₂ (LastTarget.mem hl₂).1 (LastTarget.mem hl₂).2).elim
  | later r rest r' hl ih =>
      cases h₂ with
      | here _ rest₂ hx₂ hno₂ =>
          exact (hno₂ r' (LastTarget.mem hl).1 (LastTarget.mem hl).2).elim
      | later _ rest₂ _ hl₂ => exact ih hl₂

/-- `r` is the last target in `tr₁ ++ tr₂` iff it is last in `tr₂`, or last in `tr₁` with no
target of `x` in `tr₂`. -/
theorem lastTarget_append {x : Fin G.n} {tr₁ tr₂ : Trace G s} {r : RelaxStep G s} :
    LastTarget x (tr₁ ++ tr₂) r →
      LastTarget x tr₂ r ∨ (LastTarget x tr₁ r ∧ ∀ r' ∈ tr₂, r'.v ≠ x) := by
  intro h
  induction tr₁ generalizing r with
  | nil => left; exact h
  | cons r₁ rest₁ ih =>
      cases h with
      | here _ rest hx hno =>
          right
          refine ⟨LastTarget.here r₁ rest₁ hx ?_, ?_⟩
          · intro r'' hr'' hx''; exact hno r'' (List.mem_append.mpr (Or.inl hr'')) hx''
          · intro r'' hr'' hx''; exact hno r'' (List.mem_append.mpr (Or.inr hr'')) hx''
      | later _ rest _ hrest =>
          rcases ih hrest with htr₂ | ⟨htr₁, hno⟩
          · left; exact htr₂
          · right; exact ⟨LastTarget.later r₁ rest₁ r htr₁, hno⟩

/-! ## Single-edge write and last-writer correctness -/

/-- An emitted single-edge step wrote exactly the label at its target. -/
theorem relaxGateT_emit_val (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) :
    ∀ r ∈ (relaxGateT B lo d D e).2.2, r.vv = (relaxGateT B lo d D e).1 r.v := by
  intro r hr
  have hm := relaxGateT_mem B lo d D e hr
  have hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e) := by
    rw [← hm.2.2.1]
    exact ⟨hm.2.2.2.1, hm.2.2.2.2.1, hm.2.2.2.2.2⟩
  have hrv : r.v = G.dst e := by rw [r.dst_eq.symm, hm.1]
  have hval : (relaxGateT B lo d D e).1 (G.dst e) = r.vv := by
    simp [relaxGateT, hc, hm.2.2.1]
  rw [hrv, hval.symm]

/-- The last target of a single edge's trace writes the final label at `x`. -/
theorem relaxGateT_lastTarget_val (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) :
    ∀ x r, LastTarget x (relaxGateT B lo d D e).2.2 r →
      r.vv = (relaxGateT B lo d D e).1 x := by
  intro x r h
  have hx : r.v = x := (LastTarget.mem h).2
  rw [← hx]
  exact relaxGateT_emit_val B lo d D e r (LastTarget.mem h).1

/-- A vertex sweep: the last target writes the final label. -/
theorem sweepGateT_lastTarget_val (B lo : WLab G s) (u : Fin G.n) :
    ∀ es d D x r, LastTarget x (sweepGateT B lo u es d D).2.2 r →
      r.vv = (sweepGateT B lo u es d D).1 x := by
  intro es
  induction es with
  | nil => intro d D x r h; cases h
  | cons e es ih =>
      intro d D x r h
      by_cases hsrc : G.src e = u
      · have h' : LastTarget x ((relaxGateT B lo d D e).2.2 ++
            (sweepGateT B lo u es (relaxGateT B lo d D e).1
              (relaxGateT B lo d D e).2.1).2.2) r := by
          simpa [sweepGateT, hsrc] using h
        rcases lastTarget_append h' with htail | ⟨hhead, hno⟩
        · have hv := ih (relaxGateT B lo d D e).1 (relaxGateT B lo d D e).2.1 x r htail
          simpa [sweepGateT, hsrc, hv]
        · have hv := relaxGateT_lastTarget_val B lo d D e x r hhead
          have hu := sweepGateT_unchanged B lo u es (relaxGateT B lo d D e).1
            (relaxGateT B lo d D e).2.1 x hno
          simpa [sweepGateT, hsrc, hv, hu]
      · have h' : LastTarget x (sweepGateT B lo u es d D).2.2 r := by
          simpa [sweepGateT, hsrc] using h
        have hv := ih d D x r h'
        simpa [sweepGateT, hsrc, hv]

/-- The event-list sweep: the last target writes the final label. -/
theorem sweepEvtsT_lastTarget_val (B lo : WLab G s) :
    ∀ evts d D x r, LastTarget x (sweepEvtsT B lo evts d D).2.2 r →
      r.vv = (sweepEvtsT B lo evts d D).1 x := by
  intro evts
  induction evts with
  | nil => intro d D x r h; cases h
  | cons ev evts ih =>
      intro d D x r h
      have h' : LastTarget x ((sweepGateT B lo ev.v (List.finRange G.m) d D).2.2 ++
            (sweepEvtsT B lo evts (sweepGateT B lo ev.v (List.finRange G.m) d D).1
              (sweepGateT B lo ev.v (List.finRange G.m) d D).2.1).2.2) r := by
        simpa [sweepEvtsT] using h
      rcases lastTarget_append h' with htail | ⟨hhead, hno⟩
      · have hv := ih (sweepGateT B lo ev.v (List.finRange G.m) d D).1
          (sweepGateT B lo ev.v (List.finRange G.m) d D).2.1 x r htail
        simpa [sweepEvtsT, hv]
      · have hv := sweepGateT_lastTarget_val B lo ev.v (List.finRange G.m) d D x r hhead
        have hu := sweepEvtsT_unchanged B lo evts (sweepGateT B lo ev.v (List.finRange G.m) d D).1
          (sweepGateT B lo ev.v (List.finRange G.m) d D).2.1 x hno
        simpa [sweepEvtsT, hv, hu]

/-! ## Strengthened mint connection -/

/-- A mint's value is either the last target's `vv` in `trStep` (written by this sweep) or the
child return label. -/
theorem istepTrace_mint_lastTarget (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) :
    ∀ m ∈ st'.mints, (∃ r, LastTarget m.x trStep r ∧ r.vv = m.val) ∨ m.val = fo'.d' m.x := by
  intro m hm
  have hw_or := istepTrace_mint_writer t B l i h m hm
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, _hpull, _hc, _hmerge, hsweep, _hresid, _hJ,
    _hsel, hst'⟩ := h
  subst hst'
  have hml : d3 m.x = m.val := by
    obtain ⟨j, _hj, hjm⟩ := List.mem_map.mp hm
    rw [← hjm]
  have h3 : d3 = (sweepEvtsT B Bi fo'.evts fo'.d' D2).1 := congrArg Prod.fst hsweep
  have htr : trStep = (sweepEvtsT B Bi fo'.evts fo'.d' D2).2.2 :=
    congrArg (fun x : Labels G s × DS G s × List (RelaxStep G s) => x.2.2) hsweep
  rcases hw_or with hw | hc
  · left
    obtain ⟨r, hr, hx, _hvv⟩ := hw
    obtain ⟨r', hlt⟩ := lastTarget_exists trStep ⟨r, hr, hx⟩
    refine ⟨r', hlt, ?_⟩
    have hlt' : LastTarget m.x (sweepEvtsT B Bi fo'.evts fo'.d' D2).2.2 r' := by
      rwa [htr] at hlt
    have hd3 : r'.vv = d3 m.x := by
      rw [h3]
      exact sweepEvtsT_lastTarget_val B Bi fo'.evts fo'.d' D2 m.x r' hlt'
    exact hd3.trans hml
  · right; exact hc

/-! ## Typed origin certificate -/

/-- The exact typed evidence an origin case needs.  `child i` carries the child return `co` with
`val = co.d' x` (the child's index `i` in the parent loop and its return are `IStepTrace`/
`ILoopTrace` data); `iter i` the prior labels `d` with `val = d x`; `init` the initialization
label.  Constructed in `A4.OriginTrace`: `child` unconditionally from the step's own data,
`iter` under the child-inheritance premise (derived for base-level children there).  This
certificate names *where the label came from*, not that the walk reaches a settled or seed
vertex — the ground split is a separate, still-open theorem. -/
inductive OriginCert (G : Graph) (s : Fin G.n) : Fin G.n → WLab G s → Prop where
  | init {x : Fin G.n} {val : WLab G s} (h : val = initLabels G s x) : OriginCert G s x val
  | child {x : Fin G.n} {val : WLab G s} (i : ℕ) (co : CallOut G s) (h : val = co.d' x) :
      OriginCert G s x val
  | iter {x : Fin G.n} {val : WLab G s} (i : ℕ) (d : Labels G s) (h : val = d x) :
      OriginCert G s x val

end DMSY
end Frontier

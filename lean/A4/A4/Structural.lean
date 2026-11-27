import A4.Semantics

/-!
# Frontier.DMSY.Structural — structural facts about `Run` (A4)

Work package **A4 (BMSSP recursion)**.  The structural lemmas every later clause rides on:
label monotonicity of the mechanical layers, the bound law `B' ≤ B`, entry honesty (I3) at
returns, the final-iteration mint bookkeeping behind the Q12 carve-out, and full-execution
immunity.  These are the *local* half of CORRECTED_PROOF §3 — everything except the audit's
joint first-violation induction (CORRECTED_PROOF §8.1: Lemma W/V/Rep, the W′ drop lemma and
the refusal-floor chain), whose pieces are isolated as named residual obligations here and in
`A4.Transitive` / `A4.Main`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Labels only decrease through the mechanical layers -/

/-- `relaxGate` never raises a label. -/
theorem relaxGate_le (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) (v : Fin G.n) :
    (relaxGate B lo d D e).1 v ≤ d v := by
  unfold relaxGate
  by_cases h : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos h]
    show Function.update d (G.dst e) (ext (d (G.src e)) e) v ≤ d v
    by_cases hv : v = G.dst e
    · subst hv
      simp [Function.update]
      exact h.2.2
    · rw [Function.update_of_ne hv]
  · rw [if_neg h]

/-- `sweepGate` never raises a label. -/
theorem sweepGate_le (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m))
    (d : Labels G s) (D : DS G s) (v : Fin G.n) :
    (sweepGate B lo u es d D).1 v ≤ d v := by
  induction es generalizing d D with
  | nil => exact le_rfl
  | cons e es ih =>
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact (ih _ _).trans (relaxGate_le B lo d D e v)
    · rw [if_neg hs, if_neg hs]; exact ih d D

/-- `sweepEvts` never raises a label. -/
theorem sweepEvts_le (B lo : WLab G s) (evts : List (SettlementEvent G))
    (d : Labels G s) (D : DS G s) (v : Fin G.n) :
    (sweepEvts B lo evts d D).1 v ≤ d v := by
  induction evts generalizing d D with
  | nil => exact le_rfl
  | cons ev evts ih =>
    unfold sweepEvts
    exact (ih _ _).trans (sweepGate_le B lo ev.v (List.finRange G.m) d D v)

/-- `seedIns` never raises a label (BM.25 inserts only). -/
theorem seedIns_le (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s)
    (v : Fin G.n) : (seedIns bp B S d D).1 v ≤ d v := by
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => exact le_rfl
  | cons x xs ih =>
    rw [List.foldl_cons]
    by_cases h : bp ≤ d x ∧ d x < B
    · rw [if_pos h]; exact ih _ _
    · rw [if_neg h]; exact ih d D

/-- The tail never raises a label. -/
theorem tail_le (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (v : Fin G.n) : (tail B S W st).d v ≤ st.d v := by
  unfold tail
  exact (sweepEvts_le _ _ _ _ _ _).trans (seedIns_le _ _ _ _ _ _)

/-- The `l > 0` spine lowers labels within one iteration, given the child's own monotonicity
(`fo'.d' ≤ st.d` — a child run's I2). -/
theorem istep_le_of_child (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hchild : ∀ v, fo'.d' v ≤ st.d v) (v : Fin G.n) : st'.d v ≤ st.d v := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel, hst'⟩ := h
  subst hst'
  show d3 v ≤ st.d v
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := by
    rw [← hsweep]
  rw [hd3]
  exact (sweepEvts_le _ _ _ _ _ _).trans (hchild v)

/-- One Algorithm-4 sweep never raises a label (hypothesis-free; `A1.Sweep.relaxEdge_le`
composes along the edge list). -/
theorem a1_sweep_le (B : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (v : Fin G.n) : (sweep B u es d D).1 v ≤ d v := by
  induction es generalizing d D with
  | nil => exact le_rfl
  | cons e es ih =>
    unfold sweep
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact (ih _ _).trans (relaxEdge_le B d D e v)
    · rw [if_neg hs, if_neg hs]
      exact ih d D

/-- One Algorithm-4 iteration never raises a label. -/
theorem a1_iter_le (B : WLab G s) (u : Fin G.n) (x : WLab G s) (st : BState G s) (v : Fin G.n) :
    (iter B u x st).d v ≤ st.d v :=
  a1_sweep_le B u (List.finRange G.m) st.d (DS.deleteSet st.D {u}) v

/-- A1's loop never raises a label (`A1.BaseInv.le`). -/
theorem a1_loop_le (t : ℕ) (B : WLab G s) :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' → ∀ v, st'.d v ≤ st.d v := by
  intro c st st' h
  induction h with
  | exit h => exact fun v => le_rfl
  | pull u lam x hne hg hu hxgt hxle hxrest hxeq hrest ih =>
    intro v
    exact (ih v).trans (a1_iter_le B u x _ v)

/-- A loop's labels never rise, given each child's monotonicity.  (Statement kept; the proof
chains `istep_le_of_child` over the loop and the child-entry equation `q.1.d = st.d`.) -/
theorem iloop_le (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, ∀ v, q.2.d' v ≤ q.1.d v) → ∀ v, stf.d v ≤ st.d v := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ v => le_rfl
  | step hne hg hstep hrest ih =>
    intro hchild v
    refine (ih (fun q hq => hchild q (List.mem_cons_of_mem _ hq)) v).trans
      (istep_le_of_child t B l hstep (fun w => ?_) v)
    have h1 := hchild _ List.mem_cons_self w
    obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
      hst'⟩ := hstep
    rw [hc] at h1
    exact h1

/-- Labels only decrease along a run (I2). -/
theorem run_le (t : ℕ) : ∀ {e : CallEntry G s} {out : CallOut G s},
    Run t e out → ∀ v, out.d' v ≤ e.d v := by
  intro e out h
  induction h with
  | base hl hb =>
    obtain ⟨c, st, hloop, hr⟩ := hb
    subst hr
    intro v
    exact a1_loop_le t _ hloop v
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro v
    refine (tail_le _ _ _ _ v).trans ?_
    refine (iloop_le t _ _ hloop (fun q hq => ih q hq) v).trans ?_
    rw [hst0]
    exact (fpRun_contract _ _ hfp).1.le v

/-! ## Entry honesty through the mechanical layers

`lam = d y` at insert time drifts to `d y ≤ lam` as labels lower around a kept-min entry (a
child can lower a label whose old entry survives a merge); honesty is the invariant preserved by
every layer, and it is what the mint-exactness bookkeeping (`premInD_of_run`) consumes. -/

/-- An accepted `insert`+`update` pair preserves entry honesty: the head's stored value becomes
the new label (`cand ≤ d z` forces the keep-min to pick `cand`), other keys are untouched. -/
theorem insert_update_honest (d : Labels G s) (D : DS G s) (z : Fin G.n) (cand : WLab G s)
    (hd : ∀ y val, D y = some val → d y ≤ val) (hle : cand ≤ d z) :
    ∀ y val, (DS.insert D z cand) y = some val → (Function.update d z cand) y ≤ val := by
  intro y val hy
  by_cases hyz : y = z
  · subst hyz
    rw [DS.insert_self] at hy
    rw [Function.update_self]
    cases hD : D y with
    | none =>
      rw [hD, DS.mergeVal_none_left] at hy
      exact le_of_eq (Option.some.inj hy)
    | some μ =>
      rw [hD, DS.mergeVal_some] at hy
      have hμ : cand ≤ μ := hle.trans (hd y μ hD)
      rw [min_eq_right hμ] at hy
      exact le_of_eq (Option.some.inj hy)
  · rw [DS.insert_of_ne D z cand hyz] at hy
    rw [Function.update_of_ne hyz]
    exact hd y val hy

/-- An insert at the *current* label preserves honesty without touching labels (`seedIns`, the
mint fold). -/
theorem insert_label_honest (d : Labels G s) (D : DS G s) (x : Fin G.n)
    (hd : ∀ y val, D y = some val → d y ≤ val) :
    ∀ y val, (DS.insert D x (d x)) y = some val → d y ≤ val := by
  intro y val hy
  by_cases hyx : y = x
  · subst hyx
    rw [DS.insert_self] at hy
    cases hD : D y with
    | none =>
      rw [hD, DS.mergeVal_none_left] at hy
      exact le_of_eq (Option.some.inj hy)
    | some μ =>
      rw [hD, DS.mergeVal_some] at hy
      rw [min_eq_right (hd y μ hD)] at hy
      exact le_of_eq (Option.some.inj hy)
  · rw [DS.insert_of_ne D x (d x) hyx] at hy
    exact hd y val hy

/-- `relaxGate` preserves entry honesty (E2 gate; the accept branch is `insert_update_honest`). -/
theorem relaxGate_honest (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (hd : ∀ y val, D y = some val → d y ≤ val) :
    ∀ y val, (relaxGate B lo d D e).2 y = some val → (relaxGate B lo d D e).1 y ≤ val := by
  intro y val
  unfold relaxGate
  by_cases h : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos h]
    exact insert_update_honest d D (G.dst e) (ext (d (G.src e)) e) hd h.2.2 y val
  · rw [if_neg h]
    exact hd y val

/-- `sweepGate` preserves entry honesty. -/
theorem sweepGate_honest (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (hd : ∀ y val, D y = some val → d y ≤ val) :
    ∀ y val, (sweepGate B lo u es d D).2 y = some val → (sweepGate B lo u es d D).1 y ≤ val := by
  induction es generalizing d D with
  | nil => exact hd
  | cons e es ih =>
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (relaxGate_honest B lo d D e hd)
    · rw [if_neg hs, if_neg hs]
      exact ih d D hd

/-- `sweepEvts` preserves entry honesty. -/
theorem sweepEvts_honest (B lo : WLab G s) (evts : List (SettlementEvent G)) (d : Labels G s)
    (D : DS G s) (hd : ∀ y val, D y = some val → d y ≤ val) :
    ∀ y val, (sweepEvts B lo evts d D).2 y = some val → (sweepEvts B lo evts d D).1 y ≤ val := by
  induction evts generalizing d D with
  | nil => exact hd
  | cons ev evts ih =>
    unfold sweepEvts
    exact ih _ _ (sweepGate_honest B lo ev.v (List.finRange G.m) d D hd)

/-- `seedIns` preserves entry honesty (labels untouched; inserts at the current label). -/
theorem seedIns_honest (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s)
    (hd : ∀ y val, D y = some val → d y ≤ val) :
    ∀ y val, (seedIns bp B S d D).2 y = some val → (seedIns bp B S d D).1 y ≤ val := by
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => exact hd
  | cons x xs ih =>
    rw [List.foldl_cons]
    by_cases hg : bp ≤ d x ∧ d x < B
    · rw [if_pos hg]
      refine ih d (DS.insert D x (d x)) ?_
      exact insert_label_honest d D x hd
    · rw [if_neg hg]
      exact ih d D hd

/-- `DS.merge` preserves entry honesty (keep-min of two honest stores at one label function). -/
theorem merge_honest (d : Labels G s) (D₁ D₂ : DS G s)
    (h₁ : ∀ y val, D₁ y = some val → d y ≤ val) (h₂ : ∀ y val, D₂ y = some val → d y ≤ val) :
    ∀ y val, (DS.merge D₁ D₂) y = some val → d y ≤ val := by
  intro y val hy
  rw [DS.merge_eq] at hy
  cases hd₁ : D₁ y with
  | none =>
    cases hd₂ : D₂ y with
    | none => rw [hd₁, hd₂, DS.mergeVal_none_left] at hy; exact absurd hy.symm (Option.some_ne_none val)
    | some ν =>
      rw [hd₁, hd₂, DS.mergeVal_none_left] at hy
      rw [← Option.some.inj hy]
      exact h₂ y ν hd₂
  | some μ =>
    cases hd₂ : D₂ y with
    | none =>
      rw [hd₁, hd₂, DS.mergeVal_none_right] at hy
      rw [← Option.some.inj hy]
      exact h₁ y μ hd₁
    | some ν =>
      rw [hd₁, hd₂, DS.mergeVal_some] at hy
      rw [← Option.some.inj hy]
      exact le_min (h₁ y μ hd₁) (h₂ y ν hd₂)

/-- The mint fold preserves entry honesty (each insert stores the current label of its key). -/
theorem fold_insert_honest {ι : Type} (js : List ι) (f : ι → Fin G.n) (d : Labels G s)
    (D0 : DS G s) (hd : ∀ y val, D0 y = some val → d y ≤ val) :
    ∀ y val, (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D0) y = some val → d y ≤ val := by
  induction js generalizing D0 with
  | nil => exact hd
  | cons j0 js ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    exact insert_label_honest d D0 (f j0) hd

theorem a1_relaxEdge_honest (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (hd : ∀ y val, D y = some val → d y ≤ val) :
    ∀ y val, (relaxEdge B d D e).2 y = some val → (relaxEdge B d D e).1 y ≤ val := by
  intro y val
  unfold relaxEdge
  by_cases h : ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B
  · rw [if_pos h]
    exact insert_update_honest d D (G.dst e) (ext (d (G.src e)) e) hd h.1 y val
  · rw [if_neg h]
    exact hd y val

/-- A1's sweep preserves entry honesty. -/
theorem a1_sweep_honest (B : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (hd : ∀ y val, D y = some val → d y ≤ val) :
    ∀ y val, (sweep B u es d D).2 y = some val → (sweep B u es d D).1 y ≤ val := by
  induction es generalizing d D with
  | nil => exact hd
  | cons e es ih =>
    unfold sweep
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (a1_relaxEdge_honest B d D e hd)
    · rw [if_neg hs, if_neg hs]
      exact ih d D hd

/-- One A1 iteration preserves entry honesty (delete-set spares the sweep's input honesty). -/
theorem iter_honest (B : WLab G s) (u : Fin G.n) (x : WLab G s) (st : BState G s)
    (hd : ∀ y val, st.D y = some val → st.d y ≤ val) :
    ∀ y val, (iter B u x st).D y = some val → (iter B u x st).d y ≤ val := by
  have hpre : ∀ y val, DS.deleteSet st.D {u} y = some val → st.d y ≤ val := by
    intro y val hy
    by_cases hyu : y ∈ ({u} : Finset (Fin G.n))
    · rw [DS.deleteSet_mem st.D {u} y hyu] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    · rw [DS.deleteSet_of_notMem st.D {u} y hyu] at hy
      exact hd y val hy
  exact a1_sweep_honest B u (List.finRange G.m) st.d (DS.deleteSet st.D {u}) hpre

/-- A1's loop preserves entry honesty. -/
theorem a1_loop_honest (t : ℕ) (B : WLab G s) :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' →
      (∀ y val, st.D y = some val → st.d y ≤ val) →
      ∀ y val, st'.D y = some val → st'.d y ≤ val := by
  intro c st st' h
  induction h with
  | exit h => exact fun hd => hd
  | pull u lam x hne hg hu hxgt hxle hxrest hxeq hrest ih =>
    intro hd
    exact ih (iter_honest B u x _ hd)

/-- `initD'` stores exactly the entry label. -/
theorem initD'_fresh {p : ℕ} (d : Labels G s) (piv : Fin p → Fin G.n) (y : Fin G.n)
    (val : WLab G s) (hy : initD' d piv y = some val) : val = d y := by
  have hfold : ∀ (D0 : DS G s), (∀ y val, D0 y = some val → val = d y) →
      ∀ y val, ((List.finRange p).foldl (fun D j => DS.insert D (piv j) (d (piv j))) D0) y
        = some val → val = d y := by
    intro D0
    induction (List.finRange p) generalizing D0 with
    | nil => exact fun hd y val hy => hd y val hy
    | cons j0 js ih =>
      intro hd y val hy
      rw [List.foldl_cons] at hy
      refine ih (DS.insert D0 (piv j0) (d (piv j0))) ?_ y val hy
      intro y val hy'
      by_cases hyz : y = piv j0
      · subst hyz
        rw [DS.insert_self] at hy'
        cases hD : D0 (piv j0) with
        | none =>
          rw [hD, DS.mergeVal_none_left] at hy'
          exact (Option.some.inj hy').symm
        | some μ =>
          rw [hD, DS.mergeVal_some] at hy'
          have hμ : μ = d (piv j0) := hd (piv j0) μ hD
          rw [hμ, min_self] at hy'
          exact (Option.some.inj hy').symm
      · rw [DS.insert_of_ne D0 (piv j0) (d (piv j0)) hyz] at hy'
        exact hd y val hy'
  exact hfold DS.empty (fun y val hy => absurd hy.symm (Option.some_ne_none val)) y val hy

theorem foldr_min_le (l : List (WLab G s)) (b x : WLab G s) (hx : x ∈ l) :
    l.foldr min b ≤ x := by
  induction l with
  | nil => nomatch hx
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with h | h
    · rw [h]; exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

theorem foldr_min_le_right (l : List (WLab G s)) (b : WLab G s) : l.foldr min b ≤ b := by
  induction l with
  | nil => exact le_rfl
  | cons a l ih =>
    rw [List.foldr_cons]
    exact (min_le_right _ _).trans ih

theorem initBp_le {p : ℕ} (d : Labels G s) (piv : Fin p → Fin G.n) (B : WLab G s) (j : Fin p) :
    initBp d piv B ≤ d (piv j) :=
  foldr_min_le _ _ _ (List.mem_ofFn.mpr ⟨j, rfl⟩)

theorem initBp_le_bound {p : ℕ} (d : Labels G s) (piv : Fin p → Fin G.n) (B : WLab G s) :
    initBp d piv B ≤ B :=
  foldr_min_le_right _ _

/-- The loop's running bound never exceeds the call bound: each iteration sets `bp` to the
child's `B'`, bounded by the child's entry bound (the pull separator `Bi ≤ B`). -/
theorem iloop_bp_le (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, q.2.B' ≤ q.1.B) → st.bp ≤ B → stf.bp ≤ B := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ hbp => hbp
  | step hne hg hstep hrest ih =>
    intro hchild hbp
    refine ih (fun q hq => hchild q (List.mem_cons_of_mem _ hq)) ?_
    obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
      hst'⟩ := hstep
    subst hst'
    have h1 := hchild _ List.mem_cons_self
    rw [hc] at h1
    obtain ⟨_, _, hle, _, _, _⟩ := hpull
    exact le_trans h1 hle

/-- The tail's return bound never exceeds the call bound (BM.24a: `B' = B` on drain). -/
theorem tailBP_le (B : WLab G s) {p : ℕ} (st : RState G s p) (hbp : st.bp ≤ B) :
    tailBP B st ≤ B := by
  unfold tailBP
  split_ifs with hemp
  · exact le_rfl
  · exact hbp

/-! ## The bound law -/

/-- **Bound law**: `B' ≤ B` at every return (BM.8/BM.24/BM.24a; the leaf's V5 cap has it as
`Engine.v5Cap_le_bound`).  Consumed by the transitive proposition: the final pull's separator
`B_f` satisfies `B'_f ≤ B_f ≤ B`. -/
theorem run_le_bound (t : ℕ) : ∀ {e : CallEntry G s} {out : CallOut G s},
    Run t e out → out.B' ≤ e.B := by
  intro e out h
  induction h with
  | base hl hb =>
    obtain ⟨c, st, hloop, hr⟩ := hb
    subst hr
    exact v5Cap_le_bound _ _ _
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    refine tailBP_le _ _ ?_
    refine iloop_bp_le t _ _ hloop (fun q hq => ih q hq) ?_
    rw [hst0]
    exact initBp_le_bound _ _ _

/-! ## Entry honesty (I3) and the mints -/

/-- One Algorithm-3 iteration preserves entry honesty: the merge of the pull remainder (honest at
`st.d`, transported along the child's monotonicity) and the child's structure (honest at
`fo'.d'`) is honest at `fo'.d'`; the sweep preserves honesty; the mint fold inserts at the
current label. -/
theorem istep_honest (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hmono : ∀ v, fo'.d' v ≤ c.d v)
    (hchild : ∀ y val, fo'.D y = some val → fo'.d' y ≤ val)
    (hst : ∀ y val, st.D y = some val → st.d y ≤ val) :
    ∀ y val, st'.D y = some val → st'.d y ≤ val := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hD1 : ∀ y val, D1 y = some val → st.d y ≤ val := by
    intro y val hy
    obtain ⟨_, hD', _, _, _, _⟩ := hpull
    rw [hD'] at hy
    by_cases hyS : y ∈ Si
    · rw [DS.deleteSet_mem st.D Si y hyS] at hy
      exact absurd hy (Option.some_ne_none val).symm
    · rw [DS.deleteSet_of_notMem st.D Si y hyS] at hy
      exact hst y val hy
  have hD2 : ∀ y val, D2 y = some val → fo'.d' y ≤ val := by
    intro y val hy
    rw [hmerge] at hy
    exact deleteSet_some_imp (settledFinset fo')
      (merge_honest fo'.d' D1 fo'.D
        (fun y val hy => (hmono y).trans (by rw [hc]; exact hD1 y val hy)) hchild) y val hy
  have hD3 : ∀ y val, D3 y = some val → d3 y ≤ val := by
    have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := by rw [← hsweep]
    have hD3' : D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 := by rw [← hsweep]
    intro y val hy
    rw [hD3'] at hy
    rw [hd3]
    exact sweepEvts_honest B Bi fo'.evts fo'.d' D2 hD2 y val hy
  exact fold_insert_honest J.toList sel d3 D3 hD3

/-- A loop of Algorithm-3 iterations preserves entry honesty. -/
theorem iloop_honest (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, ∀ v, q.2.d' v ≤ q.1.d v) →
      (∀ q ∈ qs, ∀ y val, q.2.D y = some val → q.2.d' y ≤ val) →
      (∀ y val, st.D y = some val → st.d y ≤ val) →
      ∀ y val, stf.D y = some val → stf.d y ≤ val := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ _ hd => hd
  | step hne hg hstep hrest ih =>
    intro hmono hhon hd
    exact ih (fun q hq => hmono q (List.mem_cons_of_mem _ hq))
      (fun q hq => hhon q (List.mem_cons_of_mem _ hq))
      (istep_honest t B l hstep (hmono _ List.mem_cons_self) (hhon _ List.mem_cons_self) hd)

/-- The tail preserves entry honesty (`seedIns` + the (E2)-gated `W'` sweep). -/
theorem tail_honest (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hd : ∀ y val, st.D y = some val → st.d y ≤ val) :
    ∀ y val, (tail B S W st).D y = some val → (tail B S W st).d y ≤ val :=
  sweepEvts_honest _ _ _ _ _ (seedIns_honest _ _ _ _ _ hd)

/-- **Entry honesty at returns** (I3, CORRECTED_PROOF §1): every stored value is `≥` the key's
current label.  Preserved by the merges (child I3 by IH), the sweeps (insert at the current
label) and the mint inserts; the tail inserts at the current label or above. -/
theorem run_entry_honest (t : ℕ) : ∀ {e : CallEntry G s} {out : CallOut G s},
    Run t e out → ∀ y val, out.D y = some val → out.d' y ≤ val := by
  intro e out h
  induction h with
  | base hl hb =>
    obtain ⟨c, st, hloop, hr⟩ := hb
    subst hr
    intro y val hy
    exact a1_loop_honest t _ hloop
      (fun y val hy => le_of_eq (initD_fresh _ _ hy).symm) y val hy
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro y val hy
    refine tail_honest _ _ _ _ ?_ y val hy
    refine iloop_honest t _ _ hloop
      (fun q hq v => run_le t (hchildren q hq) v) (fun q hq => ih q hq) ?_
    intro y val hy0
    rw [hst0] at hy0 ⊢
    exact le_of_eq (initD'_fresh _ _ _ _ hy0).symm

/-- The mint fold never drops a key. -/
theorem fold_insert_ne_none {ι : Type} (js : List ι) (f : ι → Fin G.n) (g : ι → WLab G s)
    (D0 : DS G s) (y : Fin G.n) (hy : D0 y ≠ none) :
    (js.foldl (fun D j => DS.insert D (f j) (g j)) D0) y ≠ none := by
  induction js generalizing D0 with
  | nil => exact hy
  | cons j0 js ih =>
    rw [List.foldl_cons]
    refine ih (DS.insert D0 (f j0) (g j0)) ?_
    by_cases hyz : y = f j0
    · subst hyz
      rw [DS.insert_self]
      exact DS.mergeVal_ne_none (D0 (f j0)) (g j0)
    · rw [DS.insert_of_ne D0 (f j0) (g j0) hyz]
      exact hy

/-- Every key the fold inserts stays keyed (`DS.mem_keys_insert` + key monotonicity). -/
theorem fold_insert_mem {ι : Type} (js : List ι) (f : ι → Fin G.n) (g : ι → WLab G s)
    (D0 : DS G s) : ∀ j ∈ js, (js.foldl (fun D j => DS.insert D (f j) (g j)) D0) (f j) ≠ none := by
  induction js generalizing D0 with
  | nil => intro j hj; nomatch hj
  | cons j0 js ih =>
    intro j hj
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hj with hj | hj
    · subst hj
      exact fold_insert_ne_none js f g (DS.insert D0 (f j) (g j)) (f j)
        (DS.mem_keys_insert D0 (f j) (g j))
    · exact ih (DS.insert D0 (f j0) (g j0)) j hj

/-- Every minted entry of a loop state is still keyed by its `𝒟` (the BM.23 insert; keep-min
keeps the key).  Induction hypothesis of `full_no_prem`. -/
theorem iloop_mints_keys (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ m ∈ st.mints, st.D m.x ≠ none) → ∀ m ∈ stf.mints, stf.D m.x ≠ none := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hyp m hm => hyp m hm
  | step hne hg hstep hrest ih =>
    intro hyp m hm
    refine ih ?_ m hm
    obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
      hst'⟩ := hstep
    subst hst'
    intro m' hm'
    obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hm'
    subst hjm
    exact fold_insert_mem J.toList sel (fun j => d3 (sel j)) D3 j hj

/-- A loop's final state is either the initial state or the product of a last iteration. -/
theorem iloop_mints_shape (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      stf = st ∨ ∃ st₁ c fo', IStep t B l st₁ stf c fo' := by
  intro p st stf qs h
  induction h with
  | exit h => exact Or.inl rfl
  | step hne hg hstep hrest ih =>
    rcases ih with h' | h'
    · exact Or.inr ⟨_, _, _, h' ▸ hstep⟩
    · exact Or.inr h'

/-! ## The Q12 carve-out shape (clause (2b)'s Prem) -/

/-! ## Mint bookkeeping behind the Q12 carve-out -/

/-- The fold keeps a key whose stored value already equals its label. -/
theorem fold_insert_keep {ι : Type} (js : List ι) (f : ι → Fin G.n) (d : Labels G s)
    (y : Fin G.n) (val : WLab G s) :
    ∀ (D0 : DS G s), D0 y = some val → d y = val →
      (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D0) y = some val := by
  intro D0
  induction js generalizing D0 with
  | nil => intro hy hval; exact hy
  | cons j0 js ih =>
    intro hy hval
    rw [List.foldl_cons]
    by_cases hf : f j0 = y
    · apply ih
      · rw [hf]
        rw [DS.insert_self, hy, hval, DS.mergeVal_some, min_self]
      · exact hval
    · apply ih
      · rw [DS.insert_of_ne D0 (f j0) (d (f j0)) (Ne.symm hf)]
        exact hy
      · exact hval

/-- The mint fold stores each mint's exact label value: `D3` is honest at `d3` (so the keep-min
picks the mint value) and equal-key inserts carry the same value. -/
theorem fold_insert_label_eq {ι : Type} (d : Labels G s) (f : ι → Fin G.n) :
    ∀ (js : List ι) (D0 : DS G s), (∀ y val, D0 y = some val → d y ≤ val) →
      ∀ j ∈ js, (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D0) (f j) = some (d (f j)) := by
  intro js
  induction js with
  | nil => intro D0 hd j hj; nomatch hj
  | cons j0 js ih =>
    intro D0 hd j hj
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hj with hj | hj
    · subst hj
      have hself : (DS.insert D0 (f j) (d (f j))) (f j) = some (d (f j)) := by
        rw [DS.insert_self]
        cases hD : D0 (f j) with
        | none => rw [DS.mergeVal_none_left]
        | some μ => rw [DS.mergeVal_some, min_eq_right (hd (f j) μ hD)]
      exact fold_insert_keep js f d (f j) (d (f j)) (DS.insert D0 (f j) (d (f j))) hself rfl
    · exact ih (DS.insert D0 (f j0) (d (f j0))) (insert_label_honest d D0 (f j0) hd) j hj

/-- The loop's mints land exactly in its `𝒟` at their mint values. -/
theorem istep_mints_exact (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hmono : ∀ v, fo'.d' v ≤ c.d v)
    (hchild : ∀ y val, fo'.D y = some val → fo'.d' y ≤ val)
    (hst : ∀ y val, st.D y = some val → st.d y ≤ val) :
    ∀ m ∈ st'.mints, st'.D m.x = some m.val := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  intro m hm
  obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hm
  subst hjm
  have hD3 : ∀ y val, D3 y = some val → d3 y ≤ val := by
    have hD1 : ∀ y val, D1 y = some val → st.d y ≤ val := by
      intro y val hy
      obtain ⟨_, hD', _, _, _, _⟩ := hpull
      rw [hD'] at hy
      by_cases hyS : y ∈ Si
      · rw [DS.deleteSet_mem st.D Si y hyS] at hy
        exact absurd hy (Option.some_ne_none val).symm
      · rw [DS.deleteSet_of_notMem st.D Si y hyS] at hy
        exact hst y val hy
    have hD2 : ∀ y val, D2 y = some val → fo'.d' y ≤ val := by
      intro y val hy
      rw [hmerge] at hy
      exact deleteSet_some_imp (settledFinset fo')
        (merge_honest fo'.d' D1 fo'.D
          (fun y val hy => (hmono y).trans (by rw [hc]; exact hD1 y val hy)) hchild) y val hy
    have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := by rw [← hsweep]
    have hD3' : D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 := by rw [← hsweep]
    intro y val hy
    rw [hD3'] at hy
    rw [hd3]
    exact sweepEvts_honest B Bi fo'.evts fo'.d' D2 hD2 y val hy
  show (J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3) (sel j) = some (d3 (sel j))
  exact fold_insert_label_eq d3 sel J.toList D3 hD3 j hj

theorem iloop_mints_exact (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, ∀ v, q.2.d' v ≤ q.1.d v) →
      (∀ q ∈ qs, ∀ y val, q.2.D y = some val → q.2.d' y ≤ val) →
      (∀ y val, st.D y = some val → st.d y ≤ val) →
      (∀ m ∈ st.mints, st.D m.x = some m.val) →
      ∀ m ∈ stf.mints, stf.D m.x = some m.val := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ _ _ hm => hm
  | step hne hg hstep hrest ih =>
    intro hmono hhon hd hex
    exact ih (fun q hq => hmono q (List.mem_cons_of_mem _ hq))
      (fun q hq => hhon q (List.mem_cons_of_mem _ hq))
      (istep_honest t B l hstep (hmono _ List.mem_cons_self) (hhon _ List.mem_cons_self) hd)
      (istep_mints_exact t B l hstep (hmono _ List.mem_cons_self) (hhon _ List.mem_cons_self) hd)

/-- A state's mint values are exactly its labels at the mint keys. -/
theorem iloop_mints_label (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ m ∈ st.mints, st.d m.x = m.val) → ∀ m ∈ stf.mints, stf.d m.x = m.val := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hm => hm
  | step hne hg hstep hrest ih =>
    intro hm
    refine ih ?_
    obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
      hst'⟩ := hstep
    subst hst'
    intro m hm'
    obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hm'
    subst hjm
    show d3 (sel j) = d3 (sel j)
    rfl

/-- A state's mint keys sit in its own residual pivot groups. -/
theorem iloop_mints_pl (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ m ∈ st.mints, ∃ j, m.x ∈ st.pl j) → ∀ m ∈ stf.mints, ∃ j, m.x ∈ stf.pl j := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hm => hm
  | step hne hg hstep hrest ih =>
    intro hm
    refine ih ?_
    obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
      hst'⟩ := hstep
    subst hst'
    intro m hm'
    obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hm'
    subst hjm
    exact ⟨j, (hsel j (Finset.mem_toList.mp hj)).1⟩

open Classical in
/-- Residual groups only shrink along the loop. -/
theorem iloop_pl_sub (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf → ∀ j, stf.pl j ⊆ st.pl j := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun j x hx => hx
  | step hne hg hstep hrest ih =>
    intro j x hx
    have hmid := ih j hx
    obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
      hst'⟩ := hstep
    subst hst'
    have h1 : x ∈ resid j := hmid
    rw [hresid j] at h1
    exact (Finset.mem_filter.mp h1).1

open Classical in
/-- One iteration's residual groups exclude the state's own log (BM.17 filter + append). -/
theorem istep_pl_clean (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hd : ∀ j x, x ∈ st.pl j → x ∉ settledSet st.evts) :
    ∀ j x, x ∈ st'.pl j → x ∉ settledSet st'.evts := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  intro j x hx
  have h1 : x ∈ resid j := hx
  rw [hresid j] at h1
  have h2 := Finset.mem_filter.mp h1
  change x ∉ settledSet (st.evts ++ fo'.evts)
  rw [settledSet_append, Set.mem_union]
  intro hsett
  rcases hsett with hsett | hsett
  · exact hd j x h2.1 hsett
  · exact h2.2 hsett

/-- Residual-group members are never settled in the state's own log (the BM.17 filter). -/
theorem iloop_pl_clean (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ j x, x ∈ st.pl j → x ∉ settledSet st.evts) →
      ∀ j x, x ∈ stf.pl j → x ∉ settledSet stf.evts := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hd => hd
  | step hne hg hstep hrest ih =>
    intro hd j x hx
    exact ih (istep_pl_clean t B l hstep hd) j x hx

/-- `seedIns` cannot insert below-bound keys: the gate is `bp ≤ d x`. -/
theorem seedIns_keeps (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s)
    (x : Fin G.n) (val : WLab G s) (hx : D x = some val) (hlt : d x < bp) :
    (seedIns bp B S d D).2 x = some val := by
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => exact hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    by_cases hg : bp ≤ d y ∧ d y < B
    · rw [if_pos hg]
      refine ih d (DS.insert D y (d y)) ?_ hlt
      by_cases hxy : x = y
      · subst hxy
        exact absurd hg.1 (not_le.mpr hlt)
      · rw [DS.insert_of_ne D y (d y) hxy]
        exact hx
    · rw [if_neg hg]
      exact ih d D hx hlt

/-- A keep-min entry below the (E2) gate survives `relaxGate` unchanged. -/
theorem relaxGate_keeps (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (x : Fin G.n) (val : WLab G s) (hx : D x = some val) (hlt : val < lo) :
    (relaxGate B lo d D e).2 x = some val := by
  unfold relaxGate
  by_cases h : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos h]
    show DS.insert D (G.dst e) (ext (d (G.src e)) e) x = some val
    by_cases hxe : x = G.dst e
    · subst hxe
      rw [DS.insert_self, hx, DS.mergeVal_some]
      rw [min_eq_left (le_of_lt (hlt.trans_le h.1))]
    · rw [DS.insert_of_ne D (G.dst e) (ext (d (G.src e)) e) hxe]
      exact hx
  · rw [if_neg h]
    exact hx

theorem sweepGate_keeps (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (x : Fin G.n) (val : WLab G s) (hx : D x = some val) (hlt : val < lo) :
    (sweepGate B lo u es d D).2 x = some val := by
  induction es generalizing d D with
  | nil => exact hx
  | cons e es ih =>
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (relaxGate_keeps B lo d D e x val hx hlt)
    · rw [if_neg hs, if_neg hs]
      exact ih d D hx

theorem sweepEvts_keeps (B lo : WLab G s) (evts : List (SettlementEvent G)) (d : Labels G s)
    (D : DS G s) (x : Fin G.n) (val : WLab G s) (hx : D x = some val) (hlt : val < lo) :
    (sweepEvts B lo evts d D).2 x = some val := by
  induction evts generalizing d D with
  | nil => exact hx
  | cons ev evts ih =>
    unfold sweepEvts
    exact ih _ _ (sweepGate_keeps B lo ev.v (List.finRange G.m) d D x val hx hlt)

/-- The tail keeps a below-bound entry at its exact value: `seedIns`' gate fails at `x` (its
label is below `bp`) and the (E2)-gated `W'` sweep inserts only candidates `≥ bp > val`, whose
keep-min loses to `val`. -/
theorem tail_keeps (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (x : Fin G.n) (val : WLab G s)
    (hx : st.D x = some val) (hlt : val < tailBP B st) (hd : st.d x ≤ val) :
    (tail B S W st).D x = some val :=
  sweepEvts_keeps _ _ _ _ _ x val
    (seedIns_keeps _ _ _ _ _ x val hx (lt_of_le_of_lt hd hlt)) hlt

/-- A pivot gates itself out of `W` (its canonical path visits it). -/
theorem mem_Y_not_wFin {B : WLab G s} {S Y : Finset (Fin G.n)} {y : Fin G.n}
    (hy : y ∈ Y) : y ∉ wFin (G := G) (s := s) B S Y := by
  intro hw
  have hU := (mem_wFin_iff.mp hw).1
  exact (mem_wFin_iff.mp hw).2 (mem_behind_self hy (reachable_of_dis_lt hU.1))

open Classical in
/-- `settledSet` of the boundary-append events is exactly `W'`. -/
theorem settledSet_wPrimeEvts (Wp : Finset (Fin G.n)) :
    settledSet (wPrimeEvts Wp) = (Wp : Set (Fin G.n)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨ev, hev, hxv⟩ := hx
    simp only [wPrimeEvts, List.mem_map] at hev
    obtain ⟨y, hy, rfl⟩ := hev
    rw [← hxv]
    exact Finset.mem_coe.mpr (Finset.mem_toList.mp hy)
  · intro hx
    have hx' : x ∈ Wp := Finset.mem_coe.mp hx
    refine ⟨⟨.boundaryAppend, x⟩, ?_, rfl⟩
    exact List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx', rfl⟩

/-- **Prem entries are entries of the returned `𝒟`** (clause (2b)'s `premInD`): the mint's
insert wins the keep-min (entry honesty gives the old value `≥` the mint) and the tail's inserts
are either at the unchanged label (`= val`) or gated `≥ B' > val` (E2 keeps the BM.28 sweep from
lowering a Prem key below `B'`), so nothing replaces the entry. -/
theorem premInD_of_run (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (h : Run t e out) : ∀ x val, out.Premature x val → out.D x = some val := by
  induction h with
  | base hl hb =>
    intro x val hp
    exact absurd hp.1 List.not_mem_nil
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro x val hp
    obtain ⟨hm, hlt⟩ := hp
    have hex := iloop_mints_exact t _ _ hloop
      (fun q hq v => run_le t (hchildren q hq) v)
      (fun q hq => run_entry_honest t (hchildren q hq))
      (by
        intro y val hy0
        rw [hst0] at hy0 ⊢
        exact le_of_eq (initD'_fresh _ _ _ _ hy0).symm)
      (by
        intro m hm0
        rw [hst0] at hm0
        exact absurd hm0 List.not_mem_nil)
      _ hm
    have hlab := iloop_mints_label t _ _ hloop
      (by
        intro m hm0
        rw [hst0] at hm0
        exact absurd hm0 List.not_mem_nil)
      _ hm
    exact tail_keeps _ _ _ _ _ _ hex hlt (le_of_eq hlab)

theorem settledSet_append_mem {a b : List (SettlementEvent G)} {x : Fin G.n}
    (hx : x ∈ settledSet (a ++ b)) : x ∈ settledSet a ∨ x ∈ settledSet b := by
  obtain ⟨ev, hev, hv⟩ := hx
  rcases List.mem_append.mp hev with hev | hev
  · exact Or.inl ⟨ev, hev, hv⟩
  · exact Or.inr ⟨ev, hev, hv⟩

open Classical in
/-- A settled vertex of the tail is settled in the loop log or a `W` member (the `W'` boundary
appends are the only other settlement source). -/
theorem tail_U_of_mem (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (x : Fin G.n) (hx : x ∈ settledSet (tail B S W st).evts) :
    x ∈ settledSet st.evts ∨ x ∈ W := by
  have h1 : (tail B S W st).evts = st.evts ++
      wPrimeEvts (wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1) := rfl
  rw [h1] at hx
  rcases settledSet_append_mem hx with hx | hx
  · exact Or.inl hx
  · right
    rw [settledSet_wPrimeEvts] at hx
    have h2 : x ∈ wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1 :=
      Finset.mem_coe.mp hx
    exact (Finset.mem_filter.mp h2).1

theorem mkInit_mints (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n) :
    (mkInit e fo piv).mints = ([] : List (Mint G s)) := rfl

theorem mkInit_evts (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n) :
    (mkInit e fo piv).evts = ([] : List (SettlementEvent G)) := rfl

theorem mkInit_pl (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n) :
    (mkInit e fo piv).pl = fo.P := rfl

/-- The tail's labels at a kept mint key give (2b)'s `d' x ≤ val` and the two-shape dichotomy. -/
theorem tail_le_val_premShape (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (x : Fin G.n) (val : WLab G s) (hlab : st.d x = val) :
    (tail B S W st).d x ≤ val ∧ PremShape (tail B S W st).d x val := by
  have hle : (tail B S W st).d x ≤ val := (tail_le B S W st x).trans (le_of_eq hlab)
  refine ⟨hle, ?_⟩
  by_cases hc : Complete (tail B S W st).d x
  · exact PremShape.s1 hc
  · exact PremShape.s2 hc hle

/-- **Prem shape** (clause (2b)'s `premShape`): a Prem entry is minted for a member of a final
group (the residual `Pl j` of the final re-selection, recorded in `CallOut.Pfin`), never settles
(`x ∉ U` — residual groups exclude every settled member and `Pl ∩ W = ∅` in A2's FindPivots),
has current label `≤` its mint (I2), and is two-shaped (S1/S2 — the dichotomy is classical in
`Complete out.d' x`, CORRECTED_PROOF §3 (2b)). -/
theorem premShape_of_run (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (h : Run t e out) : ∀ x val, out.Premature x val →
      x ∉ out.U ∧ (∃ j, x ∈ out.Pfin j) ∧ out.d' x ≤ val ∧ PremShape out.d' x val := by
  induction h with
  | base hl hb =>
    intro x val hp
    exact absurd hp.1 List.not_mem_nil
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro x val hp
    obtain ⟨hm, hlt⟩ := hp
    obtain ⟨j, hpl⟩ := iloop_mints_pl t _ _ hloop
      (by
        intro m hm0
        rw [hst0, mkInit_mints] at hm0
        exact absurd hm0 List.not_mem_nil)
      _ hm
    have hlab := iloop_mints_label t _ _ hloop
      (by
        intro m hm0
        rw [hst0, mkInit_mints] at hm0
        exact absurd hm0 List.not_mem_nil)
      _ hm
    have hclean := iloop_pl_clean t _ _ hloop
      (by
        intro j x' hx' hs
        rw [hst0, mkInit_evts] at hs
        obtain ⟨ev, hev, _⟩ := hs
        exact absurd hev List.not_mem_nil)
      j x hpl
    have hfoP := iloop_pl_sub t _ _ hloop j hpl
    rw [hst0, mkInit_pl] at hfoP
    obtain ⟨hpre, Y, c', st', hYsub, hYne, hcap, hloopF, hdF, hW, hpF, hP, hQ⟩ := hfp
    have hY : x ∈ Y := by rw [hP] at hfoP; exact hfoP
    obtain ⟨hle, hps⟩ := tail_le_val_premShape _ _ _ _ x val hlab
    refine ⟨?_, ⟨j, hpl⟩, hle, hps⟩
    intro hs
    rcases tail_U_of_mem _ _ _ _ x hs with hs | hs
    · exact hclean hs
    · exact mem_Y_not_wFin hY (by rw [← hW]; exact hs)

/-- **Full executions are immune** (CORRECTED_PROOF §3 (2b), §4.1): every mint inserts its key
and nothing deletes after BM.10, so a drained `𝒟` means the final iteration minted nothing —
`Prem = ∅` on full executions. -/
theorem full_no_prem (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (h : Full t e out) : ∀ x val, ¬ out.Premature x val := by
  intro x val hp
  have hd : out.D x = some val := premInD_of_run t e out h.1 x val hp
  rw [h.2 x] at hd
  cases hd

/-! ## Labels stay walks (`WalkInv` through the spine)

The `Sound d` supply of the W′ drop lemma's hypotheses — `A4.WDrop`'s instance note names this
plumbing as the piece A4 lacked ("`WalkInv` through `Run`… a different lemma").  Every
mechanical layer writes either `⊤` or the extension of an existing walk label, so `WalkInv` is
preserved by the sweeps (`relaxGate`/`relaxEdge` accept), the seed inserts (labels untouched),
the mint folds (labels untouched) and the tail — hence by `Run` (base case: A1's loop; recur
case: A2's output labels plus the loop and tail).  `reach_sound` then delivers `Sound` at every
reachable entry and return, the first of `wPrime_drop`'s three hypotheses at a reachable run's
filter moment.
-/

/-- `toW` is injective (it is the identity on `WalkOrd = List (Fin G.m)`). -/
theorem toW_inj {p q : List (Fin G.m)} (h : (toW (s := s) p : WalkOrd G s) = toW q) : p = q := h

/-- The walk core of an accepted relaxation: if the tail's label is the walk `r`, the written
head label is the walk `r ++ [e]` (used at `q` via `toW` injectivity). -/
theorem update_walk_coe {d : Labels G s} (h : WalkInv d) (e : Fin G.m) {r : List (Fin G.m)}
    (hr : d (G.src e) = ((toW r : WalkOrd G s) : WLab G s)) (q : List (Fin G.m))
    (hvq : ((toW (r ++ [e]) : WalkOrd G s) : WLab G s)
      = ((toW q : WalkOrd G s) : WLab G s)) : G.IsWalk s (G.dst e) q := by
  have hrq : r ++ [e] = q := toW_inj (WithTop.coe_injective (α := WalkOrd G s) hvq)
  subst hrq
  exact walk_ext (h (G.src e) r hr) e rfl

/-- One accepted relaxation keeps labels walks: the written value is `⊤` (vacuous) or the
extension `p ++ [e]` of a walk to `G.src e`. -/
theorem update_walk {d : Labels G s} (h : WalkInv d) (e : Fin G.m) (v : Fin G.n)
    {q : List (Fin G.m)}
    (hvq : Function.update d (G.dst e) (ext (d (G.src e)) e) v
      = ((toW q : WalkOrd G s) : WLab G s)) : G.IsWalk s v q := by
  by_cases hv : v = G.dst e
  · subst hv
    rw [Function.update_self] at hvq
    by_cases htop : d (G.src e) = ⊤
    · rw [htop, ext_top] at hvq
      simp at hvq
    · obtain ⟨w, hw⟩ := WithTop.ne_top_iff_exists.mp htop
      -- the `WalkOrd` witness `w` is (definitionally) the walk's edge list; `id` retypes it
      have hr : d (G.src e) = ((toW (id (α := List (Fin G.m)) w) : WalkOrd G s) : WLab G s) :=
        hw.symm
      refine update_walk_coe h e hr q ?_
      have h1 : ext (d (G.src e)) e
          = ((toW ((id (α := List (Fin G.m)) w) ++ [e]) : WalkOrd G s) : WLab G s) := by
        conv_lhs => rw [hr]
        exact ext_coe (id (α := List (Fin G.m)) w) e
      rw [← h1]
      exact hvq
  · rw [Function.update_of_ne hv] at hvq
    exact h v q hvq

theorem relaxGate_walk (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (h : WalkInv d) : WalkInv (relaxGate B lo d D e).1 := by
  intro v q hvq
  unfold relaxGate at hvq
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos hc] at hvq
    exact update_walk h e v hvq
  · rw [if_neg hc] at hvq
    exact h v q hvq

theorem sweepGate_walk (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (h : WalkInv d) : WalkInv (sweepGate B lo u es d D).1 := by
  induction es generalizing d D with
  | nil => exact h
  | cons e es ih =>
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (relaxGate_walk B lo d D e h)
    · rw [if_neg hs, if_neg hs]
      exact ih d D h

theorem sweepEvts_walk (B lo : WLab G s) (evts : List (SettlementEvent G)) (d : Labels G s)
    (D : DS G s) (h : WalkInv d) : WalkInv (sweepEvts B lo evts d D).1 := by
  induction evts generalizing d D with
  | nil => exact h
  | cons ev evts ih =>
    unfold sweepEvts
    exact ih _ _ (sweepGate_walk B lo ev.v (List.finRange G.m) d D h)

theorem a1_relaxEdge_walk (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (h : WalkInv d) : WalkInv (relaxEdge B d D e).1 := by
  intro v q hvq
  unfold relaxEdge at hvq
  by_cases hc : ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B
  · rw [if_pos hc] at hvq
    exact update_walk h e v hvq
  · rw [if_neg hc] at hvq
    exact h v q hvq

theorem a1_sweep_walk (B : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (h : WalkInv d) : WalkInv (sweep B u es d D).1 := by
  induction es generalizing d D with
  | nil => exact h
  | cons e es ih =>
    unfold sweep
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (a1_relaxEdge_walk B d D e h)
    · rw [if_neg hs, if_neg hs]
      exact ih d D h

theorem a1_iter_walk (B : WLab G s) (u : Fin G.n) (x : WLab G s) (st : BState G s)
    (h : WalkInv st.d) : WalkInv (iter B u x st).d :=
  a1_sweep_walk B u (List.finRange G.m) st.d (DS.deleteSet st.D {u}) h

theorem a1_loop_walk (t : ℕ) (B : WLab G s) :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' → WalkInv st.d → WalkInv st'.d := by
  intro c st st' h
  induction h with
  | exit h => exact fun hst => hst
  | pull u lam x hne hg hu hxgt hxle hxrest hxeq hrest ih =>
    intro hst
    exact ih (a1_iter_walk B u x _ hst)

theorem baseRun_walk {t : ℕ} {e : BaseIn G s} {out : BaseOut G s}
    (h : WalkInv e.d) (hb : baseRun t e out) : WalkInv out.d' := by
  obtain ⟨c, st, hloop, hr⟩ := hb
  subst hr
  exact a1_loop_walk t e.B hloop h

/-- `seedIns` never touches labels, so it keeps labels walks. -/
theorem seedIns_walk (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s)
    (h : WalkInv d) : WalkInv (seedIns bp B S d D).1 := by
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => exact h
  | cons x xs ih =>
    rw [List.foldl_cons]
    by_cases hg : bp ≤ d x ∧ d x < B
    · rw [if_pos hg]
      exact ih d (DS.insert D x (d x)) h
    · rw [if_neg hg]
      exact ih d D h

/-- One iteration's child call inherits the parent's loop labels (BM.13's `st.d`). -/
theorem istep_entry_d {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') : c.d = st.d := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  rw [hc]

/-- One iteration's post-sweep labels are walks whenever the child's return labels are. -/
theorem istep_walk (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hchild : WalkInv fo'.d') : WalkInv st'.d := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc', hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := by rw [← hsweep]
  rw [hd3]
  exact sweepEvts_walk B Bi fo'.evts fo'.d' D2 hchild

theorem iloop_walk (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      WalkInv st.d → (∀ q ∈ qs, WalkInv q.1.d → WalkInv q.2.d') → WalkInv stf.d := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hst _ => hst
  | step hne hg hstep hrest ih =>
    intro hst hkids
    refine ih ?_ (fun q hq => hkids q (List.mem_cons_of_mem _ hq))
    exact istep_walk t B l hstep
      (hkids _ List.mem_cons_self (by rw [istep_entry_d hstep]; exact hst))

/-- The loop's final state and every child entry of the loop carry walk labels. -/
theorem iloop_states_walk (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      WalkInv st.d → (∀ q ∈ qs, WalkInv q.1.d → WalkInv q.2.d') →
        WalkInv stf.d ∧ ∀ q ∈ qs, WalkInv q.1.d := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hst _ => ⟨hst, fun q hq => absurd hq List.not_mem_nil⟩
  | step hne hg hstep hrest ih =>
    intro hst hkids
    obtain ⟨h1, h2⟩ := ih (istep_walk t B l hstep
        (hkids _ List.mem_cons_self (by rw [istep_entry_d hstep]; exact hst)))
      (fun q hq => hkids q (List.mem_cons_of_mem _ hq))
    refine ⟨h1, ?_⟩
    intro q' hq'
    rcases List.mem_cons.mp hq' with hq' | hq'
    · subst hq'
      rw [istep_entry_d hstep]
      exact hst
    · exact h2 q' hq'

theorem tail_walk (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (h : WalkInv st.d) : WalkInv (tail B S W st).d :=
  sweepEvts_walk B (tailBP B st) _ _ _ (seedIns_walk (tailBP B st) B S st.d st.D h)

/-- **Labels stay walks through `Run`** (the `Sound` supply of `A4.WDrop`'s hypotheses). -/
theorem run_walk (t : ℕ) : ∀ {e : CallEntry G s} {out : CallOut G s},
    Run t e out → WalkInv e.d → WalkInv out.d' := by
  intro e out h
  induction h with
  | base hl hb => exact fun hd => baseRun_walk hd hb
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro hd
    refine tail_walk _ _ _ _ ?_
    refine iloop_walk t _ _ hloop ?_ (fun q hq => ih q hq)
    rw [hst0]
    exact (fpRun_contract _ _ hfp).1.walk

theorem run_sound (t : ℕ) {e : CallEntry G s} {out : CallOut G s}
    (h : Run t e out) (hd : WalkInv e.d) : Sound out.d' :=
  (run_walk t h hd).sound

/-- `initLabels` labels are walks (the empty walk at `s`, `⊤` elsewhere). -/
theorem initLabels_walk : WalkInv (initLabels G s) := by
  intro v p hv
  by_cases hv' : v = s
  · rw [hv'] at hv ⊢
    simp [initLabels] at hv
    have h2 : ([] : List (Fin G.m)) = p := hv
    rw [← h2]
    exact IsWalk.nil s
  · simp [initLabels, hv'] at hv

/-- `Sound` at a top-entry run's return labels (`initLabels` walks at the top; `run_sound`
through the spine). -/
theorem top_run_sound (t : ℕ) {out : CallOut G s}
    (hrun : Run t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ out) : Sound out.d' :=
  run_sound t hrun initLabels_walk

/-! ## Sound labels at every `Reach` entry

The tying fix in `A4.Semantics.ChildOf` — one `recur` derivation, its own `hchildren` — makes
this true: a reachable child entry's labels are the loop-state labels of a genuine derivation,
so `WalkInv` flows from `initLabels` through every child call (A2's output labels walk
unconditionally; the loop states walk by `iloop_states_walk` fed `run_walk` on each child).  The
former note ("`Sound` at *every* `Reach` entry is not available as stated") is resolved. -/

/-- **Labels stay walks at every reachable entry**: the tied `ChildOf` makes every `Reach`
sub-entry's `d` the loop-state labels of one genuine `recur` derivation. -/
theorem reach_sound (t : ℕ) : ∀ {e : CallEntry G s}, Reach t e → WalkInv e.d := by
  intro e h
  induction h with
  | top => exact initLabels_walk
  | sub _he hc _ih =>
    obtain ⟨out, p, fo, piv, st0, stf, qs, _hrun, _hout, _hl, hfp, _hpiv, hst0, hloop,
      hchildren, q, hq, hqc⟩ := hc
    have h1 : WalkInv q.1.d :=
      (iloop_states_walk t _ _ hloop
        (by rw [hst0]; exact (fpRun_contract _ _ hfp).1.walk)
        (fun q' hq' hd' => run_walk t (hchildren q' hq') hd')).2 q hq
    rw [← hqc]
    exact h1

/-- **Sound labels at every `Reach` entry** — the W′ drop lemma's `Sound d` supply, now
available at every reachable entry (not just the top). -/
theorem reach_entry_sound (t : ℕ) {e : CallEntry G s} (h : Reach t e) : Sound e.d :=
  (reach_sound t h).sound

/-! ## Lemma 3.6 at pulls (the child frontier preconditions of the joint induction)

DMSY26 Lemma 3.6 in the abstract is A0's `IsFrontier.split`; what A4 adds is the instantiation
at BM.10–13: the pulled set plus the BM.12 low-member expansion **is** the `Y_s` of the split,
so the child call's entry carries the frontier clause of `Lemma37Hyp`.  The two side conditions
the split needs — boundary coverage (`{x ∈ Y : d[x] < B_i} ⊆ S_child`) and the paper's (J6)
(`S_child ⊆ Ũ(B, S)`) — are exactly the joint chain's clause-(1) loop-state invariant and its
`(J6)` bookkeeping; `istep_cover_accurate` below discharges the coverage's mechanical half
(accurate keys below the separator are pulled). -/

/-- BM.11–12 membership, pulled part: every pulled key joins the child's seed set. -/
theorem mem_expand_of_pulled {d : Labels G s} {p : ℕ} {pl : Fin p → Finset (Fin G.n)}
    {piv : Fin p → Fin G.n} {Si : Finset (Fin G.n)} {Bi : WLab G s} {y : Fin G.n}
    (hy : y ∈ Si) : y ∈ expand d pl piv Si Bi :=
  Finset.mem_union_left _ hy

/-- BM.11–12 membership, expansion part: a low member of a group whose (current) pivot was
pulled joins the child's seed set (Line 8/12's rule). -/
theorem mem_expand_of_low_member {d : Labels G s} {p : ℕ} {pl : Fin p → Finset (Fin G.n)}
    {piv : Fin p → Fin G.n} {Si : Finset (Fin G.n)} {Bi : WLab G s} {j : Fin p} {y : Fin G.n}
    (hpiv : piv j ∈ Si) (hpivpl : piv j ∈ pl j) (hy : y ∈ pl j) (hlt : d y < Bi) :
    y ∈ expand d pl piv Si Bi := by
  refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩)
  split
  · exact Finset.mem_filter.mpr ⟨hy, hlt⟩
  · next h => exact absurd ⟨hpiv, hpivpl⟩ h

/-- Boundary coverage, accurate-key half: a key whose `D`-entry is **accurate** (stored value =
current label) and below the separator is pulled (`PullSpec.pulled`) and hence in the child's
seed set.  Accuracy at complete boundary keys is the joint chain's custody invariant; this
lemma is the mechanical bridge from it to the split's coverage condition. -/
theorem istep_cover_accurate (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') {y : Fin G.n}
    (hacc : st.D y = some (st.d y)) (hlt : st.d y < c.B) : y ∈ c.S := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hc
  exact mem_expand_of_pulled ((pullRun_pulled hpull).mpr ⟨st.d y, hacc, hlt⟩)

/-- **Lemma 3.6 at pulls — the child's frontier precondition**: if the loop state carries a
frontier `⟨X, Y⟩` for `Ũ(B, S)` (the joint chain's clause-(1) invariant at the iteration
state), every boundary vertex below the separator is covered by the child's seed set
(accuracy + `PullSpec.pulled` + the BM.12 expansion — see `istep_cover_accurate`), and the
seed set lies in `Ũ(B, S)` (the paper's (J6)), then `⟨∅, S_child⟩` is a frontier for
`Ũ(B_child, S_child)` at the inherited labels — the frontier clause of `Lemma37Hyp t c`. -/
theorem istep_child_frontier (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    {S : Finset (Fin G.n)} {X Y : Set (Fin G.n)}
    (hF : IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y)
    (hcover : ∀ y ∈ Y, st.d y < c.B → y ∈ c.S)
    (hsub : (c.S : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))) :
    IsFrontier c.d (Utilde c.B (c.S : Set (Fin G.n))) ∅ (c.S : Set (Fin G.n)) := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hc
  exact IsFrontier.split hF (fun y hy hlt => Finset.mem_coe.mpr (hcover y hy hlt)) hsub

/-! ## Lemma 3.5 at pulls (seed-size propagation to children)

DMSY26 Lemma 3.5's `|S'| ≤ M` is `PullSpec.size`, wired through `pullRun (pullCap t l)` in
`IStep`; A4's half is the recursion-side bound: the child's seed set (pull + BM.12 expansion)
is capped by the pull cap plus the loop state's pivot-member cap, which the loop never raises
(BM.17 only removes members), and the arithmetic fits the result into `memCap t (l−1)` — the
size clause of the child's `Lemma37Hyp`. -/

open Classical in
/-- One iteration does not raise the loop state's pivot-member total (BM.17 only filters). -/
theorem istep_bunion_pl_le (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') {cap : ℕ}
    (hcap : (Finset.univ.biUnion st.pl).card ≤ cap) :
    (Finset.univ.biUnion st'.pl).card ≤ cap := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hsub : (Finset.univ.biUnion resid) ⊆ Finset.univ.biUnion st.pl := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
    rw [hresid j] at hxj
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, (Finset.mem_filter.mp hxj).1⟩
  exact (Finset.card_mono hsub).trans hcap

/-- **Lemma 3.5 at one pull**: the child's seed set (the pull plus the BM.12 low-member
expansion) is capped by the pull cap plus the loop state's pivot-member cap. -/
theorem istep_seed_size (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') {cap : ℕ}
    (hcap : (Finset.univ.biUnion st.pl).card ≤ cap) :
    c.S.card ≤ pullCap t l + cap := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  rw [hc]
  have hsub : (Finset.univ.biUnion fun j =>
        if st.piv j ∈ Si ∧ st.piv j ∈ st.pl j then
          (st.pl j).filter (fun v => st.d v < Bi) else ∅) ⊆
      Finset.univ.biUnion st.pl := by
    intro x hx
    obtain ⟨j, _, hxj⟩ := Finset.mem_biUnion.mp hx
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ?_⟩
    split at hxj
    · exact (Finset.mem_filter.mp hxj).1
    · exact absurd hxj (by simp)
  have hmid : (Si ∪ Finset.univ.biUnion fun j =>
        if st.piv j ∈ Si ∧ st.piv j ∈ st.pl j then
          (st.pl j).filter (fun v => st.d v < Bi) else ∅).card ≤
      Si.card + cap := by
    have h1 : (Si ∪ Finset.univ.biUnion fun j =>
          if st.piv j ∈ Si ∧ st.piv j ∈ st.pl j then
            (st.pl j).filter (fun v => st.d v < Bi) else ∅).card ≤
        Si.card + (Finset.univ.biUnion fun j =>
          if st.piv j ∈ Si ∧ st.piv j ∈ st.pl j then
            (st.pl j).filter (fun v => st.d v < Bi) else ∅).card :=
      Finset.card_union_le _ _
    exact h1.trans (add_le_add le_rfl ((Finset.card_mono hsub).trans hcap))
  exact hmid.trans (add_le_add (pullRun_size hpull) le_rfl)

/-- **Lemma 3.5 through the loop**: every child call of the loop has its seed set capped by
the pull cap plus the loop state's (never-raised) pivot-member cap. -/
theorem iloop_children_seed_size (t : ℕ) (B : WLab G s) (l : ℕ) (cap : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (Finset.univ.biUnion st.pl).card ≤ cap →
      ∀ q ∈ qs, q.1.S.card ≤ pullCap t l + cap := by
  intro p st stf qs h
  induction h with
  | exit _h => exact fun _ q hq => absurd hq List.not_mem_nil
  | step _hne _hg hstep hrest ih =>
    intro hcap q hq
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq
      exact istep_seed_size t B l hstep hcap
    · exact ih (istep_bunion_pl_le t B l hstep hcap) q hq

/-- **Lemma 3.5, run form**: every child of a run has `|S_child| ≤ pullCap t l + fpCap t`
(Lemma 3.4's pull cap plus the FindPivots member cap `fpCap t` of BM.4/FIX-L13, never raised
by the loop). -/
theorem childOf_seed_size {t : ℕ} {e c : CallEntry G s} (hcd : ChildOf t e c) :
    c.S.card ≤ pullCap t e.l + fpCap t := by
  obtain ⟨out, p, fo, piv, st0, stf, qs, _hrun, _hout, _hl, hfp, _hpiv, hst0, hloop,
    _hchildren, q, hq, hqc⟩ := hcd
  have hcap : (Finset.univ.biUnion st0.pl).card ≤ fpCap t := by
    rw [hst0, mkInit_pl]
    exact (fpRun_contract _ _ hfp).2
  rw [← hqc]
  exact iloop_children_seed_size t _ _ (fpCap t) hloop hcap q hq

/-- The Lemma-3.5 arithmetic: for `t ≥ 2` (the `eventCap_lTop` regime), the pull cap plus the
member cap fits inside the child's `memCap` — `t·2^((l−1)t) + fpCap t ≤ t²·2^((l−1)t)`. -/
theorem pullCap_add_fpCap_le_memCap {t l : ℕ} (ht : 2 ≤ t) :
    pullCap t l + fpCap t ≤ memCap t (l - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  subst hk
  have hp : (1:ℕ) ≤ 2 ^ ((l - 1) * (k + 1)) := Nat.one_le_two_pow
  have hfp : fpCap (k + 1) ≤ k + 1 := max_le (by omega) (Nat.div_le_self _ _)
  have h1 : k + 1 ≤ k * (k + 1) := by
    calc k + 1 = (k + 1) * 1 := (Nat.mul_one _).symm
      _ ≤ (k + 1) * k := Nat.mul_le_mul_left _ (by omega)
      _ = k * (k + 1) := Nat.mul_comm _ _
  have h2 : fpCap (k + 1) ≤ (k + 1) * (k * 2 ^ ((l - 1) * (k + 1))) := by
    refine hfp.trans ?_
    calc k + 1 ≤ k * (k + 1) := h1
      _ ≤ (k * (k + 1)) * 2 ^ ((l - 1) * (k + 1)) := by
          have := Nat.mul_le_mul_left (k * (k + 1)) hp
          simpa using this
      _ = (k + 1) * (k * 2 ^ ((l - 1) * (k + 1))) := by ring
  unfold fpCap at h2 ⊢
  unfold pullCap memCap
  exact (add_le_add le_rfl h2).trans_eq (by ring)

end DMSY
end Frontier

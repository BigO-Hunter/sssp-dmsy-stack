import A4.Structural

/-!
# Frontier.DMSY.Transitive — the transitive proposition (bound validity, bottom-up)

Work package **A4 (BMSSP recursion)**, task key lemma 3.  CORRECTED_PROOF §4.1
(VARIANTS.md "Algorithm 3's contract, transitively"):

> Assume every leaf returns `d_B[𝒟] ≥ B'` (E1 gives this) and every child returns
> `d_B[𝒟_child] ≥ B'_child`.  Then Algorithm 3's own return satisfies `d_B[𝒟] ≥ B'`
> **except through Prem** (Lemma 3.7\*(2b)).

The proof enumerates what `𝒟` holds at return (CORRECTED_PROOF §4.1):

1. **leftovers never pulled** — the last pull's separator lower-bounds the remainder
   (`A3.pullRun_floor`) and `B' = B'_f ≤ B_f` (the bound law), so survivors are `≥ B'`;
   earlier low inserts cannot survive: some later pull consumes them (the pull takes *all*
   keys below its separator — `A3.pullRun`'s `belowKeys`);
2. **merged children** — the final child by hypothesis (`≥ B'_f`), earlier merges fall under 1;
3. **line-24 sweep inserts** — gated `≥ B_i ≥ B'_f` in the final iteration (E2);
4. **post-loop inserts (BM.25/28)** — gated `≥ B'` directly;
5. **line-29 re-selection inserts** — **ungated**, live only in the final iteration (earlier
   leaks are pulled later) — this is `Prem`.

Note the hypothesis shape: "every child returns `d_B[𝒟_child] ≥ B'_child`" is the child's
bound clause **without** a carve-out, i.e. Prem-free children.  That is exactly why the audit
proves `(2a ∧ 2b ∧ Prem = ∅)` as one joint first-violation induction (CORRECTED_PROOF §4.4) —
the transitive proposition is the bound half of that joint, and `A4.Main` states the joint
target.  Full executions need no line-29 appeal at all (`A4.Structural.full_no_prem`).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- The **bound clause** of the return `(B', U, 𝒟)` modulo the Q12 carve-out (Lemma 3.7\*(2b),
first half): every entry of `𝒟` has stored value `≥ B'`, except Prem entries. -/
def BoundClause (out : CallOut G s) : Prop :=
  ∀ y val, out.D y = some val → out.B' ≤ val ∨ out.Premature y val

/-- **Prem-free children** (the transitive proposition's hypothesis): every child of the run
returns with `d_B[𝒟_child] ≥ B'_child` unconditionally.  Proven for all children of every
reachable run by the joint induction (`A4.Main`); a child's own Prem entries are the only way
a sub-`B'` value can reach the parent's `𝒟` through a merge. -/
def BoundClauseStrict (out : CallOut G s) : Prop :=
  ∀ y val, out.D y = some val → out.B' ≤ val

def PremFreeChildren (t : ℕ) {e : CallEntry G s} {out : CallOut G s} (_h : Run t e out) : Prop :=
  ∀ (c : CallEntry G s) (co : CallOut G s), ChildOf t e c → Run t c co → BoundClauseStrict co

/-- **Transitive proposition** (CORRECTED_PROOF §4.1): bound validity propagates from the V5
leaves through the children to the call's return, modulo the final iteration's line-29 mints. -/
def TransitiveProp (t : ℕ) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s) (h : Run t e out),
    PremFreeChildren t h → BoundClause out

/-- The loop-state invariant behind the enumeration: after every iteration `i`, every entry of
the loop's `𝒟` has value `≥` the running bound `B'_i` or is one of *that* iteration's mints.
At loop exit the last iteration's mints are the call's `mints`; the tail's inserts are gated
`≥ B'` (BM.25/28) or mint-keyed keep-min no-ops. -/
def LoopBoundInv {p : ℕ} (st : RState G s p) : Prop :=
  ∀ y val, st.D y = some val → st.bp ≤ val ∨ Mint.mk y val ∈ st.mints


/-! ## `Ge` / `GOrM` preservation through the spine

`LoopBoundInv` is the keep-min invariant "every stored value is `≥ bp` or is one of the current
mints"; the preservation lemmas below are its mechanical half. -/

/-- Every stored value is at least `K`. -/
def Ge (K : WLab G s) (D : DS G s) : Prop := ∀ y val, D y = some val → K ≤ val

/-- Every stored value is at least `K` or is a recorded mint. -/
def GOrM (K : WLab G s) (D : DS G s) (ms : List (Mint G s)) : Prop :=
  ∀ y val, D y = some val → K ≤ val ∨ Mint.mk y val ∈ ms

theorem ge_of_le {K K' : WLab G s} {D : DS G s} (h : K' ≤ K) (hD : Ge K D) : Ge K' D :=
  fun y val hy => h.trans (hD y val hy)

theorem ge_merge {K : WLab G s} {D₁ D₂ : DS G s} (h₁ : Ge K D₁) (h₂ : Ge K D₂) :
    Ge K (DS.merge D₁ D₂) := by
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

/-- One (E2)-gated insert keeps `GOrM`: the new value is `≥ lo ≥ K` or a recorded mint, and
keep-min with an old `GOrM` value stays `GOrM`. -/
theorem gOrM_insert {K : WLab G s} {D : DS G s} {ms : List (Mint G s)} {z : Fin G.n}
    {v : WLab G s} (h : GOrM K D ms) (hv : K ≤ v ∨ Mint.mk z v ∈ ms) :
    GOrM K (DS.insert D z v) ms := by
  intro y val hy
  by_cases hyz : y = z
  · subst hyz
    rw [DS.insert_self] at hy
    cases hD : D y with
    | none =>
      rw [hD, DS.mergeVal_none_left] at hy
      rw [← Option.some.inj hy]
      exact hv
    | some μ =>
      rw [hD, DS.mergeVal_some] at hy
      rw [← Option.some.inj hy]
      rcases h y μ hD with hμ | hμ
      · rcases le_total μ v with hmv | hmv
        · rw [min_eq_left hmv]; exact Or.inl hμ
        · rw [min_eq_right hmv]; exact hv
      · rcases le_total μ v with hmv | hmv
        · rw [min_eq_left hmv]; exact Or.inr hμ
        · rw [min_eq_right hmv]; exact hv
  · rw [DS.insert_of_ne D z v hyz] at hy
    exact h y val hy

theorem gOrM_relaxGate {K B lo : WLab G s} {d : Labels G s} {D : DS G s} {ms : List (Mint G s)}
    {e : Fin G.m} (h : GOrM K D ms) (hlo : K ≤ lo) :
    GOrM K (relaxGate B lo d D e).2 ms := by
  intro y val
  unfold relaxGate
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos hc]
    intro hy
    exact gOrM_insert h (Or.inl (hlo.trans hc.1)) y val hy
  · rw [if_neg hc]
    exact h y val

theorem gOrM_sweepGate {K B lo : WLab G s} (u : Fin G.n) (es : List (Fin G.m))
    {ms : List (Mint G s)} : ∀ (d : Labels G s) (D : DS G s), GOrM K D ms → K ≤ lo →
      GOrM K (sweepGate B lo u es d D).2 ms := by
  induction es with
  | nil => intro d D h _; exact h
  | cons e es ih =>
    intro d D h hlo
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (gOrM_relaxGate h hlo) hlo
    · rw [if_neg hs, if_neg hs]
      exact ih d D h hlo

theorem gOrM_sweepEvts {K B lo : WLab G s} {ms : List (Mint G s)}
    (evts : List (SettlementEvent G)) :
    ∀ (d : Labels G s) (D : DS G s), GOrM K D ms → K ≤ lo →
      GOrM K (sweepEvts B lo evts d D).2 ms := by
  induction evts with
  | nil => intro d D h _; exact h
  | cons ev evts ih =>
    intro d D h hlo
    unfold sweepEvts
    exact ih _ _ (gOrM_sweepGate ev.v (List.finRange G.m) d D h hlo) hlo

theorem gOrM_seedIns {K bp B : WLab G s} {S : Finset (Fin G.n)} {ms : List (Mint G s)} :
    ∀ (d : Labels G s) (D : DS G s), GOrM K D ms → K ≤ bp →
      GOrM K (seedIns bp B S d D).2 ms := by
  intro d D
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => intro h _; exact h
  | cons x xs ih =>
    intro h hbp
    rw [List.foldl_cons]
    by_cases hg : bp ≤ d x ∧ d x < B
    · rw [if_pos hg]
      exact ih d (DS.insert D x (d x)) (gOrM_insert h (Or.inl (hbp.trans hg.1))) hbp
    · rw [if_neg hg]
      exact ih d D h hbp

theorem gOrM_fold_insert {ι : Type} {K : WLab G s} (js : List ι) (f : ι → Fin G.n)
    (g : ι → WLab G s) (ms : List (Mint G s)) :
    ∀ (D0 : DS G s), GOrM K D0 ms → (∀ j ∈ js, Mint.mk (f j) (g j) ∈ ms) →
      GOrM K (js.foldl (fun D j => DS.insert D (f j) (g j)) D0) ms := by
  intro D0
  induction js generalizing D0 with
  | nil => intro h _; exact h
  | cons j0 js ih =>
    intro h hm
    rw [List.foldl_cons]
    refine ih (DS.insert D0 (f j0) (g j0))
      (gOrM_insert h (Or.inr (hm j0 List.mem_cons_self))) ?_
    intro j hj
    exact hm j (List.mem_cons_of_mem _ hj)

theorem initD'_keys {p : ℕ} (d : Labels G s) (piv : Fin p → Fin G.n) :
    ∀ (D0 : DS G s), (∀ y val, D0 y = some val → ∃ j, y = piv j) →
      ∀ y val, ((List.finRange p).foldl (fun D j => DS.insert D (piv j) (d (piv j))) D0) y
        = some val → ∃ j, y = piv j := by
  intro D0
  induction (List.finRange p) generalizing D0 with
  | nil => exact fun hd y val hy => hd y val hy
  | cons j0 js ih =>
    intro hd y val hy
    rw [List.foldl_cons] at hy
    refine ih (DS.insert D0 (piv j0) (d (piv j0))) ?_ y val hy
    intro y val hy'
    by_cases hyz : y = piv j0
    · exact ⟨j0, hyz⟩
    · rw [DS.insert_of_ne D0 (piv j0) (d (piv j0)) hyz] at hy'
      exact hd y val hy'

/-- `LoopBoundInv` at the loop's initial state: the seed inserts carry entry labels, and
`initBp` is a lower bound for each of them. -/
theorem loopBoundInv_init (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n) :
    LoopBoundInv (mkInit e fo piv) := by
  intro y val hy
  have hval : val = fo.d' y := initD'_fresh _ _ _ _ hy
  obtain ⟨j, hj⟩ := initD'_keys fo.d' piv DS.empty
    (fun y val hy => absurd hy (Ne.symm (Option.some_ne_none val))) y val hy
  left
  rw [hval, hj]
  exact initBp_le _ _ _ _

/-- The loop preserves `LoopBoundInv` — the mechanical half of the enumeration: the pull floor
(`A3.pullRun_floor`, `B_i ≥ B'_i` by the child's bound law), the child's bound clause
(hypothesis — Prem-free children), the sweep gates (E2) and the (E0)-guarded mints.  Note the
invariant is exact: old iteration-i mints with value below `B'_{i+1}` cannot survive the next
pull (survival needs `val ≥ B_{i+1} ≥ B'_{i+1}`), so the only sub-`bp` entries at any step are
the *fresh* mints — which is precisely the Q12 carve-out's final-iteration form. -/
theorem loopBoundInv_istep (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hble : fo'.B' ≤ c.B)
    (hchild : ∀ y val, fo'.D y = some val → fo'.B' ≤ val) (hinv : LoopBoundInv st) :
    LoopBoundInv st' := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hK : fo'.B' ≤ Bi := by
    rw [hc] at hble
    exact hble
  have hD2 : Ge fo'.B' D2 := by
    rw [hmerge]
    exact deleteSet_some_imp (settledFinset fo')
      (ge_merge (ge_of_le hK (fun y val hy => pullRun_floor hpull hy)) hchild)
  have hD3 : GOrM fo'.B' D3 (J.toList.map fun j => Mint.mk (sel j) (d3 (sel j))) := by
    have hd3 : D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 := by rw [← hsweep]
    rw [hd3]
    exact gOrM_sweepEvts fo'.evts fo'.d' D2
      (fun y val hy => Or.inl (hD2 y val hy)) hK
  refine gOrM_fold_insert J.toList sel (fun j => d3 (sel j))
    (J.toList.map fun j => Mint.mk (sel j) (d3 (sel j))) D3 hD3
    (fun j hj => List.mem_map_of_mem hj)

theorem loopBoundInv_loop (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, q.2.B' ≤ q.1.B ∧ ∀ y val, q.2.D y = some val → q.2.B' ≤ val) →
      LoopBoundInv st → LoopBoundInv stf := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ hinv => hinv
  | step hne hg hstep hrest ih =>
    intro hchild hinv
    exact ih (fun q hq => hchild q (List.mem_cons_of_mem _ hq))
      (loopBoundInv_istep (G := G) (s := s) t B l hstep (hchild _ List.mem_cons_self).1
        (fun y val hy => (hchild _ List.mem_cons_self).2 y val hy) hinv)

theorem tailBP_of_isEmpty (B : WLab G s) {p : ℕ} (st : RState G s p)
    (h : DS.IsEmpty st.D) : tailBP B st = B := by
  unfold tailBP
  rw [if_pos h]

theorem tailBP_of_not_isEmpty (B : WLab G s) {p : ℕ} (st : RState G s p)
    (h : ¬ DS.IsEmpty st.D) : tailBP B st = st.bp := by
  unfold tailBP
  rw [if_neg h]

/-- The tail's return satisfies the bound clause modulo the mint carve-out, given `LoopBoundInv`
at the loop's exit: `seedIns` and the (E2)-gated `W'` sweep insert only values `≥ tailBP`, so
keep-min either keeps such a value or a recorded mint. -/
theorem tail_boundClause (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hinv : LoopBoundInv st) :
    ∀ y val, (tail B S W st).D y = some val →
      (tail B S W st).bp ≤ val ∨ (Mint.mk y val ∈ st.mints ∧ val < (tail B S W st).bp) := by
  have hK : GOrM (tailBP B st) st.D st.mints := by
    by_cases hemp : DS.IsEmpty st.D
    · intro y val hy
      rw [hemp y] at hy
      exact absurd hy (Ne.symm (Option.some_ne_none val))
    · rw [tailBP_of_not_isEmpty B st hemp]
      exact hinv
  have hchain : GOrM (tailBP B st) (tail B S W st).D st.mints :=
    gOrM_sweepEvts _ _ _ (gOrM_seedIns _ _ hK le_rfl) le_rfl
  intro y val hy
  rcases hchain y val hy with h2 | h2
  · exact Or.inl h2
  · by_cases hlt : val < tailBP B st
    · exact Or.inr ⟨h2, hlt⟩
    · exact Or.inl (not_lt.mp hlt)

/-- `ChildOf` from one recurrence's own decomposition: the tied form is exactly what this
constructor builds — the `Run` witness *is* the `recur` conclusion at the given components, and
the loop's child returns are the derivation's own `hchildren`. -/
theorem childOf_of_recur (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hl : 0 < e.l) (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
    (hst0 : st0 = mkInit e fo piv) (hloop : ILoop t e.B e.l st0 qs stf)
    (hchildren : ∀ q ∈ qs, Run t q.1 q.2) {q : CallEntry G s × CallOut G s} (hq : q ∈ qs) :
    ChildOf t e q.1 :=
  ⟨callOut (tail e.B e.S fo.W stf), fo.p, fo, piv, st0, stf, qs,
    @Run.recur G s t e fo.p fo piv st0 stf qs hl hfp hpiv hst0 hloop hchildren,
    rfl, hl, hfp, hpiv, hst0, hloop, hchildren, ⟨q, hq, rfl⟩⟩

theorem transitive_prop (t : ℕ) (G : Graph) (s : Fin G.n) : @TransitiveProp G s t := by
  intro e out h
  induction h with
  | base hl hb =>
    intro hprem
    obtain ⟨c, st, hloop, hr⟩ := hb
    subst hr
    intro y val hy
    exact Or.inl ((min_le_right _ _).trans (dMin_le_of_mem _ hy))
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro hprem
    refine tail_boundClause _ _ _ _ ?_
    refine loopBoundInv_loop t _ _ hloop
      (fun q hq => ⟨run_le_bound t (hchildren q hq),
        hprem _ _ (childOf_of_recur t hl hfp hpiv hst0 hloop hchildren hq) (hchildren q hq)⟩) ?_
    rw [hst0]
    exact loopBoundInv_init _ _ _

end DMSY
end Frontier

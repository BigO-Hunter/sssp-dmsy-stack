import A4.Structural

/-!
# Frontier.DMSY.ReachHyp — does `Reach` imply `Lemma37Hyp`?

**No.** This file pins the exact boundary and the reduced forms that *do* hold.  The question
matters because `A4.Main.theoremT` is blocked on deriving `Lemma37Hyp t e` from `Reach t e`
to feed `a4_joint`.  Under the current definitions that derivation is impossible, for three
independent reasons:

1. **Level (`0 < e.l`)** — `Reach` includes base entries (`l = 0`): the top entry has
   `l = lTop t G.n` (which is `0` for small `n`), and a child has `c.l = e.l - 1` (so a
   level-`1` parent produces a level-`0` child).  `Lemma37Hyp`'s first clause is a *recur-case*
   hypothesis; it is false on reachable base entries.  Theorem T's `l = 0` case is nonetheless
   vacuous (`baseOut.mints = []`), proved below as `base_no_prem`.
2. **Size (`e.S.card ≤ memCap t e.l`)** — needs `0 < t` at the top and `2 ≤ t` at children.
   At `t = 0`, `memCap 0 l = 0` while the reachable top entry has `|S| = 1`, so the clause is
   **false** (`reach_zero_not_implies_lemma37Hyp`).  At `t = 1` the Lemma-3.5 bound
   `pullCap + fpCap` strictly exceeds the child `memCap` (`pullCap_add_fpCap_gt_memCap_at_one`),
   so the clause is unprovable from the available bound.  With `2 ≤ t` it *is* derivable
   (`lemma37Hyp_child`).
3. **Frontier** — free at the top (`isFrontier_init`), but for a child it is exactly
   `A4.Structural.istep_child_frontier`'s conclusion, which needs the parent loop-state frontier
   plus the coverage and (J6) witnesses — the joint chain's clause-(1) invariant, absent from
   `ChildOf`/`Reach`.  This is the one genuine gap: it is *not* a missing boundary case, it is
   the content of `a4_joint`.

**Conclusion for `theoremT`.**  The statement is mathematically supportable (it is the audit's
Theorem T, one half of the joint first-violation induction).  It is **not** derivable from `Reach`
via `Lemma37Hyp`; the correct discharge is: (a) base entries by `base_no_prem`, (b) recur entries
by `a4_joint` with the frontier/size invariants carried by the induction (equivalently, a
`Reach`-strengthening that inductively carries `IsFrontier`/`memCap`), not by a
`lemma37Hyp_of_reach`.  The reduced forms that compile are below.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Negative result: `Reach` does not imply `Lemma37Hyp` -/

theorem reachHyp_memCap_zero (l : ℕ) : memCap 0 l = 0 := by
  unfold memCap
  norm_num

/-- Counterexample at `t = 0`: the reachable top entry has `|S| = 1 > 0 = memCap 0 (lTop 0 n)`,
so the size clause of `Lemma37Hyp` fails and `Reach 0 → Lemma37Hyp 0` is false (for every graph). -/
theorem reach_zero_not_implies_lemma37Hyp :
    ¬ (∀ e : CallEntry G s, Reach (t := 0) e → Lemma37Hyp 0 e) := by
  intro h
  have htop : Reach (t := 0) ⟨(⊤ : WLab G s), {s}, lTop 0 G.n, initLabels G s⟩ := Reach.top
  have hle : ({s} : Finset (Fin G.n)).card ≤ memCap 0 (lTop 0 G.n) := (h _ htop).2.2
  rw [reachHyp_memCap_zero] at hle
  rw [Finset.card_singleton] at hle
  omega

/-- At `t = 1` the Lemma-3.5 bound `pullCap + fpCap` strictly exceeds the child `memCap`
(`2^(l-1) + 1 > 2^(l-1)`), so the child size clause is unprovable from the available bound
without `2 ≤ t` (`pullCap_add_fpCap_le_memCap` is sharp). -/
theorem pullCap_add_fpCap_gt_memCap_at_one (l : ℕ) :
    memCap 1 (l - 1) < pullCap 1 l + fpCap 1 := by
  unfold memCap pullCap fpCap
  norm_num

/-! ## Positive reduced forms -/

theorem reachHyp_dis_source : dis (s := s) s = ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) := by
  rw [dis_of_reachable (⟨[], IsWalk.nil s⟩ : G.Reachable s s), path_source]

theorem reachHyp_initLabels_source : initLabels G s s = dis (s := s) s := by
  rw [reachHyp_dis_source]
  simp [initLabels]

theorem reachHyp_one_le_memCap {t l : ℕ} (ht : 0 < t) : 1 ≤ memCap t l := by
  unfold memCap
  have h2 : 0 < t ^ 2 := pow_pos ht 2
  have h3 : 0 < 2 ^ (l * t) := pow_pos (by norm_num) (l * t)
  have h4 : 0 < t ^ 2 * 2 ^ (l * t) := mul_pos h2 h3
  omega

/-- The top entry satisfies `Lemma37Hyp` under `0 < t` (size) and `0 < lTop t G.n` (level);
the frontier clause is `isFrontier_init`. -/
theorem lemma37Hyp_top (t : ℕ) (ht : 0 < t) (hl : 0 < lTop t G.n) :
    Lemma37Hyp t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ := by
  refine ⟨hl, ?_, ?_⟩
  · rw [Finset.coe_singleton]
    exact isFrontier_init reachHyp_initLabels_source
  · rw [Finset.card_singleton]
    exact reachHyp_one_le_memCap ht

/-! ## The child size clause follows from `2 ≤ t` (level drop + Lemma 3.5 arithmetic) -/

theorem reachHyp_istep_children_level {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') : c.l = l - 1 := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel, hst'⟩ := h
  rw [hc]

theorem reachHyp_iloop_children_level (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      ∀ q ∈ qs, q.1.l = l - 1 := by
  intro p st stf qs h
  induction h with
  | exit h => intro q hq; exact absurd hq List.not_mem_nil
  | step hne hg hstep hrest ih =>
    intro q' hq'
    rcases List.mem_cons.mp hq' with hq | hq
    · subst hq
      exact reachHyp_istep_children_level hstep
    · exact ih q' hq

/-- **Reduced child `Lemma37Hyp`**: the size clause is Lemma 3.5 (level drop + `pullCap`/`fpCap`
arithmetic, sharp at `2 ≤ t`); only the frontier clause needs to be supplied (it is the joint
chain's clause-(1) invariant, not derivable from `ChildOf` alone). -/
theorem lemma37Hyp_child (t : ℕ) {e c : CallEntry G s} (hcd : ChildOf t e c) (ht : 2 ≤ t)
    (hl : 0 < c.l)
    (hfrontier : IsFrontier c.d (Utilde c.B (c.S : Set (Fin G.n))) ∅ (c.S : Set (Fin G.n))) :
    Lemma37Hyp t c := by
  refine ⟨hl, hfrontier, ?_⟩
  have hsize := childOf_seed_size hcd
  obtain ⟨out, p, fo, piv, st0, stf, qs, _hrun, _hout, _hl, _hfp, _hpiv, _hst0, hloop,
    _hchildren, q, hq, hqc⟩ := hcd
  have hlev : c.l = e.l - 1 := by
    rw [← hqc]
    exact reachHyp_iloop_children_level t e.B e.l hloop q hq
  rw [hlev]
  exact hsize.trans (pullCap_add_fpCap_le_memCap ht)

/-! ## The `l = 0` case of Theorem T is vacuous -/

/-- Base-case returns have no mints, so `Premature` is empty — the `l = 0` half of Theorem T. -/
theorem base_no_prem (t : ℕ) {e : CallEntry G s} {bout : BaseOut G s}
    (_hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    ∀ x val, ¬ (baseOut bout).Premature x val := by
  intro x val hp
  exact absurd hp.1 List.not_mem_nil

end DMSY
end Frontier

import A4.BelowSeparator

/-!
# Frontier.DMSY.LeafFloor — the SSSP leaf case for `ChildFloor`

`A4.BelowSeparator.ChildFloor` is the recursion's inductive premise; its base leaves are
`Run.base` calls (`c.l = 0`, A1's `baseRun`).  Findings, against the actual A1 semantics:

* **Clause (1)** (every settlement complete at the return labels) is unconditional —
  `A1.BaseCorrect.baseRun_lemma31.settleComplete` is exactly it.
* **Clause (2)** (the refusal floor, gated `< c.B`) is **false** for capped base exits.  The
  A1 loop may stop on the (E3) event cap `t³` with `𝒟 ≠ ∅`; vertices in the band
  `(B'⁺, c.B)` are then abandoned with stale labels, and an edge out of a settled vertex can
  carry a candidate there.  Concrete counterexample (`t = 1`, `t³ = 1`): vertices `s u q p z`,
  edges `s→u (1)`, `s→q (5)`, `q→p (1)`, `p→z (1)`, `u→z (10)`, `B = 100`, `S = {s}`,
  `initLabels`.  This entry satisfies `CallPre`.  Valid loop: pull `s` (sweeps keys `u:1`,
  `q:5`), then pull `u` (separator `x = 5` over `{u:1, q:5}`; sweep `u→z`: candidate `11`,
  accepted, key `z:11`), then `|U| = 2 > 1 = t³` exits with `𝒟 = {q:5, z:11} ≠ ∅`.  `u` is
  settled and `ext (d u, u→z) = 11 < 100 = c.B`, yet `d z = 11 ≠ dis z = 7` — clause (2)
  fails, while every clause of Lemma 3.1\* still holds (`B'⁺ = 5`, `U = Ũ(5, {s}) = {s, u}`).
* **The precise missing leaf invariant** is the leaf's return bound reaching its own entry
  bound: `c.B ≤ bout.B'_plus` — with equality on full executions (`DS.IsEmpty bout.D_final`,
  by Lemma 3.1\*'s dichotomy).  Under it the below-separator gate lands inside the region
  Lemma 3.1\* actually covers, and `ChildFloor` follows from `baseRun_lemma31` (identity +
  settleComplete + cap law), Claim C of the final `BInv` state, and
  `dis_le_cand_of_settled`.  Unconditionally, the maximal provable statement is the
  `B'⁺`-truncated floor `base_floor_cap` below.

No `sorry`/`admit`/new axioms; `a4_joint` is not assumed.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The capped refusal floor (unconditional) -/

/-- **The `B'⁺`-truncated refusal floor at a base leaf.**  An edge out of a settled vertex
whose candidate is below the leaf's *returned* bound `B'_plus` has a complete head.  This is
the maximal refusal-floor statement the A1 base semantics supports: the proof rides on
`baseRun_lemma31`'s settlement identity (`U = Ũ(B'⁺, S)`), settlement completeness, and the
cap law (`B'⁺ ≤ dMin ≤ B`), plus Claim C of the final loop state and
`dis_le_cand_of_settled`. -/
theorem base_floor_cap {t : ℕ} {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    {bout : BaseOut G s} (hpre : CallPre B S d)
    (hrun : baseRun t ⟨B, S, d, initD S d⟩ bout) :
    ∀ e, G.src e ∈ settledSet bout.evts → ext (bout.d' (G.src e)) e < bout.B'_plus →
      Complete bout.d' (G.dst e) := by
  have hre : ReachBase ⟨B, S, d, initD S d⟩ := ⟨hpre, rfl⟩
  have hlem := baseRun_lemma31 hre hrun
  have hBple : bout.B'_plus ≤ B := hlem.bound.trans (dMin_le_bound B bout.D_final)
  have hUeq : settledSet bout.evts = Utilde bout.B'_plus (S : Set (Fin G.n)) := hlem.identity
  obtain ⟨_cst, st, hloop, hrout⟩ := hrun
  have hdeq : bout.d' = st.d := by rw [hrout]
  have hB : BInv B S st := loop_bInv hloop (bInv_init hre)
  intro e hu hlt
  obtain ⟨ev, hev, hv⟩ := hu
  have hcu : Complete bout.d' (G.src e) := by
    rw [← hv]; exact hlem.settleComplete ev hev
  have hdis : bout.d' (G.src e) = dis (s := s) (G.src e) := complete_iff.mp hcu
  have hlt' : dis (s := s) (G.src e) < bout.B'_plus := by
    rw [← hdis]
    refine lt_of_le_of_lt ?_ hlt
    by_cases htop : bout.d' (G.src e) = ⊤
    · rw [htop, ext_top]
    · exact le_of_lt (lt_ext_of_ne_top htop e)
  have hreach : G.Reachable s (G.src e) :=
    reachable_of_dis_lt (lt_of_lt_of_le hlt' hBple)
  have hcand : dis (s := s) (G.dst e) ≤ ext (bout.d' (G.src e)) e :=
    dis_le_cand_of_settled hcu hreach rfl
  have hdz : dis (s := s) (G.dst e) < bout.B'_plus := lt_of_le_of_lt hcand hlt
  by_cases hzU : G.dst e ∈ Utilde B (S : Set (Fin G.n))
  · -- below `B'⁺` and in `Ũ(B, S)` ⇒ in `Ũ(B'⁺, S) = U` ⇒ settled ⇒ complete
    have hzU' : G.dst e ∈ Utilde bout.B'_plus (S : Set (Fin G.n)) :=
      ⟨hdz, hzU.2⟩
    rw [← hUeq] at hzU'
    obtain ⟨ev', hev', hv'⟩ := hzU'
    rw [← hv']
    exact hlem.settleComplete ev' hev'
  · -- outside `Ũ(B, S)` but below `B`: Claim C completes it
    rw [hdeq]
    exact hB.claim (G.dst e) (lt_of_lt_of_le hdz hBple) hzU

/-! ## The leaf: `ChildFloor` when the return bound reaches the entry bound -/

/-- **`childFloor_base` — the SSSP leaf case.**  A base leaf (`c.l = 0`, A1's `baseRun`,
shaped exactly as `Run.base`'s premise) satisfies `ChildFloor` **provided the leaf's return
bound reaches its own entry bound**: `c.B ≤ bout.B'_plus`.  On a full execution (loop exit
with `𝒟` drained) this holds with equality by Lemma 3.1\*'s dichotomy, so
`childFloor_base_of_full` is the instance the recursion consumes; without it the statement is
false (see the module docstring's capped-exit counterexample).  This hypothesis is the
precise missing leaf invariant. -/
theorem childFloor_base {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d) (_hl : c.l = 0)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hB : c.B ≤ bout.B'_plus) :
    ChildFloor c (baseOut bout) := by
  have hlem := baseRun_lemma31 (⟨hpre, rfl⟩ : ReachBase ⟨c.B, c.S, c.d, initD c.S c.d⟩) hb
  refine ⟨fun ev hev => hlem.settleComplete ev hev, fun e hu hlt => ?_⟩
  exact base_floor_cap hpre hb e hu (lt_of_lt_of_le hlt hB)

/-- **The recursion-friendly instance**: a **full** base leaf (loop exit with `𝒟` drained)
delivers `ChildFloor` outright — Lemma 3.1\*'s dichotomy gives `B'_plus = c.B`.  Stated on the
`baseRun` components (`Run.base`'s own premises, `hl`/`hb`), so a caller holding a `Run.base`
derivation passes them directly; no `Run` inversion needed. -/
theorem childFloor_base_of_full {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d) (hl : c.l = 0)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hfull : DS.IsEmpty bout.D_final) :
    ChildFloor c (baseOut bout) :=
  childFloor_base hpre hl hb (by
    show c.B ≤ bout.B'_plus
    have hlem := baseRun_lemma31 (⟨hpre, rfl⟩ : ReachBase ⟨c.B, c.S, c.d, initD c.S c.d⟩) hb
    rw [hlem.dichotomy.mpr hfull])

#print axioms Frontier.DMSY.base_floor_cap
#print axioms Frontier.DMSY.childFloor_base
#print axioms Frontier.DMSY.childFloor_base_of_full

end DMSY
end Frontier

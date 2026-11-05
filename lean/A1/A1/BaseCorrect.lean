import A1.BaseInv
import Frontier.DMSY.Interfaces

/-!
# Frontier.DMSY (A1) — corrected Lemma 3.1* (base case with the V5 cap)

Work package **A1**.  The four clauses of CORRECTED_PROOF §4.1, assembled from the loop
invariant (`A1.BaseInv`) and packaged as `Lemma31Concl` (A0's statement), plus the `A1`
interface theorem `A1Contract`.

1. **Bound clause** (`d_B[𝒟] ≥ B'⁺`): by construction of the cap — `B'⁺ = min(B'_pull, d_B[𝒟])`
   is below `d_B[𝒟]`, hence below every stored value.
2. **Every settled label `< B'⁺`** (`max dis(U) < B'⁺`): pulls are non-decreasing (the separator
   strictly exceeds the pulled label), every insert strictly grows the label tuple ((O3) strict
   growth), so all settled labels sit below the final separator and the final `d_B[𝒟]`.
3. **Completeness up to `B'⁺`** (`U = Ũ(B'⁺, S)` complete): `Ũ ⊆ U` by the exit frontier
   squeeze (a key below `B'⁺` would contradict the bound clause); `U ⊆ Ũ` by key containment
   and settled completeness.
4. **Full-execution dichotomy** `B'⁺ = B ⟺ 𝒟 = ∅`: the cap against (I4) (`𝒟` entries `< B`).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## `dMin` from below -/

/-- A strict lower bound on every stored value is a lower bound on `dMinAux`. -/
theorem lt_dMinAux (D : DS G s) (i : ℕ) (x : WLab G s) (hx : x < ⊤)
    (h : ∀ y lam, D y = some lam → x < lam) : x < dMinAux D i := by
  induction i with
  | zero => exact hx
  | succ i ih =>
    show x < min ((if h : i < G.n then D ⟨i, h⟩ else none).getD ⊤) (dMinAux D i)
    refine lt_min ?_ ih
    by_cases hi : i < G.n
    · have h2 : ((if h : i < G.n then D ⟨i, h⟩ else none).getD ⊤)
          = (D ⟨i, hi⟩).getD ⊤ := by
        rw [dif_pos hi]
      rw [h2]
      cases hd : D ⟨i, hi⟩ with
      | none => rw [Option.getD]; exact hx
      | some ρ => rw [Option.getD]; exact h ⟨i, hi⟩ ρ hd
    · have h2 : ((if h : i < G.n then D ⟨i, h⟩ else none).getD ⊤) = (⊤ : WLab G s) := by
        rw [dif_neg hi, Option.getD]
      rw [h2]
      exact hx

/-- A strict lower bound below `B` and below every stored value is below `d_B[𝒟]`. -/
theorem lt_dMin (B : WLab G s) {D : DS G s} (x : WLab G s) (hxB : x < B)
    (h : ∀ y lam, D y = some lam → x < lam) : x < dMin B D :=
  lt_min hxB (lt_dMinAux D G.n x (lt_of_lt_of_le hxB le_top) h)

/-! ## The four clauses -/

/-- **Corrected Lemma 3.1\*** (CORRECTED_PROOF §4.1) for the Algorithm-4 base case with the
(E1) V5 cap: every reachable base-case run satisfies `Lemma31Concl`. -/
theorem baseRun_lemma31 {t : ℕ} {e : BaseIn G s} {out : BaseOut G s}
    (hre : ReachBase e) (hr : baseRun t e out) : Lemma31Concl e out := by
  obtain ⟨c, st, hloop, hrout⟩ := hr
  have hB : BInv e.B e.S st := loop_bInv hloop (bInv_init hre)
  have hBplus : out.B'_plus = st.x ⊓ dMin e.B st.D := by rw [hrout]
  have hBpull : out.B'_pull = st.x := by rw [hrout]
  have hU : out.U = settledSet st.evts := by rw [hrout]; rfl
  have hD : out.D_final = st.D := by rw [hrout]
  have hEvts : out.evts = st.evts := by rw [hrout]
  have hd' : out.d' = st.d := by rw [hrout]
  -- settled labels are below the returned bound
  have hlt_out : ∀ y ∈ settledSet st.evts,
      st.d y < st.x ⊓ dMin e.B st.D := by
    intro y hy
    refine lt_min (hB.sep y hy) (lt_dMin e.B (st.d y) ?_ (hB.vals y hy))
    exact lt_of_lt_of_le (hB.sep y hy) hB.xle
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (E1): `B'⁺ = min(B'_pull, d_B[𝒟])`
    show out.B'_plus = min out.B'_pull (dMin e.B out.D_final)
    rw [hBplus, hBpull, hD]
  · -- `U = Ũ(B'⁺, S)`
    rw [hU, hBplus]
    ext y
    constructor
    · intro hy
      have hc : Complete st.d y := hB.settledComplete y hy
      have hdis : dis (s := s) y = st.d y := (complete_iff.mp hc).symm
      have hyU : y ∈ Utilde e.B (e.S : Set (Fin G.n)) := hB.settledU hy
      refine ⟨?_, hyU.2⟩
      rw [hdis]
      exact hlt_out y hy
    · rintro ⟨hdis, y₀, hy₀S, hy₀U⟩
      -- exit-frontier squeeze: a `𝒟` key cannot sit below `B'⁺`
      have hltB : dis (s := s) y < e.B :=
        lt_of_lt_of_le hdis (le_trans (min_le_left st.x (dMin e.B st.D)) hB.xle)
      rcases hB.frontier y ⟨hltB, y₀, hy₀S, hy₀U⟩ with h | ⟨z, hzK, hcz, hzv⟩
      · exact h.1
      · obtain ⟨lam, hlamD⟩ := Option.ne_none_iff_exists'.mp hzK
        have hlam : lam = st.d z := hB.fresh z lam hlamD
        have hbound : st.x ⊓ dMin e.B st.D ≤ lam :=
          le_trans (min_le_right st.x (dMin e.B st.D)) (dMin_le_of_mem e.B hlamD)
        have hcz' : st.d z = dis (s := s) z := complete_iff.mp hcz
        rw [hlam, hcz'] at hbound
        have h1 : dis (s := s) y < dis (s := s) z := lt_of_lt_of_le hdis hbound
        exact absurd h1 (not_lt.mpr hzv.dis_le)
  · -- every settlement event settles a complete vertex
    intro ev hev
    rw [hd']
    exact hB.settledComplete ev.v ⟨ev, by rw [← hEvts]; exact hev, rfl⟩
  · -- `max dis(U) < B'⁺`
    intro y hy
    have hc : Complete st.d y := hB.settledComplete y (by rw [← hU]; exact hy)
    rw [← complete_iff.mp hc, hBplus]
    exact hlt_out y (by rw [← hU]; exact hy)
  · -- `d_B[𝒟] ≥ B'⁺` (by construction of the cap)
    rw [hBplus, hD]
    exact min_le_right _ _
  · -- full-execution dichotomy `B'⁺ = B ⟺ 𝒟 = ∅`
    rw [hBplus, hD]
    constructor
    · intro hBplus' y
      by_contra hnn
      obtain ⟨lam, hlamD⟩ := Option.ne_none_iff_exists'.mp hnn
      have h1 : e.B ≤ lam :=
        (le_inf_iff.mp hBplus'.ge).2.trans (dMin_le_of_mem e.B hlamD)
      exact absurd h1 (not_le.mpr (hB.below y lam hlamD))
    · intro hemp
      have hxe : st.x = e.B := by
        rcases hB.xroot with hxe | hne
        · exact hxe
        · obtain ⟨y, hy⟩ := hne
          exact absurd hy (fun h2 => h2 (hemp y))
      rw [hxe, dMin_eq_of_isEmpty e.B hemp]
      exact min_self e.B

/-- **A1 interface theorem**: Algorithm 4 with the (E1) V5 cap discharges `A1Contract`. -/
theorem a1_contract (t : ℕ) : @A1Contract G s ReachBase (baseRun t) :=
  fun e out hre hr => baseRun_lemma31 hre hr

end DMSY
end Frontier

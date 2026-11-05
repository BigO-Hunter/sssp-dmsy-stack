import Frontier.DMSY.State
import Mathlib.Data.Nat.Log

/-!
# Frontier.DMSY.Engine — the corrected engine's constants and deltas (E0)–(E3)

Work package **A0 (interface)**.  Pins the constants and predicates of the corrected
Duan–Mao–Shu–Yin engine (CORRECTED_PROOF.md §2), before any semantics is written in A1–A4:

* **(E1) V5, the leaf cap** — `B'⁺ = min(B'_pull, d_B[𝒟_final])` (fixes Q3).  *This is the V5 cap
  constant the lane correction list asks to pin before A1 is written.*
* (E0) nonempty-argmin guards (the printed pseudocode crashes on empty `P_j`);
* (E2) line-23 sweep semantics (prose reading: relax only candidates in `[B_i, B)`);
* (E3) `U` as settlement **log**; line-9 guard compares event counts;
* the Q12 premature-entry shape (S1/S2) of the carve-out;
* parameter bookkeeping: `|S| ≤ t²·2^(lt)` member cap, `t³·2^(lt)` event ceiling,
  `l_top = ⌈log₂ n / t⌉`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Parameter bookkeeping (CORRECTED_PROOF §1, §2.2) -/

/-- FindPivots / Lemma 3.7* member cap `K = t²·2^(l·t)` (hypothesis `|S| ≤ t²·2^(lt)`). -/
def memCap (t l : ℕ) : ℕ := t ^ 2 * 2 ^ (l * t)

/-- (E3) settlement-event guard ceiling `t³·2^(l·t)`; a completed run certifies
`T ≤ t³·2^(l_top·t) − n₂` on the total duplicate excess, and an overflow aborts loudly. -/
def eventCap (t l : ℕ) : ℕ := t ^ 3 * 2 ^ (l * t)

/-- Top recursion level `l_top = ⌈log₂ n / t⌉` (prescription: `t ≥ 1`). -/
def lTop (t n : ℕ) : ℕ := (Nat.log 2 n + (t - 1)) / max t 1

/-- DMSY26 Lemma 3.4's **pull-size cap** `M = t·2^((l−1)·t)` for a level-`l` call (CORRECTED_PROOF
§1).  A pull at level `l` extracts at most `M` keys; this is the clause `PullSpec.size` carries
(`pullRun`'s size conjunct), so the A4 recursion can bound a child's seed set:
`|S_i| ≤ pullCap t l + fpCap t ≤ memCap t (l - 1)`. -/
def pullCap (t l : ℕ) : ℕ := t * 2 ^ ((l - 1) * t)

/-- **lTop guard lemma** (task key lemma 2): at the top level the (E3) guard ceiling strictly
exceeds the vertex count — `eventCap t (lTop t n) > n` — so a top call settles at most `n`
vertices well below the guard and the guard cannot fire on distinct settlements
(`|U| ≤ n₂ < t³·2^(l_top·t)`, CORRECTED_PROOF §2.1 (E3)).  The hypothesis `2 ≤ t` is sharp:
at `t = 1` and `n = 2^k` one has `lTop 1 n = k` and `eventCap 1 k = 2^k = n`, not `> n`. -/
theorem eventCap_lTop (t n : ℕ) (ht : 2 ≤ t) : n < eventCap t (lTop t n) := by
  have ht1 : 1 < t := lt_of_lt_of_le (by norm_num) ht
  have ht0 : 0 < t := Nat.zero_lt_of_lt ht1
  have hmax : max t 1 = t := max_eq_left (Nat.le_of_lt ht1)
  have hlog : Nat.log 2 n ≤ lTop t n * t := by
    unfold lTop
    rw [hmax]
    have hdiv := Nat.div_add_mod (Nat.log 2 n + (t - 1)) t
    have hlt : (Nat.log 2 n + (t - 1)) % t < t := Nat.mod_lt _ ht0
    have hm : t * ((Nat.log 2 n + (t - 1)) / t) =
        Nat.log 2 n + (t - 1) - (Nat.log 2 n + (t - 1)) % t := by
      have h := congrArg (· - (Nat.log 2 n + (t - 1)) % t) hdiv
      rw [Nat.add_sub_cancel] at h
      exact h
    calc Nat.log 2 n = Nat.log 2 n + (t - 1) - (t - 1) := (Nat.add_sub_cancel _ _).symm
      _ ≤ Nat.log 2 n + (t - 1) - (Nat.log 2 n + (t - 1)) % t :=
        Nat.sub_le_sub_left (Nat.le_pred_of_lt hlt) _
      _ = t * ((Nat.log 2 n + (t - 1)) / t) := hm.symm
      _ = (Nat.log 2 n + (t - 1)) / t * t := Nat.mul_comm _ _
  have hstep : n < 2 ^ (lTop t n * t + 1) :=
    calc n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      _ ≤ 2 ^ (lTop t n * t + 1) := pow_le_pow_right' (by norm_num) (by omega)
  have h8 : (8:ℕ) ≤ t ^ 3 :=
    calc (8:ℕ) = 2 ^ 3 := by norm_num
      _ ≤ t ^ 3 := pow_le_pow_left₀ (by norm_num) ht 3
  calc n < 2 ^ (lTop t n * t + 1) := hstep
    _ = 2 ^ (lTop t n * t) * 2 := Nat.pow_succ 2 (lTop t n * t)
    _ ≤ 2 ^ (lTop t n * t) * 8 := Nat.mul_le_mul_left _ (by norm_num)
    _ = 8 * 2 ^ (lTop t n * t) := Nat.mul_comm _ _
    _ ≤ t ^ 3 * 2 ^ (lTop t n * t) := Nat.mul_le_mul_right _ h8

/-! ## (E1) V5, the leaf cap — the cap constant -/

/-- `d_B[𝒟]` (CORRECTED_PROOF §1): the minimum of the call bound `B` and every stored value of
`𝒟` (unstored keys contribute `⊤`). -/
noncomputable def dMinAux (D : DS G s) : ℕ → WLab G s
  | 0 => ⊤
  | i + 1 => min ((if h : i < G.n then D ⟨i, h⟩ else none).getD ⊤) (dMinAux D i)

noncomputable def dMin (B : WLab G s) (D : DS G s) : WLab G s := min B (dMinAux D G.n)

/-- **(E1) V5, the leaf cap** (fixes Q3): Algorithm 4 returns

  `B'⁺ = min(B'_pull, d_B[𝒟_final])`,

where `B'_pull` is the separator returned by the final Pull (`B` if `𝒟` drained) and `𝒟_final`
is the returned structure including post-final-pull inserts.  Cost: one min-peek, `O(1)`
amortized; the `D` itself is untouched.  Note: **Algorithm 3 must NOT take its `B'` at
`d_B[𝒟]`** (same move at inner levels fails — CORRECTED_PROOF §4.2); the cap is a leaf move. -/
noncomputable def v5Cap (B'_pull B : WLab G s) (D_final : DS G s) : WLab G s :=
  min B'_pull (dMin B D_final)

/-- The V5 cap law: the returned bound is the capped bound. -/
def CapLaw (B'_plus B'_pull B : WLab G s) (D_final : DS G s) : Prop :=
  B'_plus = v5Cap B'_pull B D_final

theorem v5Cap_le_pull (B'_pull B : WLab G s) (D_final : DS G s) :
    v5Cap B'_pull B D_final ≤ B'_pull :=
  min_le_left _ _

theorem v5Cap_le_dMin (B'_pull B : WLab G s) (D_final : DS G s) :
    v5Cap B'_pull B D_final ≤ dMin B D_final :=
  min_le_right _ _

theorem v5Cap_le_bound (B'_pull B : WLab G s) (D_final : DS G s) :
    v5Cap B'_pull B D_final ≤ B :=
  (v5Cap_le_dMin B'_pull B D_final).trans (min_le_left _ _)

theorem dMin_le_bound (B : WLab G s) (D : DS G s) : dMin B D ≤ B :=
  min_le_left _ _

/-! ## (E0) Nonempty-argmin guards (audit Q2/Q8) -/

/-- **(E0)**: argmin/selection steps of FindPivots (line 6) and BMSSP (lines 28–29) are taken
only over nonempty groups; empty `P_j` are skipped and line 28's re-selection is skipped when
`P_j = ∅` after removals.  Assumed by every statement below. -/
structure ArgminGuard {α : Type} (Js : Finset ℕ) (P : ℕ → Finset α) : Prop where
  guarded : ∀ j ∈ Js, (P j).Nonempty

/-! ## (Q12) Premature-entry shape -/

/-- Premature entries are **two-shaped** (Q12 addendum 18, CORRECTED_PROOF §3 (2b)): either
**S1** — `x` was already settled complete (in a different subtree; `val` is its stale
pre-settlement entry), or **S2** — `x` is unsettled (self-custodial) with current label
`≤ val`. -/
inductive PremShape (d' : Labels G s) (x : Fin G.n) (val : WLab G s) : Prop where
  | s1 (settled : Complete d' x) : PremShape d' x val
  | s2 (unsettled : ¬ Complete d' x) (custodial : d' x ≤ val) : PremShape d' x val

end DMSY
end Frontier

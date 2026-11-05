import D.Bound

/-!
# Frontier.DMSY.Main — D4: the final time bound (work package D)

Work package **D4 (final time bound)**.  The lane's final bound
`O(m √(log n) + √(m n log n loglog n))` for the corrected DMSY program, at the level of
`Time a' b' c' n m` (D1) and the assembled `Bound a b a' b' c'` (D3).  Two remarks the
theorem states honestly:

* a uniform program pays `Ω(n)` to emit its `n`-entry output arrays (`initState`'s
  `reach`/`dist` allocation alone costs `2n + 2`), so the time shape carries a lower-order
  `c'·(n+m+1)` term; the claimed `O(m √(log n) + √(m n log n loglog n))` form is exactly
  recovered in the regime where the two DMSY terms dominate it — `1 ≤ m` and
  `n ≤ m·log(n+2)·log(log(n+2)+2)` (then `n ≤ √(m n log n loglog n)` and
  `m + 1 ≤ 2m √(log(n+2))`);
* below that regime the honest statement is `O(n + m + m √(log n) + √(m n log n loglog n))`,
  which is `Time`'s own basis.

`DMSYBound` pins the closed statement the joint `Main.lean` assembles once package C's
sparse clause lands (IMPLAN §2, key lemma 10).
-/

namespace Frontier.DMSY

open Frontier Frontier.RAM

/-- **D4 — the final time bound.**  For nonnegative time parameters, `Time a' b' c' n m`
is at most a constant times `m √(log(n+2)) + √(m n log(n+2) log(log(n+2)+2))` — the lane's
`O(m √(log n) + √(m n log n loglog n))` — for all `1 ≤ n`, `1 ≤ m` in the regime
`n ≤ m·log(n+2)·log(log(n+2)+2)`. -/
theorem time_final_bound (a' b' c' : ℝ) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') :
    ∃ K : ℝ, ∀ (n m : ℕ), 1 ≤ n → 1 ≤ m →
      ((n : ℝ) ≤ (m : ℝ) * Real.log ((n : ℝ) + 2) * Real.log (Real.log ((n : ℝ) + 2) + 2)) →
      Time a' b' c' n m ≤
        K * ((m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) +
          Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
            Real.log (Real.log ((n : ℝ) + 2) + 2))) := by
  refine ⟨max (a' + 2 * c' / Real.sqrt (Real.log 3)) (b' + c'), fun n m hn1 hm1 hreg => ?_⟩
  have hregL : ((n : ℝ) ≤ (m : ℝ) * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) := hreg
  set L := Real.log ((n : ℝ) + 2) with hL
  set L2 := Real.log (L + 2) with hL2
  have hL3 : Real.log 3 ≤ L :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 3 ≤ n + 2))
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hs3 : 0 < Real.sqrt (Real.log 3) := Real.sqrt_pos.mpr hlog3
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n + 2))
  have hL20 : 0 ≤ L2 := Real.log_nonneg (by linarith)
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hrad : 0 ≤ (m : ℝ) * n * L * L2 := by positivity
  have hS : (n : ℝ) ≤ Real.sqrt ((m : ℝ) * n * L * L2) := by
    have h1 : ((n : ℝ)) ^ 2 ≤ (m : ℝ) * L * L2 * (n : ℝ) := by
      have hreg' : (n : ℝ) ≤ (m : ℝ) * Real.log ((n : ℝ) + 2) *
          Real.log (Real.log ((n : ℝ) + 2) + 2) := hreg
      rw [← hL, ← hL2] at hreg'
      have hmul := mul_le_mul_of_nonneg_right hreg' (by positivity)
      nlinarith [hmul]
    have h2 : (m : ℝ) * L * L2 * (n : ℝ) = (m : ℝ) * n * L * L2 := by ring
    rw [h2] at h1
    exact (Real.le_sqrt hn0 hrad).mpr h1
  have hm2 : (m : ℝ) + 1 ≤ 2 * m := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm1
    linarith
  have hMs : 2 * (m : ℝ) ≤ (2 / Real.sqrt (Real.log 3)) * ((m : ℝ) * Real.sqrt L) := by
    have h1 : Real.sqrt (Real.log 3) ≤ Real.sqrt L := Real.sqrt_le_sqrt hL3
    rw [div_mul_eq_mul_div, le_div_iff₀ hs3]
    have hstep : 2 * (m : ℝ) * Real.sqrt (Real.log 3) ≤ 2 * (m : ℝ) * Real.sqrt L :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    nlinarith [hstep]
  have hlower : ((m : ℝ) + n + 1) ≤ Real.sqrt ((m : ℝ) * n * L * L2) + 2 * (m : ℝ) := by
    have : ((m : ℝ) + n + 1) ≤ 2 * (m : ℝ) + (n : ℝ) := by linarith [hm2]
    linarith [hS]
  have htime : Time a' b' c' n m ≤
      (a' + 2 * c' / Real.sqrt (Real.log 3)) * ((m : ℝ) * Real.sqrt L) +
      (b' + c') * Real.sqrt ((m : ℝ) * n * L * L2) := by
    unfold Time
    have h1 : (c' : ℝ) * ((m : ℝ) + n + 1) ≤
        c' * Real.sqrt ((m : ℝ) * n * L * L2) +
          (2 * c' / Real.sqrt (Real.log 3)) * ((m : ℝ) * Real.sqrt L) := by
      have hbase : (c' : ℝ) * ((m : ℝ) + n + 1) ≤
          c' * (Real.sqrt ((m : ℝ) * n * L * L2) + 2 * (m : ℝ)) :=
        mul_le_mul_of_nonneg_left hlower hc'
      have hcl : (c' : ℝ) * (Real.sqrt ((m : ℝ) * n * L * L2) + 2 * (m : ℝ)) =
          c' * Real.sqrt ((m : ℝ) * n * L * L2) + c' * (2 * (m : ℝ)) := by ring
      rw [hcl] at hbase
      have hcb : c' * (2 * (m : ℝ)) ≤
          (2 * c' / Real.sqrt (Real.log 3)) * ((m : ℝ) * Real.sqrt L) := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hs3]
        have hstep : 2 * c' * (m : ℝ) * Real.sqrt (Real.log 3) ≤
            2 * c' * (m : ℝ) * Real.sqrt L :=
          mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hL3)
            (by positivity : (0:ℝ) ≤ 2 * c' * (m : ℝ))
        nlinarith [hstep]
      linarith
    have h2 : 0 ≤ (2 * c' / Real.sqrt (Real.log 3)) * ((m : ℝ) * Real.sqrt L) :=
      mul_nonneg (by positivity) (by positivity)
    have hAB : Real.sqrt L = Real.sqrt (Real.log ((n : ℝ) + 2)) := by rw [hL]
    have hCD : Real.sqrt ((m : ℝ) * n * L * L2) =
        Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
          Real.log (Real.log ((n : ℝ) + 2) + 2)) := by rw [hL, hL2]
    have hAA : (0:ℝ) ≤ a' * (m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) := by positivity
    have hBB : (0:ℝ) ≤ b' * Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
        Real.log (Real.log ((n : ℝ) + 2) + 2)) := by positivity
    nlinarith [mul_nonneg ha' hm0, hAA, hBB, h1, h2, hAB, hCD]
  have hK : Time a' b' c' n m ≤ max (a' + 2 * c' / Real.sqrt (Real.log 3)) (b' + c') *
      ((m : ℝ) * Real.sqrt L + Real.sqrt ((m : ℝ) * n * L * L2)) := by
    have hM : 0 ≤ (m : ℝ) * Real.sqrt L := by positivity
    have hS0 : 0 ≤ Real.sqrt ((m : ℝ) * n * L * L2) := Real.sqrt_nonneg _
    nlinarith [htime, le_max_left (a' + 2 * c' / Real.sqrt (Real.log 3)) (b' + c'),
      le_max_right (a' + 2 * c' / Real.sqrt (Real.log 3)) (b' + c')]
  simpa only [hL, hL2] using hK

/-- **D4 — unconditional shape.**  Without the regime hypothesis, `Time` is
`O(n + m + m √(log n) + √(m n log n loglog n))` — its own basis, for `1 ≤ n`. -/
theorem time_full_shape (a' b' c' : ℝ) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c') :
    ∃ K : ℝ, ∀ (n m : ℕ),
      Time a' b' c' n m ≤ K * ((n : ℝ) + m + 1 +
        (m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) +
        Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
          Real.log (Real.log ((n : ℝ) + 2) + 2))) := by
  refine ⟨a' + b' + c', fun n m => ?_⟩
  have h1 : 0 ≤ Real.sqrt (Real.log ((n : ℝ) + 2)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) := Real.sqrt_nonneg _
  have hm0 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hL20 : 0 ≤ Real.log (Real.log ((n : ℝ) + 2) + 2) := Real.log_nonneg (by linarith [hL0])
  unfold Time
  have hsum : (a' + b' + c') *
      ((n : ℝ) + m + 1 + (m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) +
        Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
          Real.log (Real.log ((n : ℝ) + 2) + 2))) =
      (a' + b' + c') * ((n : ℝ) + m + 1) +
      (a' + b' + c') * ((m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2))) +
      (a' + b' + c') * Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
        Real.log (Real.log ((n : ℝ) + 2) + 2)) := by ring
  rw [hsum]
  have hK1 : a' ≤ a' + b' + c' := by linarith
  have hK2 : b' ≤ a' + b' + c' := by linarith
  have hK3 : c' ≤ a' + b' + c' := by linarith
  have hp1 : (0 : ℝ) ≤ (m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) := by positivity
  have hp2 : (0 : ℝ) ≤ Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) := h2
  have hp3 : (0 : ℝ) ≤ (n : ℝ) + m + 1 := by linarith
  have e1 : a' * ((m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2))) ≤
      (a' + b' + c') * ((m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2))) :=
    mul_le_mul_of_nonneg_right hK1 hp1
  have e2 : b' * Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) ≤
      (a' + b' + c') * Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
        Real.log (Real.log ((n : ℝ) + 2) + 2)) :=
    mul_le_mul_of_nonneg_right hK2 hp2
  have e3 : c' * ((m : ℝ) + n + 1) ≤ (a' + b' + c') * ((n : ℝ) + m + 1) := by
    have h : (m : ℝ) + n + 1 = (n : ℝ) + m + 1 := by ring
    rw [h]
    exact mul_le_mul_of_nonneg_right hK3 hp3
  linarith [e1, e2, e3]

/-- **D4 signature** — the closed form the joint `Main.lean` assembles once package C's
sparse clause lands (IMPLAN §2 key lemma 10): some admissible parameters give the lane's
`Bound`. -/
def DMSYBound : Prop := ∃ (a b : ℕ) (a' b' c' : ℝ), Bound a b a' b' c'

end Frontier.DMSY

#print axioms Frontier.DMSY.time_final_bound
#print axioms Frontier.DMSY.time_full_shape

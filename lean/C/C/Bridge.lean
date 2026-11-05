import C.PerCall

/-!
# C4 — Bridge: from valid DMSY counters to `K · T_dmsy(n, m)`

Work package **C (cost instantiation)**, IMPLAN §2 C4 (the task's key lemmas 2 and 3).  The
CostFinal-style bridge, re-instantiated for the corrected DMSY engine and its target shape

    T_dmsy(n, m) = n + m·√(log n) + √(m·n·log n·log log n)

(DMSY26 = arXiv 2602.07868v2, the lane's directed frontier; sparse clause `m ≤ n·F n`,
IMPLAN §2 D2/D4).  Three steps:

1. **`total_cost_le` (proved).**  Summing the C3 per-call contract over the C1 forest: the
   five global terms of corrected Lemma 3.9\* in terms of the exact counter totals.
2. **`TdmsyMenu` (the named seam).**  The term menu for `T_dmsy` at the DMSY parameter
   prescription (`t ≈ √(log n·log log n / δ)`, `k = fpCap t`, `L = Lmax + 1 = lTop t n + 1`,
   degree cap `δ = Θ(min(m/n, log log n))` after GM.0 degree reduction) — the CostSkeleton
   analogue.  Each field is one monomial of step 1 (after the scale substitution
   `Σ|U| + Σ dup ≤ 2·a·n·L + T`, `Σ|J| + Σ|Cr| ≤ 2·a·m`) bounded by a constant times
   `T_dmsy`; discharging them is real analysis on the prescription.  The C-HD menu is for
   `Tchd` and does **not** transfer: the C-HD per-call shape carries a `k·|U|` vertex term
   which is `≥ n·log n` at `L = ⌈log n/t⌉` for every `k ≥ 2` — above `T_dmsy(n,n)` — so the
   corrected Lemma 3.9\* shape of C3 is load-bearing here.
3. **`total_le_Tdmsy` (proved).**  The CostFinal combination: valid counters + per-call
   contract + menu ⇒ total `≤ 5100·c·a·T_dmsy(n, m)` (the menu constants give `1802`).

**Key lemma 3 — the re-settlement contribution.**  The duplicate excess `T` enters the total
*only* through the additive surcharges `T·(l + log t)·log t`, `t·δ·T`, `l·T` (Lemma 3.9\*'
last line).  `total_le_Tdmsy_T0`: on `T = 0` (full executions / the V8–V10 settled-bit
engine) the surcharges vanish and the paper's bound is restored verbatim from a `dup`-free
menu.  For the unmarked V5 engine `A4.lemmaR` (A4 `Size`, CORRECTED_PROOF §5, **sketch
grade**) bounds `T` by `(2·(t²2^t)·(l_top+1)·n²).sqrt + (l_top + fpCap t)·n`; plugging that
bound into the `dup_vertex`/`sweepT`/`levelT` menu items is the remaining arithmetic.
-/

namespace Frontier
namespace DMSY

open Finset DmsyCounters

set_option linter.unusedSectionVars false

variable {ι V E α : Type*} [Fintype ι] [Fintype V] [Fintype E]
  [DecidableEq ι] [DecidableEq V] [DecidableEq E] [LinearOrder α]

noncomputable section

/-- **The DMSY target shape** (IMPLAN §2 C4): `n + m·√(log n) + √(m·n·log n·log log n)`,
with the safe logs `log(n+2)` and `log log(n+2)` (positive for `n ≥ 1`; `Real.sqrt` folds the
`n = 0` corner to `0`). -/
def Tdmsy (n m : ℕ) : ℝ :=
  (n : ℝ) + (m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2))
    + Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) * Real.log (Real.log ((n : ℝ) + 2)))

theorem Tdmsy_nonneg (n m : ℕ) : 0 ≤ Tdmsy n m := by
  unfold Tdmsy
  positivity

end

/-! ## Step 1: the aggregation (proved) -/

/-- **C4 step 1.**  The summed per-call contract: with the exact counter totals the total
cost is at most the five global terms of corrected Lemma 3.9\*. -/
theorem total_cost_le {t k c Lmax M0 δ T lTop lgT : ℕ}
    {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (C : DmsyCounters ι V E α) (h : C.DmsyValid t k c Lmax M0 δ T inE wit src)
    (hp : DmsyPerCall C t k c δ lTop lgT) :
    (∑ X, C.cost X) ≤
      c * (∑ X, ((C.F.U X).card + C.dup X)) * ((lTop + lgT) * lgT)
        + c * t * ((∑ X, (C.J X).card) + ∑ X, (C.Cr X).card)
        + c * t * δ * (∑ X, ((C.F.U X).card + C.dup X))
        + c * lTop * (∑ X, ((C.F.U X).card + C.dup X))
        + c * t * δ * (∑ X, C.dup X) := by
  have hper : (∑ X, C.cost X) ≤
      (∑ X, (c * ((C.F.U X).card + C.dup X) * ((lTop + lgT) * lgT)
        + c * t * ((C.J X).card + (C.Cr X).card)
        + c * t * δ * ((C.F.U X).card + C.dup X)
        + c * lTop * ((C.F.U X).card + C.dup X)
        + c * t * δ * C.dup X)) :=
    Finset.sum_le_sum fun X _ => hp.perCall X
  have hsplit : (∑ X,
        (c * ((C.F.U X).card + C.dup X) * ((lTop + lgT) * lgT)
          + c * t * ((C.J X).card + (C.Cr X).card)
          + c * t * δ * ((C.F.U X).card + C.dup X)
          + c * lTop * ((C.F.U X).card + C.dup X)
          + c * t * δ * C.dup X)) =
      (∑ X, c * ((C.F.U X).card + C.dup X) * ((lTop + lgT) * lgT))
        + (∑ X, c * t * ((C.J X).card + (C.Cr X).card))
        + (∑ X, c * t * δ * ((C.F.U X).card + C.dup X))
        + (∑ X, c * lTop * ((C.F.U X).card + C.dup X))
        + (∑ X, c * t * δ * C.dup X) := by
    simp only [Finset.sum_add_distrib]
  have s1 : (∑ X, c * ((C.F.U X).card + C.dup X) * ((lTop + lgT) * lgT)) =
      c * (∑ X, ((C.F.U X).card + C.dup X)) * ((lTop + lgT) * lgT) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have s2 : (∑ X, c * t * ((C.J X).card + (C.Cr X).card)) =
      c * t * ((∑ X, (C.J X).card) + ∑ X, (C.Cr X).card) := by
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have s3 : (∑ X, c * t * δ * ((C.F.U X).card + C.dup X)) =
      c * t * δ * (∑ X, ((C.F.U X).card + C.dup X)) := by
    rw [← Finset.mul_sum]
  have s4 : (∑ X, c * lTop * ((C.F.U X).card + C.dup X)) =
      c * lTop * (∑ X, ((C.F.U X).card + C.dup X)) := by
    rw [← Finset.mul_sum]
  have s5 : (∑ X, c * t * δ * C.dup X) = c * t * δ * (∑ X, C.dup X) := by
    rw [← Finset.mul_sum]
  rw [hsplit, s1, s2, s3, s4, s5] at hper
  exact hper

/-! ## Step 2: the term menu for `Tdmsy` (the named seam) -/

/-- **C4 step 2 — term menu** (CostSkeleton analogue; the seam).  One field per monomial of
`total_cost_le`'s right-hand side after the scale substitution.  Discharging the menu is the
DMSY parameter optimization (`m·t ≈ √(m·n·log n·log log n)`, `n·L·(l+log t)·log t` on the
`m·√(log n)` branch), plus the sparse-clause dispatch facts (D2/D4). -/
structure TdmsyMenu (n m t δ lTop lgT L T : ℕ) : Prop where
  vertex : (n * L : ℝ) * ((lTop + lgT) * lgT) ≤ 100 * Tdmsy n m
  dup_vertex : (T : ℝ) * ((lTop + lgT) * lgT) ≤ 100 * Tdmsy n m
  jumps : (t : ℝ) * m ≤ 26 * Tdmsy n m
  sweepU : (t * δ : ℝ) * (n * L) ≤ 300 * Tdmsy n m
  sweepT : (t * δ : ℝ) * T ≤ 200 * Tdmsy n m
  levelU : (lTop : ℝ) * (n * L) ≤ 150 * Tdmsy n m
  levelT : (lTop : ℝ) * T ≤ 150 * Tdmsy n m

/-! ## Step 3: the bridge (proved) -/

/-- **C4 — the overall time bound (key lemma 2).**  Valid DMSY counters, the C3 per-call
contract, the scale facts (`|V| ≤ a·n`, `|E| ≤ a·m`, `Lmax + 1 ≤ 2·L`) and the term menu give

    Σ_X cost X ≤ 5100 · c · a · T_dmsy(n, m)

(sparse clause; the menu constants above discharge `1802`).  CostFinal's shape. -/
theorem total_le_Tdmsy {t k c Lmax M0 δ T lTop lgT L a : ℕ}
    {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (C : DmsyCounters ι V E α) (n m : ℕ)
    (h : C.DmsyValid t k c Lmax M0 δ T inE wit src)
    (hp : DmsyPerCall C t k c δ lTop lgT)
    (hV : Fintype.card V ≤ a * n) (hE : Fintype.card E ≤ a * m)
    (hL : Lmax + 1 ≤ 2 * L)
    (hmenu : TdmsyMenu n m t δ lTop lgT L T) :
    ((∑ X, C.cost X : ℕ) : ℝ) ≤ 5100 * c * a * Tdmsy n m := by
  have hagg := total_cost_le C h hp
  have hU := sum_U_le h
  have hJ := sum_J_le h
  have hCr := sum_Cr_le h
  have ha1 : 1 ≤ a := by
    have hV1 : 1 ≤ Fintype.card V := by
      have := Fintype.card_pos_iff.mpr (⟨src⟩ : Nonempty V)
      omega
    by_contra ha
    have ha0 : a = 0 := by omega
    rw [ha0, zero_mul] at hV
    omega
  have hT0 : (0 : ℝ) ≤ Tdmsy n m := Tdmsy_nonneg n m
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  -- counter totals against the scale facts
  have hUD : ((∑ X, (C.F.U X).card) + ∑ X, C.dup X) ≤ 2 * L * (a * n) + T := by
    have h1 := Nat.add_le_add hU h.dup_total
    have h2 : (Lmax + 1) * Fintype.card V ≤ (2 * L) * (a * n) := Nat.mul_le_mul hL hV
    omega
  have hJC : ((∑ X, (C.J X).card) + ∑ X, (C.Cr X).card) ≤ 2 * (a * m) := by
    have := Nat.add_le_add hJ hCr
    omega
  have hS : ((∑ X, ((C.F.U X).card + C.dup X))) = (∑ X, (C.F.U X).card) + ∑ X, C.dup X := by
    simp only [Finset.sum_add_distrib]
  -- bound each of the five terms in ℕ
  have b1 : c * ((∑ X, ((C.F.U X).card + C.dup X))) * ((lTop + lgT) * lgT)
      ≤ c * (2 * L * (a * n) + T) * ((lTop + lgT) * lgT) :=
    Nat.mul_le_mul_right ((lTop + lgT) * lgT) (Nat.mul_le_mul_left c (by rw [hS]; exact hUD))
  have b2 : c * t * ((∑ X, (C.J X).card) + ∑ X, (C.Cr X).card)
      ≤ c * t * (2 * (a * m)) :=
    Nat.mul_le_mul_left (c * t) hJC
  have b3 : c * t * δ * ((∑ X, ((C.F.U X).card + C.dup X)))
      ≤ c * t * δ * (2 * L * (a * n) + T) :=
    Nat.mul_le_mul_left (c * t * δ) (by rw [hS]; exact hUD)
  have b4 : c * lTop * ((∑ X, ((C.F.U X).card + C.dup X)))
      ≤ c * lTop * (2 * L * (a * n) + T) :=
    Nat.mul_le_mul_left (c * lTop) (by rw [hS]; exact hUD)
  have b5 : c * t * δ * (∑ X, C.dup X) ≤ c * t * δ * T :=
    Nat.mul_le_mul_left (c * t * δ) h.dup_total
  -- collect in ℕ, then cast
  have hN : ((∑ X, C.cost X : ℕ)) ≤
      c * (2 * L * (a * n) + T) * ((lTop + lgT) * lgT) + c * t * (2 * (a * m))
        + c * t * δ * (2 * L * (a * n) + T) + c * lTop * (2 * L * (a * n) + T)
        + c * t * δ * T := by
    omega
  have hcast : ((∑ X, C.cost X : ℕ) : ℝ) ≤
      ((c * (2 * L * (a * n) + T) * ((lTop + lgT) * lgT) : ℕ) : ℝ)
        + ((c * t * (2 * (a * m)) : ℕ) : ℝ)
        + ((c * t * δ * (2 * L * (a * n) + T) : ℕ) : ℝ)
        + ((c * lTop * (2 * L * (a * n) + T) : ℕ) : ℝ)
        + ((c * t * δ * T : ℕ) : ℝ) := by exact_mod_cast hN
  -- reshape each term onto the menu monomials
  have e1 : ((c * (2 * L * (a * n) + T) * ((lTop + lgT) * lgT) : ℕ) : ℝ)
      = 2 * a * c * ((n * L) * ((lTop + lgT) * lgT)) + c * (T * ((lTop + lgT) * lgT)) := by
    push_cast; ring
  have e2 : ((c * t * (2 * (a * m)) : ℕ) : ℝ) = 2 * a * c * (t * m) := by push_cast; ring
  have e3 : ((c * t * δ * (2 * L * (a * n) + T) : ℕ) : ℝ)
      = 2 * a * c * ((t * δ) * (n * L)) + c * ((t * δ) * T) := by push_cast; ring
  have e4 : ((c * lTop * (2 * L * (a * n) + T) : ℕ) : ℝ)
      = 2 * a * c * (lTop * (n * L)) + c * (lTop * T) := by push_cast; ring
  have e5 : ((c * t * δ * T : ℕ) : ℝ) = c * ((t * δ) * T) := by push_cast; ring
  rw [e1, e2, e3, e4, e5] at hcast
  -- menu consumption (constants: 100 + 100 + 26 + 300 + 200 + 150 + 150, doubled on the
  -- `a`-side terms; `t·δ·T` appears twice, giving 1802 in total)
  have m1 : (2 * a * c : ℝ) * ((n * L) * ((lTop + lgT) * lgT))
      ≤ 2 * a * c * (100 * Tdmsy n m) :=
    mul_le_mul_of_nonneg_left hmenu.vertex (by positivity)
  have m2 : (c : ℝ) * (T * ((lTop + lgT) * lgT)) ≤ c * (100 * Tdmsy n m) :=
    mul_le_mul_of_nonneg_left hmenu.dup_vertex hc0
  have m3 : (2 * a * c : ℝ) * (t * m) ≤ 2 * a * c * (26 * Tdmsy n m) :=
    mul_le_mul_of_nonneg_left hmenu.jumps (by positivity)
  have m4 : (2 * a * c : ℝ) * ((t * δ) * (n * L)) ≤ 2 * a * c * (300 * Tdmsy n m) :=
    mul_le_mul_of_nonneg_left hmenu.sweepU (by positivity)
  have m5 : (c : ℝ) * ((t * δ) * T) ≤ c * (200 * Tdmsy n m) :=
    mul_le_mul_of_nonneg_left hmenu.sweepT hc0
  have m6 : (2 * a * c : ℝ) * (lTop * (n * L)) ≤ 2 * a * c * (150 * Tdmsy n m) :=
    mul_le_mul_of_nonneg_left hmenu.levelU (by positivity)
  have m7 : (c : ℝ) * (lTop * T) ≤ c * (150 * Tdmsy n m) :=
    mul_le_mul_of_nonneg_left hmenu.levelT hc0
  -- fold the bare-`c` pieces into `c·a` and collect
  have hcT : (c : ℝ) * Tdmsy n m ≤ c * a * Tdmsy n m := by
    calc (c : ℝ) * Tdmsy n m = 1 * (c * Tdmsy n m) := by ring
      _ ≤ a * (c * Tdmsy n m) := mul_le_mul_of_nonneg_right haR (mul_nonneg hc0 hT0)
      _ = c * a * Tdmsy n m := by ring
  have m1' : (2 * a * c : ℝ) * ((n * L) * ((lTop + lgT) * lgT)) ≤ 200 * (c * a * Tdmsy n m) := by
    have r : (2 * a * c : ℝ) * (100 * Tdmsy n m) = 200 * (c * a * Tdmsy n m) := by ring
    rw [r] at m1; exact m1
  have m2' : (c : ℝ) * (T * ((lTop + lgT) * lgT)) ≤ 100 * (c * a * Tdmsy n m) := by
    have r : (c : ℝ) * (100 * Tdmsy n m) = 100 * (c * Tdmsy n m) := by ring
    rw [r] at m2
    exact m2.trans (mul_le_mul_of_nonneg_left hcT (by norm_num))
  have m3' : (2 * a * c : ℝ) * (t * m) ≤ 52 * (c * a * Tdmsy n m) := by
    have r : (2 * a * c : ℝ) * (26 * Tdmsy n m) = 52 * (c * a * Tdmsy n m) := by ring
    rw [r] at m3; exact m3
  have m4' : (2 * a * c : ℝ) * ((t * δ) * (n * L)) ≤ 600 * (c * a * Tdmsy n m) := by
    have r : (2 * a * c : ℝ) * (300 * Tdmsy n m) = 600 * (c * a * Tdmsy n m) := by ring
    rw [r] at m4; exact m4
  have m5' : (c : ℝ) * ((t * δ) * T) ≤ 200 * (c * a * Tdmsy n m) := by
    have r : (c : ℝ) * (200 * Tdmsy n m) = 200 * (c * Tdmsy n m) := by ring
    rw [r] at m5
    exact m5.trans (mul_le_mul_of_nonneg_left hcT (by norm_num))
  have m6' : (2 * a * c : ℝ) * (lTop * (n * L)) ≤ 300 * (c * a * Tdmsy n m) := by
    have r : (2 * a * c : ℝ) * (150 * Tdmsy n m) = 300 * (c * a * Tdmsy n m) := by ring
    rw [r] at m6; exact m6
  have m7' : (c : ℝ) * (lTop * T) ≤ 150 * (c * a * Tdmsy n m) := by
    have r : (c : ℝ) * (150 * Tdmsy n m) = 150 * (c * Tdmsy n m) := by ring
    rw [r] at m7
    exact m7.trans (mul_le_mul_of_nonneg_left hcT (by norm_num))
  linarith [hcast, m1', m2', m3', m4', m5', m6', m7']

/-! ## Key lemma 3: the re-settlement contribution -/

/-- **Key lemma 3 — the `T = 0` menu.**  Without duplicate excess the menu drops its three
`dup` items. -/
structure TdmsyMenu0 (n m t δ lTop lgT L : ℕ) : Prop where
  vertex : (n * L : ℝ) * ((lTop + lgT) * lgT) ≤ 100 * Tdmsy n m
  jumps : (t : ℝ) * m ≤ 26 * Tdmsy n m
  sweepU : (t * δ : ℝ) * (n * L) ≤ 300 * Tdmsy n m
  levelU : (lTop : ℝ) * (n * L) ≤ 150 * Tdmsy n m

/-- The re-settlement surcharges vanish with the duplicate excess. -/
theorem menu_of_T0 {n m t δ lTop lgT L T : ℕ} (hT : T = 0)
    (h0 : TdmsyMenu0 n m t δ lTop lgT L) : TdmsyMenu n m t δ lTop lgT L T := by
  subst hT
  refine ⟨h0.vertex, ?_, h0.jumps, h0.sweepU, ?_, h0.levelU, ?_⟩
  · simp only [Nat.cast_zero, zero_mul]
    exact mul_nonneg (by norm_num) (Tdmsy_nonneg n m)
  · simp only [Nat.cast_zero, mul_zero]
    exact mul_nonneg (by norm_num) (Tdmsy_nonneg n m)
  · simp only [Nat.cast_zero, mul_zero]
    exact mul_nonneg (by norm_num) (Tdmsy_nonneg n m)

/-- **Key lemma 3 — the re-settlement bound's contribution.**  On `T = 0` (full executions,
or the V8/V10 settled-bit composition where `T = 0` by construction) the paper's stated bound
is restored verbatim: total `≤ 5100·c·a·T_dmsy(n, m)` from the `dup`-free menu.  For the
unmarked V5 engine, `A4.lemmaR` bounds `T` and the three `dup` menu items of `TdmsyMenu`
carry the surcharge additively. -/
theorem total_le_Tdmsy_T0 {t k c Lmax M0 δ T lTop lgT L a : ℕ}
    {inE : V → Finset E} {wit : ι → V → E} {src : V}
    (C : DmsyCounters ι V E α) (n m : ℕ)
    (h : C.DmsyValid t k c Lmax M0 δ T inE wit src)
    (hp : DmsyPerCall C t k c δ lTop lgT)
    (hV : Fintype.card V ≤ a * n) (hE : Fintype.card E ≤ a * m)
    (hL : Lmax + 1 ≤ 2 * L) (hT : T = 0)
    (hmenu : TdmsyMenu0 n m t δ lTop lgT L) :
    ((∑ X, C.cost X : ℕ) : ℝ) ≤ 5100 * c * a * Tdmsy n m :=
  total_le_Tdmsy C n m h hp hV hE hL (menu_of_T0 hT hmenu)

end DMSY
end Frontier

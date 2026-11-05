import D.Bound
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# D.Adapter — the verifier's `Race.bound` row, bridged from the lane's `Bound`

The trusted target statement (`challenges/directed-sssp/CHDRow.lean`, staged from
bigospeedrun/verifier) is replicated verbatim below: `BigOSpeedrun.DirectedSSSP.Bound`
with the race row's five exact rationals

* cap `a = 1`, `b = 3/4` — the C-HD density threshold `D(n) = n · ⌊(log₂ n)^(3/4)⌋`;
* time `a' = 1`, `b' = 11/12`, `c' = 0` — `T(n) = n · (log n)^(11/12)`.

`Race.bound` is then assembled from the lane's `Frontier.DMSY.bound` (`D/D/Bound.lean`,
D3) at lane parameters `a = 1`, `b = 1` (our `ℕ`-valued cap `n · log₂ n` contains the
row's), word exponent `e = 2`, time parameters `a' = 0`, `b' = 1`, `c' = 1` (killing
the `m √(log n)` DMSY term is what makes the row's `n (log n)^(11/12)` budget provable:
the surviving terms `√(m n log n loglog n) + (m + n + 1)` are dominated by
`(√12 · e^6 + 4) · n (log n)^(11/12)` — `time_dominance` below).

The **one** input not yet available is the DMSY body's sparse-clause specification
`DInputs.hsp` (package C's per-call cost + the joint `Main.lean` seam, IMPLAN §2 key
lemma 10); it is taken as the hypothesis and is the only `sorry`.
-/

namespace BigOSpeedrun.DirectedSSSP

open Frontier Frontier.RAM

/-! ## The verifier's statement (verbatim from `CHDRow.lean`) -/

/-- The edge cap `D(n) = n^a · ⌊⌊log₂ n⌋^b⌋`, with both floors exact
(`Nat.log 2 n` is `⌊log₂ n⌋`). At `a = 1`, `b = 3/4` this is the C-HD threshold. -/
noncomputable def Cap (a b : ℚ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (a : ℝ) * (⌊((Nat.log 2 n : ℕ) : ℝ) ^ (b : ℝ)⌋₊ : ℝ)

/-- A graph with `n` vertices and `m` edges is in the race's density range. -/
def Sparse (a b : ℚ) (n m : ℕ) : Prop := (m : ℝ) ≤ Cap a b n

/-- The time function `T(n) = n^a · (log n)^b · (log log n)^c` (natural logarithms). -/
noncomputable def Time (a b c : ℚ) (n : ℕ) : ℝ :=
  (n : ℝ) ^ (a : ℝ) * Real.log n ^ (b : ℝ) * Real.log (Real.log n) ^ (c : ℝ)

/-- One run of `P` on `(G, s)` terminates with the exact distances and costs at most `budget`. -/
def CorrectWithin (P : Program) (G : Graph) (s : Fin G.n) (budget : ℝ) : Prop :=
  ∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s ∧ (r.cost : ℝ) ≤ budget

/-- One uniform program, exact on every graph and source. On every graph with at
least `N` vertices and at most `D(n)` edges it runs within `C · T(n)`; on every
graph it runs within `C · (n+1) · (m+1)` (a polynomial fallback, as Bellman-Ford).
`P.Exact` follows from the fallback clause; it stays for readability. -/
def Bound (a b a' b' c' : ℚ) : Prop :=
  ∃ P : Program, P.Exact ∧ ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, 16 ≤ N ∧
    (∀ (G : Graph) (s : Fin G.n), N ≤ G.n → Sparse a b G.n G.m →
      CorrectWithin P G s (C * Time a' b' c' G.n)) ∧
    (∀ (G : Graph) (s : Fin G.n),
      CorrectWithin P G s (C * ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)))

/-! ## Numeric facts for the bridge -/

private theorem log2_ge_half : (1 : ℝ) / 2 ≤ Real.log 2 :=
  le_trans (by norm_num) Real.log_two_gt_d9.le

private theorem log2_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (two_pos)
  linarith

/-- The row's `Sparse` premise at `(a, b) = (1, 3/4)`, cast-normalized. -/
private theorem sparse_le {n m : ℕ} (h : Sparse ((1 : ℚ) / 1) ((3 : ℚ) / 4) n m) :
    (m : ℝ) ≤ (n : ℝ) * (⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℝ) := by
  simp only [Sparse, Cap] at h
  norm_num at h
  exact h

/-- The row's `Time` at `(a', b', c') = (1, 11/12, 0)`, cast-normalized. -/
private theorem time_v_eq (n : ℕ) :
    Time ((1 : ℚ) / 1) ((11 : ℚ) / 12) ((0 : ℚ) / 1) n =
      (n : ℝ) * (Real.log (n : ℝ)) ^ ((11 : ℝ) / 12) := by
  simp only [Time]
  norm_num

/-- Logarithm bookkeeping for `2^16 ≤ n`: `1 ≤ log n`, `1 ≤ log log n` (so the
`(log log n)^0` factor is harmless and `log log n` can absorb constants), and the
nat-log/real-log bridge `Nat.log 2 n ≤ 2 · log n`. -/
private theorem log_facts {n : ℕ} (hn : 65536 ≤ n) :
    1 ≤ Real.log (n : ℝ) ∧ 1 ≤ Real.log (Real.log (n : ℝ)) ∧
      ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
  have h216 : ((2 : ℝ) ^ (16 : ℕ)) ≤ (n : ℝ) := by
    have h : ((2 : ℝ) ^ (16 : ℕ)) = 65536 := by norm_num
    rw [h]; exact_mod_cast hn
  have hlogn8 : 8 ≤ Real.log (n : ℝ) := by
    have h1 : Real.log ((2 : ℝ) ^ (16 : ℕ)) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) h216
    rw [Real.log_pow] at h1
    norm_num at h1
    nlinarith [log2_ge_half]
  have hloglog1 : 1 ≤ Real.log (Real.log (n : ℝ)) := by
    have h8 : (8 : ℝ) ≤ Real.log (n : ℝ) := by linarith
    have h1 : Real.log (8 : ℝ) ≤ Real.log (Real.log (n : ℝ)) :=
      Real.log_le_log (by norm_num) h8
    have h2 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
      have h3 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
      rw [h3]; exact Real.log_pow _ _
    rw [h2] at h1
    norm_num at h1
    nlinarith [log2_ge_half]
  have hℓ : ((Nat.log 2 n : ℕ) : ℝ) ≤ 2 * Real.log (n : ℝ) := by
    have hp : (2 : ℝ) ^ ((Nat.log 2 n : ℕ) : ℝ) ≤ (n : ℝ) := by
      rw [Real.rpow_natCast]
      exact_mod_cast Nat.pow_log_le_self 2 (by omega)
    have h1 : Real.log ((2 : ℝ) ^ ((Nat.log 2 n : ℕ) : ℝ)) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) hp
    rw [Real.log_rpow two_pos] at h1
    have hℓ0 : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := Nat.cast_nonneg _
    nlinarith [h1, log2_ge_half, hℓ0]
  exact ⟨by linarith, hloglog1, hℓ⟩

/-- The row's density premise implies the lane's cap condition: `⌊(log₂ n)^(3/4)⌋ ≤ log₂ n`
once `log₂ n ≥ 1` (i.e. `n ≥ 2`), so `m ≤ n · ⌊(log₂ n)^(3/4)⌋ ≤ n · log₂ n = Cap 1 1 n`. -/
theorem cap_of_sparse {n m : ℕ} (hn : 2 ≤ n) (h : Sparse ((1 : ℚ) / 1) ((3 : ℚ) / 4) n m) :
    m ≤ Frontier.DMSY.Cap 1 1 n := by
  have hlog1 : (1 : ℕ) ≤ Nat.log 2 n := by
    have hmono := Nat.log_mono_right (b := 2) (show (2 : ℕ) ≤ n by omega)
    have h2 : Nat.log 2 2 = 1 := by decide
    rw [h2] at hmono; exact hmono
  have hℓ1R : (1 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by
    rw [← Nat.cast_one]; exact Nat.cast_le.mpr hlog1
  have h34 : ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ≤ ((Nat.log 2 n : ℕ) : ℝ) := by
    have h := Real.rpow_le_rpow_of_exponent_le hℓ1R (by norm_num : ((3 : ℝ) / 4) ≤ (1 : ℝ))
    rwa [Real.rpow_one] at h
  have hpos : (0 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_nonneg (Nat.cast_nonneg (Nat.log 2 n)) ((3 : ℝ) / 4)
  have hfl : (⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℝ) ≤
      ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := Nat.floor_le hpos
  have hfloor : (⌊((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4)⌋₊ : ℝ) ≤ (Nat.log 2 n : ℝ) :=
    hfl.trans h34
  have h2 : (m : ℝ) ≤ (n : ℝ) * ((Nat.log 2 n : ℕ) : ℝ) :=
    (sparse_le h).trans (mul_le_mul_of_nonneg_left hfloor (Nat.cast_nonneg _))
  have h5 : (m : ℝ) ≤ (Nat.cast (n * Nat.log 2 n) : ℝ) := by
    rw [Nat.cast_mul]
    exact h2
  simp only [Frontier.DMSY.Cap, one_mul, pow_one]
  exact Nat.cast_le.mp h5

/-- **Time dominance** — the heart of the bridge.  On the row's sparse regime
(`m ≤ n · ⌊(log₂ n)^(3/4)⌋`, `2^16 ≤ n`) the lane's `Time 0 1 1 n m`
(`√(m n log(n+2) log(log(n+2)+2)) + (m + n + 1)` — the DMSY bound with the first
term's coefficient zeroed) is at most a constant times the row's
`T(n) = n · (log n)^(11/12)`.  Constants, all for `n ≥ 2^16` (so `log n ≥ 8`):

* `m ≤ 2 n (log n)^(3/4)` (`Nat.log 2 n ≤ 2 log n` and `⌊x^(3/4)⌋ ≤ x^(3/4)`);
* `log(n+2) ≤ 2 log n` (`n + 2 ≤ n²`), `log(log(n+2)+2) ≤ 3 log log n`;
* the loglog factor fits the exponent slack: `t^(1/2) ≤ e^6 · x^(1/24)` for
  `t = log x`, from `12 log t ≤ t + 144` (i.e. `(√t − 12)² ≥ 0`) — the `1/24`
  is exactly the row's slack `11/12 − 7/8`. -/
theorem time_dominance {n m : ℕ} (hn : 65536 ≤ n)
    (h : Sparse ((1 : ℚ) / 1) ((3 : ℚ) / 4) n m) :
    Frontier.DMSY.Time 0 1 1 n m ≤
      (Real.sqrt 12 * Real.exp 6 + 4) * Time ((1 : ℚ) / 1) ((11 : ℚ) / 12) ((0 : ℚ) / 1) n := by
  rw [time_v_eq]
  obtain ⟨hx1, ht1, hℓle⟩ := log_facts hn
  -- abbreviations
  set x := Real.log (n : ℝ) with hxdef
  set t := Real.log x with htdef
  have hx0 : (0 : ℝ) ≤ x := by rw [hxdef]; exact Real.log_nonneg (by exact_mod_cast (by omega))
  have hx0' : 0 < x := by rw [hxdef]; exact Real.log_pos (by exact_mod_cast (by omega))
  have ht0 : 0 < t := by linarith
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega)
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega)
  -- the m bound: m ≤ 2 · n · x^(3/4)
  have hlog2n : (2 : ℕ) ≤ Nat.log 2 n := by
    have hmono := Nat.log_mono_right (b := 2) hn
    have h2 : Nat.log 2 65536 = 16 := by decide
    rw [h2] at hmono; omega
  have hℓ1R : (1 : ℝ) ≤ ((Nat.log 2 n : ℕ) : ℝ) :=
    le_trans (by norm_num : (1 : ℝ) ≤ 2) (by exact_mod_cast hlog2n)
  have hmR : (m : ℝ) ≤ (n : ℝ) * ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) :=
    (sparse_le h).trans (mul_le_mul_of_nonneg_left
      (Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg (Nat.log 2 n)) ((3 : ℝ) / 4)))
      (Nat.cast_nonneg _))
  have hℓ34 : ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ≤ ((2 : ℝ) * x) ^ ((3 : ℝ) / 4) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) hℓle (by norm_num)
  have h234 : ((2 : ℝ) * x) ^ ((3 : ℝ) / 4) = (2 : ℝ) ^ ((3 : ℝ) / 4) * x ^ ((3 : ℝ) / 4) :=
    Real.mul_rpow (by norm_num) hx0
  have h2le : (2 : ℝ) ^ ((3 : ℝ) / 4) ≤ 2 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : ((3 : ℝ) / 4) ≤ 1)
    rwa [Real.rpow_one] at h
  have hmR2 : (m : ℝ) ≤ 2 * (n : ℝ) * x ^ ((3 : ℝ) / 4) := by
    have hmid : (n : ℝ) * ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) ≤
        (n : ℝ) * (2 * x ^ ((3 : ℝ) / 4)) := by
      refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact (hℓ34.trans_eq h234).trans
        (mul_le_mul_of_nonneg_right h2le (Real.rpow_nonneg hx0 ((3 : ℝ) / 4)))
    calc (m : ℝ) ≤ (n : ℝ) * ((Nat.log 2 n : ℕ) : ℝ) ^ ((3 : ℝ) / 4) := hmR
      _ ≤ (n : ℝ) * (2 * x ^ ((3 : ℝ) / 4)) := hmid
      _ = 2 * (n : ℝ) * x ^ ((3 : ℝ) / 4) := by ring
  -- L := log (n+2) ≤ 2x
  have hLle : Real.log ((n : ℝ) + 2) ≤ 2 * x := by
    have hsq : ((n : ℝ) + 2) ≤ (n : ℝ) * (n : ℝ) := by
      nlinarith [hn2, sq_nonneg ((n : ℝ) - 2)]
    have h1 : Real.log ((n : ℝ) + 2) ≤ Real.log ((n : ℝ) * (n : ℝ)) :=
      Real.log_le_log (by positivity) hsq
    rw [Real.log_mul (by positivity) (by positivity)] at h1
    rw [hxdef]
    linarith
  have hL0 : (0 : ℝ) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_nonneg (by exact_mod_cast (by omega : (1:ℕ) ≤ n + 2))
  -- L2 := log (L+2) ≤ 3t
  have hL2le : Real.log (Real.log ((n : ℝ) + 2) + 2) ≤ 3 * t := by
    have hLx : Real.log ((n : ℝ) + 2) + 2 ≤ 4 * x := by nlinarith [hLle, hx1]
    have h1 : Real.log (Real.log ((n : ℝ) + 2) + 2) ≤ Real.log ((4 : ℝ) * x) :=
      Real.log_le_log (by positivity) hLx
    have h2 : Real.log ((4 : ℝ) * x) = 2 * Real.log 2 + t := by
      rw [Real.log_mul (by norm_num) hx0'.ne']
      have h4 : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
      rw [h4, Real.log_pow]
      rw [htdef, hxdef]
      ring
    rw [h2] at h1
    nlinarith [log2_le_one, ht1]
  have hL20 : (0 : ℝ) ≤ Real.log (Real.log ((n : ℝ) + 2) + 2) :=
    Real.log_nonneg (by nlinarith [hL0])
  -- t^(1/2) ≤ e^6 · x^(1/24)
  have ht' : t ^ ((1 : ℝ) / 2) ≤ Real.exp 6 * x ^ ((1 : ℝ) / 24) := by
    have hls : Real.log (Real.sqrt t) ≤ Real.sqrt t - 1 :=
      Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr ht0)
    have hs2 : Real.sqrt t * Real.sqrt t = t := by
      rw [← Real.sqrt_mul (le_of_lt ht0), Real.sqrt_mul_self (le_of_lt ht0)]
    have hsq : 24 * Real.sqrt t ≤ t + 144 := by nlinarith [sq_nonneg (Real.sqrt t - 12), hs2]
    have hlogt : Real.log t ≤ 12 + t / 12 := by
      have hlg : Real.log t = 2 * Real.log (Real.sqrt t) := by
        rw [Real.log_sqrt (le_of_lt ht0)]; ring
      nlinarith
    have hp1 : t ^ ((1 : ℝ) / 2) = Real.exp (Real.log t * ((1 : ℝ) / 2)) :=
      Real.rpow_def_of_pos ht0 ((1 : ℝ) / 2)
    have hp2 : Real.log t * ((1 : ℝ) / 2) ≤ 6 + t / 24 := by nlinarith
    have hp3 : t ^ ((1 : ℝ) / 2) ≤ Real.exp (6 + t / 24) := by
      rw [hp1]; exact Real.exp_le_exp.mpr hp2
    have hxexp : x = Real.exp t := by rw [htdef, hxdef, Real.exp_log hx0']
    have hp4 : Real.exp (6 + t / 24) = Real.exp 6 * x ^ ((1 : ℝ) / 24) := by
      rw [hxexp, Real.rpow_def_of_pos (Real.exp_pos t), Real.log_exp t]
      have hdiv : t * ((1 : ℝ) / 24) = t / 24 := by ring
      rw [hdiv, ← Real.exp_add]
    rw [hp4] at hp3
    exact hp3
  -- the sqrt term
  have hx34x : x ^ ((3 : ℝ) / 4) * x = x ^ ((7 : ℝ) / 4) := by
    have h1 : x ^ ((3 : ℝ) / 4) * x ^ ((1 : ℝ)) = x ^ ((3 : ℝ) / 4 + 1) :=
      (Real.rpow_add hx0' ((3 : ℝ) / 4) 1).symm
    rw [Real.rpow_one] at h1
    norm_num at h1
    exact h1
  have hmid2 : (n : ℝ) * (Real.log ((n : ℝ) + 2) * Real.log (Real.log ((n : ℝ) + 2) + 2)) ≤
      (n : ℝ) * ((2 * x) * (3 * t)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul hLle hL2le hL20 (by linarith)) (Nat.cast_nonneg _)
  have hS : (m : ℝ) * (n : ℝ) * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2) ≤
      12 * ((n : ℝ) * (n : ℝ)) * x ^ ((7 : ℝ) / 4) * t := by
    have hab : (m : ℝ) * ((n : ℝ) * (Real.log ((n : ℝ) + 2) *
        Real.log (Real.log ((n : ℝ) + 2) + 2))) ≤
        (2 * (n : ℝ) * x ^ ((3 : ℝ) / 4)) * ((n : ℝ) * ((2 * x) * (3 * t))) :=
      mul_le_mul hmR2 hmid2
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hL0 hL20))
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Nat.cast_nonneg (n : ℕ)))
          (Real.rpow_nonneg hx0 ((3 : ℝ) / 4)))
    calc (m : ℝ) * (n : ℝ) * Real.log ((n : ℝ) + 2) *
          Real.log (Real.log ((n : ℝ) + 2) + 2)
        = (m : ℝ) * ((n : ℝ) * (Real.log ((n : ℝ) + 2) *
            Real.log (Real.log ((n : ℝ) + 2) + 2))) := by ring
      _ ≤ (2 * (n : ℝ) * x ^ ((3 : ℝ) / 4)) * ((n : ℝ) * ((2 * x) * (3 * t))) := hab
      _ = 12 * ((n : ℝ) * (n : ℝ)) * x ^ ((7 : ℝ) / 4) * t := by rw [← hx34x]; ring
  have hsqrt78 : Real.sqrt (x ^ ((7 : ℝ) / 4)) = x ^ ((7 : ℝ) / 8) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0 ((7 : ℝ) / 4) ((1 : ℝ) / 2)]
    norm_num
  have hsplit : Real.sqrt (12 * ((n : ℝ) * (n : ℝ)) * x ^ ((7 : ℝ) / 4) * t) =
      Real.sqrt 12 * (n : ℝ) * x ^ ((7 : ℝ) / 8) * t ^ ((1 : ℝ) / 2) := by
    have hA : (0 : ℝ) ≤ 12 * ((n : ℝ) * (n : ℝ)) * x ^ ((7 : ℝ) / 4) :=
      mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (Nat.cast_nonneg (n : ℕ)) (Nat.cast_nonneg (n : ℕ))))
        (Real.rpow_nonneg hx0 ((7 : ℝ) / 4))
    have s1 : Real.sqrt (12 * ((n : ℝ) * (n : ℝ)) * x ^ ((7 : ℝ) / 4) * t) =
        Real.sqrt 12 * Real.sqrt ((n : ℝ) * (n : ℝ)) * Real.sqrt (x ^ ((7 : ℝ) / 4)) *
          Real.sqrt t := by
      rw [Real.sqrt_mul hA, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 12)]
    rw [s1, Real.sqrt_mul_self (Nat.cast_nonneg (n : ℕ)), hsqrt78]
    simp only [Real.sqrt_eq_rpow]
  have hsq : Real.sqrt ((m : ℝ) * (n : ℝ) * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) ≤
      Real.sqrt 12 * (n : ℝ) * x ^ ((7 : ℝ) / 8) * t ^ ((1 : ℝ) / 2) :=
    (Real.sqrt_le_sqrt hS).trans_eq hsplit
  -- combine the sqrt term with the loglog absorption
  have hxe : x ^ ((7 : ℝ) / 8) * (Real.exp 6 * x ^ ((1 : ℝ) / 24)) =
      Real.exp 6 * x ^ ((11 : ℝ) / 12) := by
    have hp : x ^ ((7 : ℝ) / 8) * x ^ ((1 : ℝ) / 24) = x ^ ((11 : ℝ) / 12) := by
      rw [← Real.rpow_add hx0']; norm_num
    rw [← hp]; ring
  have hsq' : Real.sqrt ((m : ℝ) * (n : ℝ) * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) ≤
      Real.sqrt 12 * (Real.exp 6 * ((n : ℝ) * x ^ ((11 : ℝ) / 12))) := by
    calc Real.sqrt ((m : ℝ) * (n : ℝ) * Real.log ((n : ℝ) + 2) *
          Real.log (Real.log ((n : ℝ) + 2) + 2))
        ≤ Real.sqrt 12 * (n : ℝ) * x ^ ((7 : ℝ) / 8) * t ^ ((1 : ℝ) / 2) := hsq
      _ = Real.sqrt 12 * ((n : ℝ) * (x ^ ((7 : ℝ) / 8) * t ^ ((1 : ℝ) / 2))) := by ring
      _ ≤ Real.sqrt 12 *
            ((n : ℝ) * (x ^ ((7 : ℝ) / 8) * (Real.exp 6 * x ^ ((1 : ℝ) / 24)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0 : ℝ) ≤ Real.sqrt 12)
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left ht' (Real.rpow_nonneg hx0 ((7 : ℝ) / 8)))
            (Nat.cast_nonneg (n : ℕ))
      _ = Real.sqrt 12 * (Real.exp 6 * ((n : ℝ) * x ^ ((11 : ℝ) / 12))) := by rw [hxe]; ring
  -- the linear term
  have hx34 : x ^ ((3 : ℝ) / 4) ≤ x ^ ((11 : ℝ) / 12) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  have hm11 : (m : ℝ) ≤ 2 * (n : ℝ) * x ^ ((11 : ℝ) / 12) := by
    calc (m : ℝ) ≤ 2 * (n : ℝ) * x ^ ((3 : ℝ) / 4) := hmR2
      _ = (n : ℝ) * (2 * x ^ ((3 : ℝ) / 4)) := by ring
      _ ≤ (n : ℝ) * (2 * x ^ ((11 : ℝ) / 12)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hx34 (by norm_num : (0 : ℝ) ≤ 2))
            (Nat.cast_nonneg (n : ℕ))
      _ = 2 * (n : ℝ) * x ^ ((11 : ℝ) / 12) := by ring
  have hx11 : (1 : ℝ) ≤ x ^ ((11 : ℝ) / 12) := Real.one_le_rpow hx1 (by norm_num)
  have hnc : (n : ℝ) ≤ (n : ℝ) * x ^ ((11 : ℝ) / 12) := by
    calc (n : ℝ) = (n : ℝ) * 1 := (mul_one _).symm
      _ ≤ (n : ℝ) * x ^ ((11 : ℝ) / 12) :=
          mul_le_mul_of_nonneg_left hx11 (Nat.cast_nonneg (n : ℕ))
  have hnx : (1 : ℝ) ≤ (n : ℝ) * x ^ ((11 : ℝ) / 12) := by
    calc (1 : ℝ) = 1 * 1 := (mul_one _).symm
      _ ≤ (n : ℝ) * x ^ ((11 : ℝ) / 12) :=
          mul_le_mul hn1 hx11 (by norm_num : (0 : ℝ) ≤ 1) (Nat.cast_nonneg (n : ℕ))
  have hsum : (m : ℝ) + (n : ℝ) + 1 ≤ 4 * ((n : ℝ) * x ^ ((11 : ℝ) / 12)) := by
    linarith [hm11, hnc, hnx]
  -- assemble
  have hR : (Real.sqrt 12 * Real.exp 6 + 4) * ((n : ℝ) * x ^ ((11 : ℝ) / 12)) =
      Real.sqrt 12 * (Real.exp 6 * ((n : ℝ) * x ^ ((11 : ℝ) / 12))) +
        4 * ((n : ℝ) * x ^ ((11 : ℝ) / 12)) := by ring
  simp only [Frontier.DMSY.Time, zero_mul, one_mul]
  rw [hR]
  linarith [hsq', hsum]

end BigOSpeedrun.DirectedSSSP

/-! ## The race row -/

open BigOSpeedrun.DirectedSSSP in
/-- **D3/adapter — `Race.bound`**: the corrected DMSY program (the D1 dispatcher over
the body, D2 Bellman–Ford fallback) meets the verifier's `Bound` for the race row
`(a, b, a', b', c') = (1, 3/4, 1, 11/12, 0)`, at `N = 2^16`, bridged from the lane's
`Frontier.DMSY.bound` with `(a, b, e, C₁, a', b', c') = (1, 1, 2, 1, 0, 1, 1)`.
The only unproved input is `DInputs.hsp`, the DMSY body's sparse-clause specification
(package C + the joint `Main.lean` seam); everything else — the dominance of the lane's
time shape over the row's `n (log n)^(11/12)`, the cap containment, `P.Exact`, the
fallback clause — is proved. -/
theorem Race.bound :
    BigOSpeedrun.DirectedSSSP.Bound ((1 : ℚ) / 1) ((3 : ℚ) / 4) ((1 : ℚ) / 1)
      ((11 : ℚ) / 12) ((0 : ℚ) / 1) := by
  -- the one seam: the DMSY body's sparse clause (package C + joint Main.lean).
  -- Placeholder witnesses until package C's body lands.
  have hin : Frontier.DMSY.DInputs 1 1 2 Frontier.RAM.Stmt.skip [] 1 0 1 1 :=
    ⟨by norm_num, by norm_num, by norm_num, by norm_num, le_refl _, by norm_num,
      le_refl _, by sorry⟩
  obtain ⟨P, C, hC, hsp, hfb⟩ :=
    Frontier.DMSY.bound (a := 1) (b := 1) (e := 2) hin
  refine ⟨P, ?_, C * (Real.sqrt 12 * Real.exp 6 + 4), by positivity, 65536, by norm_num,
    ?_, ?_⟩
  · -- exactness from the fallback clause
    intro G s
    obtain ⟨fuel, r, hr, hsol, -⟩ := hfb G s
    exact ⟨fuel, r, hr, hsol⟩
  · -- sparse clause: our Time (a'=0) is dominated by the row's T(n)
    intro G s hN hSp
    obtain ⟨fuel, r, hr, hsol, hcost⟩ := hsp G s (cap_of_sparse (by omega) hSp)
    refine ⟨fuel, r, hr, hsol, ?_⟩
    have hK := time_dominance hN hSp
    have hC0 : (0 : ℝ) ≤ C := hC.le
    nlinarith [hK, hC0]
  · -- fallback clause: the row's constant only enlarges the budget
    intro G s
    obtain ⟨fuel, r, hr, hsol, hcost⟩ := hfb G s
    refine ⟨fuel, r, hr, hsol, ?_⟩
    have hK1 : (1 : ℝ) ≤ Real.sqrt 12 * Real.exp 6 + 4 := by
      have h1 : (0 : ℝ) ≤ Real.sqrt 12 * Real.exp 6 := by positivity
      nlinarith
    have hX0 : (0 : ℝ) ≤ ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by positivity
    nlinarith [hcost, hC.le, hK1, mul_nonneg hC.le hX0]

#print axioms Race.bound

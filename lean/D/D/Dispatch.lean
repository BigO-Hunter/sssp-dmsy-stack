import D.Fallback

/-!
# Frontier.DMSY.Dispatch — D1: dispatcher + fallback routing (work package D)

Work package **D1 (dispatch)**.  The Tdisp-style dispatcher of the C-HD precedent
(`Frontier.CHD.Dispatch.dispatch_runs`), retargeted to the corrected DMSY program:

* `Cap a b n = a · n · (log₂ n) ^ b` — the density threshold, IMPLAN's `m ≤ n · F n`
  with `F n = a · (log₂ n) ^ b` (task key lemma 1's regime `m ≤ Cap a b n`);
* `Time a' b' c' n m` — the sparse-clause time: the two DMSY terms of the lane's final
  bound `O(m √(log n) + √(m n log n loglog n))` plus a lower-order `O(m + n)` term
  (forced: a uniform program pays `Ω(n)` to emit its `n`-entry output arrays);
* `Tdisp` — the dispatch target: sparse clause for `m ≤ Cap a b n`, polynomial
  fallback `(n+1)(m+1)` otherwise;
* `dmsyDispatch` — the RAM dispatcher: `logProg` sets `pa := log₂ n` (frozen CHD
  source), an unrolled `b`-step loop sets `pr := a · pa ^ b`, and the branch
  `pr · n < m` routes to the D2 Bellman–Ford fallback iff `Cap a b n < m`;
* `dmsy_dispatch_runs` — the composition: the DMSY body's sparse-clause spec (package
  C's per-call cost + the joint `Main.lean` assembly — the one input D does not yet
  have) and D2's fallback spec imply `Runs … (C · Tdisp …)`, dispatch overhead
  absorbed into `C := C₁ + b + 17`.  This is CHD's `chdTarget_of_body` shape.
-/

namespace Frontier.DMSY

open Frontier Frontier.RAM WExpr Stmt
open Frontier.CHD.Dispatch

/-! ## D1 statements -/

/-- **D1 — the density cap** `Cap a b n = a · n · (log₂ n) ^ b`: the sparse-clause
regime `m ≤ Cap a b n` of the lane's `Bound a b a' b' c'`. -/
def Cap (a b : ℕ) (n : ℕ) : ℕ := a * n * (Nat.log 2 n) ^ b

/-- **D1 — the sparse-clause time** `Time a' b' c' n m`: `a'·m·√(log(n+2))` (first DMSY
term) `+ b'·√(m·n·log(n+2)·log(log(n+2)+2))` (second DMSY term) `+ c'·(n+m+1)` (the
lower-order term a uniform program is forced to pay: allocating the `n`-entry `reach`
and `dist` output arrays alone costs `2n + 2`). -/
noncomputable def Time (a' b' c' : ℝ) (n m : ℕ) : ℝ :=
  a' * (m : ℝ) * Real.sqrt (Real.log ((n : ℝ) + 2)) +
    b' * Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) +
    c' * ((m : ℝ) + n + 1)

/-- **D1 — the dispatch target time**: sparse clause `Time a' b' c' n m` for
`m ≤ Cap a b n`, polynomial fallback `(n+1)(m+1)` otherwise (the Tdisp shape). -/
noncomputable def Tdisp (a b : ℕ) (a' b' c' : ℝ) (n m : ℕ) : ℝ :=
  if m ≤ Cap a b n then Time a' b' c' n m else ((n : ℝ) + 1) * ((m : ℝ) + 1)

theorem time_nonneg {a' b' c' : ℝ} (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c')
    (n m : ℕ) : 0 ≤ Time a' b' c' n m := by
  unfold Time
  have h1 : 0 ≤ Real.sqrt (Real.log ((n : ℝ) + 2)) := Real.sqrt_nonneg _
  have h2 : 0 ≤ Real.sqrt ((m : ℝ) * n * Real.log ((n : ℝ) + 2) *
      Real.log (Real.log ((n : ℝ) + 2) + 2)) := Real.sqrt_nonneg _
  have h3 : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have h4 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have h5 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have h6 : 0 ≤ Real.log (Real.log ((n : ℝ) + 2) + 2) :=
    Real.log_nonneg (by linarith)
  nlinarith [mul_nonneg ha' h3, mul_nonneg hb' (mul_nonneg (mul_nonneg h3 h4) (mul_nonneg h5 h6)),
    mul_nonneg hc' (by linarith : (0 : ℝ) ≤ (m : ℝ) + n + 1)]

/-! ## Word-safety of the threshold computation -/

/-- Core cap bound: `a · n ^ (b+1)` — the largest value the threshold computation can
reach — stays strictly below the machine cap `(n+m+2) ^ (e+1)` under the parameter
conditions `b ≤ e`, `a + 1 ≤ 3 ^ (e-b)`. -/
theorem pow_core_lt_cap {a b e n m : ℕ} (hbe : b ≤ e) (ha : a + 1 ≤ 3 ^ (e - b))
    (hn : 1 ≤ n) : a * n ^ (b + 1) < (n + m + 2) ^ (e + 1) := by
  have hN3 : 3 ≤ n + m + 2 := by omega
  have ha' : a < 3 ^ (e - b) := Nat.lt_of_succ_le ha
  have hp1 : 3 ^ (e - b) ≤ (n + m + 2) ^ (e - b) := Nat.pow_le_pow_left (by omega) (e - b)
  have hp2 : n ^ (b + 1) ≤ (n + m + 2) ^ (b + 1) := Nat.pow_le_pow_left (by omega) (b + 1)
  have hpos : 0 < n ^ (b + 1) := pow_pos (by omega : (0 : ℕ) < n) (b + 1)
  calc a * n ^ (b + 1) < 3 ^ (e - b) * n ^ (b + 1) := Nat.mul_lt_mul_of_pos_right ha' hpos
    _ ≤ (n + m + 2) ^ (e - b) * (n + m + 2) ^ (b + 1) := Nat.mul_le_mul hp1 hp2
    _ = (n + m + 2) ^ ((e - b) + (b + 1)) := (Nat.pow_add (n + m + 2) (e - b) (b + 1)).symm
    _ = (n + m + 2) ^ (e + 1) := by congr 1; omega

/-- Every intermediate `a · (log₂ n) ^ k` (`k ≤ b+1`) of the unrolled threshold loop
stays below the machine cap. -/
theorem threshold_lt_cap {a b e n m : ℕ} (hbe : b ≤ e) (ha : a + 1 ≤ 3 ^ (e - b))
    (hn : 1 ≤ n) : ∀ k ≤ b + 1, a * (Nat.log 2 n) ^ k < (n + m + 2) ^ (e + 1) := by
  intro k hk
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have h1 : a * (Nat.log 2 n) ^ k ≤ a * n ^ (b + 1) := by
    calc a * (Nat.log 2 n) ^ k ≤ a * n ^ k :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog k)
      _ ≤ a * n ^ (b + 1) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega : k ≤ b + 1))
  exact lt_of_le_of_lt h1 (pow_core_lt_cap hbe ha hn)

/-- The branch-test product `pr · n = a · (log₂ n) ^ b · n = Cap a b n` stays below cap. -/
theorem mul_cap_lt_cap {a b e n m : ℕ} (hbe : b ≤ e) (ha : a + 1 ≤ 3 ^ (e - b))
    (hn : 1 ≤ n) : a * (Nat.log 2 n) ^ b * n < (n + m + 2) ^ (e + 1) := by
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have h1 : a * (Nat.log 2 n) ^ b * n ≤ a * n ^ (b + 1) := by
    calc a * (Nat.log 2 n) ^ b * n ≤ a * n ^ b * n :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hlog b))
      _ = a * n ^ (b + 1) := by rw [Nat.pow_succ, Nat.mul_assoc]
  exact lt_of_le_of_lt h1 (pow_core_lt_cap hbe ha hn)

/-- The small literals and input registers of the dispatcher stay below cap. -/
theorem small_vals_lt_cap (e n m : ℕ) (he : 1 ≤ e) :
    2 < (n + m + 2) ^ (e + 1) ∧ n + 2 < (n + m + 2) ^ (e + 1) := by
  have hN3 : 2 ≤ n + m + 2 := by omega
  have hsq : n + m + 2 < (n + m + 2) ^ 2 := by
    have h1 : (n + m + 2) * 2 ≤ (n + m + 2) * (n + m + 2) := Nat.mul_le_mul_left _ hN3
    have h2 : (n + m + 2) * (n + m + 2) = (n + m + 2) ^ 2 := (pow_two _).symm
    omega
  have hstep : (n + m + 2) ^ 2 ≤ (n + m + 2) ^ (e + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hlt : n + m + 2 < (n + m + 2) ^ (e + 1) := lt_of_lt_of_le hsq hstep
  exact ⟨lt_of_le_of_lt hN3 hlt, lt_of_le_of_lt (by omega) hlt⟩

theorem lit_a_lt_cap {a b e n m : ℕ} (hbe : b ≤ e) (ha : a + 1 ≤ 3 ^ (e - b)) (hn : 1 ≤ n) :
    a < (n + m + 2) ^ (e + 1) := by
  have hN3 : 3 ≤ n + m + 2 := by omega
  have ha' : a < 3 ^ (e - b) := Nat.lt_of_succ_le ha
  calc a < 3 ^ (e - b) := ha'
    _ ≤ 3 ^ e := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (n + m + 2) ^ e := Nat.pow_le_pow_left (by omega) e
    _ ≤ (n + m + 2) ^ (e + 1) := Nat.pow_le_pow_right (by omega) (by omega)

theorem lit_b_lt_cap {b e n m : ℕ} (hbe : b ≤ e) : b < (n + m + 2) ^ (e + 1) := by
  have h2 : (2 : ℕ) ≤ n + m + 2 := by omega
  calc b < e + 1 := by omega
    _ ≤ 2 ^ (e + 1) := (@Nat.lt_two_pow_self (e + 1)).le
    _ ≤ (n + m + 2) ^ (e + 1) := Nat.pow_le_pow_left h2 (e + 1)

/-! ## The threshold loop and the dispatcher -/

/-- `pr := pr · pa`, repeated `b` times (unrolled: `b` is a program literal).  With
`pa = log₂ n` from the frozen `logProg`, the exit value is `pr = a · (log₂ n) ^ b`. -/
def powProg : ℕ → Stmt
  | 0 => .skip
  | b + 1 => seq (wset "pr" (mul (var "pr") (var "pa"))) (powProg b)

/-- **D1 — the dispatcher.**  `logProg` sets `pa := log₂ n`; `pr := a · pa ^ b`; run the
D2 Bellman–Ford fallback `BF.prog` iff `pr · n < m` (i.e. `Cap a b n < m`), else the
corrected DMSY `body`.  Scratch names are the frozen dispatcher's (`px pa py pr pq`), so
the body and the fallback see initial-like states (CHD `Agree`/`InitLike`). -/
def dmsyDispatch (a b : ℕ) (body : Stmt) : Stmt :=
  seq logProg (seq (wset "pr" (lit a))
    (seq (powProg b) (ite (lt (mul (var "pr") (var "n")) (var "m")) BF.prog body)))

theorem powProg_runs {V : Type} {ops : VOps V} (b : ℕ) (s : State V) {pa pr : ℕ}
    (hpa : s.w "pa" = pa) (hpr : s.w "pr" = pr)
    (hcap : ∀ k, k ≤ b + 1 → pr * pa ^ k < s.cap) :
    Runs ops (powProg b) s (fun r => r.w "pr" = pr * pa ^ b ∧ Agree ["pr"] s r ∧
      s.cost ≤ r.cost ∧ r.cost ≤ s.cost + b + 1) := by
  induction b generalizing s pr with
  | zero =>
    refine runs_skip ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [State.charge, hpr]
    · exact (Agree.refl ["pr"] s).charge 1
    · simp [State.charge]
    · simp [State.charge]
  | succ b ih =>
    have hmul : evalW s (mul (var "pr") (var "pa")) = some (pr * pa) :=
      evalW_mul_of (by rw [evalW_var, hpr]) (by rw [evalW_var, hpa])
        (by simpa using hcap 1 (by omega))
    refine runs_seq (runs_wset hmul ?_)
    set s1 := ((s.setW "pr" (pr * pa)).charge 1) with hs1
    refine (ih s1 (pr := pr * pa)
      (by simp [hs1, State.setW, State.charge, hpa]) (by simp [hs1, State.setW, State.charge])
      (fun k hk => ?_) |>.mono ?_)
    · have hkey : (pr * pa) * pa ^ k = pr * pa ^ (k + 1) := by
        rw [Nat.pow_succ]; ac_rfl
      rw [hkey, hs1]
      simpa [State.setW, State.charge] using hcap (k + 1) (by omega)
    · rintro r ⟨hr, hA, hle, hlt⟩
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [hr]
        rw [Nat.pow_succ]; ac_rfl
      · exact (((Agree.refl ["pr"] s).setW (by simp) (pr * pa)).charge 1).trans hA
      · have : s.cost ≤ s1.cost := by simp [hs1, State.setW, State.charge]
        exact le_trans this hle
      · have : s1.cost = s.cost + 1 := by simp [hs1, State.setW, State.charge]
        omega

/-! ## D1 composition theorem -/

/-- **D1 — dispatcher composition.**  If the corrected DMSY body meets its sparse-clause
specification on graphs with `m ≤ Cap a b n` (task key lemma 1's input — package C's
per-call cost + the joint `Main.lean` assembly) and the D2 fallback meets its
Bellman–Ford specification on all graphs (D2 `fallback_bodySpec`), the dispatcher runs
within `C · Tdisp a b a' b' c' n m` with `C := C₁ + b + 17`, and is exact.  Word-safety
of the threshold computation needs `1 ≤ e`, `b ≤ e`, `a + 1 ≤ 3 ^ (e-b)`. -/
theorem dmsy_dispatch_runs
    (a b e : ℕ) (he : 1 ≤ e) (hbe : b ≤ e) (ha : a + 1 ≤ 3 ^ (e - b))
    (ps : List Stmt) (body : Stmt) (C₁ : ℝ) (a' b' c' : ℝ)
    (hC₁ : 0 ≤ C₁) (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 1 ≤ c')
    (hbody : BodySpec e ps body (fun G => G.m ≤ Cap a b G.n)
      (fun n m => C₁ * Time a' b' c' n m))
    (G : Graph) (s : Fin G.n) :
    Runs realOps (dmsyDispatch a b body) (init0 e ps G s)
      (fun r => r.Solves G s ∧
        (r.cost : ℝ) ≤ (C₁ + (b : ℝ) + 17) * Tdisp a b a' b' c' G.n G.m) := by
  have hn1 : 1 ≤ G.n := s.pos
  set st0 := init0 e ps G s with hst0
  have hcap0 : st0.cap = (G.n + G.m + 2) ^ (e + 1) := rfl
  have hsv := small_vals_lt_cap e G.n G.m he
  have hcaplog : G.n + 2 < st0.cap := by rw [hcap0]; exact hsv.2
  have hw0 : st0.w "n" = G.n := by simp [hst0, init0, initState]
  have hwm0 : st0.w "m" = G.m := by simp [hst0, init0, initState]
  have hT0 : (st0.cost : ℝ) = 0 := by simp [hst0, init0, initState]
  have hTd_nonneg : 0 ≤ Tdisp a b a' b' c' G.n G.m := by
    unfold Tdisp
    split_ifs
    · exact time_nonneg ha' hb' (zero_le_one.trans hc') G.n G.m
    · positivity
  -- step 1: logProg — `pa := log₂ n`
  refine runs_seq ((logProg_runs st0 G.n hw0 hcaplog).mono ?_)
  rintro s1 ⟨ha1, hA1, hc1⟩
  have hs1cap : s1.cap = st0.cap := hA1.2.2.2.2.2.2.1
  have hs1n : s1.w "n" = G.n := by rw [hA1.1 "n" (by simp)]; exact hw0
  have hs1m : s1.w "m" = G.m := by rw [hA1.1 "m" (by simp)]; exact hwm0
  have hs1pr : s1.w "pr" = 0 := by rw [hA1.1 "pr" (by simp)]; simp [hst0, init0, initState]
  -- step 2: `pr := a`
  have hlit : evalW s1 (lit a) = some a :=
    evalW_lit_of (by rw [hs1cap, hcap0]; exact lit_a_lt_cap hbe ha hn1)
  refine runs_seq (runs_wset hlit ?_)
  set s2 := ((s1.setW "pr" a).charge 1) with hs2
  have hs2cap : s2.cap = st0.cap := by simp [hs2, State.setW, State.charge, hs1cap]
  have hs2pa : s2.w "pa" = Nat.log 2 G.n := by simp [hs2, State.setW, State.charge, ha1]
  have hs2pr : s2.w "pr" = a := by simp [hs2, State.setW, State.charge]
  have hs2n : s2.w "n" = G.n := by simp [hs2, State.setW, State.charge, hs1n]
  have hs2m : s2.w "m" = G.m := by simp [hs2, State.setW, State.charge, hs1m]
  -- step 3: `pr := a · (log₂ n) ^ b`
  refine runs_seq ((powProg_runs b s2 hs2pa hs2pr (fun k hk => ?_)).mono ?_)
  · rw [hs2cap, hcap0]
    exact threshold_lt_cap hbe ha hn1 k hk
  rintro s3 ⟨hpr3, hA3, hle3, hlt3⟩
  have hA23 : Agree scratch st0 s3 :=
    ((hA1.mono (by simp [scratch])).setW (by simp [scratch]) a |>.charge 1).trans
      (hA3.mono (by simp [scratch]))
  have hs3cap : s3.cap = st0.cap := hA23.2.2.2.2.2.2.1
  have hs3n : s3.w "n" = G.n := by rw [hA23.1 "n" (by simp [scratch])]; exact hw0
  have hs3m : s3.w "m" = G.m := by rw [hA23.1 "m" (by simp [scratch])]; exact hwm0
  -- cost bookkeeping through the threshold computation
  have hcostNat : s3.cost + 1 ≤ 3 * G.n + b + 6 := by
    have h1 : s2.cost = 3 + 3 * Nat.log 2 G.n + 1 := by
      simp [hs2, State.setW, State.charge, hc1, hst0, init0, initState]
    have h2 : s3.cost ≤ s2.cost + b + 1 := hlt3
    have hlogn : Nat.log 2 G.n ≤ G.n := Nat.log_le_self 2 G.n
    omega
  have hcostGrow : 3 * G.n + b + 6 ≤ (b + 8) * (G.n + G.m + 1) := by
    have hexp : (b + 8) * (G.n + G.m + 1) =
        b * G.n + b * G.m + b + 8 * G.n + 8 * G.m + 8 := by ring
    rw [hexp]
    have h1 : 0 ≤ b * G.n := Nat.zero_le _
    have h2 : 0 ≤ b * G.m := Nat.zero_le _
    omega
  -- step 4: the branch test `pr · n < m` (⇔ `Cap a b n < m`)
  have hmul : evalW s3 (mul (var "pr") (var "n")) = some (a * (Nat.log 2 G.n) ^ b * G.n) :=
    evalW_mul_of (by rw [evalW_var, hpr3]) (by rw [evalW_var, hs3n])
      (by rw [hs3cap, hcap0]; exact mul_cap_lt_cap hbe ha hn1)
  have htest : evalW s3 (lt (mul (var "pr") (var "n")) (var "m")) =
      some (if a * (Nat.log 2 G.n) ^ b * G.n < G.m then 1 else 0) :=
    evalW_lt_of hmul (by rw [evalW_var, hs3m])
      (by rw [hs3cap, hcap0]; omega)
  have hcapEq : a * (Nat.log 2 G.n) ^ b * G.n = Cap a b G.n := by
    simp [Cap]; ring
  have hcost4 : ((s3.charge 1).cost : ℝ) ≤ ((b : ℝ) + 8) * ((G.n : ℝ) + G.m + 1) := by
    have : (s3.charge 1).cost = s3.cost + 1 := by simp [State.charge]
    rw [this]
    exact_mod_cast le_trans hcostNat hcostGrow
  have hInit4 : InitLike e ps G s ((s3.charge 1)) := (hA23.charge 1)
  by_cases hbranch : a * (Nat.log 2 G.n) ^ b * G.n < G.m
  · -- dense: the Bellman–Ford fallback
    have htest1 : evalW s3 (lt (mul (var "pr") (var "n")) (var "m")) = some 1 := by
      rw [htest]; simp [hbranch]
    refine runs_ite_true htest1 one_ne_zero ?_
    refine (bf_bodySpec e ps G s (s3.charge 1) hInit4 trivial).mono ?_
    rintro r ⟨hsol, hcost⟩
    refine ⟨hsol, ?_⟩
    have hnd : ¬ G.m ≤ Cap a b G.n := by
      intro hc; rw [← hcapEq] at hc; omega
    have hT : Tdisp a b a' b' c' G.n G.m = ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by
      unfold Tdisp; simp [hnd]
    rw [hT]
    have hcoarse : ((s3.charge 1).cost : ℝ) ≤ ((b : ℝ) + 8) * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) := by
      have hle : ((G.n : ℝ) + G.m + 1) ≤ ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by nlinarith
      have hb8 : (0 : ℝ) ≤ b + 8 := by positivity
      nlinarith
    have h9 : (0 : ℝ) ≤ 9 := by norm_num
    have hC1b : (0 : ℝ) ≤ C₁ + (b : ℝ) + 17 := by positivity
    nlinarith
  · -- sparse: the corrected DMSY body
    refine runs_ite_false (by rw [htest]; simp [hbranch]) ?_
    have hsp : G.m ≤ Cap a b G.n := by
      rw [← hcapEq]; omega
    refine (hbody G s (s3.charge 1) hInit4 hsp).mono ?_
    rintro r ⟨hsol, hcost⟩
    refine ⟨hsol, ?_⟩
    have hT : Tdisp a b a' b' c' G.n G.m = Time a' b' c' G.n G.m := by
      unfold Tdisp; simp [hsp]
    rw [hT]
    have hcoarse : ((s3.charge 1).cost : ℝ) ≤ ((b : ℝ) + 8) * Time a' b' c' G.n G.m := by
      have hbase : ((G.n : ℝ) + G.m + 1) ≤ Time a' b' c' G.n G.m := by
        unfold Time
        have h1 : 0 ≤ Real.sqrt (Real.log ((G.n : ℝ) + 2)) := Real.sqrt_nonneg _
        have h2 : 0 ≤ Real.sqrt ((G.m : ℝ) * G.n * Real.log ((G.n : ℝ) + 2) *
            Real.log (Real.log ((G.n : ℝ) + 2) + 2)) := Real.sqrt_nonneg _
        have h3 : 0 ≤ (G.m : ℝ) := Nat.cast_nonneg G.m
        have h4 : 0 ≤ (G.n : ℝ) := Nat.cast_nonneg G.n
        have h5 : 0 ≤ Real.log ((G.n : ℝ) + 2) := Real.log_nonneg (by linarith)
        have h6 : 0 ≤ Real.log (Real.log ((G.n : ℝ) + 2) + 2) := Real.log_nonneg (by linarith)
        nlinarith [mul_nonneg ha' h3, mul_nonneg hb' (mul_nonneg (mul_nonneg h3 h4) (mul_nonneg h5 h6)),
          mul_nonneg (zero_le_one.trans hc') (by linarith : (0 : ℝ) ≤ (G.m : ℝ) + G.n + 1)]
      have hb8 : (0 : ℝ) ≤ b + 8 := by positivity
      nlinarith
    have hC1b : (0 : ℝ) ≤ C₁ + (b : ℝ) + 17 := by positivity
    have hTnn : 0 ≤ Time a' b' c' G.n G.m := time_nonneg ha' hb' (zero_le_one.trans hc') G.n G.m
    nlinarith

end Frontier.DMSY

#print axioms Frontier.DMSY.dmsy_dispatch_runs

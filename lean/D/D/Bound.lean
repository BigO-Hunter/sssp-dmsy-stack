import D.Dispatch

/-!
# Frontier.DMSY.Bound — D3: the lane's `Bound` and `Race.bound` (work package D)

Work package **D3 (Bound statement assembly)**.  The lane's `Bound a b a' b' c'`
(cap parameters `a b`, sparse-time parameters `a' b' c'`) and its assembly `Race.bound`
for the corrected DMSY program, in the C-HD precedent's `chdTarget_of_body` shape: the
program is the D1 dispatcher over the corrected DMSY body with the D2 Bellman–Ford
fallback; the sparse clause (task key lemma 1) is the one input not yet available —
it is package C's per-call cost bound, discharged at the joint `Main.lean` seam
(IMPLAN §2, key lemma 10) — and is taken as the hypothesis.  The fallback clause
(task key lemma 2) is *proved* (D2 + D1 composition).  No `sorry`, no axioms.
-/

namespace Frontier.DMSY

open Frontier Frontier.RAM WExpr Stmt
open scoped NNReal
open Frontier.CHD.Dispatch

/-- **D3 — the corrected DMSY program**: the D1 dispatcher over the corrected DMSY body
`body` (procedure table `ps`, word exponent `e`) with the D2 Bellman–Ford fallback. -/
def dmsyProgram (a b e : ℕ) (body : Stmt) (ps : List Stmt) : Program :=
  ⟨dmsyDispatch a b body, e, ps⟩

/-- **D3 — the lane's `Bound a b a' b' c'`** (task key lemma 3): one uniform program,
exact on every graph and source, within `C · Time a' b' c' n m` on sparse graphs
(`m ≤ Cap a b n`, key lemma 1) and within `C · (n+1)(m+1)` on all graphs (key lemma 2). -/
def Bound (a b : ℕ) (a' b' c' : ℝ) : Prop :=
  ∃ (P : Program) (C : ℝ), 0 < C ∧
    (∀ (G : Graph) (s : Fin G.n), G.m ≤ Cap a b G.n →
      CorrectWithin P G s (C * Time a' b' c' G.n G.m)) ∧
    (∀ (G : Graph) (s : Fin G.n),
      CorrectWithin P G s (C * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))))

/-- `Bound` implies exactness of the witnessing program (its clauses are per-input
correctness with cost). -/
theorem exact_of_bound {a b : ℕ} {a' b' c' : ℝ} (h : Bound a b a' b' c') :
    ∃ P : Program, P.Exact := by
  obtain ⟨P, C, -, hsp, hfb⟩ := h
  refine ⟨P, ?_⟩
  intro G s
  obtain ⟨fuel, r, hr, hsol, -⟩ := hfb G s
  exact ⟨fuel, r, hr, hsol⟩

/-- Bridge from the dispatcher's `Runs` to `CorrectWithin` (the program's `initState`
is the composition's start state, `initState_eq`). -/
theorem correctWithin_of_runs {P : Program} {T : ℝ} {Q : State ℝ≥0 → Prop}
    (h : Runs realOps P.body (initState P G s) Q)
    (hQ : ∀ r, Q r → r.Solves G s ∧ (r.cost : ℝ) ≤ T) : CorrectWithin P G s T := by
  obtain ⟨f, r, hr, hq⟩ := h
  exact ⟨f, r, hr, (hQ r hq).1, (hQ r hq).2⟩

/-- **Poly dominance of `Time`** — `Time a' b' c' n m ≤ (a' + 4·b' + c') · (n+1)(m+1)`.
Ingredient 1 of the constant repair: the sparse time is absorbed by the fallback clause's
polynomial at the price of `K = a' + 4·b' + c'`, so one witness `C = (C₁+b+17)·K` serves
both clauses of `Bound`.  Chain: `m+n+1 ≤ (m+1)(n+1)`; `√(log(n+2)) ≤ n+1`;
`log(n+2)·log(log(n+2)+2) ≤ 12(n+1)` via `log x ≤ 2√x` and `log(x+2) ≤ log x + 1`. -/
theorem time_le_poly {a' b' c' : ℝ} (ha' : 0 ≤ a') (hb' : 0 ≤ b') (hc' : 0 ≤ c')
    (n m : ℕ) : Time a' b' c' n m ≤ (a' + 4 * b' + c') * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
  have nn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have mm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  set L : ℝ := Real.log ((n : ℝ) + 2) with hL
  set L2 : ℝ := Real.log (L + 2) with hL2
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by linarith)
  have hL20 : 0 ≤ L2 := by
    rw [hL2]; apply Real.log_nonneg; linarith [hL0]
  have hL1 : L ≤ (n : ℝ) + 1 := by
    rw [hL]
    have h := Real.log_le_sub_one_of_pos (x := (n : ℝ) + 2) (by linarith)
    linarith
  have hL21 : L2 ≤ L + 1 := by
    rw [hL2]
    have h := Real.log_le_sub_one_of_pos (x := L + 2) (by linarith [hL0])
    linarith
  -- log x ≤ 2 √x  (via log x = 2 log √x and log y ≤ y - 1)
  have hLsqrt : L ≤ 2 * Real.sqrt ((n : ℝ) + 2) := by
    rw [hL]
    have h1 : Real.log ((n : ℝ) + 2) = 2 * Real.log (Real.sqrt ((n : ℝ) + 2)) := by
      rw [Real.log_sqrt (by positivity)]; ring
    have h2 : Real.log (Real.sqrt ((n : ℝ) + 2)) ≤ Real.sqrt ((n : ℝ) + 2) - 1 :=
      Real.log_le_sub_one_of_pos (x := Real.sqrt ((n : ℝ) + 2))
        (Real.sqrt_pos.mpr (by linarith))
    linarith
  have hLsq : L ^ 2 ≤ 4 * ((n : ℝ) + 2) := by
    have h := mul_le_mul hLsqrt hLsqrt hL0 (by positivity)
    have hz : (2 * Real.sqrt ((n : ℝ) + 2)) ^ 2 = 4 * ((n : ℝ) + 2) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
    nlinarith [hz]
  have hLle : L ≤ 2 * ((n : ℝ) + 2) := by
    have hs : Real.sqrt ((n : ℝ) + 2) ≤ (n : ℝ) + 2 := by
      have h1 : ((n : ℝ) + 2) ≤ ((n : ℝ) + 2) ^ 2 := by nlinarith [sq_nonneg ((n:ℝ) + 1), nn]
      have h2 : Real.sqrt ((n : ℝ) + 2) ≤ Real.sqrt (((n : ℝ) + 2) ^ 2) := Real.sqrt_le_sqrt h1
      rwa [Real.sqrt_sq (by positivity)] at h2
    linarith
  -- L * L2 ≤ 12 (n + 1)
  have hLL2 : L * L2 ≤ 12 * ((n : ℝ) + 1) := by
    have h3 : L * L2 ≤ L * (L + 1) := mul_le_mul_of_nonneg_left hL21 hL0
    have h4 : L * (L + 1) = L ^ 2 + L := by ring
    nlinarith [h3, h4, hLsq, hLle]
  -- √(m·n·L·L2) ≤ 4·(m+1)(n+1)
  have hsqrt : Real.sqrt ((m : ℝ) * n * L * L2) ≤ 4 * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have h5 : (0 : ℝ) ≤ (m : ℝ) * n := mul_nonneg mm nn
    have h6 : (m : ℝ) * n * (L * L2) ≤ (m : ℝ) * n * (12 * ((n : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hLL2 h5
    have h7 : (m : ℝ) * n * (12 * ((n : ℝ) + 1)) = 12 * ((m : ℝ) * (n * ((n : ℝ) + 1))) := by ring
    have h8 : (m : ℝ) * (n * ((n : ℝ) + 1)) ≤ ((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2 :=
      mul_le_mul
        (by nlinarith [sq_nonneg ((m:ℝ)), mm] : (m : ℝ) ≤ ((m : ℝ) + 1) ^ 2)
        (by nlinarith : (n : ℝ) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 2)
        (by nlinarith) (by nlinarith [sq_nonneg ((n : ℝ) + 1)])
    have h9 : (m : ℝ) * n * L * L2 ≤ 12 * (((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
      nlinarith [h6, h7, h8]
    have h10 : (m : ℝ) * n * L * L2 ≤ 16 * (((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2) := by
      nlinarith [h9, mul_nonneg (sq_nonneg ((m:ℝ) + 1)) (sq_nonneg ((n:ℝ) + 1))]
    have h11 : Real.sqrt ((m : ℝ) * n * L * L2) ≤
        Real.sqrt (16 * (((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2)) := Real.sqrt_le_sqrt h10
    have h12 : Real.sqrt (16 * (((m : ℝ) + 1) ^ 2 * ((n : ℝ) + 1) ^ 2)) =
        4 * (((m : ℝ) + 1) * ((n : ℝ) + 1)) := by
      have hm1 : 0 ≤ (m : ℝ) + 1 := by linarith
      have hn1 : 0 ≤ (n : ℝ) + 1 := by linarith
      have h4s : (16 : ℝ) = 4 ^ 2 := by norm_num
      rw [h4s, Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4 ^ 2), Real.sqrt_sq (by norm_num),
        Real.sqrt_mul (by positivity : (0:ℝ) ≤ ((m:ℝ) + 1) ^ 2),
        Real.sqrt_sq hm1, Real.sqrt_sq hn1]
    have h13 : Real.sqrt ((m : ℝ) * n * L * L2) ≤ 4 * (((m : ℝ) + 1) * ((n : ℝ) + 1)) :=
      le_trans h11 (by nlinarith [h12])
    nlinarith [h13]
  -- the three terms of `Time`
  have t1 : a' * (m : ℝ) * Real.sqrt L ≤ a' * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have hs : Real.sqrt L ≤ (n : ℝ) + 1 := by
      calc Real.sqrt L ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt hL1
        _ ≤ Real.sqrt (((n : ℝ) + 1) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg ((n:ℝ)), nn])
        _ = (n : ℝ) + 1 := Real.sqrt_sq (by linarith)
    have hms : (m : ℝ) * Real.sqrt L ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) :=
      mul_le_mul (by linarith : (m : ℝ) ≤ (m : ℝ) + 1) hs (Real.sqrt_nonneg _)
        (by linarith : (0 : ℝ) ≤ (m : ℝ) + 1)
    nlinarith [ha', hms]
  have t2 : b' * Real.sqrt ((m : ℝ) * n * L * L2) ≤ (4 * b') * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have h : 0 ≤ ((m : ℝ) + 1) * ((n : ℝ) + 1) := mul_nonneg (by linarith) (by linarith)
    nlinarith [hb', hsqrt, mul_nonneg hb' h]
  have t3 : c' * ((m : ℝ) + n + 1) ≤ c' * (((n : ℝ) + 1) * ((m : ℝ) + 1)) := by
    have h : (m : ℝ) + n + 1 ≤ ((n : ℝ) + 1) * ((m : ℝ) + 1) := by nlinarith [mul_nonneg mm nn]
    exact mul_le_mul_of_nonneg_left h hc'
  have hsum : Time a' b' c' n m = a' * (m : ℝ) * Real.sqrt L +
      b' * Real.sqrt ((m : ℝ) * n * L * L2) + c' * ((m : ℝ) + n + 1) := by
    rw [hL2, hL]; rfl
  nlinarith [t1, t2, t3, hsum]

/-- The three inputs of the assembly: parameter admissibility, the sparse clause of the
DMSY body (key lemma 1's input — package C + joint `Main.lean`), and nonnegative
time parameters. -/
structure DInputs (a b e : ℕ) (body : Stmt) (ps : List Stmt)
    (C₁ a' b' c' : ℝ) : Prop where
  he : 1 ≤ e
  hbe : b ≤ e
  ha : a + 1 ≤ 3 ^ (e - b)
  hC₁ : 0 ≤ C₁
  ha' : 0 ≤ a'
  hb' : 0 ≤ b'
  hc' : 1 ≤ c'
  /-- **Key lemma 1's input** (the one seam left): the DMSY body is correct within
  `C₁ · Time a' b' c' n m` from every initial-like state on graphs with `m ≤ Cap a b n`. -/
  hsp : BodySpec e ps body (fun G => G.m ≤ Cap a b G.n)
    (fun n m => C₁ * Time a' b' c' n m)

/-- **Key lemma 1 — sparse clause.**  The corrected DMSY program is correct within
`C · Time a' b' c' n m` on every graph with `m ≤ Cap a b n`. -/
theorem sparse_clause {a b e : ℕ} {body : Stmt} {ps : List Stmt} {C₁ a' b' c' : ℝ}
    (hin : DInputs a b e body ps C₁ a' b' c') (G : Graph) (s : Fin G.n)
    (hsp : G.m ≤ Cap a b G.n) :
    CorrectWithin (dmsyProgram a b e body ps) G s
      (((C₁ + (b : ℝ) + 17) * (a' + 4 * b' + c')) * Time a' b' c' G.n G.m) := by
  have hruns := dmsy_dispatch_runs a b e hin.he hin.hbe hin.ha ps body C₁ a' b' c'
    hin.hC₁ hin.ha' hin.hb' hin.hc' hin.hsp G s
  refine correctWithin_of_runs
    (Q := fun r => r.Solves G s ∧ (r.cost : ℝ) ≤ (C₁ + (b : ℝ) + 17) * Tdisp a b a' b' c' G.n G.m) ?_ ?_
  · simpa [dmsyProgram, Program.run, initState_eq] using hruns
  · rintro r ⟨hsol, hcost⟩
    refine ⟨hsol, ?_⟩
    have hT : Tdisp a b a' b' c' G.n G.m = Time a' b' c' G.n G.m := by
      unfold Tdisp; simp [hsp]
    rw [hT] at hcost
    have hK : (1:ℝ) ≤ a' + 4 * b' + c' := by linarith [hin.ha', hin.hb', hin.hc']
    have hpos : 0 ≤ Time a' b' c' G.n G.m :=
      time_nonneg hin.ha' hin.hb' (zero_le_one.trans hin.hc') G.n G.m
    have hC1b : (0 : ℝ) ≤ C₁ + (b : ℝ) + 17 := by have := hin.hC₁; positivity
    nlinarith [hcost, hK, hpos, hC1b]

/-- **Key lemma 2 — fallback clause.**  The corrected DMSY program is correct within
`C · (n+1)(m+1)` on *every* graph (the dispatcher routes `Cap a b n < m` to the D2
Bellman–Ford fallback). -/
theorem fallback_clause {a b e : ℕ} {body : Stmt} {ps : List Stmt} {C₁ a' b' c' : ℝ}
    (hin : DInputs a b e body ps C₁ a' b' c') (G : Graph) (s : Fin G.n) :
    CorrectWithin (dmsyProgram a b e body ps) G s
      (((C₁ + (b : ℝ) + 17) * (a' + 4 * b' + c')) * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))) := by
  have hruns := dmsy_dispatch_runs a b e hin.he hin.hbe hin.ha ps body C₁ a' b' c'
    hin.hC₁ hin.ha' hin.hb' hin.hc' hin.hsp G s
  refine correctWithin_of_runs
    (Q := fun r => r.Solves G s ∧ (r.cost : ℝ) ≤ (C₁ + (b : ℝ) + 17) * Tdisp a b a' b' c' G.n G.m) ?_ ?_
  · simpa [dmsyProgram, Program.run, initState_eq] using hruns
  · rintro r ⟨hsol, hcost⟩
    refine ⟨hsol, ?_⟩
    have hK : (1:ℝ) ≤ a' + 4 * b' + c' := by linarith [hin.ha', hin.hb', hin.hc']
    have hC1b : (0 : ℝ) ≤ C₁ + (b : ℝ) + 17 := by have := hin.hC₁; positivity
    have hnn : 0 ≤ ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by positivity
    have hpos : 0 ≤ Time a' b' c' G.n G.m :=
      time_nonneg hin.ha' hin.hb' (zero_le_one.trans hin.hc') G.n G.m
    by_cases hsp : G.m ≤ Cap a b G.n
    · have hT : Tdisp a b a' b' c' G.n G.m = Time a' b' c' G.n G.m := by
        unfold Tdisp; simp [hsp]
      rw [hT] at hcost
      have hpoly : Time a' b' c' G.n G.m ≤
          (a' + 4 * b' + c') * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1)) :=
        time_le_poly hin.ha' hin.hb' (zero_le_one.trans hin.hc') G.n G.m
      nlinarith [hcost, hpoly, hC1b]
    · have hT : Tdisp a b a' b' c' G.n G.m = ((G.n : ℝ) + 1) * ((G.m : ℝ) + 1) := by
        unfold Tdisp; simp [hsp]
      rw [hT] at hcost
      nlinarith [hcost, hK, hC1b, hnn]

/-- **D3 — `Race.bound`**: the corrected DMSY program meets the lane's `Bound a b a' b' c'`
at cap parameters `(a, b)` and sparse-time parameters `(a', b', c')`, from the sparse
clause of the DMSY body (task key lemma 1's input — package C's per-call cost, discharged
at the joint `Main.lean` seam) and the proved D2 fallback clause (task key lemma 2).  The
constant is `C := (C₁ + b + 17) · (a' + 4·b' + c')` — the `poly` factor makes the fallback
clause's `(n+1)(m+1)` absorb the sparse clause's `Time` on sparse graphs (key lemma 2 must
hold on *all* graphs); the witnessing program is `dmsyProgram a b e body ps`. -/
theorem bound {a b e : ℕ} {body : Stmt} {ps : List Stmt} {C₁ a' b' c' : ℝ}
    (hin : DInputs a b e body ps C₁ a' b' c') : Bound a b a' b' c' :=
  ⟨dmsyProgram a b e body ps, (C₁ + (b : ℝ) + 17) * (a' + 4 * b' + c'),
    by have hC1b : (0:ℝ) < C₁ + (b : ℝ) + 17 := by have := hin.hC₁; positivity
       have hK : (0:ℝ) ≤ a' + 4 * b' + c' := by linarith [hin.ha', hin.hb', hin.hc']
       have hK1 : (1:ℝ) ≤ a' + 4 * b' + c' := by linarith [hin.ha', hin.hb', hin.hc']
       nlinarith,
    fun G s hsp => sparse_clause hin G s hsp, fun G s => fallback_clause hin G s⟩

end Frontier.DMSY

namespace Race

open Frontier Frontier.RAM
open Frontier.DMSY

/-- **`Race.bound_lane`** (the lane-statement wrapper; the submission entrypoint
`Race.bound` — the verifier's `BigOSpeedrun.DirectedSSSP.Bound` row — is assembled in
`D/D/Adapter.lean` from this module's `Frontier.DMSY.bound`): the corrected DMSY program
satisfies `Bound a b a' b' c'`, conditional only on the DMSY body's sparse-clause
specification `DInputs.hsp` (package C + joint Main.lean). -/
theorem bound_lane {a b e : ℕ} {body : Stmt} {ps : List Stmt} {C₁ a' b' c' : ℝ}
    (hin : Frontier.DMSY.DInputs a b e body ps C₁ a' b' c') :
    Frontier.DMSY.Bound a b a' b' c' :=
  Frontier.DMSY.bound hin

end Race

#print axioms Race.bound_lane

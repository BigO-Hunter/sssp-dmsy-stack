import Frontier.RAMLogic

/-!
# B.Frag — cost-tracked composition of `Runs` specs (work package **B**)

Key lemma 1 of the B work order (`Program.RunsWithin` bounds `r.cost`) needs cost to
*compose* through `seq`/`ite`/`while`/`call`.  `Frontier.RAMLogic` composes runs but
hides cost; `RunsB ops c s K Q` is its cost-tracking variant: a run of `c` from `s`
ending in `Q`, costing **at most `s.cost + K`**.  The composition rules below are the
VCG-style building blocks every B5–B8 fragment spec plugs into (`runsB_*`, mirroring
RAMLogic's `runs_*` and RAMWP's `wp` discipline).

The counted-`while` rule charges exactly what the machine charges: `1` per test
(the `s.charge 1` handed to the body), the body's own budget `K1`, `1` per exit test
— hence `K * (K1 + 1) + 1`.
-/

namespace Frontier.RAM

variable {V : Type} (ops : VOps V)

/-- A run of `c` from `s` ending in `Q`, costing at most `s.cost + K`. -/
def RunsB (c : Stmt) (s : State V) (K : ℕ) (Q : State V → Prop) : Prop :=
  Runs ops c s (fun r => r.cost ≤ s.cost + K ∧ Q r)

variable {ops}

theorem runsB_mono {c : Stmt} {s : State V} {K : ℕ} {Q Q' : State V → Prop}
    (h : RunsB ops c s K Q) (hQ : ∀ r, Q r → Q' r) : RunsB ops c s K Q' :=
  Runs.mono h fun r ⟨hc, hq⟩ => ⟨hc, hQ r hq⟩

/-- Budgets may be re-stated at an equal cost. -/
theorem runsB_congr {c : Stmt} {s : State V} {K K' : ℕ} {Q : State V → Prop}
    (h : K = K') (hb : RunsB ops c s K Q) : RunsB ops c s K' Q := h ▸ hb

theorem runsB_skip {s : State V} {K : ℕ} {Q : State V → Prop} (hK : 1 ≤ K)
    (hQ : Q (s.charge 1)) : RunsB ops .skip s K Q :=
  runs_skip (Q := fun r => r.cost ≤ s.cost + K ∧ Q r)
    ⟨by show s.cost + 1 ≤ s.cost + K; omega, hQ⟩

theorem runsB_wset {x : String} {e : WExpr} {s : State V} {K : ℕ} {Q : State V → Prop} {a : ℕ}
    (he : evalW s e = some a) (hK : 1 ≤ K) (hQ : Q ((s.setW x a).charge 1)) :
    RunsB ops (.wset x e) s K Q :=
  runs_wset he (Q := fun r => r.cost ≤ s.cost + K ∧ Q r)
    ⟨by show s.cost + 1 ≤ s.cost + K; omega, hQ⟩

theorem runsB_wstore {arr : String} {i e : WExpr} {s : State V} {K : ℕ} {Q : State V → Prop}
    {j a : ℕ} (hi : evalW s i = some j) (he : evalW s e = some a) (hj : j < s.wlen arr)
    (hK : 1 ≤ K) (hQ : Q ((s.storeW arr j a).charge 1)) :
    RunsB ops (.wstore arr i e) s K Q :=
  runs_wstore hi he hj (Q := fun r => r.cost ≤ s.cost + K ∧ Q r)
    ⟨by show s.cost + 1 ≤ s.cost + K; omega, hQ⟩

theorem runsB_vstore {arr : String} {i : WExpr} {e : VExpr} {s : State V} {K : ℕ}
    {Q : State V → Prop} {j : ℕ} {a : V} (hi : evalW s i = some j) (he : evalV ops s e = some a)
    (hj : j < s.vlen arr) (hK : 1 ≤ K) (hQ : Q ((s.storeV arr j a).charge 1)) :
    RunsB ops (.vstore arr i e) s K Q :=
  runs_vstore hi he hj (Q := fun r => r.cost ≤ s.cost + K ∧ Q r)
    ⟨by show s.cost + 1 ≤ s.cost + K; omega, hQ⟩

theorem runsB_walloc {arr : String} {e : WExpr} {s : State V} {K : ℕ} {Q : State V → Prop} {k : ℕ}
    (he : evalW s e = some k) (hK : k + 1 ≤ K) (hQ : Q ((s.allocW arr k).charge (k + 1))) :
    RunsB ops (.walloc arr e) s K Q :=
  runs_walloc he (Q := fun r => r.cost ≤ s.cost + K ∧ Q r)
    ⟨by show s.cost + (k + 1) ≤ s.cost + K; omega, hQ⟩

theorem runsB_valloc {arr : String} {e : WExpr} {s : State V} {K : ℕ} {Q : State V → Prop} {k : ℕ}
    (he : evalW s e = some k) (hK : k + 1 ≤ K) (hQ : Q ((s.allocV arr k ops.zero).charge (k + 1))) :
    RunsB ops (.valloc arr e) s K Q :=
  runs_valloc he (Q := fun r => r.cost ≤ s.cost + K ∧ Q r)
    ⟨by show s.cost + (k + 1) ≤ s.cost + K; omega, hQ⟩

/-- Sequencing adds budgets. -/
theorem runsB_seq {a b : Stmt} {s : State V} {K1 K2 : ℕ} {Q : State V → Prop}
    (h : RunsB ops a s K1 (fun s' => RunsB ops b s' K2 Q)) :
    RunsB ops (.seq a b) s (K1 + K2) Q := by
  have h' : Runs ops a s (fun s' => Runs ops b s' (fun r => r.cost ≤ s.cost + (K1 + K2) ∧ Q r)) :=
    Runs.mono h fun r ⟨hc, hb⟩ =>
      Runs.mono hb fun t ⟨ht, hq⟩ => ⟨by omega, hq⟩
  exact runs_seq h'

/-- Conditionals add the test charge `1` to the taken branch's budget. -/
theorem runsB_ite_true {c : WExpr} {a b : Stmt} {s : State V} {K : ℕ} {Q : State V → Prop} {x : ℕ}
    (hc : evalW s c = some x) (hx : x ≠ 0) (h : RunsB ops a (s.charge 1) K Q) :
    RunsB ops (.ite c a b) s (K + 1) Q := by
  have h' : Runs ops a (s.charge 1) (fun r => r.cost ≤ s.cost + (K + 1) ∧ Q r) :=
    Runs.mono h fun r ⟨hc', hq⟩ => ⟨by
      have h1 : r.cost ≤ s.cost + 1 + K := hc'
      omega, hq⟩
  exact runs_ite_true hc hx h'

theorem runsB_ite_false {c : WExpr} {a b : Stmt} {s : State V} {K : ℕ} {Q : State V → Prop}
    (hc : evalW s c = some 0) (h : RunsB ops b (s.charge 1) K Q) :
    RunsB ops (.ite c a b) s (K + 1) Q := by
  have h' : Runs ops b (s.charge 1) (fun r => r.cost ≤ s.cost + (K + 1) ∧ Q r) :=
    Runs.mono h fun r ⟨hc', hq⟩ => ⟨by
      have h1 : r.cost ≤ s.cost + 1 + K := hc'
      omega, hq⟩
  exact runs_ite_false hc h'

/-- Procedure calls add the entry charge `1` (one return-point cell of space). -/
theorem runsB_call {p : ℕ} {s : State V} {K : ℕ} {Q : State V → Prop} {body : Stmt}
    (hp : s.procs[p]? = some body) (h : RunsB ops body s.enter K Q) :
    RunsB ops (.call p) s (K + 1) Q := by
  have h' : Runs ops body s.enter (fun r => r.cost ≤ s.cost + (K + 1) ∧ Q r) :=
    Runs.mono h fun r ⟨hc', hq⟩ => ⟨by
      have h1 : r.cost ≤ s.cost + 1 + K := hc'
      omega, hq⟩
  exact runs_call hp h'

/-- Counted `while` with a per-iteration budget: `K` iterations of a body that costs
at most `K1` each (from the charged state), then exit.  Total budget
`K * (K1 + 1) + 1`: `1` per test (handed to the body as `s.charge 1`), `K1` of body,
`1` for the final test. -/
theorem runsB_while {c : WExpr} {b : Stmt} (I : ℕ → State V → Prop) (K K1 : ℕ)
    (Q : State V → Prop)
    (hstep : ∀ k < K, ∀ s, I k s → ∃ x, evalW s c = some x ∧ x ≠ 0 ∧
      RunsB ops b (s.charge 1) K1 (I (k + 1)))
    (hexit : ∀ s, I K s → evalW s c = some 0 ∧ Q (s.charge 1)) :
    ∀ s, I 0 s → RunsB ops (.while c b) s (K * (K1 + 1) + 1) Q := by
  intro s0 hs0
  have hstep' : ∀ k < K, ∀ st, (I k st ∧ st.cost ≤ s0.cost + k * (K1 + 1)) →
      ∃ x, evalW st c = some x ∧ x ≠ 0 ∧
        Runs ops b (st.charge 1) (fun r => I (k + 1) r ∧ r.cost ≤ s0.cost + (k + 1) * (K1 + 1)) := by
    intro k hk st ⟨hI, hcost⟩
    obtain ⟨x, hx, hne, hb⟩ := hstep k hk st hI
    exact ⟨x, hx, hne, Runs.mono hb fun r ⟨hr, hI'⟩ => ⟨hI', by
      have hr' : r.cost ≤ st.cost + 1 + K1 := hr
      have hk1 : k * (K1 + 1) + (K1 + 1) = (k + 1) * (K1 + 1) := by ring
      omega⟩⟩
  have hexit' : ∀ st, (I K st ∧ st.cost ≤ s0.cost + K * (K1 + 1)) →
      evalW st c = some 0 ∧
        (fun r => r.cost ≤ s0.cost + (K * (K1 + 1) + 1) ∧ Q r) (st.charge 1) := by
    intro st ⟨hI, hcost⟩
    obtain ⟨hc, hQ⟩ := hexit st hI
    exact ⟨hc, by
      show st.cost + 1 ≤ s0.cost + (K * (K1 + 1) + 1) ∧ Q (st.charge 1)
      exact ⟨by omega, hQ⟩⟩
  exact runs_while (ops := ops) (I := fun k st => I k st ∧ st.cost ≤ s0.cost + k * (K1 + 1))
    (K := K) (Q := fun r => r.cost ≤ s0.cost + (K * (K1 + 1) + 1) ∧ Q r)
    hstep' hexit' s0 ⟨hs0, by omega⟩

end Frontier.RAM

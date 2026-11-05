import B.Frag
import B.Rep
import B.Code
import A4.Semantics

open scoped ENNReal NNReal

/-!
# B.Realize — RAM realization of the corrected DMSY semantics (work package **B**)

The realization seam between `B.Code`'s `Stmt` tree and A4's corrected engine
semantics `Run t` (IMPLAN §2 B5–B8).  Three layers, in the C-HD `RamBody`/`Spine*`
order:

1. **proved glue texts** — `cmpLen_runs` (the O(1) label-comparison primitive, `vle`)
   and `export_runs` (the output loop: full `RunsB` spec, exact write set
   `Unchanged`, and the `OutRep` post that feeds `outRep_solves`);
2. **the realization predicate** `Realizes t P` — every run of the program from
   `initState` returns output arrays decoding the labels of some `Run t` top call —
   and the **key lemmas**: (1) `Program.RunsWithin` bounds `r.cost`
   (`runsWithin_bounds_cost`, `runsWithin_of_runsB`, `runsWithin_of_realizes`);
   (2) `Program.Exact` implies `State.Solves` (`exact_of_realizes`, `solves_of_exact`,
   `exact_solves`);
3. **the B5–B8 obligations** — `BaseSpec`/`FPSpec`/`LevelRealizes`, the contracts the
   deep subroutine texts must discharge (their bodies are the remaining proof work;
   the skeleton is closed without them).

Key lemma 2's hypothesis is `TopComplete` — every `Run` of the top entry is complete
— the deterministic strength of A4's `TopExactAt` (existence); once A4's joint chain
lands (or `Run` determinism at the top entry) the two coincide.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD
open RAM

variable {G : Graph} {s : Fin G.n}

/-! ## The `vle` label-comparison primitive (proved) -/

/-- `cmpLenStmt` writes only `cmp.lt`, sets it to `[lab.dlen[cmp.i] ≤ lab.dlen[cmp.j]]`,
and costs `1`. -/
theorem cmpLen_runs {st : State ℝ≥0} {i j : ℕ}
    (hi : st.w "cmp.i" = i) (hj : st.w "cmp.j" = j)
    (hbi : i < st.vlen "lab.dlen") (hbj : j < st.vlen "lab.dlen")
    (hcap : 1 < st.cap) :
    RunsB realOps cmpLenStmt st 1 (fun r =>
      r.w "cmp.lt" = (if st.va "lab.dlen" i ≤ st.va "lab.dlen" j then 1 else 0) ∧
        Unchanged st r [] [] ["cmp.lt"] []) := by
  have ha : evalV realOps st (.load "lab.dlen" (.var "cmp.i")) = some (st.va "lab.dlen" i) :=
    evalV_load_of (by simp [hi]) hbi
  have hb : evalV realOps st (.load "lab.dlen" (.var "cmp.j")) = some (st.va "lab.dlen" j) :=
    evalV_load_of (by simp [hj]) hbj
  refine runs_vle ha hb hcap (Q := fun r =>
    r.cost ≤ st.cost + 1 ∧
      (r.w "cmp.lt" = (if st.va "lab.dlen" i ≤ st.va "lab.dlen" j then 1 else 0) ∧
        Unchanged st r [] [] ["cmp.lt"] [])) ?_
  refine ⟨?_, ?_, ?_⟩
  · show st.cost + 1 ≤ st.cost + 1; omega
  · show ((st.setW "cmp.lt"
        (if realOps.le (st.va "lab.dlen" i) (st.va "lab.dlen" j) then 1 else 0)).charge 1).w
        "cmp.lt" = if st.va "lab.dlen" i ≤ st.va "lab.dlen" j then 1 else 0
    by_cases h : st.va "lab.dlen" i ≤ st.va "lab.dlen" j <;>
      simp [State.charge, State.setW, realOps, h]
  · exact Unchanged.trans (unchanged_setW "cmp.lt" _)
      (Unchanged.charge _ _ [] [] ["cmp.lt"] [])

/-! ## The output export loop (proved) -/

/-- The export loop's budget: `2n + 3` of prelude (`wset` + two zeroing allocations)
plus `4n + 1` for `n` loop iterations of 3 statements and their tests. -/
def exportBudget (n : ℕ) : ℕ := 6 * n + 4

/-- Export loop state at counter `k`, relative to the export start `st0`. -/
def ExpInv (st0 : State ℝ≥0) (d : Labels G s) (k : ℕ) (q : State ℝ≥0) : Prop :=
  LabTabRep q d ∧ q.w "n" = G.n ∧ 1 < q.cap ∧ G.n < q.cap ∧
    q.wlen "reach" = G.n ∧ q.vlen "dist" = G.n ∧ q.w "v.i" = k ∧
    Unchanged st0 q ["reach"] ["dist"] ["v.i"] [] ∧
    ∀ v : Fin G.n, (v : ℕ) < k → (q.wa "reach" v = 0 ↔ d v = ⊤) ∧
      (d v ≠ ⊤ → ((q.va "dist" v : ℝ≥0) : ℝ≥0∞) = labelLen (d v))

/-- One export-body iteration advances the counter and extends the partial decode. -/
theorem exportBody_runs {st0 : State ℝ≥0} {d : Labels G s} {k : ℕ} {q : State ℝ≥0}
    (hq : ExpInv st0 d k q) (hk : k < G.n) :
    RunsB realOps exportBody (q.charge 1) 3 (ExpInv st0 d (k + 1)) := by
  obtain ⟨hlab, hnq, hcapq, hcapnq, hwlen, hvlen, hvi, hunch, hacc⟩ := hq
  have hi1 : evalW (q.charge 1) (.var "v.i") = some k := by simp [State.charge, hvi]
  have he1 : evalW (q.charge 1) (.load "lab.dfin" (.var "v.i")) = some (q.wa "lab.dfin" k) :=
    evalW_load_of hi1 (by simp [State.charge, hlab.wlen, hk])
  have hj1 : k < (q.charge 1).wlen "reach" := by simp [State.charge, hwlen, hk]
  refine runsB_seq (K1 := 1) (K2 := 2) ?_
  · refine runsB_wstore hi1 he1 hj1 le_rfl ?_
    set q1 : State ℝ≥0 := ((q.charge 1).storeW "reach" k (q.wa "lab.dfin" k)).charge 1 with hq1
    have hi2 : evalW q1 (.var "v.i") = some k := by
      simp [hq1, State.charge, State.storeW, hvi]
    have he2 : evalV realOps q1 (.load "lab.dlen" (.var "v.i")) = some (q1.va "lab.dlen" k) :=
      evalV_load_of hi2 (by simp [hq1, State.charge, State.storeW, hlab.vlen, hk])
    have hj2 : k < q1.vlen "dist" := by
      simp [hq1, State.charge, State.storeW, hvlen, hk]
    refine runsB_seq (K1 := 1) (K2 := 1) ?_
    · refine runsB_vstore hi2 he2 hj2 le_rfl ?_
      set q2 : State ℝ≥0 := ((q1.storeV "dist" k (q1.va "lab.dlen" k)).charge 1) with hq2
      have hi3 : evalW q2 (.var "v.i") = some k := by
        simp [hq2, hq1, State.charge, State.storeW, State.storeV, hvi]
      have he3 : evalW q2 (.lit 1) = some 1 :=
        evalW_lit_of (by simp [hq2, hq1, State.charge, State.storeW, State.storeV, hcapq])
      have h3 : k + 1 < q2.cap := by
        simp [hq2, hq1, State.charge, State.storeW, State.storeV]
        exact lt_of_le_of_lt (by omega : k + 1 ≤ G.n) hcapnq
      have hadd : evalW q2 (.add (.var "v.i") (.lit 1)) = some (k + 1) :=
        evalW_add_of hi3 he3 h3
      refine runsB_wset (a := k + 1) hadd le_rfl ?_
      set q3 : State ℝ≥0 := ((q2.setW "v.i" (k + 1)).charge 1) with hq3
      have u1 : Unchanged q q1 ["reach"] ["dist"] ["v.i"] [] :=
        Unchanged.w3 (Unchanged.trans (Unchanged.charge q 1 ["reach"] [] [] [])
          (Unchanged.trans (unchanged_storeW "reach" k (q.wa "lab.dfin" k))
            (Unchanged.charge _ 1 ["reach"] [] [] [])))
          (fun _ hx => hx) (nil_subset _) (nil_subset _) (fun _ hx => hx)
      have u2 : Unchanged q1 q2 ["reach"] ["dist"] ["v.i"] [] :=
        Unchanged.w3 (Unchanged.trans (unchanged_storeV "dist" k (q1.va "lab.dlen" k))
          (Unchanged.charge _ 1 [] ["dist"] [] []))
          (nil_subset _) (fun _ hx => hx) (nil_subset _) (fun _ hx => hx)
      have u3 : Unchanged q2 q3 ["reach"] ["dist"] ["v.i"] [] :=
        Unchanged.w3 (Unchanged.trans (unchanged_setW "v.i" (k + 1))
          (Unchanged.charge _ 1 [] [] ["v.i"] []))
          (nil_subset _) (nil_subset _) (fun _ hx => hx) (fun _ hx => hx)
      -- assemble `ExpInv st0 d (k + 1) q3`
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact ⟨hlab.wlen, hlab.vlen, hlab.flag, hlab.len⟩
      · exact hnq
      · exact hcapq
      · exact hcapnq
      · simpa [hq3, hq2, hq1, State.charge, State.storeW, State.storeV, State.setW] using hwlen
      · simpa [hq3, hq2, hq1, State.charge, State.storeW, State.storeV, State.setW] using hvlen
      · simp [hq3, hq2, hq1, State.charge, State.storeW, State.storeV, State.setW]
      · exact Unchanged.trans hunch (Unchanged.trans u1 (Unchanged.trans u2 u3))
      · intro v hv
        by_cases hvk : (v : ℕ) = k
        · refine ⟨?_, ?_⟩
          · have hq : q3.wa "reach" v = q.wa "lab.dfin" v := by
              simp [hq3, hq2, hq1, State.charge, State.storeW, State.storeV, State.setW, hvk]
            rw [hq]
            exact hlab.flag v
          · intro hd
            have hq : q3.va "dist" v = q.va "lab.dlen" v := by
              simp [hq3, hq2, hq1, State.charge, State.storeW, State.storeV, State.setW, hvk]
            rw [hq]
            exact hlab.len v (fun e => hd (e ▸ rfl))
        · have h1 := hacc v (by omega)
          refine ⟨?_, ?_⟩
          · have hq : q3.wa "reach" v = q.wa "reach" v := by
              simp [hq3, hq2, hq1, State.charge, State.storeW, State.storeV, State.setW, hvk]
            rw [hq]
            exact h1.1
          · intro hd
            have hq : q3.va "dist" v = q.va "dist" v := by
              simp [hq3, hq2, hq1, State.charge, State.storeW, State.storeV, State.setW, hvk]
            rw [hq]
            exact h1.2 hd

/-- **The export loop is correct RAM code**: from a label table representing `d`, it
produces the output arrays representing `d` (feeding `outRep_solves`), writing only
`reach`/`dist`/`v.i`, within `exportBudget G.n`. -/
theorem export_runs {st : State ℝ≥0} {d : Labels G s}
    (h : LabTabRep st d) (hn : st.w "n" = G.n) (hcap : 1 < st.cap) (hcapn : G.n < st.cap) :
    RunsB realOps exportStmt st (exportBudget G.n)
      (fun r => OutRep r d ∧ Unchanged st r ["reach"] ["dist"] ["v.i"] []) := by
  -- prelude step 1: v.i := 0
  have p1 : RunsB realOps (.wset "v.i" (.lit 0)) st 1 (fun q =>
      LabTabRep q d ∧ q.w "n" = G.n ∧ 1 < q.cap ∧ G.n < q.cap ∧ q.w "v.i" = 0 ∧
      Unchanged st q ["reach"] ["dist"] ["v.i"] []) := by
    refine runsB_wset (evalW_lit_of (by omega)) le_rfl ?_
    exact ⟨⟨h.wlen, h.vlen, h.flag, h.len⟩, hn, hcap, hcapn,
      by simp [State.charge, State.setW],
      Unchanged.w3 (Unchanged.trans (unchanged_setW "v.i" 0)
        (Unchanged.charge _ _ [] [] ["v.i"] [])) (nil_subset _) (nil_subset _) (fun _ hx => hx) (fun _ hx => hx)⟩
  -- prelude step 2: walloc "reach" n
  have p2 : ∀ q, (LabTabRep q d ∧ q.w "n" = G.n ∧ 1 < q.cap ∧ G.n < q.cap ∧ q.w "v.i" = 0 ∧
      Unchanged st q ["reach"] ["dist"] ["v.i"] []) →
      RunsB realOps (.walloc "reach" (.var "n")) q (G.n + 1) (fun q' =>
        LabTabRep q' d ∧ q'.w "n" = G.n ∧ 1 < q'.cap ∧ G.n < q'.cap ∧ q'.w "v.i" = 0 ∧
        q'.wlen "reach" = G.n ∧ Unchanged st q' ["reach"] ["dist"] ["v.i"] []) := by
    intro q hq
    obtain ⟨hlab, hnq, hcapq, hcapnq, hvi, hunch⟩ := hq
    refine runsB_walloc (he := by simp [hnq]) le_rfl ?_
    exact ⟨⟨hlab.wlen, hlab.vlen, hlab.flag, hlab.len⟩, hnq, hcapq, hcapnq,
      by simp [State.charge, State.allocW, hvi],
      by simp [State.charge, State.allocW],
      Unchanged.trans hunch (Unchanged.w3
        (Unchanged.trans (unchanged_allocW "reach" G.n)
          (Unchanged.charge _ _ ["reach"] [] [] []))
        (fun _ hx => hx) (nil_subset _) (nil_subset _) (fun _ hx => hx))⟩
  -- prelude step 3: valloc "dist" n
  have p3 : ∀ q, (LabTabRep q d ∧ q.w "n" = G.n ∧ 1 < q.cap ∧ G.n < q.cap ∧ q.w "v.i" = 0 ∧
      q.wlen "reach" = G.n ∧ Unchanged st q ["reach"] ["dist"] ["v.i"] []) →
      RunsB realOps (.valloc "dist" (.var "n")) q (G.n + 1) (fun q' =>
        LabTabRep q' d ∧ q'.w "n" = G.n ∧ 1 < q'.cap ∧ G.n < q'.cap ∧
        q'.wlen "reach" = G.n ∧ q'.vlen "dist" = G.n ∧ q'.w "v.i" = 0 ∧
        Unchanged st q' ["reach"] ["dist"] ["v.i"] []) := by
    intro q hq
    obtain ⟨hlab, hnq, hcapq, hcapnq, hvi, hwr, hunch⟩ := hq
    refine runsB_valloc (he := by simp [hnq]) le_rfl ?_
    exact ⟨⟨hlab.wlen, hlab.vlen, hlab.flag, hlab.len⟩, hnq, hcapq, hcapnq,
      by simpa [State.charge, State.allocV] using hwr,
      by simp [State.charge, State.allocV],
      by simp [State.charge, State.allocV, hvi],
      Unchanged.trans hunch (Unchanged.w3
        (Unchanged.trans (unchanged_allocV "dist" G.n 0)
          (Unchanged.charge _ _ [] ["dist"] [] []))
        (nil_subset _) (fun _ hx => hx) (nil_subset _) (fun _ hx => hx))⟩
  -- the loop
  have hstep : ∀ k < G.n, ∀ q, ExpInv st d k q → ∃ x,
      evalW q (.lt (.var "v.i") (.var "n")) = some x ∧ x ≠ 0 ∧
      RunsB realOps exportBody (q.charge 1) 3 (ExpInv st d (k + 1)) := by
    intro k hk q hq
    have hall : ExpInv st d k q := hq
    obtain ⟨-, hnq, hcapq, -, -, -, hvi, -, -⟩ := hq
    refine ⟨1, ?_, by norm_num, exportBody_runs hall hk⟩
    have h1 : evalW q (.var "v.i") = some k := by simp [hvi]
    have h2 : evalW q (.var "n") = some G.n := by simp [hnq]
    have h3 := evalW_lt_of h1 h2 hcapq
    simpa [hk] using h3
  have hexit : ∀ q, ExpInv st d G.n q →
      evalW q (.lt (.var "v.i") (.var "n")) = some 0 ∧
      (fun r => OutRep r d ∧ Unchanged st r ["reach"] ["dist"] ["v.i"] []) (q.charge 1) := by
    intro q hq
    obtain ⟨hlab, hnq, hcapq, -, hwlen, hvlen, hvi, hunch, hacc⟩ := hq
    refine ⟨?_, ?_⟩
    · have h1 : evalW q (.var "v.i") = some G.n := by simp [hvi]
      have h2 : evalW q (.var "n") = some G.n := by simp [hnq]
      have h3 := evalW_lt_of h1 h2 hcapq
      simpa using h3
    · exact ⟨⟨hwlen, hvlen, fun v => (hacc v v.isLt).1, fun v hd => (hacc v v.isLt).2 hd⟩,
        Unchanged.trans hunch (Unchanged.charge _ _ ["reach"] ["dist"] ["v.i"] [])⟩
  -- assemble: prelude · loop
  refine runsB_congr ?_ (runsB_seq (K1 := 1)
    (K2 := G.n + 1 + (G.n + 1 + (G.n * (3 + 1) + 1))) ?_)
  · show 1 + (G.n + 1 + (G.n + 1 + (G.n * (3 + 1) + 1))) = 6 * G.n + 4
    omega
  · refine Runs.mono p1 ?_
    intro q hq0
    obtain ⟨hc, hq⟩ := hq0
    refine ⟨hc, ?_⟩
    refine runsB_seq (K1 := G.n + 1) (K2 := G.n + 1 + (G.n * (3 + 1) + 1)) ?_
    refine Runs.mono (p2 q hq) ?_
    intro q' hq'0
    obtain ⟨hc', hq'⟩ := hq'0
    refine ⟨hc', ?_⟩
    refine runsB_seq (K1 := G.n + 1) (K2 := G.n * (3 + 1) + 1) ?_
    refine Runs.mono (p3 q' hq') ?_
    intro q'' hq''0
    obtain ⟨hc'', hq''⟩ := hq''0
    refine ⟨hc'', ?_⟩
    exact runsB_while (ExpInv st d) G.n 3
      (fun r => OutRep r d ∧ Unchanged st r ["reach"] ["dist"] ["v.i"] [])
      hstep hexit q''
      ⟨hq''.1, hq''.2.1, hq''.2.2.1, hq''.2.2.2.1, hq''.2.2.2.2.1,
        hq''.2.2.2.2.2.1, hq''.2.2.2.2.2.2.1, hq''.2.2.2.2.2.2.2,
        fun v hv => absurd hv (by omega)⟩

/-! ## The realization predicate and the key lemmas -/

/-- The top call `BMSSP*(⊤, {s}, lTop t n)` from `initLabels` (A4 `Reach.top`). -/
def topEntry (t : ℕ) (G : Graph) (s : Fin G.n) : CallEntry G s :=
  ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩

/-- **Top-level completeness of every top run** — the deterministic strength of A4's
`TopExactAt` (existence).  Key lemma 2's hypothesis. -/
def TopComplete (t : ℕ) : Prop :=
  ∀ (G : Graph) (s : Fin G.n) (out : CallOut G s),
    Run t (topEntry t G s) out → ∀ v : Fin G.n, Complete out.d' v

/-- **Realization** (the B work order's central target): on every graph and source,
the program's run from `initState` terminates and its output arrays decode the
labels `out.d'` of some `Run t` top call — the RAM program realizes the A4 semantics
at the machine's input/output seam.  The per-call walk (each fragment realizing its
A4 step) is the B5–B8 body work, pinned by `BaseSpec`/`FPSpec`/`LevelRealizes`. -/
def Realizes (t : ℕ) (P : Program) : Prop :=
  ∀ (G : Graph) (s : Fin G.n),
    Reach t (topEntry t G s) →
    ∃ (fuel : ℕ) (r : State ℝ≥0) (out : CallOut G s),
      P.run fuel G s = some r ∧ Run t (topEntry t G s) out ∧ OutRep r out.d'

/-! ### Key lemma 1 — `Program.RunsWithin` bounds `r.cost` -/

/-- Every successful run of `(G, s)` costs at most `T` (determinism). -/
theorem runsWithin_bounds_cost {P : Program} {T : ℝ} (h : P.RunsWithin G s T)
    {fuel : ℕ} {r : State ℝ≥0} (hr : P.run fuel G s = some r) : (r.cost : ℝ) ≤ T :=
  Program.runsWithin_unique h hr

/-- A cost-tracked run of the program body turns any budget into `RunsWithin`. -/
theorem runsWithin_of_runsB {P : Program} {K : ℕ} {Q : State ℝ≥0 → Prop}
    (h : RunsB realOps P.body (initState P G s) K Q) : P.RunsWithin G s K := by
  obtain ⟨f, r, hr, hc, _⟩ := h
  refine ⟨f, r, hr, ?_⟩
  have h0 : (initState P G s).cost = 0 := rfl
  have : r.cost ≤ K := by omega
  exact_mod_cast this

/-- Key lemma 1 at the realization seam: a realizing program whose runs cost at most
`K G.n G.m` runs within that budget. -/
theorem runsWithin_of_realizes {t : ℕ} {P : Program} {K : ℕ → ℕ → ℕ}
    (h : Realizes t P)
    (hcost : ∀ (G : Graph) (s : Fin G.n) (fuel : ℕ) (r : State ℝ≥0) (out : CallOut G s),
      Reach t (topEntry t G s) → P.run fuel G s = some r →
        Run t (topEntry t G s) out → OutRep r out.d' → r.cost ≤ K G.n G.m)
    (G : Graph) (s : Fin G.n) (hre : Reach t (topEntry t G s)) :
    P.RunsWithin G s (K G.n G.m) := by
  obtain ⟨fuel, r, out, hr, hrun, hrep⟩ := h G s hre
  exact ⟨fuel, r, hr, by exact_mod_cast hcost G s fuel r out hre hr hrun hrep⟩

/-! ### Key lemma 2 — `Program.Exact` implies `State.Solves` -/

/-- A realizing program with a complete top call is `Exact`. -/
theorem exact_of_realizes {t : ℕ} {P : Program} (h : Realizes t P) (hc : TopComplete t) :
    P.Exact := by
  intro G s
  obtain ⟨fuel, r, out, hr, hrun, hrep⟩ := h G s (Reach.top (t := t))
  exact ⟨fuel, r, hr, outRep_solves hrep (fun v => hc G s out hrun v)⟩

/-- `Program.Exact` supplies a run that `Solves`. -/
theorem solves_of_exact {P : Program} (h : P.Exact) (G : Graph) (s : Fin G.n) :
    ∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s := h G s

/-- **`Program.Exact` implies `State.Solves`** for *every* run (determinism of
`exec`). -/
theorem exact_solves {P : Program} (h : P.Exact) {fuel : ℕ} {r : State ℝ≥0}
    (hr : P.run fuel G s = some r) : r.Solves G s := by
  obtain ⟨fuel', r', hr', hs⟩ := h G s
  simp only [Program.run] at hr hr'
  rw [exec_det realOps hr hr']
  exact hs

/-! ## The B5–B8 fragment obligations (pinned; discharged by their texts) -/

/-- Standing machine facts every fragment must preserve: the input register `n` and
the word cap (no statement changes the cap; `n` is written by no fragment). -/
def FrameOK (st : State ℝ≥0) : Prop := st.w "n" = G.n ∧ 1 < st.cap ∧ G.n < st.cap

/-- **B8 obligation** — the top-call setup text establishes the entry frame of the
top call from the input registers: label table = `initLabels`, bound block = `⊤`,
seed table = `{s}`, `l.cur = lTop t n`. -/
structure EntrySpec (body : Stmt) (t : ℕ) (wa va wr vr : List String) (Ce : ℕ) : Prop where
  run : ∀ (st : State ℝ≥0) (G : Graph) (s : Fin G.n),
    st.w "n" = G.n → st.w "m" = G.m → st.w "s" = (s : ℕ) → FrameOK (G := G) st →
    RunsB realOps body st Ce (fun r =>
      EntryRep r (topEntry t G s) ∧ FrameOK (G := G) r ∧ Unchanged st r wa va wr vr)

/-- **B5 obligation** — the base-case text realizes A1's `baseRun` (Algorithm 4 with
the (E1) V5 cap): on an entry frame for `⟨e.B, e.S, e.d, initD e.S e.d⟩` it returns
the labels of some `baseRun`, at bounded cost, writing only its names. -/
structure BaseSpec (body : Stmt) (t : ℕ) (wa va wr vr : List String) (Cb : ℕ) : Prop where
  run : ∀ (G : Graph) (s : Fin G.n) (st : State ℝ≥0) (e : BaseIn G s),
    LabTabRep st e.d → st.w "l.cur" = 0 → 1 < st.cap →
    RunsB realOps body st Cb (fun r => ∃ bout,
      baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout ∧
        LabTabRep r bout.d' ∧ Unchanged st r wa va wr vr)

/-- **B6 obligation** — the FindPivots text realizes A2's `fpRun`: labels only
decrease and stay in the label table; the group table `pg.*` decodes `o.P`. -/
structure FPSpec (body : Stmt) (wa va wr vr : List String) (Cf : ℕ) : Prop where
  run : ∀ (G : Graph) (s : Fin G.n) (st : State ℝ≥0) (i : FPIn G s),
    LabTabRep st i.d → 1 < st.cap →
    RunsB realOps body st Cf (fun r => ∃ o, fpRun i o ∧
      LabTabRep r o.d' ∧ GroupRep r o.p o.P ∧ Unchanged st r wa va wr vr)

/-- **B7 obligation** (the spine's realization): the level procedure, called on any
entry frame of a reachable call, returns the exit frame of some `Run t e out` within
the per-call budget `Cl` (package C3's), preserving the procedure table and the
standing machine frame.  Instantiated at the top entry and combined with the
(export) glue, this is `Realizes` (`realizes_of_assembly`). -/
structure LevelRealizes (t : ℕ) (tx : Texts) (Cl : ℕ) : Prop where
  run : ∀ (G : Graph) (s : Fin G.n) (st : State ℝ≥0) (e : CallEntry G s),
    EntryRep st e → st.procs = procs tx → FrameOK (G := G) st → Reach t e →
    RunsB realOps (.call P_LEVEL) st Cl (fun r => ∃ out,
      Run t e out ∧ ExitRep r out ∧ FrameOK (G := G) r ∧ r.procs = procs tx)

end DMSY
end Frontier

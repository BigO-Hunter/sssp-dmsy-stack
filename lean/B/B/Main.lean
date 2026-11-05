import B.Realize

open scoped ENNReal NNReal

/-!
# B.Main — assembly of the RAM realization (work package **B**)

The top of the B work package: the input-frame facts of `initState`, and the
**assembly theorem** `realizes_of_assembly` — given the pinned B5–B8 fragment
obligations (`EntrySpec`, `LevelRealizes`; plus `BaseSpec`/`FPSpec` for their
submodules), the assembled `dmsyProgram tx` **realizes the A4 semantics** `Run t`
(`Realizes`), hence is `Program.Exact` with every run's final state `State.Solves`
(key lemma 2), and runs within the assembled budget (key lemma 1).  Key lemma 3
(name disjointness at assembly) is `B.Names`'s `decide` facts, restated for the
assembly surface below.

Remaining seam (honest): the fragment *texts* of `Texts` and their spec proofs
(`EntrySpec.run`, `LevelRealizes.run`, `BaseSpec.run`, `FPSpec.run`) — the B5–B8
body work.  Everything the skeleton and the glue can prove without them is proved.

Relation to A4's `TopExactAt`: key lemma 2 takes `TopComplete` (every top `Run` is
complete).  A4's `top_exact_at` is the *existence* form; the two coincide once `Run`
is deterministic at the top entry (package C/D), which is the remaining bridge.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD
open RAM

variable {G : Graph} {s : Fin G.n}

/-! ## The input frame of `initState` -/

/-- The input registers of `initState` for `(G, s)`. -/
theorem initState_regs (P : Program) (G : Graph) (s : Fin G.n) :
    (initState P G s).w "n" = G.n ∧ (initState P G s).w "m" = G.m ∧
      (initState P G s).w "s" = (s : ℕ) := by
  simp [initState]

/-- The word cap of `initState` dominates `1` and `n` (words are `O(log n)`-bit:
`wordExp + 1 ≥ 1` powers of `n + m + 2 ≥ 2`). -/
theorem initState_frame (P : Program) (G : Graph) (s : Fin G.n) :
    FrameOK (G := G) (initState P G s) := by
  have hx : 0 < G.n + G.m + 2 := by omega
  have h1 : 1 ≤ (G.n + G.m + 2) ^ P.wordExp := Nat.one_le_pow P.wordExp (G.n + G.m + 2) hx
  have h2 : G.n + G.m + 2 ≤ (G.n + G.m + 2) ^ P.wordExp * (G.n + G.m + 2) := by
    simpa using Nat.mul_le_mul_right (G.n + G.m + 2) h1
  have h3 : (G.n + G.m + 2) ^ (P.wordExp + 1) =
      (G.n + G.m + 2) ^ P.wordExp * (G.n + G.m + 2) := Nat.pow_succ _ _
  have h4 : 2 ≤ G.n + G.m + 2 := by omega
  have h5 : (initState P G s).cap = (G.n + G.m + 2) ^ (P.wordExp + 1) := rfl
  refine ⟨by simp [initState], ?_, ?_⟩
  · show 1 < (initState P G s).cap
    rw [h5, h3]
    omega
  · show G.n < (initState P G s).cap
    rw [h5, h3]
    omega

/-! ## Assembly: the procedure table realizes `Run t` -/

/-- **Assembly** (the B work order's "the program realizes the A4 semantics"):
given the B5–B8 fragment obligations, the assembled program's run from `initState`
returns the output arrays of some `Run t` top call — `Realizes t (dmsyProgram tx)`. -/
theorem realizes_of_assembly {t : ℕ} {tx : Texts} {Ce Cl : ℕ}
    (hentry : EntrySpec tx.entry t [] [] [] [] Ce) (hlev : LevelRealizes t tx Cl) :
    Realizes t (dmsyProgram tx) := by
  intro G s hre
  -- the entry call (from `initState`)
  have hE : RunsB realOps (.call P_ENTRY) (initState (dmsyProgram tx) G s) (Ce + 1)
      (fun r1 => EntryRep r1 (topEntry t G s) ∧ FrameOK (G := G) r1 ∧
        Unchanged ((initState (dmsyProgram tx) G s).enter) r1 [] [] [] []) := by
    refine runsB_call (body := tx.entry) ?_ ?_
    · exact procs_entry tx
    · refine hentry.run ((initState (dmsyProgram tx) G s).enter) G s ?_ ?_ ?_ ?_
      · exact (initState_regs (dmsyProgram tx) G s).1
      · exact (initState_regs (dmsyProgram tx) G s).2.1
      · exact (initState_regs (dmsyProgram tx) G s).2.2
      · exact initState_frame (dmsyProgram tx) G s
  obtain ⟨f1, r1, he1, hq1⟩ := hE
  have hprocs : r1.procs = procs tx := by
    rw [hq1.2.2.2.procs]
    exact dmsyProgram_procs tx
  -- the level call (the `LevelRealizes` obligation covers `call P_LEVEL` itself)
  have hL : RunsB realOps (.call P_LEVEL) r1 Cl
      (fun r2 => ∃ out, Run t (topEntry t G s) out ∧ ExitRep r2 out ∧
        FrameOK (G := G) r2 ∧ r2.procs = procs tx) :=
    hlev.run G s r1 (topEntry t G s) hq1.2.1 hprocs hq1.2.2.1 hre
  obtain ⟨f2, r2, he2, hq2⟩ := hL
  obtain ⟨_, out, hrun, hrep2, hframe2, hprocs2⟩ := hq2
  -- the export call (its body runs from `r2.enter`)
  have hlab' : LabTabRep (r2.enter) out.d' :=
    ⟨hrep2.lab.wlen, hrep2.lab.vlen, hrep2.lab.flag, hrep2.lab.len⟩
  have hX : RunsB realOps (.call P_EXPORT) r2 (exportBudget G.n + 1)
      (fun r3 => OutRep r3 out.d' ∧ Unchanged (r2.enter) r3 ["reach"] ["dist"] ["v.i"] []) := by
    refine runsB_call (s := r2) (body := exportStmt) ?_ ?_
    · rw [hprocs2]; exact procs_export tx
    · exact export_runs hlab' hframe2.1 hframe2.2.1 hframe2.2.2
  obtain ⟨f3, r3, he3, hq3⟩ := hX
  -- assemble the witness
  refine ⟨max (max f1 f2) f3 + 2, r3, out, ?_, hrun, hq3.2.1⟩
  simp only [Program.run]
  show exec realOps (max (max f1 f2) f3 + 2)
    (.seq (.call P_ENTRY) (.seq (.call P_LEVEL) (.call P_EXPORT)))
    (initState (dmsyProgram tx) G s) = some r3
  rw [exec_seq]
  simp only [Option.bind_eq_some_iff]
  refine ⟨r1, ?_, ?_⟩
  · exact exec_mono realOps he1 (by omega)
  · rw [exec_seq]
    simp only [Option.bind_eq_some_iff]
    refine ⟨r2, ?_, ?_⟩
    · exact exec_mono realOps he2 (by omega)
    · exact exec_mono realOps he3 (by omega)

/-! ## The three key lemmas at the assembled program -/

/-- **Key lemma 1** — the assembled program runs within the assembled budget
(once the C3 per-call budgets `Ce`/`Cl` are instantiated). -/
theorem dmsy_runsWithin {t : ℕ} {tx : Texts} {Ce Cl : ℕ}
    (hentry : EntrySpec tx.entry t [] [] [] [] Ce) (hlev : LevelRealizes t tx Cl)
    (hcost : ∀ (G : Graph) (s : Fin G.n) (fuel : ℕ) (r : State ℝ≥0) (out : CallOut G s),
      Reach t (topEntry t G s) → Program.run (dmsyProgram tx) fuel G s = some r →
        Run t (topEntry t G s) out → OutRep r out.d' →
          r.cost ≤ Ce + 1 + (Cl + (exportBudget G.n + 1)))
    (G : Graph) (s : Fin G.n) : (dmsyProgram tx).RunsWithin G s
      ((Ce + 1 + (Cl + (exportBudget G.n + 1)) : ℕ)) :=
  runsWithin_of_realizes (K := fun n _ => Ce + 1 + (Cl + (exportBudget n + 1)))
    (realizes_of_assembly hentry hlev) hcost G s (Reach.top (t := t))

/-- **Key lemma 2** — the assembled program is `Exact`, and every run's final state
`State.Solves`. -/
theorem dmsy_exact {t : ℕ} {tx : Texts} {Ce Cl : ℕ}
    (hentry : EntrySpec tx.entry t [] [] [] [] Ce) (hlev : LevelRealizes t tx Cl)
    (htop : TopComplete t) : (dmsyProgram tx).Exact :=
  exact_of_realizes (realizes_of_assembly hentry hlev) htop

theorem dmsy_solves {t : ℕ} {tx : Texts} {Ce Cl : ℕ}
    (hentry : EntrySpec tx.entry t [] [] [] [] Ce) (hlev : LevelRealizes t tx Cl)
    (htop : TopComplete t) {fuel : ℕ} {r : State ℝ≥0}
    (hr : Program.run (dmsyProgram tx) fuel G s = some r) : r.Solves G s :=
  exact_solves (dmsy_exact hentry hlev htop) hr

/-- **Key lemma 3** — name disjointness at assembly over the concrete inventory
(the full `decide` table is `B.Names`; this is the assembly-surface slice). -/
theorem assembly_names_disjoint :
    (∀ x ∈ glueRegs, x ∉ allWArrs ++ allVArrs) ∧
    (∀ x ∈ outWArrs, x ∉ labWArrs ++ dsWArrs ++ cfWArrs ++ hpWArrs) ∧
    (∀ x ∈ outVArrs, x ∉ labVArrs ++ dsVArrs ++ cfVArrs) ∧
    (∀ x ∈ allRegs, x ∉ allWArrs) ∧
    (∀ x ∈ allRegs, x ∉ allVArrs) := by decide

end DMSY
end Frontier

import Frontier.RAMWitness
import Frontier.CHD.Dispatch

/-!
# Frontier.DMSY.Fallback — D2: the verified Bellman–Ford fallback (work package D)

Work package **D2 (fallback)**.  The polynomial fallback clause of the lane's `Bound`:
one uniform program exact on every graph within `9 · (n + 1) · (m + 1)`.  The program and
its verification are **reused, not rebuilt** (IMPLAN §1): the frozen c-hd-proof source
`Frontier.RAMWitness` supplies the textbook Bellman–Ford `BF.prog` with kernel-checked
`BF.prog_runs_gen` (`n` passes relaxing every edge: cost `≤ 2n + 4 + (9m + 4)n + 1`,
output labels `= G.dist`), and the frozen `Frontier.CHD.Dispatch` supplies the
initial-state wrapper `bf_bodySpec` at the `BodySpec` shape D's dispatcher consumes.

This module also pins `CorrectWithin` — the per-`(G, s)` correctness-with-cost predicate
used by both clauses of the lane's `Bound` (task key lemmas 1 and 2).
-/

namespace Frontier.DMSY

open Frontier Frontier.RAM
open Frontier.CHD.Dispatch

/-- A program correct on `(G, s)` within cost `T`: its run terminates without getting
stuck, outputs exact shortest-path distances, and costs at most `T`. -/
def CorrectWithin (P : Program) (G : Graph) (s : Fin G.n) (T : ℝ) : Prop :=
  ∃ fuel r, P.run fuel G s = some r ∧ r.Solves G s ∧ (r.cost : ℝ) ≤ T

/-- **D2 — the Bellman–Ford fallback** meets the polynomial clause on *every* graph:
`BF.bfProgram` solves `(G, s)` within `9 · (n + 1) · (m + 1)`.  Task key lemma 2 at the
standalone fallback program; the dispatcher-level fallback clause follows from
`dmsy_dispatch_runs` (D1). -/
theorem bf_correctWithin (G : Graph) (s : Fin G.n) :
    CorrectWithin BF.bfProgram G s (9 * (((G.n : ℝ) + 1) * ((G.m : ℝ) + 1))) := by
  have hInit : InitLike 0 [] G s (init0 0 [] G s) := Agree.refl scratch _
  have hruns := bf_bodySpec 0 [] G s (init0 0 [] G s) hInit trivial
  obtain ⟨f, r, hr, hsol, hcost⟩ := hruns
  refine ⟨f, r, ?_, hsol, ?_⟩
  · -- `BF.bfProgram.run` is `exec` from `init0` (`initState_eq`, rfl-defeq)
    simpa [BF.bfProgram, Program.run, initState_eq] using hr
  · have hz : (init0 0 [] G s).cost = 0 := rfl
    simpa [hz] using hcost

/-- The fallback clause in `BodySpec` form (D1's dispatcher consumes exactly this;
CHD's frozen `bf_bodySpec` at the DMSY body-table parameters). -/
theorem fallback_bodySpec (e : ℕ) (ps : List Stmt) :
    BodySpec e ps BF.prog (fun _ => True) (fun n m => 9 * (((n : ℝ) + 1) * ((m : ℝ) + 1))) :=
  bf_bodySpec e ps

end Frontier.DMSY

#print axioms Frontier.DMSY.bf_correctWithin

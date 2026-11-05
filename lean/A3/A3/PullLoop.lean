import A3.PullInv

/-!
# Frontier.DMSY (A3) — the pull subroutine (DMSY Lemma 3.4 in the engine)

Work package **A3 (Pull)**.  The pull subroutine: *pull vertices below the separator from the
priority queue and relax their out-edges*, feeding A4's BMSSP recursion.  Two layers:

* the **pure extraction** (`A3.DStruct.pullRun`): `S'` = keys of `𝒟` below the separator
  `x ≤ Bd`, remainder `𝒟 ∖ S'` — discharges `PullSpec` (`A3Contract`);
* the **settle-and-relax loop** (`PLoop`, this file): while `𝒟` holds a value below `x`, extract
  a *minimum*-key entry (`IsFrontier.complete_of_min` — Dijkstra's selection rule), settle it
  (a `basePull` settlement event, (E3)), and sweep its out-edges under `Bd` (A1's `iter`).

Key lemmas (task spec), all over the loop:

1. **Frontier persists under pull** — `pullLoop_frontier`: `⟨U, 𝒟⟩` stays a frontier for
   `Ũ(Bd, S)` (framework step `IsFrontier.step` per settled vertex, A3.PullInv).
2. **Bound invariant maintained (no label below the separator)** — `pullLoop_bound`: at exit
   every remaining value is `≥ x`, and `x ≤ Bd` (plus `sep`: settled labels `< x`).
3. **Pull set satisfies the invariant needed by A4** — `pullSet_invariant`: every key below the
   separator at entry (`PullSpec`'s `S'`, via `pullRun_pulled`) is settled at exit — settled,
   complete, in `Ũ(Bd, S)`, below the separator and below `Bd`.

Cost: the loop carries A0's operation-table index (`A1.iterCost` per iteration); the extraction
cost is `A3.DStruct.pullCost`; per-call inequalities are package C3's.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The pull-and-relax loop -/

/-- The pull subroutine's loop at bound `Bd` (cost-indexed per A0's operation table): while `𝒟`
holds a value below the pull separator `st.x`, extract a minimum-key entry `(u, lam)` with
`lam < st.x`, settle `u` and sweep its out-edges (`iter`).  The exit condition is exactly the
*no label below the separator* floor. -/
inductive PLoop (Bd : WLab G s) : ℕ → BState G s → BState G s → Prop
  | exit {st : BState G s} (h : ¬ ∃ y v, st.D y = some v ∧ v < st.x) : PLoop Bd 0 st st
  | pull {c : ℕ} {st st' : BState G s} (u : Fin G.n) (lam : WLab G s)
      (hu : st.D u = some lam) (hlt : lam < st.x)
      (hmin : ∀ y μ, st.D y = some μ → lam ≤ μ)
      (hrest : PLoop Bd c (iter Bd u st.x st) st') :
      PLoop Bd (c + iterCost u st) st st'

/-- The invariant holds at every state the loop reaches. -/
theorem loop_pullInv {Bd : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {D0 : DS G s} :
    ∀ {c : ℕ} {st st' : BState G s}, PLoop Bd c st st' → PullInv Bd S d0 D0 st →
      PullInv Bd S d0 D0 st' := by
  intro c st st' h
  induction h with
  | exit h => intro hB; exact hB
  | pull u lam hu hlt hmin hrest ih =>
    intro hB
    exact ih (pullInv_step hB u lam hu hlt hmin)

/-- The pull separator is fixed for the whole loop. -/
theorem loop_x_eq {Bd : WLab G s} {c : ℕ} {st st' : BState G s} (h : PLoop Bd c st st') :
    st'.x = st.x := by
  induction h with
  | exit h => rfl
  | pull u lam hu hlt hmin hrest ih => exact ih.trans rfl

/-- The final state of any loop derivation has no value below the separator. -/
theorem loop_end_floor {Bd : WLab G s} {c : ℕ} {st st' : BState G s} (h : PLoop Bd c st st') :
    ¬ ∃ y v, st'.D y = some v ∧ v < st'.x := by
  induction h with
  | exit h => exact h
  | pull u lam hu hlt hmin hrest ih => exact ih

/-! ## Key lemmas (task spec) -/

/-- **Key lemma 1 — frontier persists under pull.**  `⟨U, 𝒟⟩` remains a frontier for `Ũ(Bd, S)`
through the whole pull-and-relax subroutine. -/
theorem pullLoop_frontier {Bd : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {D0 : DS G s}
    {c : ℕ} {st st' : BState G s} (h : PLoop Bd c st st') (hinv : PullInv Bd S d0 D0 st) :
    IsFrontier st'.d (Utilde Bd (S : Set (Fin G.n))) (settledSet st'.evts) (DS.keys st'.D) :=
  (loop_pullInv h hinv).frontier

/-- At the exit of the loop no remaining value sits below the separator. -/
theorem pullLoop_floor {Bd : WLab G s} {c : ℕ} {st st' : BState G s} (h : PLoop Bd c st st')
    (y : Fin G.n) (v : WLab G s) (hy : st'.D y = some v) : st'.x ≤ v :=
  not_lt.mp (fun hlt => loop_end_floor h ⟨y, v, hy, hlt⟩)

/-- **Key lemma 2 — bound invariant maintained (no label below the separator).**  At the exit
of the loop every remaining value is `≥ x` (the pull separator) and `x ≤ Bd`; settled labels
sit below `x` (`PullInv.sep`). -/
theorem pullLoop_bound {Bd : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {D0 : DS G s}
    {c : ℕ} {st st' : BState G s} (h : PLoop Bd c st st') (hinv : PullInv Bd S d0 D0 st) :
    (∀ y v, st'.D y = some v → st'.x ≤ v) ∧ st'.x ≤ Bd :=
  ⟨fun y v hy => pullLoop_floor h y v hy, (loop_pullInv h hinv).xle⟩

/-- **Key lemma 3 — the pull set satisfies the invariant needed by A4.**  Every key below the
separator at entry — exactly `PullSpec`'s pulled set `S'` (by `pullRun_pulled`) — is settled by
the subroutine at exit: a settlement event of a complete vertex of `Ũ(Bd, S)`, with its label
below the separator and below `Bd`.  This is the `CallPre`-shaped package A4 consumes when it
hands the pulled set on to FindPivots and the children. -/
theorem pullSet_invariant {Bd : WLab G s} {S : Finset (Fin G.n)} {c : ℕ} {st st' : BState G s}
    (h : PLoop Bd c st st') (hinv : PullInv Bd S st.d st.D st) {y : Fin G.n}
    (hy : ∃ μ, st.D y = some μ ∧ μ < st.x) :
    y ∈ settledSet st'.evts ∧ Complete st'.d y ∧ y ∈ Utilde Bd (S : Set (Fin G.n)) ∧
      st'.d y < st'.x ∧ st'.d y < Bd := by
  obtain ⟨μ, hyD, hμlt⟩ := hy
  have hfin := loop_pullInv h hinv
  have hx : st'.x = st.x := loop_x_eq h
  rcases hfin.keep y (by rw [hyD]; simp) with hs | hs
  · exact ⟨hs, hfin.settledComplete y hs, hfin.settledU hs, hfin.sep y hs,
      lt_of_lt_of_le (hfin.sep y hs) hfin.xle⟩
  · exfalso
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hs
    have hv' : v = st'.d y := hfin.fresh y v hv
    have hfloor : st'.x ≤ v := pullLoop_floor h y v hv
    exact absurd
      (calc st'.x ≤ v := hfloor
        _ = st'.d y := hv'
        _ ≤ st.d y := hfin.le y
        _ = μ := (hinv.fresh y μ hyD).symm
        _ < st.x := hμlt
        _ = st'.x := hx.symm)
      (lt_irrefl _)

/-- `PullSpec`'s pulled set is exactly the keys below the separator (`pullRun`'s output), so
`pullSet_invariant` applies verbatim to the contract's `S'`. -/
theorem pullSet_of_pullRun {cap : ℕ} {D : DS G s} {Bd : WLab G s} {S' : Finset (Fin G.n)}
    {x : WLab G s} {D' : DS G s} (h : pullRun cap D Bd S' x D') : S' = belowKeys D x := h.1

end DMSY
end Frontier

import Frontier.DMSY.Basic

/-!
# Frontier.DMSY.State — the corrected DMSY program's key data structures

Work package **A0 (interface)**.  The types on which the corrected algorithm
(CORRECTED_PROOF.md §2, engine deltas E0–E3) operates: call/return records for BMSSP
(Algorithm 3), FindPivots (Algorithm 2) and the base case (Algorithm 4), the settlement-event
log of (E3), and the line-29 re-selection mints behind the Q12 premature-entry carve-out.

These records are the *signature* of the relational big-step judgments written in A1–A4:
A4's `Run : CallEntry → CallOut → Prop` is Algorithm 3 with (E0), (E1), (E3);
A1's `baseRun`, A2's `fpRun` and A3's `pullRun` are the subroutine judgments.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Settlement events (E3: `U` is the settlement log) -/

/-- A **settlement event** (CORRECTED_PROOF §1): a base-case pull (Alg. 4) or a `W'` boundary
append (Alg. 3, line 34). -/
inductive SettleKind where
  | basePull
  | boundaryAppend
  deriving DecidableEq, Repr

/-- One settlement event. -/
structure SettlementEvent (G : Graph) where
  kind : SettleKind
  v : Fin G.n
  deriving DecidableEq, Repr

/-- The vertex set settled by a list of events. -/
def settledSet {G : Graph} (evts : List (SettlementEvent G)) : Set (Fin G.n) :=
  {x | ∃ ev ∈ evts, ev.v = x}

/-! ## Labels as the run's initial state -/

/-- Run initialization (CORRECTED_PROOF §2.2): `d[s] = 0` (the empty walk), `d[v] = ⊤` else. -/
def initLabels (G : Graph) (s : Fin G.n) : Labels G s :=
  fun v => if v = s then ((toW [] : WalkOrd G s) : WLab G s) else ⊤

/-! ## FindPivots (Algorithm 2) -/

/-- FindPivots input: bound `B`, seed set `S`, tree-member cap `k`, entry labels. -/
structure FPIn (G : Graph) (s : Fin G.n) where
  B : WLab G s
  S : Finset (Fin G.n)
  k : ℕ
  d : Labels G s

/-- FindPivots output state: post labels, the `p` pivot groups `P_1 … P_p`, the member set `Q`,
and the completed region `W` (the tree's roots plus interior). -/
structure FPOut (G : Graph) (s : Fin G.n) where
  d' : Labels G s
  p : ℕ
  P : Fin p → Finset (Fin G.n)
  Q : Finset (Fin G.n)
  W : Finset (Fin G.n)

/-! ## BMSSP (Algorithm 3) -/

/-- A `BMSSP*` call's entry state: bound `B`, seed set `S`, level `l`, entry labels `d`. -/
structure CallEntry (G : Graph) (s : Fin G.n) where
  B : WLab G s
  S : Finset (Fin G.n)
  l : ℕ
  d : Labels G s

/-- One entry `(x, val)` minted by Algorithm 3's line-29 re-selection
(`p_j ← argmin_{x ∈ P_j} d[x]; 𝒟.Insert(⟨p_j, d[p_j]⟩)`) — the only unguarded `D`-insert.
`val` is `d[x]` at mint time. -/
structure Mint (G : Graph) (s : Fin G.n) where
  x : Fin G.n
  val : WLab G s

/-- A `BMSSP*` call's return record (CORRECTED_PROOF §3): returned bound `B'`, the settlement
log `U`, the returned structure `𝒟`, return labels, the mints of the **final iteration's**
line-29 re-selection, and that iteration's pivot groups (clause (2b) reads `x ∈ P_j` from them). -/
structure CallOut (G : Graph) (s : Fin G.n) where
  B' : WLab G s
  evts : List (SettlementEvent G)
  D : DS G s
  d' : Labels G s
  mints : List (Mint G s)
  pfin : ℕ
  Pfin : Fin pfin → Finset (Fin G.n)

namespace CallOut

/-- `U`, the settled vertex set (the log projected to vertices). -/
def U (out : CallOut G s) : Set (Fin G.n) := settledSet out.evts

/-- **Premature entries** (Q12 carve-out, CORRECTED_PROOF §3): exactly the entries minted by
the final iteration's line-29 re-selection with `val = d[x]` at mint time and `val < B'`.
`Prem = ∅` automatically if that iteration minted nothing below `B'`. -/
def Premature (out : CallOut G s) (x : Fin G.n) (val : WLab G s) : Prop :=
  Mint.mk x val ∈ out.mints ∧ val < out.B'

/-- The premature set as a predicate on entries. -/
def premature (out : CallOut G s) : Set (Mint G s) :=
  {m | out.Premature m.x m.val}

/-- The carve-out keys `K` (clause (2c)): premature keys with `dis < B'` whose canonical path
visits `S`, i.e. `keys(Prem) ∩ Ũ(B', S)`. -/
def carveKeys (out : CallOut G s) (S : Finset (Fin G.n)) : Set (Fin G.n) :=
  {x | (∃ val, out.Premature x val) ∧ x ∈ Utilde out.B' (S : Set (Fin G.n))}

end CallOut

/-! ## Base case (Algorithm 4, with the (E1) V5 cap) -/

/-- Base-case input: bound `B`, seed set `S`, entry labels, the working structure `𝒟`. -/
structure BaseIn (G : Graph) (s : Fin G.n) where
  B : WLab G s
  S : Finset (Fin G.n)
  d : Labels G s
  D : DS G s

/-- Base-case output record (CORRECTED_PROOF §4.1): the final Pull's separator `B'_pull`
(`B` if `𝒟` drained), the capped return bound `B'_plus`, the returned structure `𝒟_final`
(including post-final-pull inserts), the settlement log, and return labels. -/
structure BaseOut (G : Graph) (s : Fin G.n) where
  B'_pull : WLab G s
  B'_plus : WLab G s
  D_final : DS G s
  evts : List (SettlementEvent G)
  d' : Labels G s

namespace BaseOut

/-- `U`, the settled vertex set. -/
def U (out : BaseOut G s) : Set (Fin G.n) := settledSet out.evts

end BaseOut

end DMSY
end Frontier

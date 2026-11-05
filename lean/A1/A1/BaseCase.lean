import Frontier.DMSY.Lemma37

/-!
# Frontier.DMSY.BaseCase — Algorithm 4 semantics with the (E1) V5 cap

Work package **A1 (base case)**.  The relational big-step semantics `baseRun` of Algorithm 4,
the base case of BMSSP (Duan–Mao–Shu–Yin 2026), on the corrected engine
(CORRECTED_PROOF.md §2.1, §4.1): (E0)–(E3), in particular

* **(E1) V5 cap**: `B'⁺ = min(B'_pull, d_B[𝒟_final])` (`Engine.v5Cap`, `CapLaw`);
* **(E3)** `U` is the settlement **log**; the loop guard `|U| ≤ t³` counts events
  (`t³ = Engine.eventCap t 0`).

The algorithm (task spec): `𝒟` is a min-heap of (label, vertex) pairs **initialized from `S`**.
Loop while `𝒟 ≠ ∅` and `|U| ≤ t³`: pull `(u, x)` from `𝒟` (pull-min at separator `x`, entry of
`u` removed), add `u` to `U`, relax `u`'s out-edges with bound `B`, insert accepted labels.
Return `(B'⁺, U, 𝒟)` with `B'⁺ = min(B'_pull, d_B[𝒟_final])`, `B'_pull` the separator of the
final pull (`B` if `𝒟` was drained).

Conventions (A0): labels are walks (`WLab = WithTop (WalkOrd G s)`), so distinct vertices never
share a finite label; `ext` is the relaxation; `DS` is the keyed keep-min structure.  The pull
separator `x` is chosen relationally (A0's `PullSpec`-style): `u`'s value `< x ≤ B`, `x` is `B`
or a remaining stored value.  Cost is carried as an index of `Loop` per A0's operation table;
per-call cost inequalities are package C3.

Work-horse lemmas used later live in `Frontier.DMSY.BaseInv` / `Frontier.DMSY.BaseCorrect`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Initialization and the pull separator -/

/-- Algorithm 4's `𝒟` initialization from `S`: key `x ∈ S` with value `d x`. -/
def initD (S : Finset (Fin G.n)) (d : Labels G s) : DS G s :=
  fun y => if y ∈ S then some (d y) else none

theorem initD_keys (S : Finset (Fin G.n)) (d : Labels G s) :
    DS.keys (initD (G := G) (s := s) S d) = S := by
  ext y
  simp [DS.keys, initD]

theorem initD_fresh (S : Finset (Fin G.n)) (d : Labels G s) {y : Fin G.n} {lam : WLab G s}
    (h : initD (G := G) (s := s) S d y = some lam) : lam = d y := by
  rw [initD] at h
  split at h <;> simp_all

theorem initD_eq_some {S : Finset (Fin G.n)} {d : Labels G s} {y : Fin G.n} :
    initD (G := G) (s := s) S d y = if y ∈ S then some (d y) else none := rfl

/-! ## Loop state -/

/-- One loop state of Algorithm 4: labels, the structure `𝒟`, the settlement log `evts`, and
the separator `x` of the most recent pull (`B` before the first pull). -/
structure BState (G : Graph) (s : Fin G.n) where
  d : Labels G s
  D : DS G s
  evts : List (SettlementEvent G)
  x : WLab G s

/-! ## One iteration -/

/-- Relaxation of one edge `e` from a label `d` under bound `B` (accept-and-insert; ties are
re-accepted — idempotent store, CORRECTED_PROOF §1): the candidate `d[src] ⊕ e` replaces the
head's label and is inserted into `D` iff `candidate ≤ d[dst]` and `candidate < B`. -/
noncomputable def relaxEdge (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) :
    Labels G s × DS G s :=
  if ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B then
    (Function.update d (G.dst e) (ext (d (G.src e)) e),
      DS.insert D (G.dst e) (ext (d (G.src e)) e))
  else (d, D)

/-- The relaxation sweep of Algorithm 4: all out-edges of `u` (edge-index order), bound `B`. -/
noncomputable def sweep (B : WLab G s) (u : Fin G.n) : List (Fin G.m) → Labels G s → DS G s →
    Labels G s × DS G s
  | [], d, D => (d, D)
  | e :: es, d, D =>
    sweep B u es (if G.src e = u then (relaxEdge B d D e).1 else d)
      (if G.src e = u then (relaxEdge B d D e).2 else D)

/-- One Algorithm-4 iteration: pull `(u, ·)` at separator `x` (entry removed), settle `u`,
sweep `u`'s out-edges with bound `B`, keep the separator for the return. -/
noncomputable def iter (B : WLab G s) (u : Fin G.n) (x : WLab G s) (st : BState G s) :
    BState G s :=
  { d := (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).1,
    D := (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).2,
    evts := st.evts ++ [⟨.basePull, u⟩], x := x }

/-! ## The loop (E3: guard on settlement events) -/

/-- Cost of one iteration (A0 operation table, coarse): two loop/guard tests, an argmin scan of
`|keys 𝒟| ≤ n` comparisons, one delete, one event append, and 2 ops per scanned out-edge. -/
def iterCost (u : Fin G.n) (_st : BState G s) : ℕ :=
  2 + G.n + 2 * ((List.finRange G.m).filter (fun e => G.src e = u)).length

/-- The Algorithm-4 loop: while `𝒟 ≠ ∅` and `|U| ≤ t³` (event count, (E3)), pull-min at a
separator `x` with `lam < x ≤ B` (`x` = `B` or a remaining stored value), settle the pulled
vertex and sweep its out-edges.  The separator `x` of each pull is remembered in the state. -/
inductive Loop (t : ℕ) (B : WLab G s) : ℕ → BState G s → BState G s → Prop
  | exit {st : BState G s} (h : DS.IsEmpty st.D ∨ t ^ 3 < st.evts.length) :
      Loop t B 0 st st
  | pull {c : ℕ} {st st' : BState G s} (u : Fin G.n) (lam x : WLab G s)
      (hne : ¬ DS.IsEmpty st.D) (hg : st.evts.length ≤ t ^ 3)
      (hu : st.D u = some lam)
      (hxgt : lam < x) (hxle : x ≤ B)
      (hxrest : ∀ y μ, y ≠ u → st.D y = some μ → x ≤ μ)
      (hxeq : x = B ∨ ∃ y μ, y ≠ u ∧ st.D y = some μ ∧ x = μ)
      (hrest : Loop t B c (iter B u x st) st') :
      Loop t B (c + iterCost u st) st st'

/-! ## The base-case judgment -/

/-- **Algorithm 4** (base case of BMSSP) with the (E1) V5 cap and (E3) event semantics, as the
cost-indexed relational semantics `baseRun t e out` (A0's `A1` signature, `t` the BMSSP
parameter of the guard `|U| ≤ t³`): `𝒟` initialized from `S`, loop, then
`B'⁺ = min(B'_pull, d_B[𝒟_final])`. -/
def baseRun (t : ℕ) (e : BaseIn G s) (out : BaseOut G s) : Prop :=
  ∃ c st, Loop t e.B c ⟨e.d, e.D, [], e.B⟩ st ∧
    out = { B'_pull := st.x, B'_plus := st.x ⊓ dMin e.B st.D, D_final := st.D,
            evts := st.evts, d' := st.d }

/-- Reachable base-case inputs (CORRECTED_PROOF §2.3, operational closure at the base case):
the entry labels satisfy `CallPre` (walks, Claim C, frontier `⟨∅, S⟩`, `S` below `B`) and `𝒟`
is the Algorithm-4 initialization from `S`.  A4 constructs base-case calls by execution; the
Q9 off-path instance is excluded exactly by this predicate. -/
def ReachBase (e : BaseIn G s) : Prop :=
  CallPre e.B e.S e.d ∧ e.D = initD e.S e.d

end DMSY
end Frontier

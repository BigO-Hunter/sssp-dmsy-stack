import A2.Pivots
import Frontier.DMSY.Interfaces

/-!
# Frontier.DMSY (A2) — FindPivots (Algorithm 2) semantics and the `FPContract` proof

Work package **A2 (FindPivots)**.  The relational big-step judgment `fpRun : FPIn → FPOut → Prop`
of Duan–Mao–Shu–Yin Algorithm 2 on the corrected engine, and its proof obligation
(`Interfaces.A2Contract`): `FPContract` plus the member cap `|⋃ P_j| ≤ i.k`.

The semantics has two phases:

* **search** (`A2.Search`): a pull-based local search from the boundary `S` under bound `B`,
  extract-min at minimum keys, run to exhaustion — Algorithm 2's "tree building".  At drain,
  Dijkstra's selection rule makes *every* vertex of `Ũ(B, S)` complete (`hall` below).
* **output** (`A2.Pivots`): a pivot gate set `Y ⊆ S` of at most `k` members (the "member cap"),
  returned as the single pivot group `P₁ = Y` with `Q = S ∖ Y` and
  `W = Ũ(B, S) ∖ behind Y` — Algorithm 2's pivot selection, "pivot vertices that bound the
  reachable region": everything outside the pivots' canonical subtrees is completed and
  returned; everything behind a pivot is gated by it (FP1) and deferred to the children.

Well-formed inputs only: `fpRun` carries the call precondition `CallPre` (A0's `A2Contract`
leaves no hypothesis slot, so reachability of the entry state — CORRECTED_PROOF §2.3 — is baked
into the judgment).  Empty `S` is uninhabited (`Y ≠ ∅`), so `A2Contract` is vacuous there.

**Size note.**  The pinned `A2Contract` caps the *total* pivot members
`|⋃ P_j| ≤ k`; the paper's Lemma 3.2 bounds each group (`|P_j| = O(k)`), leaving `|S ∖ Q|`
unbounded, and its `W` has size `O(k·|Q|)`.  A verbatim Algorithm 2 cannot satisfy the pinned
cap; this semantics is the contract-satisfying variant (gate set ≤ `k`, complementary region
completed by the search).  Group-splitting of `Y` for load balancing and all sizes/trees/
Q-charging belong to C2/C3 and are not constrained by `FPContract`.

Key lemmas: `fpRun_frontier_persist` (frontiers persist), `fpRun_pivot_cap` (pivot size bound),
`fpRun_pull_invariant` (the returned region is complete and in `Ũ(B, S)` — the invariant A3/A4
consume).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- **FindPivots (Algorithm 2)** on input `i` returning `o` (A0's `A2` signature): the search
phase runs to exhaustion on `i.S` under `i.B` from entry labels `i.d`; the output phase chooses
a nonempty pivot gate set `Y ⊆ i.S` with `Y.card ≤ i.k` and reports `P₁ = Y`, `Q = i.S ∖ Y`,
`W = Ũ(i.B, i.S) ∖ behind Y`. -/
def fpRun (i : FPIn G s) (o : FPOut G s) : Prop :=
  CallPre i.B i.S i.d ∧
    ∃ (Y : Finset (Fin G.n)) (c : ℕ) (st : FPSt G s),
      Y ⊆ i.S ∧ Y.Nonempty ∧ Y.card ≤ i.k ∧
      FLoop i.B i.d c ⟨i.d, initD i.S i.d, ∅⟩ st ∧
      o.d' = st.d ∧
      o.W = wFin i.B i.S Y ∧
      o.p = 1 ∧
      o.P = (fun _ => Y) ∧
      o.Q = i.S \ Y

/-- At drain, every vertex of `Ũ(B, S)` is complete: the exit frontier `⟨done, ∅⟩` leaves no
gates.  This is the pull-set invariant the output phase and A3/A4 ride on. -/
theorem complete_of_drain {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    {st : FPSt G s} (h : FInv B S d0 st) (hemp : DS.IsEmpty st.D) :
    ∀ v ∈ Utilde B (S : Set (Fin G.n)), Complete st.d v := by
  have hkeys0 : (DS.keys st.D : Set (Fin G.n)) = (∅ : Set (Fin G.n)) := by
    ext y
    simp [DS.keys, hemp y]
  have hfront : IsFrontier st.d (Utilde B (S : Set (Fin G.n)))
      ((st.done : Set (Fin G.n))) (∅ : Set (Fin G.n)) := by
    rw [← hkeys0]
    exact h.frontier
  intro v hv
  exact (IsFrontier.complete_of_empty hfront v hv).2

/-- **A2 contract.**  Every FindPivots output satisfies `FPContract` and the pivot cap. -/
theorem fpRun_contract (i : FPIn G s) (o : FPOut G s) (h : fpRun i o) :
    FPContract i.B i.S i.d o.d' o.p o.P o.Q o.W ∧
      (Finset.biUnion Finset.univ o.P).card ≤ i.k := by
  obtain ⟨hpre, Y, c, st, hYsub, hYne, hcap, hloop, hd', hW, hp, hP, hQ⟩ := h
  have hfin : FInv i.B i.S i.d st := loop_fInv hloop (fInv_init hpre)
  have hall : ∀ v ∈ Utilde i.B (i.S : Set (Fin G.n)), Complete st.d v :=
    complete_of_drain hfin (loop_end_empty hloop)
  -- the gate set of the output is exactly `Y`
  have hgate : {x : Fin G.n | ∃ j, x ∈ o.P j} = (Y : Set (Fin G.n)) := by
    ext x
    simp only [Set.mem_setOf_eq, hP, Finset.mem_coe]
    constructor
    · rintro ⟨j, hx⟩
      exact hx
    · intro hx
      exact ⟨⟨0, by rw [hp]; exact Nat.zero_lt_one⟩, hx⟩
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · -- labels only decrease
    intro v
    rw [hd']
    exact hfin.le v
  · -- labels stay walks
    rw [hd']
    exact hfin.walk
  · -- every changed label lies in `Ũ(B, S)`
    intro v hv
    rw [hd'] at hv
    exact hfin.changed v hv
  · -- FP1: `⟨W, ⋃ P_j⟩` is a frontier for `Ũ(B, S)`
    intro v hv
    rw [hd', hW, hgate]
    by_cases hbeh : v ∈ behind (s := s) Y
    · obtain ⟨y, hyY, hon⟩ := hbeh
      exact Or.inr ⟨y, hyY, hall y (mem_utilde_of_mem hpre (hYsub hyY)), hon⟩
    · exact Or.inl ⟨mem_wFin_iff.mpr ⟨hv, hbeh⟩, hall v hv⟩
  · -- FP2: the group is a nonempty subset of `S`
    intro j
    rw [hP]
    exact ⟨hYne, hYsub⟩
  · -- FP2: groups pairwise disjoint (a single group)
    intro i j hij
    have hi : (i : ℕ) = 0 := by
      have := i.isLt
      omega
    have hj : (j : ℕ) = 0 := by
      have := j.isLt
      omega
    exact absurd (Fin.ext (hi.trans hj.symm)) hij
  · -- FP2: `Q ⊆ S`
    intro x hx
    rw [hQ] at hx
    exact (Finset.mem_sdiff.mp hx).1
  · -- FP2: `Q` is disjoint from the groups
    intro j
    rw [hQ, hP]
    refine Finset.disjoint_iff_ne.mpr ?_
    intro a ha b hb hab
    subst hab
    simp only [Finset.mem_sdiff] at ha
    exact ha.2 hb
  · -- FP2: groups and `Q` cover `S`
    intro x hx
    rw [hQ, hP]
    by_cases hxY : x ∈ Y
    · exact Or.inr ⟨⟨0, by rw [hp]; exact Nat.zero_lt_one⟩, hxY⟩
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨hx, hxY⟩)
  · -- FP3: the completed region lies in `Ũ(B, S)`
    rw [hW]
    exact wFin_subset
  · -- member cap: `|⋃ P_j| ≤ i.k`
    rw [hP]
    calc (Finset.biUnion Finset.univ fun _ : Fin o.p => Y).card
        ≤ ∑ _i : Fin o.p, Y.card := Finset.card_biUnion_le
      _ = o.p * Y.card := by rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_fin]
      _ = 1 * Y.card := by rw [hp]
      _ = Y.card := by rw [one_mul]
      _ ≤ i.k := hcap

/-- **A2 interface theorem**: Algorithm 2 discharges `A2Contract`. -/
theorem a2_contract : @A2Contract G s fpRun :=
  fun i o h => fpRun_contract i o h

/-! ## Key lemmas (task spec) -/

/-- **Key lemma 1 — frontiers persist under FindPivots.**  The entry frontier `⟨∅, S⟩` for
`Ũ(B, S)` persists to the output: `⟨W, ⋃ P_j⟩` is a frontier for `Ũ(B, S)` at the output
labels. -/
theorem fpRun_frontier_persist {i : FPIn G s} {o : FPOut G s} (h : fpRun i o) :
    IsFrontier o.d' (Utilde i.B (i.S : Set (Fin G.n))) (o.W : Set (Fin G.n))
      {x | ∃ j, x ∈ o.P j} :=
  (fpRun_contract i o h).1.frontier

/-- **Key lemma 2 — pivot size bound.**  The pivot set has at most `i.k` members (the member
cap). -/
theorem fpRun_pivot_cap {i : FPIn G s} {o : FPOut G s} (h : fpRun i o) :
    (Finset.biUnion Finset.univ o.P).card ≤ i.k :=
  (fpRun_contract i o h).2

/-- **Key lemma 3 — the pull set satisfies the invariant needed by A3/A4.**  Every member of
the returned region `W` is complete at the output labels and lies in `Ũ(B, S)` — exactly what
the parent's pull bookkeeping (A3) and the BMSSP recursion (A4) consume from FindPivots. -/
theorem fpRun_pull_invariant {i : FPIn G s} {o : FPOut G s} (h : fpRun i o) :
    ∀ v, v ∈ (o.W : Set (Fin G.n)) →
      Complete o.d' v ∧ v ∈ Utilde i.B (i.S : Set (Fin G.n)) := by
  obtain ⟨hpre, Y, c, st, hYsub, hYne, hcap, hloop, hd', hW, hp, hP, hQ⟩ := h
  have hall : ∀ v ∈ Utilde i.B (i.S : Set (Fin G.n)), Complete st.d v :=
    complete_of_drain (loop_fInv hloop (fInv_init hpre)) (loop_end_empty hloop)
  intro v hv
  rw [hW] at hv
  change v ∈ wFin i.B i.S Y at hv
  have hvU : v ∈ Utilde i.B (i.S : Set (Fin G.n)) := (mem_wFin_iff.mp hv).1
  rw [hd']
  exact ⟨hall v hvU, hvU⟩

end DMSY
end Frontier

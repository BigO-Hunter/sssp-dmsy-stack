import A2.Search

/-!
# Frontier.DMSY (A2) — the pivot gate structure (Algorithm 2, output phase)

Work package **A2 (FindPivots)**.  The pivot output of Algorithm 2: a pivot gate set
`Y ⊆ S` of at most `k` members (the **member cap** of the lane's `A2Contract`), the pivot
groups `P₁ … P_p` partitioning `Y`, the residual `Q = S ∖ Y`, and the completed region
`W = Ũ(B, S) ∖ behind Y`.  The pivots **bound the reachable region**: every vertex of
`Ũ(B, S)` outside `behind Y` is completed and returned in `W`, and every remaining vertex is
gated by a complete pivot on its canonical path (FP1).  The gated region is what the parent
call's children are seeded with.

Size note: the lane's pinned `A2Contract` caps the *total* pivot members
`|⋃ P_j| ≤ k`; the paper's Lemma 3.2 caps each group only (`|P_j| = O(k)`, union `|S ∖ Q|`).
This output phase is the contract-satisfying variant: a ≤ `k`-sized gate set with the
complementary region completed by the search phase (`A2.Search`).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- The pivot-gated region `behind Y`: vertices whose canonical path visits a pivot of `Y`. -/
def behind {G : Graph} {s : Fin G.n} (Y : Finset (Fin G.n)) : Set (Fin G.n) :=
  {v | ∃ y ∈ Y, OnPath (s := s) y v}

/-- A pivot gates itself. -/
theorem mem_behind_self {Y : Finset (Fin G.n)} {y : Fin G.n} (hy : y ∈ Y)
    (hreach : G.Reachable s y) : y ∈ behind (s := s) Y :=
  ⟨y, hy, onPath_self hreach⟩

/-- Boundary members lie in `Ũ(B, S)`: their canonical path visits themselves. -/
theorem mem_utilde_of_mem {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    (h : CallPre B S d0) {y : Fin G.n} (hy : y ∈ S) : y ∈ Utilde B (S : Set (Fin G.n)) := by
  have hdis : dis (s := s) y < B := by
    have h1 : dis (s := s) y ≤ d0 y := (WalkInv.sound h.walk) y
    exact lt_of_le_of_lt h1 (h.inRange y hy)
  exact ⟨hdis, y, hy, onPath_self (reachable_of_dis_lt hdis)⟩

open Classical in
/-- `W` of the FindPivots output: the completed region not gated by a pivot. -/
noncomputable def wFin (B : WLab G s) (S : Finset (Fin G.n)) (Y : Finset (Fin G.n)) :
    Finset (Fin G.n) :=
  (Finset.univ : Finset (Fin G.n)).filter fun v =>
    v ∈ Utilde B (S : Set (Fin G.n)) ∧ v ∉ behind (s := s) Y

open Classical in
/-- Membership in `W`. -/
theorem mem_wFin_iff {B : WLab G s} {S : Finset (Fin G.n)} {Y : Finset (Fin G.n)}
    {v : Fin G.n} : v ∈ wFin (G := G) (s := s) B S Y ↔
      v ∈ Utilde B (S : Set (Fin G.n)) ∧ v ∉ behind (s := s) Y := by
  unfold wFin
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ v, h⟩⟩

/-- `W` lies in `Ũ(B, S)` (FP3). -/
theorem wFin_subset {B : WLab G s} {S : Finset (Fin G.n)} {Y : Finset (Fin G.n)} :
    (wFin (G := G) (s := s) B S Y : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n)) := by
  intro v hv
  change v ∈ wFin (G := G) (s := s) B S Y at hv
  exact (mem_wFin_iff.mp hv).1

/-- `W` contains exactly the non-gated part of `Ũ(B, S)`. -/
theorem coe_wFin {B : WLab G s} {S : Finset (Fin G.n)} {Y : Finset (Fin G.n)} :
    (wFin (G := G) (s := s) B S Y : Set (Fin G.n))
      = Utilde B (S : Set (Fin G.n)) \ behind (s := s) Y := by
  ext v
  change v ∈ wFin (G := G) (s := s) B S Y ↔
    v ∈ Utilde B (S : Set (Fin G.n)) \ behind (s := s) Y
  rw [mem_wFin_iff]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨h₁, h₂⟩

end DMSY
end Frontier

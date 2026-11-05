import A3.DStruct
import A1.BaseInv

/-!
# Frontier.DMSY (A3) — the pull-and-relax invariant

Work package **A3 (Pull)**.  `PullInv`, the invariant of the pull subroutine "pull vertices
below the separator from `𝒟` and relax their out-edges", and its one-step preservation.  The
step is A1's `iter` (pull a minimum-key entry `(u, lam)` with `lam < x`, settle `u` as a
`basePull` settlement event, sweep `u`'s out-edges under the call bound `Bd`) reused verbatim;
the invariant is A1's `BInv` and A2's `FInv` minus the base-case separator bookkeeping, plus
the two clauses the pull subroutine owes its callers:

* `sep` — every settled label is below the pull separator `st.x` (*bound invariant* half);
* `keep` — every key of the pre-pull store `D0` is either settled or still keyed (labels only
  decrease via `le`, so no below-separator value can survive to the exit).

Settlement completeness (`settledComplete`) rides on the same min-selection rule as A1's
`bInv_step` (`IsFrontier.complete_of_min`): the pull extracts at minimum keys.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The invariant -/

/-- The pull subroutine invariant at bound `Bd` for the frontier region `Ũ(Bd, S)`, entry
labels `d0`, entry store `D0`.  `st.x` is the pull separator (fixed for the whole subroutine). -/
structure PullInv (Bd : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (D0 : DS G s)
    (st : BState G s) : Prop where
  /-- labels are walks (hence sound) -/
  walk : WalkInv st.d
  /-- Claim C of the call precondition survives label lowering -/
  claim : ∀ v, dis (s := s) v < Bd → v ∉ Utilde Bd (S : Set (Fin G.n)) → Complete st.d v
  /-- labels only decrease from the entry labels -/
  le : ∀ v, st.d v ≤ d0 v
  /-- `⟨U, 𝒟⟩` is a frontier for `Ũ(Bd, S)` -/
  frontier : IsFrontier st.d (Utilde Bd (S : Set (Fin G.n))) (settledSet st.evts) (DS.keys st.D)
  /-- keys of `𝒟` lie in `Ũ(Bd, S)` -/
  keys_sub : DS.keys st.D ⊆ Utilde Bd (S : Set (Fin G.n))
  /-- every settled vertex lies in `Ũ(Bd, S)` -/
  settledU : settledSet st.evts ⊆ Utilde Bd (S : Set (Fin G.n))
  /-- entries are fresh (I3): the stored value is the key's current label -/
  fresh : ∀ y lam, st.D y = some lam → lam = st.d y
  /-- entries lie below `Bd` (I4) -/
  below : ∀ y lam, st.D y = some lam → lam < Bd
  /-- every settled label is below the pull separator -/
  sep : ∀ y ∈ settledSet st.evts, st.d y < st.x
  /-- settlements are complete at the current labels -/
  settledComplete : ∀ y ∈ settledSet st.evts, Complete st.d y
  /-- every key of the entry store is settled or still keyed -/
  keep : ∀ y, D0 y ≠ none → y ∈ settledSet st.evts ∨ st.D y ≠ none
  /-- the separator never exceeds the bound -/
  xle : st.x ≤ Bd

/-! ## One pull-and-relax step -/

/-- One pull iteration preserves the invariant.  The pulled vertex `u` is a minimum-key entry
(`hmin`) with `lam < st.x` (the pull separator); `iter` settles `u` and sweeps its out-edges
under `Bd`. -/
theorem pullInv_step {Bd : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {D0 : DS G s}
    {st : BState G s} (h : PullInv Bd S d0 D0 st) (u : Fin G.n) (lam : WLab G s)
    (hu : st.D u = some lam) (hlt : lam < st.x) (hmin : ∀ y μ, st.D y = some μ → lam ≤ μ) :
    PullInv Bd S d0 D0 (iter Bd u st.x st) := by
  have hlam : lam = st.d u := h.fresh u lam hu
  have huK : u ∈ DS.keys st.D := by
    show st.D u ≠ none
    rw [hu]
    simp
  -- `u` is complete: a minimum key of the frontier's `Y` side (Dijkstra's selection rule)
  have hcu : Complete st.d u := by
    refine IsFrontier.complete_of_min (hF := h.frontier) (hY := h.keys_sub)
      (hsound := WalkInv.sound h.walk) (huK) ?_
    intro y' hy'
    obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.mp hy'
    rw [← hlam, ← h.fresh y' μ hμ]
    exact hmin y' μ hμ
  -- sweep facts (freshness/below survive the delete-set)
  have hDpre_none : DS.deleteSet st.D {u} u = none := by
    show (if u ∈ ({u} : Finset (Fin G.n)) then none else st.D u) = none
    rw [if_pos (by simp)]
  have hDpre_fresh : ∀ y lam, DS.deleteSet st.D {u} y = some lam → lam = st.d y := by
    intro y lam hy
    by_cases hyu : y = u
    · subst hyu
      rw [hDpre_none] at hy
      exact absurd hy (by simp)
    · have hy2 : (if y ∈ ({u} : Finset (Fin G.n)) then none else st.D y) = some lam := hy
      rw [if_neg (by simp [hyu])] at hy2
      exact h.fresh y lam hy2
  have hDpre_below : ∀ y lam, DS.deleteSet st.D {u} y = some lam → lam < Bd := by
    intro y lam hy
    by_cases hyu : y = u
    · subst hyu
      rw [hDpre_none] at hy
      exact absurd hy (by simp)
    · have hy2 : (if y ∈ ({u} : Finset (Fin G.n)) then none else st.D y) = some lam := hy
      rw [if_neg (by simp [hyu])] at hy2
      exact h.below y lam hy2
  have hsw := sweep_inv Bd u st.d (DS.deleteSet st.D {u}) (List.finRange G.m)
    h.walk hDpre_fresh hDpre_below
  have hmem : ∀ e : Fin G.m, e ∈ List.finRange G.m := List.mem_finRange
  -- write `d1`/`D1` for the post-sweep store (defeq to the `iter` projections)
  set d1 : Labels G s := (sweep Bd u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).1 with hd1
  set D1 : DS G s := (sweep Bd u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).2 with hD1
  have hiterd : (iter Bd u st.x st).d = d1 := rfl
  have hiterD : (iter Bd u st.x st).D = D1 := rfl
  have hd1u : d1 u = st.d u := hsw.u_same
  have hSU : settledSet ((iter Bd u st.x st).evts) = (settledSet st.evts : Set (Fin G.n)) ∪ {u} := by
    show settledSet (st.evts ++ [⟨.basePull, u⟩]) = _
    rw [settledSet_append, settledSet_cons, settledSet_nil]
    simp
  have huU : u ∈ Utilde Bd (S : Set (Fin G.n)) := h.keys_sub huK
  -- settled labels are frozen by the sweep (complete labels cannot lower)
  have hun : ∀ y ∈ settledSet st.evts, d1 y = st.d y := by
    intro y hy
    exact le_antisymm (hsw.le y)
      (by rw [complete_iff.mp (h.settledComplete y hy)]; exact (WalkInv.sound hsw.walk) y)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hsw.fresh, hsw.below, ?_, ?_, ?_, ?_⟩
  · -- labels stay walks
    show WalkInv (iter Bd u st.x st).d
    rw [hiterd]
    exact hsw.walk
  · -- Claim C survives lowering
    intro v hv hnv
    show Complete (iter Bd u st.x st).d v
    rw [hiterd]
    exact Complete.of_le (h.claim v hv hnv) (WalkInv.sound hsw.walk) (hsw.le v)
  · -- labels only decrease from the entry labels
    intro v
    show (iter Bd u st.x st).d v ≤ d0 v
    rw [hiterd]
    exact (hsw.le v).trans (h.le v)
  · -- frontier `⟨U, 𝒟⟩` (framework step: `u` complete, out-edges of `u` relaxed)
    have hZ : ∀ z ∈ ({u} : Set (Fin G.n)), Complete d1 z := by
      intro z hz
      have hzu : z = u := hz
      subst hzu
      exact Complete.of_eq hcu hd1u
    have hrelax : ∀ e, G.src e ∈ ({u} : Set (Fin G.n)) → ext (d1 (G.src e)) e < Bd →
        d1 (G.dst e) ≤ ext (d1 (G.src e)) e := by
      intro e he hlt
      have hs : G.src e = u := he
      rw [hs, hd1u] at hlt
      have h1 := hsw.relax e (hmem e) hs hlt
      rw [hs, hd1u]
      exact h1
    have hstep := IsFrontier.step (hF := h.frontier)
      (hU := fun v hv => hv.1)
      (hsound := WalkInv.sound hsw.walk) (hle := hsw.le) (hZ := hZ) (hrelax := hrelax)
    have hkeys' : ((DS.keys st.D \ ({u} : Set (Fin G.n))) ∪ Relaxed d1 Bd ({u} : Set (Fin G.n)))
        ⊆ DS.keys D1 := by
      rintro z (hz | hz)
      · have hzp : z ∈ DS.keys (DS.deleteSet st.D {u}) := by
          show DS.deleteSet st.D {u} z ≠ none
          show (if z ∈ ({u} : Finset (Fin G.n)) then none else st.D z) ≠ none
          rw [if_neg (by simpa using hz.2)]
          exact hz.1
        exact hsw.keys hzp
      · obtain ⟨hzu, e, hs, hd, htid, hlt⟩ := hz
        have hs' : G.src e = u := hs
        rw [← hd, hs', hd1u] at htid
        rw [← hd] at hlt
        have hk := hsw.relax_keys e (hmem e) hs' htid hlt
        show D1 z ≠ none
        rw [← hd]
        exact hk
    show IsFrontier (iter Bd u st.x st).d (Utilde Bd (S : Set (Fin G.n)))
      (settledSet (iter Bd u st.x st).evts) (DS.keys (iter Bd u st.x st).D)
    rw [hiterd, hiterD, hSU]
    exact IsFrontier.mono (hF := hstep) (hU := Set.Subset.refl _)
      (hX := Set.Subset.refl _) (hY := hkeys')
  · -- keys stay in `Ũ(Bd, S)` (refusal-floor via `utilde_of_relax`)
    intro z hz
    show z ∈ Utilde Bd (S : Set (Fin G.n))
    obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.mp hz
    have hμ' : D1 z = some μ := hμ
    rcases hsw.vals z μ hμ' with hpre | ⟨e, he, hs, hd, hm⟩
    · by_cases hzu : z = u
      · subst hzu
        rw [hDpre_none] at hpre
        exact absurd hpre (by simp)
      · have hpre2 : (if z ∈ ({u} : Finset (Fin G.n)) then none else st.D z) = some μ := hpre
        rw [if_neg (by simp [hzu])] at hpre2
        have hK : z ∈ DS.keys st.D := by
          show st.D z ≠ none
          rw [hpre2]
          simp
        exact h.keys_sub hK
    · have hfd : d1 z = μ := (hsw.fresh z μ hμ').symm
      have hle : ext (st.d u) e ≤ st.d z := by
        rw [← hm, ← hfd]
        exact hsw.le z
      have hltB : ext (st.d u) e < Bd := by
        rw [← hm]
        exact hsw.below z μ hμ'
      exact utilde_of_relax h.walk h.claim hcu huU hs hd hltB hle
  · -- settled vertices lie in `Ũ(Bd, S)`
    intro y hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · exact h.settledU hy
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      exact huU
  · -- every settled label is below the pull separator
    intro y hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · rw [hiterd, hun y hy]
      exact h.sep y hy
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      show (iter Bd u st.x st).d u < st.x
      rw [hiterd, hd1u, ← hlam]
      exact hlt
  · -- settlement completeness
    intro y hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · exact Complete.of_le (h.settledComplete y hy) (WalkInv.sound hsw.walk) (hsw.le y)
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      exact Complete.of_eq hcu hd1u
  · -- every key of the entry store is settled or still keyed
    intro y hyD
    rcases h.keep y hyD with hy | hy
    · exact Or.inl (by rw [hSU]; exact Or.inl hy)
    · by_cases hyu : y = u
      · exact Or.inl (by rw [hSU]; exact Or.inr hyu)
      · right
        show D1 y ≠ none
        have hzp : DS.deleteSet st.D {u} y ≠ none := by
          show (if y ∈ ({u} : Finset (Fin G.n)) then none else st.D y) ≠ none
          rw [if_neg (by simp [hyu])]
          exact hy
        exact hsw.keys hzp
  · -- the separator is unchanged (`iter` remembers `st.x`)
    show (iter Bd u st.x st).x ≤ Bd
    exact h.xle

end DMSY
end Frontier

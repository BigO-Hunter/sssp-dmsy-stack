import A1.BaseInv

/-!
# Frontier.DMSY (A2) — the FindPivots tree-building search (Algorithm 2, search phase)

Work package **A2 (FindPivots)**.  The relational semantics of the *search phase* of
Duan–Mao–Shu–Yin Algorithm 2 (CORRECTED_PROOF.md engine (E0)–(E3)): a pull-based local search
from the boundary set `S` under bound `B`, extract-min at a minimum key (Dijkstra's selection
rule), settling the pulled vertex and sweeping its out-edges with bound `B`
(`A1.Sweep.relaxEdge`/`sweep`, reused verbatim — IMPLAN §1: import, do not rebuild).  The loop
runs to **exhaustion** (working store `𝒟` drained); unlike A1's base case there is no separator
bookkeeping (Algorithm 2 does not report a pull separator) and no (E3) event guard (FindPivots
is not a settlement loop).

Conventions (A0): labels are walks (`WLab`), `ext` is the relaxation, `DS` is the keyed keep-min
structure, `initD` seeds the working store from `S` (A1).  Cost is carried as an index of `FLoop`
per A0's operation table (A1's `iterCost` shape); per-call cost inequalities are package C3.

The invariant `FInv` is A1's `BInv` minus separator/event bookkeeping, plus the two clauses the
FPContract needs: labels only decrease (`le`) and every changed label lies in `Ũ(B, S)`
(`changed`).  A1 work-horse lemmas (`sweep_inv`, `utilde_of_relax`, `initD_*`, `deleteSet_*`) are
reused; the new sweep fact `sweep_changed_key` ties label changes to `𝒟` keys.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## One iteration of the local search -/

/-- Loop state of the FindPivots search: labels, the working structure `𝒟`, and the settled
(`done`) vertices. -/
structure FPSt (G : Graph) (s : Fin G.n) where
  d : Labels G s
  D : DS G s
  done : Finset (Fin G.n)

/-- The sweep of one pull: all out-edges of `u` (edge-index order), bound `B`, after removing
`u`'s entry. -/
noncomputable def fpSweep (B : WLab G s) (u : Fin G.n) (st : FPSt G s) : Labels G s × DS G s :=
  sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})

/-- Cost of one iteration (A0 operation table, coarse; A1's `iterCost` shape): two guard tests,
an argmin scan of `|keys 𝒟| ≤ n` comparisons, one delete, and 2 ops per scanned out-edge. -/
def fpCost (u : Fin G.n) (_st : FPSt G s) : ℕ :=
  2 + G.n + 2 * ((List.finRange G.m).filter (fun e => G.src e = u)).length

/-- One pull iteration: settle the min-key vertex `u`, sweep its out-edges with bound `B`. -/
noncomputable def fpIter (B : WLab G s) (u : Fin G.n) (st : FPSt G s) : FPSt G s :=
  { d := (fpSweep B u st).1, D := (fpSweep B u st).2, done := insert u st.done }

/-! ## The loop -/

/-- The FindPivots search loop: while `𝒟 ≠ ∅`, pull a minimum-key vertex, settle it, sweep its
out-edges.  Extract-min at a minimum key is what makes settled vertices complete (Dijkstra's
selection rule, `IsFrontier.complete_of_min`). -/
inductive FLoop (B : WLab G s) (d0 : Labels G s) : ℕ → FPSt G s → FPSt G s → Prop
  | exit {st : FPSt G s} (h : DS.IsEmpty st.D) : FLoop B d0 0 st st
  | pull {c : ℕ} {st st' : FPSt G s} (u : Fin G.n) (lam : WLab G s)
      (hne : ¬ DS.IsEmpty st.D) (hu : st.D u = some lam)
      (hmin : ∀ y μ, st.D y = some μ → lam ≤ μ)
      (hrest : FLoop B d0 c (fpIter B u st) st') :
      FLoop B d0 (c + fpCost u st) st st'

/-- The final state of any loop derivation has a drained `𝒟`. -/
theorem loop_end_empty {B : WLab G s} {d0 : Labels G s} {c : ℕ} {st st' : FPSt G s}
    (h : FLoop B d0 c st st') : DS.IsEmpty st'.D := by
  induction h with
  | exit h => exact h
  | pull u lam hne hu hmin hrest ih => exact ih

/-! ## Sweep fact: a changed label leaves a key behind -/

/-- One accepted relaxation writes the head's label and its `𝒟` entry together, so a changed
label leaves a key behind. -/
theorem relaxEdge_changed_key (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (v : Fin G.n) (h : (relaxEdge B d D e).1 v ≠ d v) : (relaxEdge B d D e).2 v ≠ none := by
  revert h
  unfold relaxEdge
  split_ifs with hh
  · intro h
    by_cases hv : v = G.dst e
    · subst hv
      show DS.insert D (G.dst e) (ext (d (G.src e)) e) (G.dst e) ≠ none
      rw [DS.insert, Function.update_self]
      exact mergeVal_ne_none (D (G.dst e)) (ext (d (G.src e)) e)
    · have hupd : Function.update d (G.dst e) (ext (d (G.src e)) e) v = d v := by
        rw [Function.update_of_ne hv]
      exact absurd hupd h
  · intro h
    exact absurd rfl h

/-- A vertex whose label changed under the sweep has a key in the post-sweep store. -/
theorem sweep_changed_key (B : WLab G s) (u : Fin G.n) (d : Labels G s) (D : DS G s)
    (es : List (Fin G.m)) (v : Fin G.n)
    (hwalk : WalkInv d) (hfresh : ∀ y lam, D y = some lam → lam = d y)
    (hbelow : ∀ y lam, D y = some lam → lam < B)
    (h : (sweep B u es d D).1 v ≠ d v) : (sweep B u es d D).2 v ≠ none := by
  induction es generalizing d D with
  | nil => exact absurd rfl h
  | cons e es ih =>
    by_cases hsrc : G.src e = u
    · have hd1 : (if G.src e = u then (relaxEdge B d D e).1 else d) = (relaxEdge B d D e).1 := by
        rw [if_pos hsrc]
      have hd2 : (if G.src e = u then (relaxEdge B d D e).2 else D) = (relaxEdge B d D e).2 := by
        rw [if_pos hsrc]
      have hsw : sweep B u (e :: es) d D
          = sweep B u es (relaxEdge B d D e).1 (relaxEdge B d D e).2 := by
        simp only [sweep, hd1, hd2]
      rw [hsw] at h
      rw [hsw]
      by_cases hchg : (sweep B u es (relaxEdge B d D e).1 (relaxEdge B d D e).2).1 v
          = (relaxEdge B d D e).1 v
      · have h1 : (relaxEdge B d D e).1 v ≠ d v := by
          intro hh
          exact h (hchg.trans hh)
        have h2 : (relaxEdge B d D e).2 v ≠ none := relaxEdge_changed_key B d D e v h1
        have hkeys : DS.keys (relaxEdge B d D e).2
            ⊆ DS.keys (sweep B u es (relaxEdge B d D e).1 (relaxEdge B d D e).2).2 :=
          (sweep_inv B u (relaxEdge B d D e).1 (relaxEdge B d D e).2 es
            (relaxEdge_walk B e hwalk) (relaxEdge_fresh B d e hfresh)
            (relaxEdge_below B d e hbelow)).keys
        exact hkeys h2
      · exact ih (relaxEdge B d D e).1 (relaxEdge B d D e).2
          (relaxEdge_walk B e hwalk) (relaxEdge_fresh B d e hfresh)
          (relaxEdge_below B d e hbelow) hchg
    · have hd1 : (if G.src e = u then (relaxEdge B d D e).1 else d) = d := by
        rw [if_neg hsrc]
      have hd2 : (if G.src e = u then (relaxEdge B d D e).2 else D) = D := by
        rw [if_neg hsrc]
      have hsw : sweep B u (e :: es) d D = sweep B u es d D := by
        simp only [sweep, hd1, hd2]
      rw [hsw] at h
      rw [hsw]
      exact ih d D hwalk hfresh hbelow h

/-! ## The loop invariant -/

/-- The FindPivots search invariant at bound `B` for boundary set `S`, entry labels `d0`. -/
structure FInv (B : WLab G s) (S : Finset (Fin G.n)) (d0 : Labels G s) (st : FPSt G s) : Prop where
  /-- labels are walks (hence sound) -/
  walk : WalkInv st.d
  /-- Claim C of the call precondition survives label lowering -/
  claim : ∀ v, dis (s := s) v < B → v ∉ Utilde B (S : Set (Fin G.n)) → Complete st.d v
  /-- labels only decrease from the entry labels -/
  le : ∀ v, st.d v ≤ d0 v
  /-- every changed label lies in `Ũ(B, S)` -/
  changed : ∀ v, st.d v ≠ d0 v → v ∈ Utilde B (S : Set (Fin G.n))
  /-- `⟨done, 𝒟⟩` is a frontier for `Ũ(B, S)` -/
  frontier : IsFrontier st.d (Utilde B (S : Set (Fin G.n)))
    (st.done : Set (Fin G.n)) (DS.keys st.D)
  /-- keys of `𝒟` lie in `Ũ(B, S)` -/
  keys_sub : DS.keys st.D ⊆ Utilde B (S : Set (Fin G.n))
  /-- every settled vertex lies in `Ũ(B, S)` -/
  doneU : (st.done : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))
  /-- entries are fresh (I3): the stored value is the key's current label -/
  fresh : ∀ y lam, st.D y = some lam → lam = st.d y
  /-- entries lie below `B` (I4) -/
  below : ∀ y lam, st.D y = some lam → lam < B
  /-- settled vertices are complete at the current labels -/
  doneComplete : ∀ y ∈ st.done, Complete st.d y

/-- The invariant holds initially: `𝒟` seeded from `S`, nothing settled. -/
theorem fInv_init {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    (h : CallPre B S d0) : FInv B S d0 ⟨d0, initD S d0, ∅⟩ := by
  have hkeys : DS.keys (initD (G := G) (s := s) S d0) = (S : Set (Fin G.n)) :=
    initD_keys S d0
  have hfrontier : IsFrontier d0 (Utilde B (S : Set (Fin G.n)))
      ((∅ : Finset (Fin G.n)) : Set (Fin G.n)) (DS.keys (initD S d0)) := by
    rw [Finset.coe_empty, hkeys]
    exact h.frontier
  have hsub : DS.keys (initD (G := G) (s := s) S d0) ⊆ Utilde B (S : Set (Fin G.n)) := by
    intro y hy
    have hyS : y ∈ (S : Set (Fin G.n)) := by rw [← hkeys]; exact hy
    have hdis : dis (s := s) y < B := by
      have h1 : dis (s := s) y ≤ d0 y := (WalkInv.sound h.walk) y
      exact lt_of_le_of_lt h1 (h.inRange y hyS)
    exact ⟨hdis, y, hyS, onPath_self (reachable_of_dis_lt hdis)⟩
  have hfresh : ∀ y lam, initD (G := G) (s := s) S d0 y = some lam → lam = d0 y := by
    intro y lam hy
    exact initD_fresh S d0 hy
  have hbelow : ∀ y lam, initD (G := G) (s := s) S d0 y = some lam → lam < B := by
    intro y lam hy
    have hyS : y ∈ (S : Set (Fin G.n)) := by
      rw [initD_eq_some] at hy
      by_cases hh : y ∈ S
      · exact hh
      · rw [if_neg hh] at hy
        simp at hy
    have hlam : lam = d0 y := hfresh y lam hy
    rw [hlam]
    exact h.inRange y hyS
  refine ⟨h.walk, h.claimC, ?_, ?_, hfrontier, hsub, ?_, hfresh, hbelow, ?_⟩
  · intro v
    exact le_rfl
  · intro v hv
    exact (hv rfl).elim
  · intro y hy
    exact absurd hy (by simp)
  · intro y hy
    exact absurd hy (by simp)

/-- One pull iteration of the FindPivots search preserves the invariant. -/
theorem fInv_step {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} {st : FPSt G s}
    (h : FInv B S d0 st) (u : Fin G.n) (lam : WLab G s)
    (hu : st.D u = some lam) (hmin : ∀ y μ, st.D y = some μ → lam ≤ μ) :
    FInv B S d0 (fpIter B u st) := by
  have hlam : lam = st.d u := h.fresh u lam hu
  have huK : u ∈ DS.keys st.D := by
    show st.D u ≠ none
    rw [hu]
    simp
  have hmin' : ∀ y' ∈ DS.keys st.D, st.d u ≤ st.d y' := by
    intro y' hy'
    obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.mp hy'
    have h2 : lam ≤ μ := hmin y' μ hμ
    rw [← hlam, ← h.fresh y' μ hμ]
    exact h2
  have hcu : Complete st.d u := by
    refine IsFrontier.complete_of_min (hF := h.frontier) (hY := h.keys_sub)
      (hsound := WalkInv.sound h.walk) huK ?_
    intro y' hy'
    obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.mp hy'
    have h2 : lam ≤ μ := hmin y' μ hμ
    rw [← hlam, ← h.fresh y' μ hμ]
    exact h2
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
  have hDpre_below : ∀ y lam, DS.deleteSet st.D {u} y = some lam → lam < B := by
    intro y lam hy
    by_cases hyu : y = u
    · subst hyu
      rw [hDpre_none] at hy
      exact absurd hy (by simp)
    · have hy2 : (if y ∈ ({u} : Finset (Fin G.n)) then none else st.D y) = some lam := hy
      rw [if_neg (by simp [hyu])] at hy2
      exact h.below y lam hy2
  have hsw := sweep_inv B u st.d (DS.deleteSet st.D {u}) (List.finRange G.m)
    h.walk hDpre_fresh hDpre_below
  have hmem : ∀ e : Fin G.m, e ∈ List.finRange G.m := List.mem_finRange
  -- write `d1`/`D1` for the post-sweep store (defeq to the `fpIter` projections)
  set d1 : Labels G s := (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).1 with hd1
  set D1 : DS G s := (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).2 with hD1
  have hiterd : (fpIter B u st).d = d1 := rfl
  have hiterD : (fpIter B u st).D = D1 := rfl
  have hd1u : d1 u = st.d u := hsw.u_same
  have hSU : ((fpIter B u st).done : Set (Fin G.n))
      = ((st.done : Set (Fin G.n)) : Set (Fin G.n)) ∪ {u} := by
    change ((insert u st.done : Finset (Fin G.n)) : Set (Fin G.n)) = _
    rw [Finset.coe_insert]
    ext y
    simp [Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
  have huU : u ∈ Utilde B (S : Set (Fin G.n)) := h.keys_sub huK
  -- keys of the post-sweep store lie in `Ũ(B, S)` (refusal-floor via `utilde_of_relax`)
  have hkeys_sub : DS.keys D1 ⊆ Utilde B (S : Set (Fin G.n)) := by
    intro z hz
    show z ∈ Utilde B (S : Set (Fin G.n))
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
    · -- swept-in key: the stored value is the candidate (freshness), which is a
      -- walk out of `u ∈ Ũ` below `B` and at most `d z` — the refusal-floor argument
      have hfd : d1 z = μ := (hsw.fresh z μ hμ').symm
      have hle : ext (st.d u) e ≤ st.d z := by
        rw [← hm, ← hfd]
        exact hsw.le z
      have hltB : ext (st.d u) e < B := by
        rw [← hm]
        exact hsw.below z μ hμ'
      exact utilde_of_relax h.walk h.claim hcu huU hs hd hltB hle
  -- every changed label lies in `Ũ(B, S)`
  have hchanged : ∀ v, d1 v ≠ d0 v → v ∈ Utilde B (S : Set (Fin G.n)) := by
    intro v hv
    by_cases hst : d1 v = st.d v
    · rw [hst] at hv
      exact h.changed v hv
    · have hk : D1 v ≠ none := by
        have h1 : (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).2 v ≠ none :=
          sweep_changed_key B u st.d (DS.deleteSet st.D {u}) (List.finRange G.m) v
            h.walk hDpre_fresh hDpre_below (by rw [hd1] at hst; exact hst)
        rw [hD1]
        exact h1
      exact hkeys_sub hk
  -- settled labels are unchanged by the sweep
  have hun : ∀ y ∈ (st.done : Set (Fin G.n)), d1 y = st.d y := by
    intro y hy
    exact le_antisymm (hsw.le y)
      (by rw [complete_iff.mp (h.doneComplete y hy)]; exact (WalkInv.sound hsw.walk) y)
  refine ⟨?_, ?_, ?_, hchanged, ?_, hkeys_sub, ?_, hsw.fresh, hsw.below, ?_⟩
  · -- labels stay walks
    show WalkInv (fpIter B u st).d
    rw [hiterd]
    exact hsw.walk
  · -- Claim C survives lowering
    intro v hv hnv
    show Complete (fpIter B u st).d v
    rw [hiterd]
    exact Complete.of_le (h.claim v hv hnv) (WalkInv.sound hsw.walk) (hsw.le v)
  · -- labels only decrease from the entry labels
    intro v
    show (fpIter B u st).d v ≤ d0 v
    rw [hiterd]
    exact (hsw.le v).trans (h.le v)
  · -- frontier `⟨done, 𝒟⟩`
    have hZ : ∀ z ∈ ({u} : Set (Fin G.n)), Complete d1 z := by
      intro z hz
      have hzu : z = u := hz
      subst hzu
      exact Complete.of_eq hcu hd1u
    have hrelax : ∀ e, G.src e ∈ ({u} : Set (Fin G.n)) → ext (d1 (G.src e)) e < B →
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
    have hkeys' : ((DS.keys st.D \ ({u} : Set (Fin G.n))) ∪ Relaxed d1 B ({u} : Set (Fin G.n)))
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
    show IsFrontier (fpIter B u st).d (Utilde B (S : Set (Fin G.n)))
      ((fpIter B u st).done : Set (Fin G.n)) (DS.keys (fpIter B u st).D)
    rw [hiterd, hiterD, hSU]
    exact IsFrontier.mono (hF := hstep) (hU := Set.Subset.refl _)
      (hX := Set.Subset.refl _) (hY := hkeys')
  · -- settled vertices lie in `Ũ(B, S)`
    intro y hy
    change y ∈ ((fpIter B u st).done : Set (Fin G.n)) at hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · exact h.doneU hy
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      exact huU
  · -- settlement completeness
    intro y hy
    change y ∈ ((fpIter B u st).done : Set (Fin G.n)) at hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · exact Complete.of_le (h.doneComplete y hy) (WalkInv.sound hsw.walk) (hsw.le y)
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      exact Complete.of_eq hcu hd1u

/-- The invariant holds at every state the loop reaches. -/
theorem loop_fInv {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s} :
    ∀ {c : ℕ} {st st' : FPSt G s}, FLoop B d0 c st st' → FInv B S d0 st → FInv B S d0 st' := by
  intro c st st' h
  induction h with
  | exit h => intro hB; exact hB
  | pull u lam hne hu hmin hrest ih =>
    intro hB
    exact ih (fInv_step hB u lam hu hmin)

end DMSY
end Frontier

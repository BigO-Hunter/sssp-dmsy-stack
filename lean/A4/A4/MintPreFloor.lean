import A4.LoopBInv

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.MintPreFloor — the base leaf of the mint/label floor, and why it is not free

`A4.LoopBInv` reduced Theorem T's value bound (`out.B' ≤ m.val`) to a *label floor* at the
child's boundary — `ChildLabelFloor st fo'` (pointwise, `LabelFloorHyp`) or its minimal
mint-key form `MintPreFloor`/`MintPreHyp` — and left the premises undischarged.  This file
attacks their **base case**: a child that is an A1 leaf (`Run.base`, `c.l = 0`,
`fo' = baseOut bout`), where the leaf's facts come from `CallPre` + `baseRun_lemma31`.

## What is proved (standard axioms only; no `sorry`/`admit`/new axioms; `a4_joint` not assumed)

The base case is **not** a consequence of the leaf interface.  The exact, sharp result is:

* `base_floor_iff_dis` — **at a base leaf the label floor is exactly the canonical-label
  floor**: for *every* vertex `y`,
  `bout.B'_plus ≤ bout.d' y  ↔  bout.B'_plus ≤ dis y`.
  (Settled vertices: `bout.d' y = dis y < B'⁺` by `Lemma31Concl.progress`, both sides false.
  Unsettled vertices below `B'⁺`: `y ∉ U = Ũ(B'⁺, c.S)` by the settlement identity, `dis y <
  B'⁺ ≤ c.B`, so `y`'s canonical path misses `c.S` and `CallPre.claimC` makes `c.d y` complete
  — `bout.d' y ≤ c.d y = dis y < B'⁺`.  This is precisely the `CallPre.claimC` route the task
  flagged: a canonical path avoids the child's seed set.)
* `noAbandonedBelow_iff_floor` — the leaf's floor (off the settlement set) holds **iff**
  `NoAbandonedBelow bout` (no unsettled vertex has canonical label below `B'⁺`), so that
  hypothesis is exactly the missing invariant: neither stronger nor weaker than the floor.
* `childLabelFloor_base_iff`, `mintPreFloor_base_iff` — the **base case of the two premises
  `run_mintFloor` needs**, in canonical-label form:
  `ChildLabelFloor st (baseOut bout) ↔ ∀ j y ∈ st.pl j, y ∉ U → B'⁺ ≤ dis y` and
  `MintPreFloor st' (baseOut bout) ↔ ∀ m ∈ st'.mints, B'⁺ ≤ dis m.x`.
  These are *not* circular (the right side never mentions `bout.d'`), and they are what the
  joint induction should carry at a leaf.
* `childLabelFloor_base`, `mintPreFloor_base` — the sufficient direction: holding
  `NoAbandonedBelow bout` (plus, for mints, that every mint key is unsettled) yields the
  premise outright.
* `full_leaf_noAbandonedBelow_iff` — at a **full** leaf (`D_final` drained, so `B'⁺ = c.B` by
  Lemma 3.1\*'s dichotomy) the invariant reads exactly: *every vertex with `dis < c.B` is
  settled*, i.e. `Ũ(c.B, c.S) = {v | dis v < c.B}`.  Nothing in `CallPre` + `baseRun_lemma31`
  forces that (the seed set's canonical cone need not be everything below the bound).
* `base_floor_fails_of_below`, `not_childLabelFloor_base`, `not_mintPreFloor_base`,
  `full_leaf_top_floor_false` — the **failure direction**: any unsettled vertex below `B'⁺`
  refutes the floor at `bout.d'`, and at a full leaf with `c.B = ⊤` the premise fails at every
  unsettled vertex whose label is finite.
* `base_leaf_counterexample` — **the concrete, fully formalized counterexample**: the
  one-vertex zero-edge graph `ceGraph`, `S = ∅`, `c.B = ⊤`, `d = initLabels`, `t = 1`.  `𝒟` is
  empty at entry so `Loop.exit` fires at once (cost `0`, a **full** leaf: `D_final` drained),
  Lemma 3.1\*'s dichotomy gives `B'⁺ = ⊤ ⊓ dMin ⊤ ∅ = ⊤`, and the only vertex is unsettled
  (`evts = []`) with `dis v = [] < ⊤` — so `B'⁺ ≤ bout.d' v` is **false**, `NoAbandonedBelow`
  is **false**, and the leaf satisfies `CallPre` + `baseRun` throughout.  Every vertex is
  complete here (`initLabels` is complete on a one-vertex graph), so the failure is purely the
  abandoned-below-`B'⁺` phenomenon, not incompleteness.

## The remaining gap, stated exactly

`MintPreHyp`/`LabelFloorHyp` are **Theorem-T-strength**: at a leaf they say "the parent's
residual/mint keys are not abandoned below the child's returned bound", which is the
`Prem = ∅` (Q12) statement restricted to that leaf.  The minimal extra hypothesis that closes
the base case is `NoAbandonedBelow`, in the equivalent full-leaf form
`∀ y, dis y < c.B → y ∈ settledSet bout.evts`.  It is *not* derivable from `CallPre` +
`baseRun_lemma31` + `Claim C`; deriving it requires the structural linkage the leaf interface
does not expose: that every residual group member of the parent either lies in the child's
seed cone `Ũ(c.B, c.S)` (hence settles) or is at canonical label `≥ c.B`.  That is the missing
leaf invariant, and it must come from the parent's `pullRun`/`expand`/`FPContract` linkage
(`resid j ⊆ expand … Si Bi`-style), not from A1.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The missing leaf invariant -/

/-- **`NoAbandonedBelow bout`** — the leaf's minimal missing invariant: no vertex outside the
leaf's settlement set sits at canonical label below the returned bound `B'⁺`.  Equivalently (at
a full leaf) every vertex below `c.B` is settled.  Necessary *and* sufficient for the label
floor at the leaf — `noAbandonedBelow_iff_floor`. -/
def NoAbandonedBelow (bout : BaseOut G s) : Prop :=
  ∀ y, y ∉ settledSet bout.evts → bout.B'_plus ≤ dis (s := s) y

/-! ## Leaf facts inherited from `baseRun` / `baseRun_lemma31` -/

/-- A base leaf never raises a label: its return labels sit below its entry labels. -/
theorem baseRun_le {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) :
    ∀ v, bout.d' v ≤ c.d v := by
  obtain ⟨_cst, st, hloop, hr⟩ := hb
  subst hr
  intro v
  exact a1_loop_le t c.B hloop v

/-- A settled vertex is complete at the leaf's return labels (`Lemma31Concl.settleComplete`). -/
theorem base_settled_complete {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) {y : Fin G.n}
    (hy : y ∈ settledSet bout.evts) : Complete bout.d' y := by
  have hlem := baseRun_lemma31 (⟨hpre, rfl⟩ : ReachBase ⟨c.B, c.S, c.d, initD c.S c.d⟩) hb
  obtain ⟨ev, hev, hv⟩ := hy
  rw [← hv]
  exact hlem.settleComplete ev hev

/-- A settled vertex sits strictly below the leaf's returned bound (`Lemma31Concl.progress`). -/
theorem base_settled_lt {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) {y : Fin G.n}
    (hy : y ∈ settledSet bout.evts) : dis (s := s) y < bout.B'_plus :=
  (baseRun_lemma31 (⟨hpre, rfl⟩ : ReachBase ⟨c.B, c.S, c.d, initD c.S c.d⟩) hb).progress y hy

/-! ## The sharp characterization: the floor is exactly the canonical-label floor -/

/-- **At a base leaf, the label floor holds exactly where the canonical label reaches the
bound.**  Both clauses are decided by `CallPre.claimC` + `Lemma31Concl`: a settled vertex has
`d' y = dis y < B'⁺`; an unsettled one below `B'⁺` has a canonical path avoiding the seed set
`c.S`, hence `c.d y = dis y` by Claim C and `bout.d' y ≤ c.d y = dis y < B'⁺`. -/
theorem base_floor_iff_dis {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) (y : Fin G.n) :
    bout.B'_plus ≤ bout.d' y ↔ bout.B'_plus ≤ dis (s := s) y := by
  have hre : ReachBase ⟨c.B, c.S, c.d, initD c.S c.d⟩ := ⟨hpre, rfl⟩
  have hlem := baseRun_lemma31 hre hb
  have hmono : ∀ v, bout.d' v ≤ c.d v := baseRun_le hb
  obtain ⟨_cst, st, hloop, hr⟩ := hb
  have hd' : bout.d' = st.d := by rw [hr]
  have hwalk : WalkInv bout.d' := by
    rw [hd']
    exact (loop_bInv hloop (bInv_init hre)).walk
  have hBle : bout.B'_plus ≤ c.B := hlem.bound.trans (dMin_le_bound c.B bout.D_final)
  refine ⟨fun h => ?_, fun h => h.trans (WalkInv.sound hwalk y)⟩
  by_contra hlt
  have hdlt : dis (s := s) y < bout.B'_plus := lt_of_not_ge hlt
  by_cases hset : y ∈ settledSet bout.evts
  · obtain ⟨ev, hev, hv⟩ := hset
    have hc : Complete bout.d' y := by
      rw [← hv]
      exact hlem.settleComplete ev hev
    rw [Complete] at hc
    exact hlt (hc ▸ h)
  · -- unsettled: the canonical path misses the child's seed set, so Claim C completes it
    have hnotU : y ∉ Utilde bout.B'_plus (c.S : Set (Fin G.n)) := fun hmem => by
      have h1 : y ∈ bout.U := by rw [hlem.identity]; exact hmem
      exact hset h1
    have hnotU' : y ∉ Utilde c.B (c.S : Set (Fin G.n)) := fun hmem =>
      hnotU ⟨hdlt, hmem.2⟩
    have hcomp : Complete c.d y := hpre.claimC y (lt_of_lt_of_le hdlt hBle) hnotU'
    have hle : c.d y = dis (s := s) y := hcomp
    exact hlt (h.trans ((hmono y).trans (le_of_eq hle)))

/-! ## The minimal invariant is neither weaker nor stronger than the floor -/

/-- `NoAbandonedBelow` is exactly the leaf's floor off the settlement set. -/
theorem noAbandonedBelow_iff_floor {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) :
    NoAbandonedBelow bout ↔ ∀ y, y ∉ settledSet bout.evts → bout.B'_plus ≤ bout.d' y := by
  refine ⟨fun hnp y hy => ?_, fun h y hy => ?_⟩
  · exact (base_floor_iff_dis hpre hb y).mpr (hnp y hy)
  · exact (base_floor_iff_dis hpre hb y).mp (h y hy)

/-- **The two premises `A4.LoopBInv.run_mintFloor` consumes, at a base leaf** — in
canonical-label form (no occurrence of `bout.d'`), which is the non-circular shape the joint
induction should carry at a leaf: the child's floor is a statement about `dis`, not about the
child's own labels. -/
theorem childLabelFloor_base_iff {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s} {p : ℕ}
    (st : RState G s p) (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) :
    ChildLabelFloor st (baseOut bout) ↔
      ∀ j, ∀ y ∈ st.pl j, y ∉ settledSet bout.evts → bout.B'_plus ≤ dis (s := s) y := by
  show (∀ j, ∀ y ∈ st.pl j, y ∉ settledSet bout.evts → bout.B'_plus ≤ bout.d' y) ↔ _
  simp only [base_floor_iff_dis hpre hb]

/-- The mint-key form of the base case: only the selected keys matter. -/
theorem mintPreFloor_base_iff {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s} {p : ℕ}
    (st' : RState G s p) (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) :
    MintPreFloor st' (baseOut bout) ↔
      ∀ m ∈ st'.mints, bout.B'_plus ≤ dis (s := s) m.x := by
  show (∀ m ∈ st'.mints, bout.B'_plus ≤ bout.d' m.x) ↔ _
  simp only [base_floor_iff_dis hpre hb]

/-- The sufficient direction for `LabelFloorHyp`'s base case. -/
theorem childLabelFloor_base {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s} {p : ℕ}
    {st : RState G s p} (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hnp : NoAbandonedBelow bout) : ChildLabelFloor st (baseOut bout) :=
  (childLabelFloor_base_iff st hpre hb).mpr fun _ _ _ huns => hnp _ huns

/-- The sufficient direction for `MintPreHyp`'s base case (mint keys must be unsettled — the
parent selects them from `resid j`, which filters the settled set out). -/
theorem mintPreFloor_base {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s} {p : ℕ}
    {st' : RState G s p} (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hnp : NoAbandonedBelow bout) (hkey : ∀ m ∈ st'.mints, m.x ∉ settledSet bout.evts) :
    MintPreFloor st' (baseOut bout) :=
  (mintPreFloor_base_iff st' hpre hb).mpr fun m hm => hnp m.x (hkey m hm)

/-! ## The failure direction — the base case is refutable, not merely unproved -/

/-- **Any unsettled vertex below the returned bound sits below it in the leaf's labels.** -/
theorem base_floor_fails_of_below {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) {y : Fin G.n}
    (huns : y ∉ settledSet bout.evts) (hlt : dis (s := s) y < bout.B'_plus) :
    bout.d' y < bout.B'_plus :=
  lt_of_not_ge fun h => (not_le.mpr hlt) ((base_floor_iff_dis hpre hb y).mp h)

/-- An abandoned vertex in a pivot group refutes the child's label floor. -/
theorem not_childLabelFloor_base {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s} {p : ℕ}
    (st : RState G s p) (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) {y : Fin G.n}
    (hpl : ∃ j, y ∈ st.pl j) (huns : y ∉ settledSet bout.evts)
    (hlt : dis (s := s) y < bout.B'_plus) : ¬ ChildLabelFloor st (baseOut bout) := by
  intro hfloor
  exact not_le.mpr (base_floor_fails_of_below hpre hb huns hlt)
    (hfloor hpl.choose y hpl.choose_spec huns)

/-- An abandoned vertex among the mint keys refutes the mint floor. -/
theorem not_mintPreFloor_base {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s} {p : ℕ}
    (st' : RState G s p) (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) {y : Fin G.n}
    (hkey : ∃ m ∈ st'.mints, m.x = y) (huns : y ∉ settledSet bout.evts)
    (hlt : dis (s := s) y < bout.B'_plus) : ¬ MintPreFloor st' (baseOut bout) := by
  obtain ⟨m, hm, rfl⟩ := hkey
  intro hfloor
  exact not_le.mpr (base_floor_fails_of_below hpre hb huns hlt) (hfloor m hm)

/-! ## Full leaves: the gate is `c.B`, and the invariant is a cone-coverage statement -/

/-- Lemma 3.1\*'s dichotomy at a full leaf: the returned bound is the entry bound. -/
theorem full_leaf_gate {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hfull : DS.IsEmpty bout.D_final) : bout.B'_plus = c.B :=
  (baseRun_lemma31 (⟨hpre, rfl⟩ : ReachBase ⟨c.B, c.S, c.d, initD c.S c.d⟩) hb).dichotomy.mpr
    hfull

/-- **At a full leaf the missing invariant is cone coverage**: every vertex below `c.B` is
settled, i.e. `Ũ(c.B, c.S)` is everything below the bound.  This is what `CallPre` +
`baseRun_lemma31` do *not* give (the seed set's canonical cone can be smaller). -/
theorem full_leaf_noAbandonedBelow_iff {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hfull : DS.IsEmpty bout.D_final) :
    NoAbandonedBelow bout ↔ ∀ y, dis (s := s) y < c.B → y ∈ settledSet bout.evts := by
  have hB' := full_leaf_gate hpre hb hfull
  constructor
  · intro hnp y hlt
    by_contra huns
    have h1 : c.B ≤ dis (s := s) y := by
      rw [← hB']
      exact hnp y huns
    exact (not_le.mpr hlt) h1
  · intro h y huns
    have h1 : c.B ≤ dis (s := s) y := by
      by_contra hlt
      exact huns (h y (lt_of_not_ge hlt))
    rw [hB']
    exact h1

/-- **A full leaf with `c.B = ⊤` refutes the floor at every unsettled vertex with a finite
label** — the concrete shape of the failure (`⊤ ≤ bout.d' y` forces `bout.d' y = ⊤`). -/
theorem full_leaf_top_floor_false {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hfull : DS.IsEmpty bout.D_final) (hBtop : c.B = ⊤) {y : Fin G.n}
    (huns : y ∉ settledSet bout.evts) (hyne : bout.d' y ≠ ⊤) :
    ¬ (bout.B'_plus ≤ bout.d' y) := by
  intro h
  rw [full_leaf_gate hpre hb hfull, hBtop] at h
  exact hyne (le_antisymm h le_top).symm

/-! ## The concrete full-leaf counterexample

A **full** base leaf (`c.l = 0`, `D_final` drained, `c.B = ⊤`, seed set `∅`) on the one-vertex
zero-edge graph: `𝒟` is empty at entry, so `Loop.exit` fires immediately, `B'⁺ = ⊤ ⊓ dMin ⊤ ∅ =
⊤` by the dichotomy, and the single vertex is unsettled with canonical label `[] < ⊤`.  The
label floor therefore fails at the only vertex — with every hypothesis of the leaf interface
(`CallPre`, `baseRun`, `Full`) in hand. -/

/-- The one-vertex, zero-edge graph. -/
def ceGraph : Graph where
  n := 1
  m := 0
  src := fun e => e.elim0
  dst := fun e => e.elim0
  w := fun e => e.elim0

/-- The only vertex of `ceGraph`. -/
def ceV : Fin ceGraph.n := ⟨0, Nat.one_pos⟩

/-- The counterexample leaf's return record: `B'⁺ = ⊤ ⊓ dMin ⊤ ∅`, no settlements, entry labels. -/
noncomputable def ceBout (s : Fin ceGraph.n) : BaseOut ceGraph s where
  B'_pull := ⊤
  B'_plus := ⊤ ⊓ dMin (⊤ : WLab ceGraph s) (initD (∅ : Finset (Fin ceGraph.n)) (initLabels ceGraph s))
  D_final := initD (∅ : Finset (Fin ceGraph.n)) (initLabels ceGraph s)
  evts := []
  d' := initLabels ceGraph s

theorem ce_empty : DS.IsEmpty (initD (∅ : Finset (Fin ceGraph.n)) (initLabels ceGraph ceV)) := by
  intro y
  simp [initD]

/-- The leaf's entry labels are honest walks (there is only one walk: `[]`). -/
theorem ce_walk (s : Fin ceGraph.n) : WalkInv (initLabels ceGraph s) := by
  intro v p hp
  have hvs : v = s := by
    have hv : v.1 < 1 := v.isLt
    have hs : s.1 < 1 := s.isLt
    exact Fin.ext (by omega)
  rw [hvs] at hp ⊢
  have h0 : initLabels ceGraph s s
      = ((toW ([] : List (Fin ceGraph.m)) : WalkOrd ceGraph s) : WLab ceGraph s) := by
    simp [initLabels]
  rw [h0] at hp
  have hpe : ([] : List (Fin ceGraph.m)) = p := WithTop.coe_injective hp
  rw [← hpe]
  exact Graph.IsWalk.nil s

/-- The only vertex's canonical label is the empty walk. -/
theorem ce_dis (s : Fin ceGraph.n) :
    dis (s := s) s = ((toW ([] : List (Fin ceGraph.m)) : WalkOrd ceGraph s) : WLab ceGraph s) := by
  rw [dis_of_reachable ⟨[], Graph.IsWalk.nil s⟩, path_source]

theorem ce_claimC (s : Fin ceGraph.n) :
    ∀ v, dis (s := s) v < ⊤ →
      v ∉ Utilde (⊤ : WLab ceGraph s) ((∅ : Finset (Fin ceGraph.n)) : Set (Fin ceGraph.n)) →
        Complete (initLabels ceGraph s) v := by
  intro v _ _
  have hvs : v = s := by
    have hv : v.1 < 1 := v.isLt
    have hs : s.1 < 1 := s.isLt
    exact Fin.ext (by omega)
  rw [hvs]
  show initLabels ceGraph s s = dis (s := s) s
  rw [ce_dis]
  simp [initLabels]

theorem ce_frontier (s : Fin ceGraph.n) :
    IsFrontier (initLabels ceGraph s)
      (Utilde (⊤ : WLab ceGraph s) ((∅ : Finset (Fin ceGraph.n)) : Set (Fin ceGraph.n)))
      ∅ ((∅ : Finset (Fin ceGraph.n)) : Set (Fin ceGraph.n)) := by
  intro v hv
  exact absurd hv.2 (by rintro ⟨y, hy, -⟩; exact absurd hy (by simp))

/-- The leaf entry satisfies `CallPre` (nothing is below `⊤` outside `Ũ(⊤, ∅) = ∅`). -/
theorem ce_pre : CallPre (⊤ : WLab ceGraph ceV) (∅ : Finset (Fin ceGraph.n))
    (initLabels ceGraph ceV) where
  walk := ce_walk ceV
  claimC := ce_claimC ceV
  frontier := ce_frontier ceV
  inRange := by intro x hx; exact absurd hx (Finset.notMem_empty x)

/-- The leaf run: the structure is empty at entry, so the loop exits at once (cost `0`). -/
theorem ce_run : baseRun 1 ⟨(⊤ : WLab ceGraph ceV), (∅ : Finset (Fin ceGraph.n)), initLabels ceGraph ceV,
    initD (∅ : Finset (Fin ceGraph.n)) (initLabels ceGraph ceV)⟩ (ceBout ceV) :=
  ⟨0, _, Loop.exit (Or.inl ce_empty), rfl⟩

/-- `B'⁺ = ⊤` at the counterexample leaf (the dichotomy's `c.B = ⊤` instance, computed). -/
theorem ce_Bplus : (ceBout ceV).B'_plus = ⊤ := by
  show (⊤ : WLab ceGraph ceV) ⊓ dMin ⊤ (initD ∅ (initLabels ceGraph ceV)) = ⊤
  rw [dMin_eq_of_isEmpty ⊤ ce_empty, inf_idem]

/-- **The full-leaf counterexample, formalized.**  A `CallPre`-satisfying, `baseRun`-derived,
**full** base leaf (`c.B = ⊤`, `D_final` drained) on which the label floor fails at the only
vertex and the missing invariant `NoAbandonedBelow` is false.  Hence no discharge of the base
case of `ChildLabelFloor`/`MintPreFloor` exists from `CallPre` + `baseRun_lemma31` alone. -/
theorem base_leaf_counterexample :
    CallPre (⊤ : WLab ceGraph ceV) (∅ : Finset (Fin ceGraph.n)) (initLabels ceGraph ceV) ∧
      baseRun 1 ⟨(⊤ : WLab ceGraph ceV), (∅ : Finset (Fin ceGraph.n)), initLabels ceGraph ceV,
        initD (∅ : Finset (Fin ceGraph.n)) (initLabels ceGraph ceV)⟩ (ceBout ceV) ∧
      DS.IsEmpty (ceBout ceV).D_final ∧ (⊤ : WLab ceGraph ceV) = ⊤ ∧
      ¬ NoAbandonedBelow (ceBout ceV) ∧
      ¬ ∀ y, (ceBout ceV).B'_plus ≤ (ceBout ceV).d' y := by
  have hkey : (ceV : Fin ceGraph.n) ∉ settledSet (ceBout ceV).evts := by
    simp [ceBout, settledSet]
  have hlow : dis (s := ceV) ceV < (ceBout ceV).B'_plus := by
    rw [ce_Bplus, ce_dis]
    exact WithTop.coe_lt_top _
  refine ⟨ce_pre, ce_run, ce_empty, rfl, ?_, ?_⟩
  · intro hnp
    exact (not_le.mpr hlow) (hnp ceV hkey)
  · intro h
    have h1 : (⊤ : WLab ceGraph ceV) ≤ (ceBout ceV).d' ceV := by
      rw [← ce_Bplus]
      exact h ceV
    have h2 : (ceBout ceV).d' ceV
        = ((toW ([] : List (Fin ceGraph.m)) : WalkOrd ceGraph ceV) : WLab ceGraph ceV) := by
      show initLabels ceGraph ceV ceV = _
      simp [initLabels]
    rw [h2] at h1
    exact (WithTop.coe_lt_top _).not_ge h1

/-! ## Signatures and axiom audit -/

#check @NoAbandonedBelow
#check @baseRun_le
#check @base_settled_complete
#check @base_settled_lt
#check @base_floor_iff_dis
#check @noAbandonedBelow_iff_floor
#check @childLabelFloor_base_iff
#check @mintPreFloor_base_iff
#check @childLabelFloor_base
#check @mintPreFloor_base
#check @base_floor_fails_of_below
#check @not_childLabelFloor_base
#check @not_mintPreFloor_base
#check @full_leaf_gate
#check @full_leaf_noAbandonedBelow_iff
#check @full_leaf_top_floor_false
#check @base_leaf_counterexample

#print axioms base_floor_iff_dis
#print axioms childLabelFloor_base_iff
#print axioms mintPreFloor_base_iff
#print axioms noAbandonedBelow_iff_floor
#print axioms full_leaf_noAbandonedBelow_iff
#print axioms not_mintPreFloor_base
#print axioms base_leaf_counterexample

end DMSY
end Frontier

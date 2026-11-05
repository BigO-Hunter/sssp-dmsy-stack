import A4.StepSplitFloor
import A4.LeafFloor

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.NoLoose — the refusal floor, attacked at the label layer

`A4.StepSplitFloor` proved `floorL_iff_noLoose`: at a `Sound` label assignment the refusal floor
is *exactly* the no-loose-head statement `NoLoose R d evts`.  `A4.LeafFloor` then settled the
`l = 0` leaf (`base_floor_cap`, `childFloor_base_of_full`) and named its missing invariant
(`c.B ≤ bout.B'_plus`, i.e. a **full** base exit).  What neither file does is attack the
recursion case (`Run.recur`): nothing in the lane proves `NoLoose` for a run of Algorithm 3.

This file attacks that leaf and reports the two things the label layer can decide.

## 1. Why `Sound`/`dis ≤ d` cannot reach the floor: canonical vs arbitrary labels

`NoLoose`'s conclusion is `¬(dis v < d v)`, which under `Sound d` is `Complete d v`, i.e. it asks
for an **equation** between a label and the **canonical walk** `dis v`.  A `Sound` label is only
an inequality, and labels are walks (`WLab G s = WithTop (WalkOrd G s)`) — so the gap is not
"label too long", it is "label is a *different, strictly heavier walk*":

* `loose_strict_gap` — if `d u` is complete and the head's label is the accepted candidate
  `ext (d u) e`, then a loose head satisfies `dis v < ext (dis u) e` **strictly**.  The accepted
  walk is therefore non-canonical for `v`: no amount of `Sound`-ness turns it into `dis v`.
* `complete_cand_iff_canonical` — the exact label-level characterisation: under the same
  hypothesis, the head is complete **iff** the candidate walk *is* the canonical walk of the
  head, `dis v = ext (dis u) e`.  That is the "tight acceptance out of a complete source"
  (Dijkstra-order) condition, and it is an **iff** — so it is both necessary and sufficient.
  `IStep` pins no labels (`A4.StepSplitFloor` §2: `IStep`'s `d3` is only the *sweep image* of the
  child's labels), so nothing structural can supply it: only acceptance tightness can.
* `noLoose_canonical` / `noLoose_top` — the two degenerate label assignments that satisfy the
  floor for opposite reasons: the canonical assignment `fun v => dis v` satisfies it because every
  label *is* canonical, and the all-`⊤` assignment satisfies it **vacuously** (`ext ⊤ e = ⊤` is
  never below a threshold).  This is the precise sense in which the floor is a statement about
  walk *content*, not about bounds: `Sound` admits both, and only the first is complete.

## 2. The exact strengthened invariant the recursion needs: `CandSettled`

The route the actual semantics runs (leaf `base_floor_cap`, and the per-iteration split
`floorL_of_below_above` = child floor at `c.B` + `AboveSep`) passes through **settlement**, not
through label tightness: a below-threshold candidate's head is *settled* by some child, and
settlement completeness (`ChildFloor`'s clause 1, or `Lemma31Concl.settleComplete`) makes its
label complete.  That statement is strictly stronger than `NoLoose` (a head can be complete
without being settled — the leaf's `Claim C` completes heads below `B'⁺` that sit *outside*
`Ũ(B,S)` and are never settled), and it is the one the pull/custody machinery can pay for:

* `noLoose_of_candSettled` — settled heads + settled-completeness ⇒ `NoLoose`;
* `floor_of_candSettled` / `childFloor_of_candSettled` — the same in `FloorL`/`ChildFloor` shape,
  so it plugs straight into `BelowSeparator.hbelow_of_floor`;
* `wPrime_label_lt` / `wPrime_not_settled` — the tail's `W'` settlement source is structurally
  *below* the returned bound and *outside* the loop's log (`wPrime`'s own filter), which is the
  only part of the tail that can add a below-threshold settled source.  On a full execution
  `tailBP B st = B` (`FIX-EMPTY`), so the tail's own settlements are below `B` — they are exactly
  the sources `CandSettled` has to cover.

## 3. The remaining gap, stated exactly

`NoLoose` at a recursion run `Run t e out` is **not** derivable from the lane's run semantics
without two hypotheses, each of which fails for a documented reason:

1. **Full execution at every level** (`DS.IsEmpty stf.D`, hence `tailBP B stf = B`).  Capped
   exits abandon keys in the band `(B'⁺, c.B)` and leave their heads loose — the concrete
   `t = 1` counterexample is `A4.LeafFloor`'s module docstring, and it already refutes
   `ChildFloor`'s clause 2 at the *leaf* while every clause of Lemma 3.1\* still holds.  This
   file does not re-measure it; `base_floor_cap` is the maximal unconditional statement there.
2. **`CandSettled`**, i.e. no pulled seed is abandoned below the threshold.  The only way a key
   leaves `𝒟` is a pull (`belowKeys`/`deleteSet`, `A3.DStruct`) or ★BM.15's deletion of a child's
   `settledFinset` — so on a full execution every key *is* pulled, and a pulled seed `x ∈ S_i`
   lies in `Ũ(B_i, S_i)` (`dis x ≤ val < x_i ≤ B` plus `OnPath x x`), hence is settled by the
   child **unless** it falls in that child's carve-out `carveKeys` (`A4.IdentityCover`),
   i.e. **unless it is a premature mint of the child's final iteration**.  So the exact residual
   of the recursion floor is:

     `full execution` + `no pulled seed below B is a child's premature (carve-out) key`.

   That second conjunct is `Prem = ∅`-shaped, not floor-shaped: `A4.IdentityCover`'s
   `Yclear`/`LowKeyAccurate` and `A4.StepSplitFloor`'s `GatedMint`/`NoPremGated` are the named
   routes to it.  Absent it, a pulled seed can be dropped (identity cover's `∖ K`), stay loose,
   and be a head of a settled source's below-`B` candidate — which is precisely a `NoLoose`
   counterexample and no contradiction with any clause of the run's contract.

No `sorry`/`admit`, no new axiom, `a4_joint` not assumed (and not used).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. Canonical walk labels vs arbitrary sound labels -/

/-- **A loose label is a strictly heavier walk.**  If `d u` is complete (so the accepted
candidate out of `u` is the walk `ext (dis u) e`) and the head `v`'s label *is* that candidate
but `v` is not complete, then the canonical label of `v` is **strictly** below the candidate.
The accepted walk is not merely longer — it is a different, heavier walk of `κ`; `Sound` can
never close the gap. -/
theorem loose_strict_gap {d : Labels G s} (hsound : Sound d) {u v : Fin G.n} {e : Fin G.m}
    (hcomp : Complete d u) (hlab : d v = ext (d u) e) (hloose : ¬ Complete d v) :
    dis (s := s) v < ext (dis (s := s) u) e := by
  have hle : dis (s := s) v ≤ d v := hsound v
  have hlt : dis (s := s) v < d v := lt_of_le_of_ne hle (fun h => hloose h.symm)
  rwa [hlab, hcomp] at hlt

/-- **The label-level characterisation of the floor's leaf.**  For a complete source `u` and a
head whose label is the accepted candidate `ext (d u) e`, completeness of the head is
**equivalent** to the candidate being the head's *canonical walk*:
`dis v = ext (dis u) e` — the Dijkstra-order/tight-acceptance condition.  Since `IStep` never
pins labels, this is an iff on label content that no structural clause of the run can decide. -/
theorem complete_cand_iff_canonical {d : Labels G s} {u v : Fin G.n} {e : Fin G.m}
    (hcomp : Complete d u) (hlab : d v = ext (d u) e) :
    Complete d v ↔ dis (s := s) v = ext (dis (s := s) u) e := by
  constructor
  · intro hv
    rw [← hv, hlab, hcomp]
  · intro hcanon
    show d v = dis (s := s) v
    rw [hlab, hcomp, hcanon]

/-- The canonical assignment satisfies the floor for trivial reasons: every label *is* the
canonical walk, so no head can be loose.  This is the case the paper's `d = dis` reading lives
in — and the case the engine never has (its labels are tentative). -/
theorem noLoose_canonical (R : WLab G s) (evts : List (SettlementEvent G)) :
    NoLoose R (fun v => dis (s := s) v) evts := by
  intro e₀ _ _ hlt
  exact lt_irrefl _ hlt

/-- The all-`⊤` assignment satisfies the floor **vacuously**: `ext ⊤ e = ⊤` is never below any
threshold, so the floor's premise is unreachable.  Together with `noLoose_canonical` this
locates the floor strictly above `Sound`: it is neither implied by all labels being canonical
nor refuted by all labels being junk — it is about the *middle* labels the engine carries. -/
theorem noLoose_top (R : WLab G s) (evts : List (SettlementEvent G)) :
    NoLoose R (fun _ => (⊤ : WLab G s)) evts := by
  intro e₀ _ hlt
  have htop : ext ((fun _ : Fin G.n => (⊤ : WLab G s)) (G.src e₀)) e₀ = ⊤ := ext_top e₀
  rw [htop] at hlt
  exact absurd hlt (not_lt.mpr le_top)

/-! ## 2. The strengthened invariant the recursion can actually pay for -/

/-- **`CandSettled R d evts`** — the recursion's below-threshold heads are **settled** heads.
This is the invariant the pull/child route delivers (a below-`R` candidate out of a settled
source has its head settled by some child, whose settlement completeness then makes the label
complete), and it is *strictly stronger* than `NoLoose` (`A4.LeafFloor`'s `Claim C` completes
heads below the bound that are never settled).  It is stated on the log, not on labels: the
label arithmetic is discharged once, by `noLoose_of_candSettled`. -/
def CandSettled (R : WLab G s) (d : Labels G s) (evts : List (SettlementEvent G)) : Prop :=
  ∀ e₀, G.src e₀ ∈ settledSet evts → ext (d (G.src e₀)) e₀ < R → G.dst e₀ ∈ settledSet evts

/-- **`CandSettled` + settled completeness ⇒ the floor.**  No label tightening, no `Sound`
hypothesis, no bounds: the whole content of `NoLoose` is bought by settling the head and taking
its completeness from the settlement log. -/
theorem noLoose_of_candSettled {R : WLab G s} {d : Labels G s}
    {evts : List (SettlementEvent G)} (hset : ∀ v ∈ settledSet evts, Complete d v)
    (h : CandSettled R d evts) : NoLoose R d evts := by
  intro e₀ hu hlt hloose
  have hc : Complete d (G.dst e₀) := hset _ (h e₀ hu hlt)
  rw [hc] at hloose
  exact lt_irrefl _ hloose

/-- The same reduction in `FloorL` shape (the form `BelowSeparator.hbelow_of_floor` and
`StepSplitFloor.floorL_istep` consume). -/
theorem floor_of_candSettled {R : WLab G s} {d : Labels G s}
    {evts : List (SettlementEvent G)} (hsound : Sound d)
    (hset : ∀ v ∈ settledSet evts, Complete d v) (h : CandSettled R d evts) :
    FloorL R d evts :=
  (floorL_iff_noLoose hsound).mpr (noLoose_of_candSettled hset h)

/-- **`ChildFloor` at a call, from `CandSettled` at the call's own bound.**  Clause (1) is the
child's `settleComplete`; clause (2) is `CandSettled c.B` plus clause (1).  This is the shape the
joint induction's step consumes when the head of a below-separator candidate is settled by the
child (in place of — and strictly stronger than — the floor's own label content). -/
theorem childFloor_of_candSettled {c : CallEntry G s} {fo : CallOut G s} (hsound : Sound fo.d')
    (hset : ∀ ev ∈ fo.evts, Complete fo.d' ev.v) (h : CandSettled c.B fo.d' fo.evts) :
    ChildFloor c fo :=
  ⟨hset, floor_of_candSettled hsound (complete_settledSet hset) h⟩

/-! ### 2b. The two run-level bridges -/

/-- **The leaf in `NoLoose` language, at the corrected (E1) V5 cap.**  `A4.LeafFloor`'s
`base_floor_cap` is the floor at the leaf's *returned* bound `B'⁺ = min(B'_pull, d_B[𝒟_final])`;
`floorL_iff_noLoose` turns it into the no-loose-head statement at that cap.  So the V5 cap is
exactly what the leaf's floor can certify, and `B'⁺` — not the entry bound `c.B` — is its
threshold.  This is the maximal `NoLoose` statement A1's semantics supports. -/
theorem base_noLoose_cap {t : ℕ} {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    {bout : BaseOut G s} (hpre : CallPre B S d)
    (hrun : baseRun t ⟨B, S, d, initD S d⟩ bout) (hsound : Sound bout.d') :
    NoLoose bout.B'_plus bout.d' bout.evts :=
  (floorL_iff_noLoose hsound).mp (base_floor_cap hpre hrun)

/-- **The recursion-flagged floor of a `Run`, from `CandSettled`.**  Stated on the run's own
return record and its own bound `e.B` — the `Floor e out` shape (`StepSplitFloor`) that
`BelowSeparator` consumes.  The hypothesis is the strengthened invariant: below `e.B`, a settled
source's candidate head is *settled*; completeness then comes from the run's own settlement log.
Nothing here assumes `a4_joint`; the missing content is exactly `hset`/`h`. -/
theorem floor_of_run_candSettled {t : ℕ} {e : CallEntry G s} {out : CallOut G s}
    (hset : ∀ ev ∈ out.evts, Complete out.d' ev.v) (hsound : Sound out.d')
    (h : CandSettled e.B out.d' out.evts) : Floor e out :=
  floor_of_candSettled hsound (complete_settledSet hset) h

/-- The same at `ChildFloor` shape (`BelowSeparator`'s premise, clauses (1)+(2)). -/
theorem childFloor_of_run_candSettled {e : CallEntry G s} {out : CallOut G s}
    (hset : ∀ ev ∈ out.evts, Complete out.d' ev.v) (hsound : Sound out.d')
    (h : CandSettled e.B out.d' out.evts) : ChildFloor e out :=
  childFloor_of_candSettled hsound hset h

/-! ## 3. The tail's contribution: `W'` sources are below the returned bound -/

theorem mem_wPrime_iff {bp : WLab G s} {W : Finset (Fin G.n)}
    {evts : List (SettlementEvent G)} {d : Labels G s} {x : Fin G.n} :
    x ∈ wPrime bp W evts d ↔ x ∈ W ∧ x ∉ settledSet evts ∧ d x < bp := by
  classical
  unfold wPrime
  exact Finset.mem_filter

/-- A tail-settled (`W'`) source carries a label strictly below the returned bound `B'` — by
`wPrime`'s own filter, before any sweep.  So the tail can only add *below-`B'`* settled sources;
on a full execution (`tailBP B st = B`, `FIX-EMPTY`) those are below `B`, i.e. inside the band
`CandSettled` must cover. -/
theorem wPrime_label_lt {bp : WLab G s} {W : Finset (Fin G.n)}
    {evts : List (SettlementEvent G)} {d : Labels G s} {x : Fin G.n}
    (hx : x ∈ wPrime bp W evts d) : d x < bp :=
  ((mem_wPrime_iff.mp hx).2.2)

/-- A tail-settled (`W'`) source is **not** already settled by the loop — so it is a genuinely
new settled source for `CandSettled`, never a redundant one. -/
theorem wPrime_not_settled {bp : WLab G s} {W : Finset (Fin G.n)}
    {evts : List (SettlementEvent G)} {d : Labels G s} {x : Fin G.n}
    (hx : x ∈ wPrime bp W evts d) : x ∉ settledSet evts :=
  ((mem_wPrime_iff.mp hx).2.1)

/-- The tail's `W'` events settle exactly the `W'` members (the log is that list mapped to
events) — so `CandSettled`'s tail half is a statement about the finitely many `W'` vertices. -/
theorem mem_settled_wPrimeEvts {Wp : Finset (Fin G.n)} {x : Fin G.n} :
    x ∈ settledSet (wPrimeEvts Wp) ↔ x ∈ Wp := by
  constructor
  · rintro ⟨ev, hev, hv⟩
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hev
    exact hv ▸ (Finset.mem_toList.mp hy)
  · intro hx
    exact ⟨⟨.boundaryAppend, x⟩, List.mem_map.mpr ⟨x, Finset.mem_toList.mpr hx, rfl⟩, rfl⟩

/-! ## Axiom profile -/

#print axioms Frontier.DMSY.loose_strict_gap
#print axioms Frontier.DMSY.complete_cand_iff_canonical
#print axioms Frontier.DMSY.noLoose_canonical
#print axioms Frontier.DMSY.noLoose_top
#print axioms Frontier.DMSY.noLoose_of_candSettled
#print axioms Frontier.DMSY.floor_of_candSettled
#print axioms Frontier.DMSY.base_noLoose_cap
#print axioms Frontier.DMSY.floor_of_run_candSettled
#print axioms Frontier.DMSY.childFloor_of_run_candSettled
#print axioms Frontier.DMSY.childFloor_of_candSettled
#print axioms Frontier.DMSY.mem_wPrime_iff
#print axioms Frontier.DMSY.wPrime_label_lt
#print axioms Frontier.DMSY.wPrime_not_settled
#print axioms Frontier.DMSY.mem_settled_wPrimeEvts

end DMSY
end Frontier

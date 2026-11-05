import A4.LowKeyClosure
import A4.LemmaD

/-!
# Frontier.DMSY.TailIdentity — the tail's identity cover, with the `W` side discharged

`A4.LowKeyClosure` reduced clause (2c) — `U = Ũ(B′,S) ∖ K` — to the joint exit statement
`ExitJoint`: every unsettled member of the returned cone is a boundary append (`W′`) or a
recorded sub-floor final mint.  This file takes the `W′` disjunct apart against the actual
`Run.recur` components and shows it is **free**, so what is left is only the mint disjunct,
and only for cone members that FindPivots' own region did *not* return.

## 1. The `W′` disjunct is free (`fo.W` at the loop exit)

`Run`'s tail is `tail e.B e.S fo.W stf`: its boundary filter is the FindPivots output region
`fo.W`.  Two facts compose, and neither needs a hypothesis beyond the `recur` components:

* `A4.LemmaD.fp_label_eq_loop_exit` — a `fo.W` member is **complete at the loop exit and its
  label is unchanged** (`stf.d z = fo.d′ z`).  (Completeness survives the loop because the loop
  only lowers labels — `iloop_le` — and `Complete.of_le` catches the result.)
* `wPrime`'s filter — a `fo.W` member below `tailBP`, not yet settled, *is* a `W′` member.

Composing: `z ∈ fo.W` and `z ∈ Ũ(tailBP, S)` and `z ∉ stf.evts` give `z ∈ tailWp`, hence
`z ∈ out.U` (`tail_U_of_mem_foW`).  This is exactly the "`X ⊆ fo.W ∪ settledSet`" half: clause
(1)'s `X` side (`out.U`) is `settledSet stf.evts ∪ tailWp`, and `tailWp ⊆ fo.W` by the filter,
so `X` never needs custody, `LowKeyAccurate`, a label floor or a mint.

## 2. What remains is one gated mint statement

`GatedMint B S W st` says: a cone member that the loop did not settle **and** that `W` does not
contain is a recorded sub-floor mint.  Given §1, `GatedMint` alone yields `ExitJoint`
(`exitJoint_of_gatedMint`), the cover (`tail_cover_of_gatedMint`) and, with the two halves
`ReturnClauses` already proves (`tail_uSubset`, the `Prem`/`U` disjointness), the settlement
identity itself (`tail_identity_of_gatedMint`).

The guard `x ∉ W` is not a weakening for convenience: `exists_gate_of_cone_not_mem_foW` proves
that a cone member outside `fo.W` is *gated behind a pivot* of the FindPivots output
(`fpRun_frontier_persist`'s `Y` side).  So `GatedMint` constrains exactly the vertices the
entry frontier defers to the pivot subtrees — the ones the paper's clause (2c) discharges by
the child recursion, and this engine's `Run` only exposes as `ChildOf` records.

`gatedMint_of_keyfloor` records that Route 2 (`LowKeyClosure`'s value floor at unsettled cone
keys plus `ExitLive`/`Custody`/`LoopBoundInv`) is *strictly stronger*: it implies `GatedMint`
with no use of the `x ∉ W` guard.  Hence this file's residue sits below Route 2, below
`ExitJoint`, and below Route 1's `Yclear`.

## 3. Why BM.15 and draining do not close it

★BM.15 deletes the loop's child settled sets from the parent's `𝒟`; that removes stale *keys*,
not the question of which vertices the cone reaches.  And a drained loop (`DS.IsEmpty stf.D`)
does not empty the returned store: the tail re-enters the seeds (BM.25) and sweeps `W′`
(BM.27–28) *after* the loop drains (`tailOut_D`, `tailOut_U`), so `out.D` and `out.U` are
built from `fo.W` and the seed set, not from the loop's remains — which is why §1's `W`-side
argument leaves a genuine residue at the gated vertices rather than resolving in the drained
case.

No `sorry`/`admit`, no new axiom, `a4_joint` not assumed.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The boundary half: `W`-members are boundary appends -/

/-- **A complete `W`-member below the returned floor is a `W′` member.**  No soundness, no
custody, no store: `Complete` identifies the label with the canonical distance, and `wPrime`'s
filter asks exactly for `W`-membership, unsettledness and a sub-floor label. -/
theorem mem_tailWp_of_complete {B : WLab G s} (S : Finset (Fin G.n)) {W : Finset (Fin G.n)}
    {p : ℕ} {st : RState G s p} {z : Fin G.n} (hcomp : Complete st.d z) (hzW : z ∈ W)
    (hzs : z ∉ settledSet st.evts) (hdis : dis (s := s) z < tailBP B st) :
    z ∈ tailWp B S W st := by
  classical
  rw [tailWp_reads_state]
  refine Finset.mem_filter.mpr ⟨hzW, hzs, ?_⟩
  rw [hcomp]
  exact hdis

/-- **The `W′` disjunct of the cover is free.**  A FindPivots region member that lies in the
returned cone and that the loop did not settle is settled by the tail's boundary append —
`fp_label_eq_loop_exit` supplies completeness at the loop exit, `wPrime` does the rest.  This is
the whole content of "`X ⊆ fo.W ∪ settledSet`": no key, no mint, no frontier is consulted. -/
theorem tail_U_of_mem_foW (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) (hst0 : st0 = mkInit e fo piv)
    (hloop : ILoop t e.B e.l st0 qs stf) (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    {z : Fin G.n} (hzW : z ∈ fo.W)
    (hzU : z ∈ Utilde (tailBP e.B stf) (e.S : Set (Fin G.n)))
    (hzs : z ∉ settledSet stf.evts) :
    z ∈ (callOut (tail e.B e.S fo.W stf)).U := by
  have hcomp : Complete stf.d z := (fp_label_eq_loop_exit hfp hst0 hloop hchildren hzW).1
  exact tailOut_U_mem.mpr (Or.inr (mem_tailWp_of_complete e.S hcomp hzW hzs hzU.1))

/-! ## 2. The residual premise: gated cone members are sub-floor mints -/

/-- **The remaining leaf, sharply.**  Every unsettled member of the returned cone that FindPivots'
region `W` does not contain is a **recorded sub-floor final mint** — the exact shape that
`CallOut.carveKeys` turns into the carve-out `K`.  It mentions no label, no stored value and no
frontier: the `W` side is §1's (proved), so this is the only content left for the cover. -/
def GatedMint (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x, x ∈ Utilde (tailBP B st) (S : Set (Fin G.n)) → x ∉ settledSet st.evts → x ∉ W →
    ∃ val, Mint.mk x val ∈ st.mints ∧ val < tailBP B st

/-- **`GatedMint` gives the joint exit statement.**  Split the cone member three ways: settled
(the loop log), in `W` (§1's boundary append), otherwise the premise. -/
theorem exitJoint_of_gatedMint (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) (hst0 : st0 = mkInit e fo piv)
    (hloop : ILoop t e.B e.l st0 qs stf) (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (hgated : GatedMint e.B e.S fo.W stf) :
    ExitJoint e.B e.S fo.W stf := by
  intro x hxU hzs
  by_cases hxW : x ∈ fo.W
  · have hcomp : Complete stf.d x := (fp_label_eq_loop_exit hfp hst0 hloop hchildren hxW).1
    exact Or.inl (Finset.mem_coe.mpr (mem_tailWp_of_complete e.S hcomp hxW hzs hxU.1))
  · exact Or.inr (hgated x hxU hzs hxW)

/-- **The identity cover from `GatedMint`**: `Ũ(B′,S) ⊆ out.U ∪ out.carveKeys S`.  The settled
and `W` branches are unconditional; only the gated branch is the premise. -/
theorem tail_cover_of_gatedMint (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) (hst0 : st0 = mkInit e fo piv)
    (hloop : ILoop t e.B e.l st0 qs stf) (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (hgated : GatedMint e.B e.S fo.W stf) :
    Utilde (tailBP e.B stf) (e.S : Set (Fin G.n)) ⊆
      (callOut (tail e.B e.S fo.W stf)).U ∪
        (callOut (tail e.B e.S fo.W stf)).carveKeys e.S := by
  intro x hxU
  by_cases hzs : x ∈ settledSet stf.evts
  · exact Or.inl (settledSet_subset_tail_U e.B e.S fo.W stf hzs)
  · rcases exitJoint_of_gatedMint t hfp hst0 hloop hchildren hgated x hxU hzs with
      h | ⟨val, hm, hlt⟩
    · exact Or.inl (tailOut_U_mem.mpr (Or.inr (Finset.mem_coe.mp h)))
    · exact Or.inr (mem_carveKeys_tail e.B e.S fo.W stf |>.mpr ⟨⟨val, hm, hlt⟩, hxU⟩)

/-- **Clause (2c) — the settlement identity — from `GatedMint`.**  `ReturnClauses.tail_identity`
with `hcover` supplied by `tail_cover_of_gatedMint`; the other two halves are the ones
`ReturnClauses` already proves (`tail_uSubset`, and `PremShape`'s `x ∉ U` for the
`Prem`/`carveKeys` disjointness). -/
theorem tail_identity_of_gatedMint (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) (hst0 : st0 = mkInit e fo piv)
    (hloop : ILoop t e.B e.l st0 qs stf) (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (hgated : GatedMint e.B e.S fo.W stf)
    (hsub : (callOut (tail e.B e.S fo.W stf)).U ⊆
      Utilde (tailBP e.B stf) (e.S : Set (Fin G.n)))
    (hdisj : ∀ x, x ∈ (callOut (tail e.B e.S fo.W stf)).U →
      x ∉ (callOut (tail e.B e.S fo.W stf)).carveKeys e.S) :
    (callOut (tail e.B e.S fo.W stf)).U =
      Utilde (tailBP e.B stf) (e.S : Set (Fin G.n)) \
        (callOut (tail e.B e.S fo.W stf)).carveKeys e.S :=
  tail_identity e.B e.S fo.W stf hsub hdisj
    (tail_cover_of_gatedMint t hfp hst0 hloop hchildren hgated)

/-! ## 3. Where the guard comes from: gated vertices are pivot subtrees

`fpRun` returns the frontier `⟨fo.W, ⋃ P_j⟩` for `Ũ(B, S)`.  So a cone member outside `fo.W` is
not merely "not in `W`": it is **behind a pivot** of the FindPivots output, which is precisely
the region the recursion hands to its children.  That is why the premise's guard is the natural
one, and why the paper discharges this branch through the child induction while `Run` only
exposes `ChildOf` records for it. -/

/-- A `Ũ(B,S)` member outside the FindPivots region is gated behind a pivot group member
(`fpRun_frontier_persist`'s `Y` side, unrolled to a named group). -/
theorem exists_gate_of_not_mem_foW {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) {v : Fin G.n}
    (hvU : v ∈ Utilde e.B (e.S : Set (Fin G.n))) (hvW : v ∉ fo.W) :
    ∃ j : Fin fo.p, ∃ y ∈ fo.P j, Complete fo.d' y ∧ OnPath (s := s) y v := by
  rcases fpRun_frontier_persist hfp v hvU with h | h
  · exact absurd (Finset.mem_coe.mpr h.1) hvW
  · obtain ⟨y, ⟨j, hyP⟩, hcy, hyv⟩ := h
    exact ⟨j, y, hyP, hcy, hyv⟩

/-- The same at the **returned** cone: a gated cone member is behind a pivot group member.  Only
the bound monotonicity `stf.bp ≤ B` is needed to move the cone inclusion up from `tailBP` to
`B`. -/
theorem exists_gate_of_cone_not_mem_foW {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {stf : RState G s fo.p} (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hmono : stf.bp ≤ e.B) {v : Fin G.n}
    (hvU : v ∈ Utilde (tailBP e.B stf) (e.S : Set (Fin G.n))) (hvW : v ∉ fo.W) :
    ∃ j : Fin fo.p, ∃ y ∈ fo.P j, Complete fo.d' y ∧ OnPath (s := s) y v :=
  exists_gate_of_not_mem_foW hfp
    (utilde_mono (tailBP_le e.B stf hmono) hvU) hvW

/-! ## 4. Relation to Route 2: the new residue is below the value floor

`LowKeyClosure`'s Route 2 supplies the mint disjunct for *every* unsettled cone member (no `W`
guard) from a value floor at keys plus a live-label premise.  So `GatedMint` is implied by that
pair — the guard only narrows the requirement, and this records that nothing here is stronger
than the previously named Route 2 hypotheses. -/

/-- Route 2's hypotheses imply `GatedMint` (the `x ∉ W` guard is simply not used). -/
theorem gatedMint_of_keyfloor {B : WLab G s} (S W : Finset (Fin G.n)) {p : ℕ}
    {st : RState G s p} (hinv : LoopBoundInv st) (hcust : Custody st)
    (hlive : ExitLive (tailBP B st) S st) (hkey : KeyFloorLow (tailBP B st) S st) :
    GatedMint B S W st := by
  intro x hxU hzs _hxW
  rcases hcust x (hlive x hxU hzs) with h | h
  · exact absurd h hzs
  · obtain ⟨val, hval⟩ := Option.ne_none_iff_exists'.mp h
    have hp := prem_of_key_below B S W st hinv hval (hkey x hxU hzs val hval)
    exact ⟨val, hp.1, hp.2⟩

/-! ## 5. Closure of the residue: what `a4_joint` still owes

Everything in §1–§4 is proved.  The single unproved statement is `GatedMint` — and, by
`exists_gate_of_cone_not_mem_foW`, at a vertex behind a FindPivots pivot.  `ExitJoint`
(`LowKeyClosure`) is the *consequence* of `GatedMint` plus §1, so the residue has shrunk to the
pivot-gated branch; the mint/value-floor transport inside that branch is already
`LowKeyClosure.prem_of_key_below` + `gatedMint_of_keyfloor`, and `Prem = ∅` (Q12) is a separate
statement (`A4.MintPreFloor`). -/

#print axioms Frontier.DMSY.mem_tailWp_of_complete
#print axioms Frontier.DMSY.tail_U_of_mem_foW
#print axioms Frontier.DMSY.exitJoint_of_gatedMint
#print axioms Frontier.DMSY.tail_cover_of_gatedMint
#print axioms Frontier.DMSY.tail_identity_of_gatedMint
#print axioms Frontier.DMSY.exists_gate_of_not_mem_foW
#print axioms Frontier.DMSY.exists_gate_of_cone_not_mem_foW
#print axioms Frontier.DMSY.gatedMint_of_keyfloor

end DMSY
end Frontier

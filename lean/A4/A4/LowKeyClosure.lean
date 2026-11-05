import A4.IdentityCover

/-!
# Frontier.DMSY.LowKeyClosure — Route 2's residue, sharpened and located

`A4.IdentityCover` left `a4_joint` a choice between Route 1 (`Yclear`) and Route 2's pair
`LowKeyAccurate (tailBP B st) st.d st.D` **and** `BelowLabelFloor (tailBP B st) S st`.  This file
takes Route 2 apart against the actual loop-exit semantics and shows that the pair is *not* the
residue: one half is free, the other is stronger than the clause needs, and what remains is an
exactly stated joint statement about the loop's own settlement log and mint list.

## 1. The value half is free (no label accuracy involved)

`prem_of_key_below`: **a stored value below `tailBP` is already a `Premature` entry** — from
`LoopBoundInv` (`Transitive.LoopBoundInv`: every stored value is `≥ st.bp` or is one of the
state's recorded mints) plus the fact that `tailBP = st.bp` whenever `𝒟 ≠ ∅` (BM.24a).  No label
is mentioned: `IdentityCover.prem_of_low_key` obtained this only *through* `LowKeyAccurate`, but
`hacc` was used solely to transport `st.d y < B′` to `val < B′`.  Drop `hacc`.

## 2. Route 2 needs *live* labels, not the label floor

`tail_cover_of_minimal` replaces `BelowLabelFloor` by the strictly weaker

  `ExitLive B′ S st := ∀ x ∈ Ũ(B′,S), x ∉ st.evts → st.d x ≠ ⊤`

— the label is only ever consulted to know it is not `⊤`, so that `Custody` yields a key.  A *value*
floor at the keys (`KeyFloorLow`, `LowKeyAccurate` restricted to unsettled cone members) supplies
the rest.  `exitLive_of_belowLabelFloor` and `keyFloorLow_of_accurate` record that this is a
weakening, not a change of subject.

## 3. The residual is exactly the joint exit statement — proved equivalent, both ways

`ExitJoint B S W st` says: **every unsettled member of the returned cone is a boundary settlement
(`W′`) or a recorded sub-`B′` final mint.**  It mentions neither `st.d` nor `st.D`.
`cover_iff_exitJoint` proves

  `Ũ(B′,S) ⊆ U ∪ K  ↔  ExitJoint B S W st`

with no hypotheses at all (`mem_carveKeys_tail` unfolds the carve-out; `tailOut_U_mem` splits `U`).
So Route 2's `hcover` *is* the joint completeness invariant, in mint language, and
`exitJoint_of_keyfloor` shows Route 2 maps into it.

## 4. Consequences: `BelowLabelFloor` is not an independent premise

`belowLabelFloor_of_exitJoint`: given the mint-label bookkeeping `st.d m.x = m.val` — free at a loop
exit, `mint_labels_of_loop` (that is `Structural.iloop_mints_label` with the vacuous `mkInit`
base, whose mint list is empty) — `ExitJoint` *implies* `BelowLabelFloor`.  So the label floor can
never be the residual: whatever supplies `hcover` supplies it.  `KeyFloorLow` in turn implies
`ExitJoint` (`exitJoint_of_keyfloor`), but **not conversely**: `ExitJoint` constrains only the mint
list, so a vertex that is *both* a recorded sub-floor mint and the holder of a key at value `≥ B′`
satisfies `ExitJoint` and refutes `KeyFloorLow`.  `keyFloorLow_iff_noStaleKey` is exactly that gap
in first-violation form: a value floor at keys is "no unsettled cone member carries a key at value
`≥ B′`".  (Whether the engine can produce such a stale-high-key/mint coincidence is *not* settled
here — only that the cover does not exclude it, so Route 2's pair is strictly stronger than the
cover.)

## 5. The exact remaining leaf

The one thing §3–§4 do not manufacture, and the only piece `a4_joint` must still carry, is the
**mint disjunct of `ExitJoint` at an unsettled cone vertex**: for every `x ∈ Ũ(tailBP B st, S)`
that the loop log does not settle and `W′` does not append, the final iteration's re-selection
recorded `(x, val)` with `val < tailBP B st`.  `exitJoint_of_keyfloor` shows the value floor
supplies it; the converse direction (mint ⟹ key value floor) additionally needs that a recorded
mint's value survives as the key's value at `x` (`prem_of_key_value_lt` + `LoopBoundInv`), i.e. the
`Prem = ∅` (Q12) statement at BM.29 — the same leaf `A4.MintPreFloor` isolates at `Run.base`.  No
further splitting is hidden: the cover ← mint is proved, and the mint ⟸ cover is proved.

No `sorry`/`admit`, no new axiom, `a4_joint` not assumed.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The value half of the floor, label-free -/

/-- **A stored value below the returned floor is a `Premature` entry** — `LoopBoundInv` alone.  This
is `IdentityCover.prem_of_low_key` with its `LowKeyAccurate` hypothesis removed: only the *value*
side of the invariant is used (the label side transported nothing but `val < tailBP`). -/
theorem prem_of_key_below (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) {x : Fin G.n} {val : WLab G s}
    (hx : st.D x = some val) (hlt : val < tailBP B st) :
    (callOut (tail B S W st)).Premature x val := by
  refine ⟨?_, hlt⟩
  have hne : ¬ DS.IsEmpty st.D := fun h =>
    absurd (h x) (by rw [hx]; exact Option.some_ne_none val)
  rw [tailBP_of_not_isEmpty B st hne] at hlt
  rcases hinv x val hx with h | h
  · exact absurd h (not_le.mpr hlt)
  · exact h

/-! ## 2. Route 2 with the minimal premise: live labels and a value floor at keys -/

/-- **The value floor, restricted to the vertices Route 2 actually queries**: an unsettled member
of the returned cone whose key carries a sub-floor value.  Strictly weaker than
`IdentityCover.LowKeyAccurate`, which also constrains keys at *settled* vertices — where the engine
provably cannot help (a child may lower a label whose parent key survives the merge). -/
def KeyFloorLow (B' : WLab G s) (S : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x, x ∈ Utilde B' (S : Set (Fin G.n)) → x ∉ settledSet st.evts →
    ∀ val, st.D x = some val → val < B'

/-- `LowKeyAccurate` plus the label floor give the restricted floor (this is exactly the pair
`IdentityCover.Route 2` consumes; the restriction is what makes §2's route weaker). -/
theorem keyFloorLow_of_accurate {B' : WLab G s} {S : Finset (Fin G.n)} {p : ℕ}
    {st : RState G s p} (hacc : LowKeyAccurate B' st.d st.D)
    (hlow : BelowLabelFloor B' S st) : KeyFloorLow B' S st :=
  fun x hxU hs val hval => hacc x val hval (hlow x hxU hs)

/-- **The label the floor really needs is only that it is live.** An unsettled cone member with
label `⊤` is not a key (`Custody` is vacuous there), so all Route 2 needs is `≠ ⊤` — not
`< B′`. -/
def ExitLive (B' : WLab G s) (S : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x, x ∈ Utilde B' (S : Set (Fin G.n)) → x ∉ settledSet st.evts → st.d x ≠ ⊤

/-- `BelowLabelFloor` implies liveness (a floor is in particular not `⊤`). -/
theorem exitLive_of_belowLabelFloor {B' : WLab G s} {S : Finset (Fin G.n)} {p : ℕ}
    {st : RState G s p} (hlow : BelowLabelFloor B' S st) : ExitLive B' S st := by
  intro x hxU hs htop
  have hlt := hlow x hxU hs
  rw [htop] at hlt
  exact not_top_lt hlt

/-- **Route 2, sharpened.**  A live label plus a value floor at unsettled cone keys delivers
`hcover` with the carve-out doing the work — no frontier, no `LowKeyAccurate`, no label floor. -/
theorem tail_cover_of_minimal (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) (hcust : Custody st)
    (hlive : ExitLive (tailBP B st) S st) (hkey : KeyFloorLow (tailBP B st) S st) :
    Utilde (tailBP B st) (S : Set (Fin G.n)) ⊆
      (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S := by
  intro x hxU
  by_cases hs : x ∈ settledSet st.evts
  · exact Or.inl (settledSet_subset_tail_U B S W st hs)
  · refine Or.inr (mem_carveKeys.mpr ⟨?_, hxU⟩)
    rcases hcust x (hlive x hxU hs) with h | h
    · exact absurd h hs
    · obtain ⟨val, hval⟩ := Option.ne_none_iff_exists'.mp h
      exact ⟨val, prem_of_key_below B S W st hinv hval (hkey x hxU hs val hval)⟩

/-! ## 3. The joint exit invariant, in mint language -/

/-- **The joint exit statement**: every unsettled member of the returned cone is a boundary
settlement or a recorded sub-floor final mint.  No label, no stored value. -/
def ExitJoint (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x, x ∈ Utilde (tailBP B st) (S : Set (Fin G.n)) → x ∉ settledSet st.evts →
    x ∈ (tailWp B S W st : Set (Fin G.n)) ∨
      ∃ val, Mint.mk x val ∈ st.mints ∧ val < tailBP B st

/-- The tail's carve-out at a loop-exit state, in the loop's own mint list. -/
theorem mem_carveKeys_tail (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) {x : Fin G.n} :
    x ∈ (callOut (tail B S W st)).carveKeys S ↔
      (∃ val, Mint.mk x val ∈ st.mints ∧ val < tailBP B st) ∧
        x ∈ Utilde (tailBP B st) (S : Set (Fin G.n)) :=
  Iff.rfl

/-- **`hcover` is exactly the joint exit statement.**  Both directions are the decomposition of the
tail's `U` (loop log plus `W′`) and of the carve-out (a `Premature` entry is a recorded sub-floor
mint); no hypothesis is consumed, and no label or stored value appears on the right. -/
theorem cover_iff_exitJoint (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) :
    Utilde (tailBP B st) (S : Set (Fin G.n)) ⊆
        (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S ↔
      ExitJoint B S W st := by
  constructor
  · intro h x hxU hxev
    rcases h hxU with hU | hK
    · rcases tailOut_U_mem.mp hU with h | h
      · exact absurd h hxev
      · exact Or.inl (Finset.mem_coe.mpr h)
    · obtain ⟨⟨val, hm, hlt⟩, _⟩ := mem_carveKeys_tail B S W st |>.mp hK
      exact Or.inr ⟨val, hm, hlt⟩
  · intro h x hxU
    by_cases hxev : x ∈ settledSet st.evts
    · exact Or.inl (settledSet_subset_tail_U B S W st hxev)
    · rcases h x hxU hxev with hW | ⟨val, hm, hlt⟩
      · exact Or.inl (tailOut_U_mem.mpr (Or.inr (Finset.mem_coe.mp hW)))
      · exact Or.inr (mem_carveKeys_tail B S W st |>.mpr ⟨⟨val, hm, hlt⟩, hxU⟩)

/-- Route 2's hypotheses (value floor + live labels + custody + `LoopBoundInv`) land in the joint
exit statement. -/
theorem exitJoint_of_keyfloor (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) (hcust : Custody st)
    (hlive : ExitLive (tailBP B st) S st) (hkey : KeyFloorLow (tailBP B st) S st) :
    ExitJoint B S W st :=
  (cover_iff_exitJoint B S W st).mp
    (tail_cover_of_minimal B S W st hinv hcust hlive hkey)

/-! ## 4. What the joint statement gives back, and what it cannot -/

/-- At a loop exit the mints are keyed at their own labels (`Structural.iloop_mints_label`, whose
`mkInit` base is vacuous). -/
theorem mint_labels_of_loop (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ m ∈ st.mints, st.d m.x = m.val) → ∀ m ∈ stf.mints, stf.d m.x = m.val :=
  fun hloop h0 => iloop_mints_label t B l hloop h0

/-- **`BelowLabelFloor` is not an independent premise**: the joint exit statement implies it, given
the mint-label bookkeeping.  So no Route-2 caller owes the label floor on top of the cover — the
low-label content is carried by the mints (`W′` members are below the floor by the boundary filter
alone). -/
theorem belowLabelFloor_of_exitJoint (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hmlab : ∀ m ∈ st.mints, st.d m.x = m.val)
    (hjoint : ExitJoint B S W st) : BelowLabelFloor (tailBP B st) S st := by
  intro x hxU hxev
  rcases hjoint x hxU hxev with hW | ⟨val, hm, hlt⟩
  · have h' : x ∈ wPrime (tailBP B st) W st.evts st.d := by
      rwa [tailWp_reads_state] at hW
    exact (mem_wPrime.mp h').2.2
  · rw [hmlab (Mint.mk x val) hm]
    exact hlt

/-- **The first-violation form of the value floor**: `KeyFloorLow` is exactly "no unsettled cone
member carries a key at value `≥ B′`".  This is the only shape in which the residue survives in the
key language — and it is where `ExitJoint` has slack, since a vertex may be *both* a recorded low
mint (satisfying `ExitJoint`) and the holder of a stale-high key (refuting `KeyFloorLow`). -/
theorem keyFloorLow_iff_noStaleKey {B' : WLab G s} {S : Finset (Fin G.n)} {p : ℕ}
    {st : RState G s p} :
    KeyFloorLow B' S st ↔
      ∀ x, x ∈ Utilde B' (S : Set (Fin G.n)) → x ∉ settledSet st.evts →
        ¬ ∃ val, st.D x = some val ∧ B' ≤ val := by
  constructor
  · intro hk x hxU hs ⟨val, hval, hle⟩
    exact absurd (hk x hxU hs val hval) (not_lt.mpr hle)
  · intro h x hxU hs val hval
    by_contra hge
    exact h x hxU hs ⟨val, hval, not_lt.mp hge⟩

#print axioms Frontier.DMSY.prem_of_key_below
#print axioms Frontier.DMSY.tail_cover_of_minimal
#print axioms Frontier.DMSY.mem_carveKeys_tail
#print axioms Frontier.DMSY.cover_iff_exitJoint
#print axioms Frontier.DMSY.exitJoint_of_keyfloor
#print axioms Frontier.DMSY.belowLabelFloor_of_exitJoint
#print axioms Frontier.DMSY.keyFloorLow_iff_noStaleKey

end DMSY
end Frontier

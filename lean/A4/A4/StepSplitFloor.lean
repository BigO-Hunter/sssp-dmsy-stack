import A4.BelowSeparator
import A4.JointAssembly
import A4.TailIdentity

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.StepSplitFloor — the two strengthened clauses, at their smallest

`A4.DrainedClauses` named two things that `IStep` does not supply and that the joint induction
therefore has to carry: `BelowSeparator.ChildFloor`'s **refusal floor** (clause 2, not a
`Lemma37Concl` field), and `A4.JointAssembly.StepSplit`'s **`hcover`/`j6`** pair.  This file
derives the smallest strengthened predicate that carries them, proves its initialisation and its
one-step form from `IStep`/`pullRun`/`fpRun`, and names exactly what is left over.  `GatedMint`
(`A4.TailIdentity`) is folded in as the identity side's counterpart.

## 1. The refusal floor is the run-level predicate `Floor`

`Floor e out` is `ChildFloor`'s clause 2 with the child's `CallEntry` abstracted to `(e, out)`; by
`childFloor_iff` the pair `(settleComplete, Floor)` *is* `ChildFloor`.  `FloorL R d evts`
parameterises the threshold, and that parameter is the whole story:

* `FloorL.mono` — the floor is **antitone** in the threshold (a bigger threshold asks for more);
* `FloorL.transport` — it survives any sound label lowering (`hsrc` is `settleComplete`, i.e.
  `ChildFloor`'s clause 1);
* `floorL_init` — vacuous at `mkInit` (the log is empty);
* `floor_step` — one iteration hands the floor at `c.B` from the **child's** floor (this is
  `BelowSeparator.hbelow_of_floor`, i.e. exactly what `SettleSweep` consumes);
* `floorL_append` — the floor at a *fixed* `R` accumulates over the log.

The composition question is `floorL_of_below_above`: the floor at `B` is the floor at `c.B`
(the child's, derivable) **plus** `AboveSep` — the heads of settled sources whose candidate lies
in `[c.B, B)`.  `c.B ≤ B` always (`istep_childB_le`), so the child's own `ChildFloor` can never
supply the parent's threshold: the minimal composable clause is therefore `FloorAll`, the floor at
*every* threshold at or above the call's own bound (`floorAll_child_at_parent`,
`childFloor_of_floorAll`).

## 2. `StepSplit`, decomposed

* `hcover`'s pull content is **derived**: `mem_childS_of_key_below` — a key of the loop store whose
  *stored value* is below the pull separator is in the child's seed set (`pullRun`'s
  `Si = belowKeys`).  What `pullRun` cannot see is `LabelKey`: the *label* is below the separator
  but the store's value is not.  Honesty (`Structural.istep_honest`) runs the other way
  (`d y ≤ stored`), so this is a genuine residual — stale values on the store, not stale keys.
* `j6` splits with `expand`: `expand_self` is `Si ⊆ c.S`; the group half is **derived** from
  `pl ⊆ S` (`pl_init` from `fpRun`'s `P = fun _ => Y`, `Y ⊆ S`; `pl_step` from `resid`'s filter;
  `iloop_pl_seeds`) plus the filter's `d v < Bi` and label soundness (`j6_group`); the `Si` half is
  the residual `KeyCone` (every stored key below `B` lies in `Ũ(B,S)`).

`stepSplit_of_residuals` assembles `StepSplit` from the three per-state facts, two of which are
residuals and one (`pl ⊆ S`) of which is a theorem.

## 3. `GatedMint`: the mint equations give the shape, not the converse

`mint_is_selected_pivot` — every mint of a loop's final state is a **selected pivot**: it is the
final state's own `piv` and lies in its own residual group at its own label.  That is the whole
content of `IStep`'s `mints := J.map (fun j => Mint.mk (sel j) (d3 (sel j)))` transported through
`ILoop`.

`GatedMint` asks for the **converse**: every unsettled gated cone member *is* such a mint.  Its
conclusion is literally a `Premature` witness (`gatedMint_premature`), which is the **opposite
polarity** to Q12's `Prem = ∅` — so it can be neither derived from `Prem`-freeness nor imply it,
and `cover_empty_carve_of_premFree` records what the two together buy: the identity cover with an
**empty** carve-out (clause (2c) verbatim).  The exact leaf is `GatedSel` + `MintBelow`
(`gatedMint_of_gatedSel_val`), and `not_gatedSel_of_remainder` shows the obstruction is a
**residual group with a non-selected member in the cone** — the group filter, not a bound, not a
value and not `Prem`.

No `sorry`/`admit`, no new axiom, `a4_joint` not assumed.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The refusal floor -/

/-- `FloorL R d evts`: below the threshold `R`, an edge out of a settled vertex finds its head
complete at the labels `d`.  `R` is a *parameter*, and the whole composition question is which `R`
the joint induction carries. -/
def FloorL (R : WLab G s) (d : Labels G s) (evts : List (SettlementEvent G)) : Prop :=
  ∀ e₀, G.src e₀ ∈ settledSet evts → ext (d (G.src e₀)) e₀ < R → Complete d (G.dst e₀)

/-- The run-level refusal floor: `FloorL` at the call's **own** bound.  `ChildFloor c fo'` is
`(settleComplete, Floor c fo')` — `childFloor_iff`. -/
def Floor (e : CallEntry G s) (out : CallOut G s) : Prop :=
  FloorL e.B out.d' out.evts

/-- `ChildFloor` **is** the pair (clause 1, `Floor`): clause 2 is `Floor` verbatim. -/
theorem childFloor_iff (c : CallEntry G s) (fo' : CallOut G s) :
    ChildFloor c fo' ↔ (∀ ev ∈ fo'.evts, Complete fo'.d' ev.v) ∧ Floor c fo' :=
  Iff.rfl

/-- The floor is antitone in its threshold: a smaller threshold asks for fewer heads. -/
theorem FloorL.mono {R R' : WLab G s} (hRR : R' ≤ R) {d : Labels G s}
    {evts : List (SettlementEvent G)} (h : FloorL R d evts) : FloorL R' d evts :=
  fun e₀ hu hlt => h e₀ hu (lt_of_lt_of_le hlt hRR)

/-- The floor over a sub-log. -/
theorem FloorL.subset {R : WLab G s} {d : Labels G s}
    {evts evts' : List (SettlementEvent G)} (hsub : settledSet evts' ⊆ settledSet evts)
    (h : FloorL R d evts) : FloorL R d evts' :=
  fun e₀ hu hlt => h e₀ (hsub hu) hlt

/-- **The floor survives any sound, monotone label lowering.**  `hsrc` is `settleComplete`
(`ChildFloor`'s clause 1): a settled source is complete, so it keeps its label, and the candidate
threshold is unchanged; the head's completeness is carried by `Complete.of_le`.  This is the
"sweep never raises a label" step, used by `floor_step` and by the tail's transport. -/
theorem FloorL.transport {R : WLab G s} {d d' : Labels G s}
    {evts : List (SettlementEvent G)} (h : FloorL R d evts) (hsound : Sound d')
    (hle : ∀ v, d' v ≤ d v) (hsrc : ∀ v ∈ settledSet evts, Complete d v) : FloorL R d' evts := by
  intro e₀ hu hlt
  have hcs : Complete d' (G.src e₀) := Complete.of_le (hsrc _ hu) hsound (hle _)
  have hdu : d' (G.src e₀) = d (G.src e₀) := hcs.trans (hsrc _ hu).symm
  rw [hdu] at hlt
  exact Complete.of_le (h e₀ hu hlt) hsound (hle _)

/-- **Initialisation.**  `mkInit`'s log is empty, so the floor holds at every threshold —
the strengthened clause costs nothing at the base. -/
theorem floorL_init (R : WLab G s) (e : CallEntry G s) (fo : FPOut G s)
    (piv : Fin fo.p → Fin G.n) :
    FloorL R (mkInit e fo piv).d (mkInit e fo piv).evts := by
  intro e₀ hu
  simp [mkInit, settledSet] at hu

/-- **The floor at a fixed threshold accumulates over the log.** -/
theorem floorL_append {R : WLab G s} {d : Labels G s}
    {a b : List (SettlementEvent G)} (ha : FloorL R d a) (hb : FloorL R d b) :
    FloorL R d (a ++ b) := by
  intro e₀ hu hlt
  rw [settledSet_append, Set.mem_union] at hu
  rcases hu with h | h
  · exact ha e₀ h hlt
  · exact hb e₀ h hlt

/-- **The child's bound is below the call bound** (`pullRun`'s `x ≤ Bd`).  So `FloorL`'s threshold
for the parent is never the child's own: the parent's ceiling is at or above it. -/
theorem istep_childB_le {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') : c.B ≤ B := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _hmerge, _hsweep, _hresid, _hJ, _hsel,
    _hst'⟩ := h
  have hcB : c.B = Bi := by rw [hc]
  rw [hcB]
  exact hpull.2.2.1

/-- **One iteration hands the floor at `c.B`** from the child's own floor (`ChildFloor`'s clause 2,
i.e. `Floor c fo'`) and the child's settlement completeness.  This is
`BelowSeparator.hbelow_of_floor` in `FloorL` language: it is the precise form in which the step
*consumes* the strengthened clause. -/
theorem floor_step {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hwalk : WalkInv fo'.d') (hsettle : ∀ ev ∈ fo'.evts, Complete fo'.d' ev.v)
    (hfloor : Floor c fo') :
    FloorL c.B st'.d fo'.evts :=
  hbelow_of_floor t B l h hwalk ⟨hsettle, hfloor⟩

/-- Settlement completeness over the log (`ChildFloor`'s clause 1) read as completeness over the
settled **set** — the form `FloorL.transport` consumes. -/
theorem complete_settledSet {d : Labels G s} {evts : List (SettlementEvent G)}
    (h : ∀ ev ∈ evts, Complete d ev.v) : ∀ v ∈ settledSet evts, Complete d v := by
  intro v hv
  obtain ⟨ev, hev, hve⟩ := hv
  rw [← hve]
  exact h ev hev

/-- **One step, at a fixed threshold.**  Both halves of the successor's log — the state's own
events and the child's — satisfy the floor at `R` after the sweep: `FloorL.transport` twice (the
sweep only lowers labels, and `hsrcS`/`hsrcC` are `ChildFloor`'s clause 1 at each half), then
`floorL_append`.  Each `hle` is an existing lane lemma (`istep_le_of_child` for the state,
`sweepEvts_le` for the child via `IStep`'s sweep equation).  At `R = c.B` the child's half is
exactly `floor_step`. -/
theorem floorL_istep {t : ℕ} {B : WLab G s} {l : ℕ} {R : WLab G s} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (hstate : FloorL R st.d st.evts) (hchild : FloorL R fo'.d' fo'.evts)
    (hsrcS : ∀ v ∈ settledSet st.evts, Complete st.d v)
    (hsrcC : ∀ v ∈ settledSet fo'.evts, Complete fo'.d' v)
    (hwalk' : WalkInv st'.d) (hleS : ∀ v, st'.d v ≤ st.d v) (hleC : ∀ v, st'.d v ≤ fo'.d' v) :
    FloorL R st'.d (st.evts ++ fo'.evts) :=
  floorL_append
    (FloorL.transport hstate (WalkInv.sound hwalk') hleS hsrcS)
    (FloorL.transport hchild (WalkInv.sound hwalk') hleC hsrcC)

/-! ### The composition question: `c.B` is not `B` -/

/-- **The above-separator half**: the heads of settled sources whose candidate lies in `[c.B, B)`.
`IStep` does not supply it (`SettleSweep`'s above-separator branch only gives
`d dst ≤ candidate`, and an *un-tight* accepted relaxation leaves the head at the candidate, which
need not be canonical). -/
def AboveSep (B : WLab G s) (c : CallEntry G s) (d : Labels G s)
    (evts : List (SettlementEvent G)) : Prop :=
  ∀ e₀, G.src e₀ ∈ settledSet evts → c.B ≤ ext (d (G.src e₀)) e₀ →
    ext (d (G.src e₀)) e₀ < B → Complete d (G.dst e₀)

/-- **The floor at `B` = the child's floor at `c.B` + `AboveSep`.**  This is the exact
decomposition: the below-separator half is the joint induction's IH (`floor_step`), the
above-separator half is the residual. -/
theorem floorL_of_below_above {B : WLab G s} {c : CallEntry G s} {d : Labels G s}
    {evts : List (SettlementEvent G)} (hbelow : FloorL c.B d evts) (habove : AboveSep B c d evts) :
    FloorL B d evts := by
  intro e₀ hu hlt
  by_cases hge : c.B ≤ ext (d (G.src e₀)) e₀
  · exact habove e₀ hu hge hlt
  · exact hbelow e₀ hu (lt_of_not_ge hge)

/-- The minimal composable clause: the floor at **every** threshold at or above the call's own
bound.  Strictly stronger than `Floor` (= `R = e.B`) iff the above-separator part can fail. -/
def FloorAll (e : CallEntry G s) (out : CallOut G s) : Prop :=
  ∀ R : WLab G s, e.B ≤ R → FloorL R out.d' out.evts

/-- `FloorAll` at the call's own bound is `Floor`. -/
theorem floorAll_own {e : CallEntry G s} {out : CallOut G s} (h : FloorAll e out) : Floor e out :=
  h e.B le_rfl

/-- **A child's `FloorAll` supplies the parent's threshold** — the composition the parent needs and
that the child's own `Floor` (at `c.B`) cannot supply. -/
theorem floorAll_child_at_parent {B : WLab G s} {c : CallEntry G s} {fo' : CallOut G s}
    (hcB : c.B ≤ B) (h : FloorAll c fo') : FloorL B fo'.d' fo'.evts :=
  h B hcB

/-- `FloorAll` discharges `ChildFloor` (with clause 1). -/
theorem childFloor_of_floorAll {c : CallEntry G s} {fo' : CallOut G s}
    (hset : ∀ ev ∈ fo'.evts, Complete fo'.d' ev.v) (h : FloorAll c fo') : ChildFloor c fo' :=
  ⟨hset, floorAll_own h⟩

/-! ## 2. `StepSplit`, decomposed into derived and residual parts -/

/-! ### 2a. `hcover`: `pullRun`'s half, and the residual bridge -/

/-- **`pullRun`'s contribution to `hcover`.**  A key of the loop store whose **stored value** is
below the pull separator is in the child's seed set: the pull extracts exactly `belowKeys`, the
BM.12 expansion starts from `Si`.  This is the part of `hcover` that is a theorem. -/
theorem mem_childS_of_key_below (t : ℕ) {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') {y : Fin G.n}
    (hkey : ∃ v, st.D y = some v ∧ v < c.B) : y ∈ c.S := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _hmerge, _hsweep, _hresid, _hJ,
    _hsel, _hst'⟩ := h
  obtain ⟨v, hv, hlt⟩ := hkey
  have hcB : c.B = Bi := by rw [hc]
  have hcS : c.S = expand st.d st.pl st.piv Si Bi := by rw [hc]
  have hySi : y ∈ Si := by
    rw [hpull.1]
    exact mem_belowKeys.mpr ⟨v, hv, by rwa [hcB] at hlt⟩
  rw [hcS]
  exact Finset.mem_union.mpr (Or.inl hySi)

/-- **The residual `hcover` cannot see from `pullRun`**: below the separator, the *label* is below
it but the *store's value* is not.  Store honesty runs the other way
(`Structural.istep_honest`: `d y ≤ stored`), so a store whose value was inserted before the label
fell defeats this — not a stale *key* (`★BM.15`), a stale *value*. -/
def LabelKey (B : WLab G s) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ y, st.d y < B → ∃ v, st.D y = some v ∧ v < B

/-- **`hcover`'s first conjunct, from `LabelKey`** — no frontier is consulted once the bridge is
global over the state. -/
theorem hcover_of_labelKey (t : ℕ) {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hk : LabelKey c.B st) :
    ∀ y, st.d y < c.B → y ∈ c.S :=
  fun y hy => mem_childS_of_key_below t h (hk y hy)

/-! ### 2b. `j6`: the group half is derived, the `Si` half is `KeyCone` -/

/-- The initial residual groups are FindPivots' gate set, which is a subset of the seed set. -/
theorem pl_init {t : ℕ} {e : CallEntry G s} {fo : FPOut G s} {piv : Fin fo.p → Fin G.n}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) :
    ∀ j, (mkInit e fo piv).pl j ⊆ e.S := by
  obtain ⟨_hpre, Y, _cc, _stf, hYsub, _hYne, _hcap, _hloop, _hd', _hW, _hp, hP, _hQ⟩ := hfp
  intro j x hx
  have hx' : x ∈ fo.P j := by simpa [mkInit] using hx
  have hxY : x ∈ Y := by simpa [hP] using hx'
  exact hYsub hxY

/-- One iteration's residual groups are the old groups minus the child's settlements: only a
filter, so `pl ⊆ S` is preserved with no content from `pullRun`. -/
theorem pl_step {t : ℕ} {B : WLab G s} {l : ℕ} {S : Finset (Fin G.n)} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hpl : ∀ j, st.pl j ⊆ S) : ∀ j, st'.pl j ⊆ S := by
  classical
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _hmerge, _hsweep, hresid, _hJ,
    _hsel, hst'⟩ := h
  subst hst'
  intro j x hx
  have hx' : x ∈ resid j := hx
  rw [hresid j] at hx'
  exact hpl j (Finset.mem_filter.mp hx').1

/-- **`pl ⊆ S` is a theorem of the loop** (`mkInit` from `fpRun`'s `P = fun _ => Y`, `Y ⊆ S`; the
iteration by `pl_step`).  It is the half of `j6` that needs no premise at all. -/
theorem iloop_pl_seeds (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ j, st.pl j ⊆ S) → ∀ j, stf.pl j ⊆ S := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hinv => hinv
  | step hne hg hstep hrest ih => exact fun hinv => ih (pl_step hstep hinv)

/-- **The residual `j6` cannot see from `pullRun`**: every stored key below `B` lies in the cone
`Ũ(B,S)`.  Keys enter from the seeds (`S ⊆ Ũ` by `onPath_self`), from children (inductively
`Ũ(c.B,c.S) ⊆ Ũ(B,S)` via `utilde_subset`/`utilde_mono_bound`) and from sweep inserts — the last is
the gap, a head reached from a settled source need not have a canonical path through `S`. -/
def KeyCone (B : WLab G s) (S : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ y v, st.D y = some v → v < B → y ∈ Utilde B (S : Set (Fin G.n))

/-- **The group half of `j6`, derived.**  A BM.12 expansion member that came from a group `j` is in
`pl j ⊆ S`, and its label is below `Bi ≤ B`; label soundness turns that into `dis v < B`, and
`onPath_self` closes the visit.  No separator discipline, no store. -/
theorem j6_group {B : WLab G s} {p : ℕ} {st : RState G s p} {Si : Finset (Fin G.n)}
    {Bi : WLab G s} {S : Finset (Fin G.n)} (hpl : ∀ j, st.pl j ⊆ S) (hwalk : WalkInv st.d)
    (hBiB : Bi ≤ B) {v : Fin G.n} (hv : v ∈ Finset.univ.biUnion fun j =>
      if st.piv j ∈ Si ∧ st.piv j ∈ st.pl j then (st.pl j).filter (fun x => st.d x < Bi) else ∅) :
    v ∈ Utilde B (S : Set (Fin G.n)) := by
  obtain ⟨j, -, hvj⟩ := Finset.mem_biUnion.mp hv
  split_ifs at hvj with hc
  · obtain ⟨hvpl, hvlt⟩ := Finset.mem_filter.mp hvj
    have hdis : dis (s := s) v < B :=
      lt_of_le_of_lt (WalkInv.sound hwalk v) (lt_of_lt_of_le hvlt hBiB)
    have hreach : G.Reachable s v := by
      by_contra hn
      rw [dis_of_not_reachable hn] at hdis
      exact (lt_irrefl (⊤ : WLab G s)) (lt_of_lt_of_le hdis le_top)
    exact ⟨hdis, v, Finset.mem_coe.mpr (hpl j hvpl), onPath_self hreach⟩
  · exact absurd hvj (Finset.notMem_empty v)

/-- **`j6`, from `pl ⊆ S`, label soundness and `KeyCone`.**  Only the `Si` half is a premise. -/
theorem j6_of_pl_keyCone (t : ℕ) {B : WLab G s} {l : ℕ} {S : Finset (Fin G.n)} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hpl : ∀ j, st.pl j ⊆ S) (hkey : KeyCone B S st)
    (hwalk : WalkInv st.d) :
    (c.S : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n)) := by
  have hcle : c.B ≤ B := istep_childB_le h
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _hmerge, _hsweep, _hresid, _hJ,
    _hsel, _hst'⟩ := h
  have hcB : c.B = Bi := by rw [hc]
  have hcS : c.S = expand st.d st.pl st.piv Si Bi := by rw [hc]
  have hBiB : Bi ≤ B := by rw [← hcB]; exact hcle
  intro v hv
  rw [hcS] at hv
  have hv' : v ∈ Si ∪ (Finset.univ.biUnion fun j =>
      if st.piv j ∈ Si ∧ st.piv j ∈ st.pl j then
        (st.pl j).filter (fun x => st.d x < Bi) else ∅) := hv
  rcases Finset.mem_union.mp hv' with hSi | hgrp
  · -- the pulled half: `KeyCone`
    have hmem : ∃ val, st.D v = some val ∧ val < Bi := by
      rw [hpull.1] at hSi
      exact mem_belowKeys.mp hSi
    obtain ⟨val, hval, hlt⟩ := hmem
    exact hkey v val hval (lt_of_lt_of_le hlt hBiB)
  · exact j6_group hpl hwalk hBiB hgrp

/-! ### 2c. `StepSplit`, assembled -/

/-- **`StepSplit` from the residual pair.**  The `hcover` conjunct needs only `LabelKey` (the
frontier argument is irrelevant once the bridge is global); `j6` needs `pl ⊆ S` (a theorem of the
loop, `iloop_pl_seeds`) plus `KeyCone`; `c.B ≤ B` and the state's walk are `IStep`/loop facts.
So `StepSplit` is *not* an irreducible premise: it is `LabelKey ∧ KeyCone` per step. -/
theorem stepSplit_of_residuals (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n))
    (hwalk : ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
      IStep t B l st st' c fo' → WalkInv st.d)
    (hpl : ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
      IStep t B l st st' c fo' → ∀ j, st.pl j ⊆ S)
    (hlabel : ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
      IStep t B l st st' c fo' → LabelKey c.B st)
    (hkey : ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
      IStep t B l st st' c fo' → KeyCone B S st) :
    StepSplit t B l S := by
  intro p st st' c fo' hst Y _hfront
  exact ⟨fun y _hy hlt => hcover_of_labelKey t hst (hlabel st st' c fo' hst) y hlt,
    j6_of_pl_keyCone t hst (hpl st st' c fo' hst) (hkey st st' c fo' hst)
      (hwalk st st' c fo' hst)⟩
/-! ## 3. `GatedMint`: what the mint equations give, and the leaf they do not

`A4.TailIdentity.GatedMint` is the identity side's residue: every unsettled gated cone member is a
recorded sub-floor mint.  Its conclusion is *literally* a `Premature` witness, so it is the
**opposite polarity** to Q12 (`Prem = ∅`) — the two constrain the same mint list from opposite
sides and neither can yield the other.  What the engine *does* expose is the shape of the mints it
records, and that is what `mint_is_selected_pivot` states. -/

/-- A non-drained loop exit has `B' := bp` (BM.24a's `FIX-EMPTY` sits on the drained case only). -/
theorem tailBP_eq_bp {B : WLab G s} {p : ℕ} {st : RState G s p} (hne : ¬ DS.IsEmpty st.D) :
    tailBP B st = st.bp := by
  unfold tailBP
  split
  · next h => exact absurd h hne
  · rfl

/-- **Every mint of a loop's final state is a selected pivot**: it is the state's own `piv`, it
lies in the state's own residual group, and its value is the state's own label there.  This is the
whole content of `IStep`'s `mints := J.map (fun j => Mint.mk (sel j) (d3 (sel j)))`, transported
through `ILoop` by `iloop_mints_shape` (the loop either never ran, so the mints are `mkInit`'s
`[]`, or it ends on one `IStep`). -/
theorem mint_is_selected_pivot (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf → st.mints = [] →
      ∀ m ∈ stf.mints, ∃ j, stf.piv j = m.x ∧ m.x ∈ stf.pl j ∧ stf.d m.x = m.val := by
  intro p st stf qs hloop
  rcases iloop_mints_shape t B l hloop with rfl | ⟨st₁, c, fo', hstep⟩
  · intro hinit m hm
    rw [hinit] at hm
    exact absurd hm List.not_mem_nil
  · intro _hinit m hm
    classical
    obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _hmerge, _hsweep, hresid, hJ, hsel,
      hst'⟩ := hstep
    subst hst'
    obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hm
    subst hjm
    have hjJ : j ∈ J := Finset.mem_toList.mp hj
    refine ⟨j, ?_, ?_, ?_⟩
    · simp only [ite_eq_left hjJ]
    · exact (hsel j hjJ).1
    · rfl

/-- `Prem`-freeness **at the loop's returned floor**: no recorded mint sits below `tailBP`.  This is
Q12's `∀ x val, ¬ Premature x val` written against `tailBP` so that it covers the drained case too
(non-drained: `noPremGated_of_premFree`). -/
def NoPremGated (B : WLab G s) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x val, Mint.mk x val ∈ st.mints → ¬ (val < tailBP B st)

/-- On a non-drained exit, `NoPremGated` is Q12 / `Lemma37Concl.fullImmune`'s `Prem = ∅`. -/
theorem noPremGated_of_premFree {B : WLab G s} {p : ℕ} {st : RState G s p}
    (hne : ¬ DS.IsEmpty st.D)
    (hnp : ∀ x val, ¬ (callOut st).Premature x val) : NoPremGated B st := by
  intro x val hm hlt
  exact hnp x val ⟨hm, by rwa [tailBP_eq_bp hne] at hlt⟩

/-- **`GatedMint`'s conclusion is a `Premature` witness** — its polarity is the opposite of Q12's.
(Stated on a non-drained exit, where `Premature`'s `B'` is `tailBP`.) -/
theorem gatedMint_premature {B : WLab G s} {S W : Finset (Fin G.n)} {p : ℕ} {st : RState G s p}
    (hne : ¬ DS.IsEmpty st.D) (h : GatedMint B S W st) {x : Fin G.n}
    (hxU : x ∈ Utilde (tailBP B st) (S : Set (Fin G.n))) (hxs : x ∉ settledSet st.evts)
    (hxW : x ∉ W) : ∃ val, (callOut st).Premature x val := by
  obtain ⟨val, hm, hlt⟩ := h x hxU hxs hxW
  exact ⟨val, hm, by rwa [tailBP_eq_bp hne] at hlt⟩

/-- **The leaf, sharply.**  `GatedMint` is the *converse* of `mint_is_selected_pivot`: the gated
cone member must be one of the final iteration's selected pivots.  No label, no stored value, no
bound — just membership in `piv`/`mints`. -/
def GatedSel (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x, x ∈ Utilde (tailBP B st) (S : Set (Fin G.n)) → x ∉ settledSet st.evts → x ∉ W →
    ∃ j, st.piv j = x ∧ Mint.mk x (st.d x) ∈ st.mints

/-- `GatedSel` plus the mint's own sub-floor value gives `GatedMint` (the value half is separated
because it is *not* a selection fact: it is the mint-below-bound statement, the mirror image of
`TheoremT`'s `B' ≤ m.val`). -/
theorem gatedMint_of_gatedSel_val {B : WLab G s} {S W : Finset (Fin G.n)} {p : ℕ}
    {st : RState G s p} (h : GatedSel B S W st)
    (hval : ∀ x, x ∈ Utilde (tailBP B st) (S : Set (Fin G.n)) → x ∉ settledSet st.evts →
      x ∉ W → st.d x < tailBP B st) : GatedMint B S W st := by
  intro x hxU hxs hxW
  obtain ⟨_j, _hpiv, hm⟩ := h x hxU hxs hxW
  exact ⟨st.d x, hm, hval x hxU hxs hxW⟩

/-- **The obstruction is a residual group's non-selected member.**  This is where the group filter
(A2/A3) bites and nothing else does: a gated cone member with no mint of its own key refutes
`GatedSel`, hence `GatedMint` — i.e. the engine does not mint every residual group member, it mints
the group's minimum (`hsel`).  So `GatedMint` is false unless non-selected members are settled, in
`W`, or outside the cone. -/
theorem not_gatedSel_of_no_mint {B : WLab G s} {S W : Finset (Fin G.n)} {p : ℕ}
    {st : RState G s p} {y : Fin G.n}
    (hyU : y ∈ Utilde (tailBP B st) (S : Set (Fin G.n))) (hys : y ∉ settledSet st.evts)
    (hyW : y ∉ W) (hnomint : ∀ m ∈ st.mints, m.x ≠ y) : ¬ GatedSel B S W st := by
  intro h
  obtain ⟨_j, _hpiv, hm⟩ := h y hyU hys hyW
  exact hnomint _ hm rfl

/-- **`GatedMint` + `NoPremGated` completes the identity cover with an *empty* carve-out**
(clause (2c) verbatim, no `Prem`): the two opposite-polarity clauses together say that no gated
cone member exists, so §1's `W′` half alone settles every unsettled cone member. -/
theorem cover_of_gatedMint_noPrem (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) (hst0 : st0 = mkInit e fo piv)
    (hloop : ILoop t e.B e.l st0 qs stf) (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (hg : GatedMint e.B e.S fo.W stf) (hnp : NoPremGated e.B stf) :
    Utilde (tailBP e.B stf) (e.S : Set (Fin G.n)) ⊆
      (callOut (tail e.B e.S fo.W stf)).U := by
  intro x hx
  rcases tail_cover_of_gatedMint t hfp hst0 hloop hchildren hg hx with h | h
  · exact h
  · exfalso
    rw [mem_carveKeys_tail] at h
    obtain ⟨⟨val, hm, hlt⟩, _⟩ := h
    exact hnp x val hm hlt

/-! ## 4. What the floor *is*: no loose head — not reachability, not mints

Three residues are now on the table: this file's floor, `A4.TailIdentity`'s `GatedMint` (identity
outside `fo.W`), and `A4.NonDrainedBp`'s cone closure `hcone` + `Prem = ∅` + capped-leaf
`SeedChildLabFloor`.  They are *distinct*: the floor's target is `Complete`, and by
`complete_iff_not_loose` that is the statement that the head carries **no loose label** —
`dis dst < d dst` is impossible.  Cone closure is about which canonical paths run; `Prem` is about
which mints were recorded; `BpChain` is about bounds.  None of them mentions a label being *above*
its canonical value, and that is exactly the floor's leaf. -/

/-- `Complete` at a sound label assignment is "not loose" (`dis v < d v` is impossible). -/
theorem complete_iff_not_loose {d : Labels G s} (hsound : Sound d) {v : Fin G.n} :
    Complete d v ↔ ¬ (dis (s := s) v < d v) := by
  constructor
  · intro h hlt
    rw [h] at hlt
    exact lt_irrefl _ hlt
  · intro h
    exact le_antisymm (le_of_not_gt h) (hsound v)

/-- **The floor's leaf, named**: no head of a settled source carries a label strictly above its
canonical value, below the threshold. -/
def NoLoose (R : WLab G s) (d : Labels G s) (evts : List (SettlementEvent G)) : Prop :=
  ∀ e₀, G.src e₀ ∈ settledSet evts → ext (d (G.src e₀)) e₀ < R →
    ¬ (dis (s := s) (G.dst e₀) < d (G.dst e₀))

/-- **The refusal floor ≡ `NoLoose`** at a sound label assignment.  So the joint induction's
carried clause *is* the no-loose-head statement; nothing about reachability, mints or bounds
enters it, and no such statement can discharge it. -/
theorem floorL_iff_noLoose {R : WLab G s} {d : Labels G s} {evts : List (SettlementEvent G)}
    (hsound : Sound d) : FloorL R d evts ↔ NoLoose R d evts := by
  constructor
  · intro h e₀ hu hlt
    exact (complete_iff_not_loose hsound).mp (h e₀ hu hlt)
  · intro h e₀ hu hlt
    exact (complete_iff_not_loose hsound).mpr (h e₀ hu hlt)

/-- **The floor supplies the relaxation inequality the sweep consumes** (`SettleSweep`'s clause 2
form, `IsFrontier.step`'s `hrelax`).  So the carried clause is *sufficient* for its consumer; the
converse fails, because `Complete` is strictly stronger than the relaxation inequality, and
`complete_iff_not_loose` says which extra content it adds. -/
theorem floor_imp_relax {R : WLab G s} {d : Labels G s} {evts : List (SettlementEvent G)}
    (hfloor : FloorL R d evts) (hsrc : ∀ v ∈ settledSet evts, Complete d v) :
    ∀ e₀, G.src e₀ ∈ settledSet evts → ext (d (G.src e₀)) e₀ < R →
      d (G.dst e₀) ≤ ext (d (G.src e₀)) e₀ := by
  intro e₀ hu hlt
  have hcs : Complete d (G.src e₀) := hsrc _ hu
  have hcd : Complete d (G.dst e₀) := hfloor e₀ hu hlt
  rw [hcd, hcs]
  have hreach : G.Reachable s (G.src e₀) := by
    by_contra hn
    have htop : d (G.src e₀) = ⊤ := hcs.trans (dis_of_not_reachable hn)
    rw [htop, ext_top] at hlt
    exact (lt_irrefl (⊤ : WLab G s)) (lt_of_lt_of_le hlt le_top)
  have hcand : ext (dis (s := s) (G.src e₀)) e₀
      = ((toW (path (s := s) (G.src e₀) ++ [e₀]) : WalkOrd G s) : WLab G s) := by
    conv_lhs => rw [dis_of_reachable hreach]
    exact ext_coe (path (s := s) (G.src e₀)) e₀
  rw [hcand]
  exact dis_le_walk (walk_ext (path_isMinWalk hreach).1 e₀ rfl)

/-! ### The one leaf the other workstreams *do* supply: cone closure → `KeyCone` -/

/-- Every stored value is a walk label for its key: an inserted value is always some
`ext (d src) e` (BM.14 keep-min of such values, ★BM.15 deletes only keys, the sweep inserts its
candidate), so it is never below the key's canonical label.  This is the store-side bridge
`KeyCone` needs, and it is *not* `Keyed` (which the lane establishes is not an invariant). -/
def StoreSound {p : ℕ} (st : RState G s p) : Prop :=
  ∀ y val, st.D y = some val → dis (s := s) y ≤ val

/-- **Cone closure + `StoreSound` give `KeyCone`** — i.e. the reachability leaf that
`A4.NonDrainedBp` names for clause (2c) also discharges this file's `j6` residue on the `Si` side.
One leaf, two consumers; neither is a separator/`PullSpec` fact. -/
theorem keyCone_of_storeSound_coneClosure {B : WLab G s} {S : Finset (Fin G.n)} {p : ℕ}
    {st : RState G s p} (hss : StoreSound st)
    (hcone : ∀ y, dis (s := s) y < B → ∃ x ∈ (S : Set (Fin G.n)), OnPath (s := s) x y) :
    KeyCone B S st := by
  intro y val hy hlt
  exact ⟨lt_of_le_of_lt (hss y val hy) hlt, hcone y (lt_of_le_of_lt (hss y val hy) hlt)⟩

/-! Summing up §4: of this file's three split residues (`LabelKey`, `KeyCone`, and the floor's
`NoLoose`), cone closure discharges `KeyCone` outright (`keyCone_of_storeSound_coneClosure`), and
nothing in the lane discharges `LabelKey` or `NoLoose`: both are statements about a label's
distance from its own canonical value (a *store/label drift* and a *loose head* respectively), and
`hcone`/`Prem`/`BpChain` are reachability, mint and bound statements. -/

/-! ## Axiom profile -/

#print axioms Frontier.DMSY.childFloor_iff
#print axioms Frontier.DMSY.floorL_init
#print axioms Frontier.DMSY.complete_settledSet
#print axioms Frontier.DMSY.floorL_istep
#print axioms Frontier.DMSY.floorL_of_below_above
#print axioms Frontier.DMSY.floorAll_child_at_parent
#print axioms Frontier.DMSY.mem_childS_of_key_below
#print axioms Frontier.DMSY.pl_init
#print axioms Frontier.DMSY.pl_step
#print axioms Frontier.DMSY.iloop_pl_seeds
#print axioms Frontier.DMSY.j6_group
#print axioms Frontier.DMSY.j6_of_pl_keyCone
#print axioms Frontier.DMSY.stepSplit_of_residuals
#print axioms Frontier.DMSY.mint_is_selected_pivot
#print axioms Frontier.DMSY.gatedMint_premature
#print axioms Frontier.DMSY.gatedMint_of_gatedSel_val
#print axioms Frontier.DMSY.not_gatedSel_of_no_mint
#print axioms Frontier.DMSY.cover_of_gatedMint_noPrem
#print axioms Frontier.DMSY.complete_iff_not_loose
#print axioms Frontier.DMSY.floorL_iff_noLoose
#print axioms Frontier.DMSY.floor_imp_relax
#print axioms Frontier.DMSY.keyCone_of_storeSound_coneClosure

end DMSY
end Frontier

import A4.LiveFloor
import A4.LowKeyClosure

/-!
# Frontier.DMSY.ValueBpChain — `BpChain` in label/value form, and where the value form ends

`A4.LiveFloor` settled the *distance* form of the running-bound chain negatively (``LiveFloor``
fails on pull remainders, explicit `IStep`).  This file states the chain in the form the engine
can actually feed — **labels and stored values** — and locates its exact remaining premise.

## 1. The chain kernel in label form (no distance floor anywhere)

The child consumes the parent's *labels* (`c = ⟨B_i, expand …, l-1, st.d⟩`), so the two floors
`istep_bp_mono` needs are label floors:

* `SeedLabFloor bp c := ∀ v ∈ c.S, bp ≤ c.d v`;
* `SeedChildLabFloor c co := ∃ v ∈ c.S, c.d v ≤ co.B'`  (the paper's (R5) read at labels).

`istep_bp_mono_lab`, `bpChain_of_chainLabFloor`, `iloop_chainLabFloor`,
`iloop_bpChain_of_labFloor` are the label-form mirror of `A4.BpMonotonicity`'s chain, with
**no** `LiveFloor`/`SeedFloor` occurrence.

## 2. What the engine supplies, and the one bridge it does not

`seedLabFloor_of_labFloor` (`LabFloor` = key-label floor + `LoopBInv`) is immediate.
`ge_of_loopBoundInv_mint` is `A4.LemmaV.ge_of_loopBoundInv`: it turns `LoopBoundInv` + a
**mint floor** (`MintFloor st`, i.e. `∀ m ∈ st.mints, st.bp ≤ m.val`) into the value floor at
keys — that is exactly where the `Prem`/Q12 carve-out is needed, and nowhere else.  `seedLabFloor_of_valueFloor` then needs **one** more fact, `KeyLabEq`: a key's
stored value *is* its label (`LoopBoundInv` floors values, `A4.Structural`'s honesty floors
labels from *below* only, so without this bridge value and label face away from each other).

Premise ledger (each item proved or named):

| premise | owner |
|---|---|
| `LoopBInv st.bp st` (group label floor) | preserved: `A4.LoopBInv.istep_bInv_of_le` (needs the child's `ChildLabelFloor`) |
| value floor at keys | preserved: `A4.Transitive.loopBoundInv_istep` (needs the child's Prem-free value law) |
| mint floor `∀ m ∈ st.mints, st.bp ≤ m.val` | `A4.LoopBInv.istep_mintFloor_of_pre` (`MintPreFloor`) |
| `SeedChildLabFloor` ((R5) at labels) | `seedChildLabFloor_base_of_full` at **full leaves**; the partial-leaf case is Lemma 3.1\*'s `dMin` argument |
| `KeyLabEq` at keys | **not derivable** — §3's `Step` counterexample refutes the value form on a *pulled* key |

## 3. The value form fails on a pull remainder (`valueForm_fails`)

`Gcx` again (`0 → 1`, self-loop at `1`).  The entry state keys `0 ↦ ↑[e0]` and `1 ↦ ↑[e0,e1]` at
`bp = ↑[e0]` but gives vertex `1` the **label** `↑[]`.  Then: the value floor at keys holds, the
group label floor holds (no groups), no key is a recorded mint, the child returns
`B' = ↑[] ≤ c.B = ⊤` with `D = ∅` (Prem-free), the pull at `⊤` takes both keys — and
`st'.bp = ↑[] < ↑[e0] = st.bp`.  The failing vertex is a **pulled key** whose value cleared `bp`
while its label did not: the value floor says nothing about the label the child actually reads,
so `BpChain` drops.  The corrected invariant is the **label floor at keys** (`LabFloor`), and the
only bridge from the engine's value data to it is `KeyLabEq` — the two-sided version of honesty
(`A4.Structural.iloop_honest` gives `d ≤ val` only).

## 4. Q12 integration with `A4.LowKeyClosure`

Now that `BpMonotonicity.SeedChildFloor` no longer collides with `BelowSeparator.ChildFloor`,
this file imports `LowKeyClosure` directly.  `keyFloorLow_of_exitJoint_mint`: `ExitJoint`'s
**mint** branch supplies `KeyFloorLow` at every unsettled cone member outside `W′` — because a
recorded mint's key cannot be stale-high (`mints_key_le`) and its value is below the floor.  The
`W′` branch is *not* converted (there `st.d x < B′` says nothing about the stored value); that
branch is the one `A4.LowKeyClosure.tail_cover_of_minimal` already routes through `U`.  So the
cover's residual is exactly "the `W′` branch or the value floor", and the value form of `BpChain`
is blocked at the same key-value/key-label seam.

No `sorry`/`admit`, no new axiom.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The chain in label form -/

/-- **Seed label floor**: the entry label the child reads at each of its seeds is at least the
running bound.  This is the label-side counterpart of `A4.BpMonotonicity.SeedFloor`. -/
def SeedLabFloor (bp : WLab G s) (c : CallEntry G s) : Prop := ∀ v ∈ c.S, bp ≤ c.d v

/-- **Seed child floor in label form**: the child's returned bound dominates one seed's entry
label (the paper's (R5) read where the child reads: `c.d`). -/
def SeedChildLabFloor (c : CallEntry G s) (co : CallOut G s) : Prop := ∃ v ∈ c.S, c.d v ≤ co.B'

/-- **One iteration is monotone in `B'`**, from the two label floors. -/
theorem istep_bp_mono_lab {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hseed : SeedLabFloor st.bp c) (hchild : SeedChildLabFloor c fo') : st.bp ≤ st'.bp := by
  rw [istep_bp h]
  obtain ⟨v, hv, hle⟩ := hchild
  exact (hseed v hv).trans hle

/-- The seed label floor along an iteration sequence. -/
def ChainLabFloor : WLab G s → List (CallEntry G s × CallOut G s) → Prop
  | _, [] => True
  | b, q :: qs => SeedLabFloor b q.1 ∧ ChainLabFloor q.2.B' qs

/-- **`BpChain` from the seed label floors plus the children's label floors.** -/
theorem bpChain_of_chainLabFloor : ∀ (b : WLab G s) {qs : List (CallEntry G s × CallOut G s)},
    ChainLabFloor b qs → (∀ q ∈ qs, SeedChildLabFloor q.1 q.2) → BpChain b qs := by
  intro b qs
  induction qs generalizing b with
  | nil => intro _ _; trivial
  | cons q qs ih =>
    intro hcl hch
    obtain ⟨hseed, hrest⟩ := hcl
    obtain ⟨v, hv, hle⟩ := hch q List.mem_cons_self
    exact ⟨(hseed v hv).trans hle,
      ih q.2.B' hrest (fun q' hq' => hch q' (List.mem_cons_of_mem _ hq'))⟩

/-- The step-uniform seed label floor. -/
def StepSeedLabFloor (t : ℕ) (B : WLab G s) (l : ℕ) : Prop :=
  ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
    IStep t B l st st' c fo' → SeedLabFloor st.bp c

/-- **The loop threads the seed label floor.** -/
theorem iloop_chainLabFloor (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf →
      (∀ (B0 : WLab G s) (l0 : ℕ), StepSeedLabFloor (G := G) (s := s) t B0 l0) →
      ChainLabFloor st.bp qs := by
  intro p st stf qs h
  induction h with
  | exit _ => intro _; exact trivial
  | step hne hg hstep hrest ih =>
    intro hfloor
    refine ⟨hfloor B l _ _ _ _ hstep, ?_⟩
    rw [← istep_bp hstep]
    exact ih (fun B0 l0 p0 st0 st0' c fo0 h0 => hfloor B0 l0 st0 st0' c fo0 h0)

/-- **`BpChain` at a loop, derived in label form.** -/
theorem iloop_bpChain_of_labFloor (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf →
      (∀ (B0 : WLab G s) (l0 : ℕ), StepSeedLabFloor (G := G) (s := s) t B0 l0) →
      (∀ q ∈ qs, SeedChildLabFloor q.1 q.2) → BpChain st.bp qs := by
  intro p st stf qs hloop hseed hchild
  exact bpChain_of_chainLabFloor st.bp (iloop_chainLabFloor t B l hloop hseed) hchild

/-! ## 2. The floors the engine owns, and the bridge it does not -/

/-- The label floor at the live set: keys' and residual group members' labels clear `bp`. -/
def LabFloor {p : ℕ} (st : RState G s p) : Prop :=
  (∀ y val, st.D y = some val → st.bp ≤ st.d y) ∧ LoopBInv st.bp st

/-- **Two-sided keyedness**: a key's stored value *is* its label.  Honesty
(`A4.Structural.istep_honest`) gives `d y ≤ val`; this is the missing `val ≤ d y`. -/
def KeyLabEq {p : ℕ} (st : RState G s p) : Prop :=
  ∀ y val, st.D y = some val → val = st.d y

/-- `LabFloor` discharges the seed label floor outright (keys and groups are the two sources). -/
theorem seedLabFloor_of_labFloor {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hlab : LabFloor st) : SeedLabFloor st.bp c := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  intro v hv
  subst hc
  rw [expand, Finset.mem_union] at hv
  rcases hv with hv | hv
  · obtain ⟨val, hval, -⟩ := (pullRun_pulled hpull).mp hv
    exact hlab.1 v val hval
  · obtain ⟨j, -, hmem⟩ := Finset.mem_biUnion.mp hv
    split_ifs at hmem with hcnd
    · exact hlab.2 j v (Finset.mem_filter.mp hmem).1
    · exact absurd hmem (Finset.notMem_empty v)

/-- The value floor at keys from `LoopBoundInv` + the mint floor: this is exactly
`A4.LemmaV.ge_of_loopBoundInv` (whose `MintFloor` is the hypothesis; the one escape branch of
`LoopBoundInv` is a recorded sub-`bp` mint, i.e. the Q12 carve-out). -/
theorem ge_of_loopBoundInv_mint {p : ℕ} {st : RState G s p} (hinv : LoopBoundInv st)
    (hmint : MintFloor st) : Ge st.bp st.D :=
  ge_of_loopBoundInv hinv hmint

/-- **The value form's bridge**: value floor at keys + `KeyLabEq` + group label floor give the
seed label floor.  This is the whole difference between the value form and the label form. -/
theorem seedLabFloor_of_valueFloor {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hval : Ge st.bp st.D) (heq : KeyLabEq st)
    (hlab : LoopBInv st.bp st) : SeedLabFloor st.bp c := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  intro v hv
  subst hc
  rw [expand, Finset.mem_union] at hv
  change st.bp ≤ st.d v
  rcases hv with hv | hv
  · obtain ⟨val, hvalv, -⟩ := (pullRun_pulled hpull).mp hv
    rw [← heq v val hvalv]
    exact hval v val hvalv
  · obtain ⟨j, -, hmem⟩ := Finset.mem_biUnion.mp hv
    split_ifs at hmem with hcnd
    · exact hlab j v (Finset.mem_filter.mp hmem).1
    · exact absurd hmem (Finset.notMem_empty v)

/-- **The child's label floor at a full base leaf**: the leaf's returned bound is the entry bound
(`MintPreFloor.full_leaf_gate`), and every seed sits below it (`CallPre.inRange`).  The
partial-leaf case is Lemma 3.1\*'s `dMin` argument (`B'⁺ = B'_pull ⊓ dMin`), which is the one
remaining half of this premise. -/
theorem seedChildLabFloor_base_of_full {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hfull : DS.IsEmpty bout.D_final) (hS : c.S.Nonempty) :
    SeedChildLabFloor c (baseOut bout) := by
  obtain ⟨v, hv⟩ := hS
  refine ⟨v, hv, ?_⟩
  show c.d v ≤ bout.B'_plus
  rw [full_leaf_gate hpre hb hfull]
  exact (hpre.inRange v hv).le

/-- **The group half of `LabFloor` is preserved by a step** (re-export of
`A4.LoopBInv.istep_bInv_of_le`): it needs the child's `ChildLabelFloor` and the bound law. -/
theorem labFloor_groups_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hble : fo'.B' ≤ c.B) (hfloor : ChildLabelFloor st fo') :
    LoopBInv B st' :=
  istep_bInv_of_le t B l h hble hfloor

/-- **The value floor is preserved by a step** (re-export of
`A4.Transitive.loopBoundInv_istep`): the child must return Prem-free values
(`∀ y val, fo'.D y = some val → fo'.B' ≤ val`), which is the one place `Prem = ∅` enters. -/
theorem loopBoundInv_istep_re (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hble : fo'.B' ≤ c.B) (hchild : ∀ y val, fo'.D y = some val → fo'.B' ≤ val)
    (hinv : LoopBoundInv st) : LoopBoundInv st' :=
  loopBoundInv_istep t B l h hble hchild hinv

/-! ## 3. The value form fails on a pull remainder

The counterexample lives in `A4.LiveFloor`'s `Counterexample` namespace (same graph `Gcx`,
same walks `lam0 < lam1 < lam2`). -/

namespace Counterexample

/-- The entry state: vertex `1` is keyed at value `lam2` with the *label* `lam0`, so the value
floor clears `bp = lam1` while the label the child reads does not. -/
noncomputable def stv : RState Gcx v0 0 where
  d := fun v => if v = v1 then lam0 else lam1
  D := DS.insert (DS.insert DS.empty v0 lam1) v1 lam2
  evts := []
  bp := lam1
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

theorem stv_D_v0 : stv.D v0 = some lam1 := by
  show DS.insert (DS.insert DS.empty v0 lam1) v1 lam2 v0 = some lam1
  rw [DS.insert_of_ne _ v1 lam2 (by decide : v0 ≠ v1)]
  exact insert_none_key DS.empty v0 lam1 rfl

theorem stv_D_v1 : stv.D v1 = some lam2 := by
  show DS.insert (DS.insert DS.empty v0 lam1) v1 lam2 v1 = some lam2
  exact insert_none_key _ v1 lam2
    (insert_none_other DS.empty v0 v1 lam1 (by decide) rfl)

/-- The value floor at the keys holds. -/
theorem stv_ge : Ge stv.bp stv.D := by
  intro y val hy
  rcases eq_v0_or_v1 y with rfl | rfl
  · rw [stv_D_v0] at hy
    show lam1 ≤ val
    rw [← Option.some.inj hy]
  · rw [stv_D_v1] at hy
    show lam1 ≤ val
    rw [← Option.some.inj hy]
    exact (coe_e0_lt_coe_e0_e1).le

/-- The group label floor holds (there are no groups). -/
theorem stv_loopBInv : LoopBInv stv.bp stv := fun j => j.elim0

/-- The label floor at the keys fails: the `lam2` key carries the label `lam0 < lam1`. -/
theorem stv_not_keyLabFloor : ¬ ∀ y val, stv.D y = some val → stv.bp ≤ stv.d y := by
  intro h
  have h1 : stv.bp ≤ stv.d v1 := h v1 lam2 stv_D_v1
  have h2 : stv.d v1 = lam0 := by
    show (if v1 = v1 then lam0 else lam1) = lam0
    rw [if_pos rfl]
  rw [h2] at h1
  exact absurd h1 (not_le.mpr coe_nil_lt_coe_e0)

theorem stv_not_keyLabEq : ¬ KeyLabEq stv := by
  intro h
  have h1 : lam2 = stv.d v1 := h v1 lam2 stv_D_v1
  have h2 : stv.d v1 = lam0 := by
    show (if v1 = v1 then lam0 else lam1) = lam0
    rw [if_pos rfl]
  rw [h2] at h1
  exact coe_nil_lt_coe_e0_e1.ne h1.symm

/-- The pull at separator `⊤` takes every key (both values are below `⊤`). -/
theorem belowKeys_stv : belowKeys (G := Gcx) (s := v0) stv.D ⊤ = Finset.univ := by
  ext y
  rw [mem_belowKeys]
  constructor
  · intro _; exact Finset.mem_univ y
  · intro _
    rcases eq_v0_or_v1 y with rfl | rfl
    · exact ⟨lam1, stv_D_v0, WithTop.coe_lt_top _⟩
    · exact ⟨lam2, stv_D_v1, WithTop.coe_lt_top _⟩

theorem pull_stv : pullRun (G := Gcx) (s := v0) (pullCap 2 1) stv.D ⊤ Finset.univ ⊤
    (DS.deleteSet stv.D Finset.univ) := by
  refine ⟨belowKeys_stv.symm, rfl, le_rfl, Or.inl rfl,
    Or.inr ⟨v0, lam1, stv_D_v0, WithTop.coe_lt_top _⟩, ?_⟩
  show (Finset.univ : Finset (Fin Gcx.n)).card ≤ pullCap 2 1
  rw [Finset.card_univ]
  decide

/-- The child's return: bound `lam0` — *below* the parent's running bound.  It is Prem-free and
obeys the bound law `lam0 ≤ ⊤ = c.B`, so nothing but the label floor rules it out. -/
noncomputable def fov : CallOut Gcx v0 where
  B' := lam0
  evts := []
  D := DS.empty
  d' := stv.d
  mints := []
  pfin := 0
  Pfin := fun j => j.elim0

/-- The entry the iteration produces. -/
noncomputable def cv : CallEntry Gcx v0 where
  B := ⊤
  S := Finset.univ
  l := 0
  d := stv.d

/-- The state after the iteration: the pull drained `𝒟` and the child added nothing. -/
noncomputable def stv' : RState Gcx v0 0 where
  d := stv.d
  D := DS.merge (DS.deleteSet stv.D Finset.univ) DS.empty
  evts := []
  bp := lam0
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

theorem expand_stv : expand (s := v0) stv.d stv.pl stv.piv Finset.univ ⊤ = Finset.univ := by
  rw [expand, biUnion_fin0, Finset.union_empty]

/-- **One genuine `IStep` whose `B'` drops**, with the value floor at the keys, the group label
floor, no recorded mint, a Prem-free child and the bound law all in hand. -/
theorem istep_stv : IStep (G := Gcx) (s := v0) 2 ⊤ 1 stv stv' cv fov := by
  refine ⟨Finset.univ, ⊤, DS.deleteSet stv.D Finset.univ, (fun j => j.elim0), ∅,
    (fun j => j.elim0), DS.merge (DS.deleteSet stv.D Finset.univ) DS.empty, fov.d',
    DS.merge (DS.deleteSet stv.D Finset.univ) DS.empty, pull_stv, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [CallEntry.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · show (Finset.univ : Finset (Fin Gcx.n)) = expand stv.d stv.pl stv.piv Finset.univ ⊤
      rw [expand_stv]
    · show (1 - 1 : ℕ) = 0
      rfl
  · intro j
    exact j.elim0
  · ext j
    exact ⟨fun h => absurd h (Finset.notMem_empty j), fun _ => j.elim0⟩
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [RState.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩
    · simp [stv']
    · simp [stv', stv, fov]
    · funext j
      exact j.elim0
    · simp [stv']

/-- The seed label floor fails at the pulled key `v1`: `stv.d v1 = lam0 < lam1 = stv.bp`. -/
theorem stv_not_seedLabFloor : ¬ SeedLabFloor stv.bp cv := by
  intro h
  have h1 : stv.bp ≤ cv.d v1 := h v1 (Finset.mem_univ v1)
  have h2 : cv.d v1 = lam0 := by
    show (if v1 = v1 then lam0 else lam1) = lam0
    rw [if_pos rfl]
  rw [h2] at h1
  exact absurd h1 (not_le.mpr coe_nil_lt_coe_e0)

theorem cv_S_eq : cv.S = Finset.univ := rfl

/-- **The value form does not close `BpChain`.**  Every engine-owned premise holds —
`Ge stv.bp stv.D` (value floor), `LoopBInv stv.bp stv` (group label floor), no recorded mint,
`fov.B' ≤ cv.B` (bound law), `fov` Prem-free — and the step still drops `B'` from `lam1` to
`lam0` on a **pulled key** whose value cleared `bp` while its label did not.  The corrected
invariant is the label floor at keys (`LabFloor`), i.e. the missing half of two-sided honesty. -/
theorem valueForm_fails :
    Ge stv.bp stv.D ∧ LoopBInv stv.bp stv ∧ stv.mints = [] ∧
      IStep (G := Gcx) (s := v0) 2 ⊤ 1 stv stv' cv fov ∧ fov.B' ≤ cv.B ∧
      (∀ x val, ¬ fov.Premature x val) ∧ ¬ SeedLabFloor stv.bp cv ∧
      ¬ (stv.bp ≤ stv'.bp) := by
  refine ⟨stv_ge, stv_loopBInv, rfl, istep_stv, le_top, ?_, stv_not_seedLabFloor, ?_⟩
  · intro x val h
    exact absurd h.1 (by simp [fov])
  · intro hle
    have h1 : lam0 < lam1 := coe_nil_lt_coe_e0
    exact absurd hle (not_le.mpr h1)

end Counterexample

/-! ## 4. Q12: the mint branch of `ExitJoint` *is* the value floor -/

/-- **`ExitJoint`'s mint branch supplies `KeyFloorLow`** at every unsettled cone member outside
`W′`, for a loop state that is a step output (so `mints_key_le` applies): the recorded mint's key
survives at a value `≤ m.val < B′`.  The `W′` branch is not convertible this way — there the
label, not the value, is below the floor — and that is the branch `U` already covers. -/
theorem keyFloorLow_of_exitJoint_mint {t : ℕ} {Bv : WLab G s} {l : ℕ} {p : ℕ}
    {st0 st : RState G s p} {c : CallEntry G s} {fo0 : CallOut G s}
    {Sv Wv : Finset (Fin G.n)} (hstep : IStep t Bv l st0 st c fo0)
    (hj : ExitJoint Bv Sv Wv st)
    (hnotW : ∀ x, x ∈ Utilde (tailBP Bv st) (Sv : Set (Fin G.n)) → x ∉ settledSet st.evts →
      x ∉ tailWp Bv Sv Wv st) :
    KeyFloorLow (tailBP Bv st) Sv st := by
  intro x hxU hxs val hval
  rcases hj x hxU hxs with hW | ⟨mval, hm, hlt⟩
  · exact absurd hW (hnotW x hxU hxs)
  · obtain ⟨v, hv, hle⟩ := mints_key_le hstep hm
    rw [hval] at hv
    have hle' : val ≤ mval := by
      rw [← Option.some.inj hv] at hle
      exact hle
    exact hle'.trans_lt hlt

/-- **And back**: the value floor at a key below the floor *is* the mint branch (given a key),
by `A4.LiveFloor.mint_iff_keyBelow`.  So on the non-`W′` branch the two are the same statement,
and `a4_joint`'s residual is "the `W′` branch or the value floor" — not a mint-analysis leaf. -/
theorem exitJoint_mint_of_keyFloorLow {t : ℕ} {Bv : WLab G s} {l : ℕ} {p : ℕ}
    {st0 st : RState G s p} {c : CallEntry G s} {fo0 : CallOut G s} {x : Fin G.n}
    (hstep : IStep t Bv l st0 st c fo0) (hinv : LoopBoundInv st) {val : WLab G s}
    (hval : st.D x = some val) (hlt : val < st.bp) :
    ∃ m ∈ st.mints, m.x = x ∧ m.val < st.bp :=
  (mint_iff_keyBelow hstep hinv x).mpr ⟨val, hval, hlt⟩

/-! ## Signatures and axiom audit -/

#check @istep_bp_mono_lab
#check @bpChain_of_chainLabFloor
#check @iloop_bpChain_of_labFloor
#check @seedLabFloor_of_labFloor
#check @ge_of_loopBoundInv_mint
#check @seedLabFloor_of_valueFloor
#check @seedChildLabFloor_base_of_full
#check @Counterexample.valueForm_fails
#check @keyFloorLow_of_exitJoint_mint
#check @exitJoint_mint_of_keyFloorLow

#print axioms istep_bp_mono_lab
#print axioms seedLabFloor_of_valueFloor
#print axioms Counterexample.valueForm_fails
#print axioms keyFloorLow_of_exitJoint_mint

end DMSY
end Frontier

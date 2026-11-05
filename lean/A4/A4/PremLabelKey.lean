import A4.StepSplitFloor
import A4.NonDrainedBp
import A4.Structural
import A4.NoLoose
import A4.ConeClosure

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.PremLabelKey — `Prem = ∅` off the drained branch, and the key-custody residue

`A4.StepSplitFloor` left two obligations: `Prem = ∅` (§3 there: `GatedMint` has the *opposite*
polarity, so the empty-carve cover needs both) and `LabelKey` (§2a there: `hcover`'s
label→store bridge).  `A4.NoLoose` then reduced the refusal floor to `CandSettled` and named
`Prem = ∅` as the second of its two residues; `A4.ConeClosure` reduced `KeyCone` to
`NoCompleteKey`.  This file closes the parts the engine can pay for and states what is left.

## 1. `Prem = ∅`

`A4.Structural.full_no_prem` already gives `Prem = ∅` on **full** executions (drained `𝒟`, so no
mints — the tail's `B' = B` branch of `FIX-EMPTY`).  This file supplies the **capped** branch:

* `prem_empty_drained` — no premise at all beyond the empty store: a mint is always its own key
  (`iloop_mints_keys`), so a drained `𝒟` means an empty mint list.
* `mint_floor_of_loopBInv` — every final mint is a selected pivot of a residual group
  (`iloop_mints_pl`), its value is the state's own label there (`iloop_mints_label`), and
  `LoopBInv` floors that label by the running bound.  So `val < B'` is impossible.
* `prem_empty_tail` — the dichotomy: full branch as above, capped branch via
  `nondrained_tailBP` + the mint floor.  `prem_empty_recur` instantiates it at `mkInit` (whose
  mint list is empty), so the only premise is `LoopBInv` = `A4.LoopBInv.ChildLabelFloor`'s per-step
  clause, which the joint induction already carries.
* `prem_tail_iff_noPremGated` records that this *is* Q12 at a state: `Prem = ∅` ⟺ the mints clear
  `tailBP`.  `cover_empty_carve_of_gatedMint` then hands
  `A4.StepSplitFloor.cover_of_gatedMint_noPrem` a `NoPremGated`, i.e. the identity cover with an
  empty carve-out, end to end.

## 2. `LabelKey` is not an invariant — it is a pre-pull precondition

`LabelKey = presence + agreement` (`labelKey_iff_present_agree`) and `= live ∧ settled`
(`labelKey_iff_split`).  Both halves fail for *different* engine channels, and neither is a
per-step premise:

* the **pull** removes the keys it extracts (`pullRun`'s `D' = deleteSet D S'`), so after a genuine
  `IStep` a vertex sits below the separator with no value at all —
  `labelKey_refuted_at_engine_state` (§2b).  `LabelKey` holds at the *pre-pull* state, which is
  exactly how `A4.StepSplitFloor.hcover_of_labelKey` can consume it;
* **custody** (§4) forbids a key from carrying a complete label (`NoCompleteKey`), while a settled
  vertex *is* complete (`ChildFloor`'s clause 1).  So `LabelKey` + custody forces every settled
  label to sit **at or above** the threshold (`settled_ge_of_labelKey_custody`) — the invariant
  ★BM.15 deliberately breaks.  That is the honest "equivalent premise" reading: `LabelKey` asserts
  settled-below-threshold is empty, and the engine's settled vertices are exactly the ones the
  pull took out.

What the store laws *do* give (the direction `hcover` can use) is §2c: `belowKeys_label_lt` (pulled
keys have low labels — honesty), `labelAgree_deleteSet_iff` (★BM.15 is inert on agreement: it only
drops keys), `labelAgree_merge`/`merge_value_lt` (the keep-min can only lower a value, so a child
that *re-keys* a vertex repairs the parent's stale-high entry).  Hence the residual is exactly the
keys the child did **not** re-key: `StoreTight` (§2d), stated on the live carrier and at the
child's own bound (`ChildStoreTight`), so it is *self-similar* and can be carried by the induction
on `l` — unlike `LabelKey`.

## 3. `NoLoose` from §1

`A4.NoLoose.noLoose_of_candSettled` turns `CandSettled` into the floor.  The pull/child route gives
`CandSettled` *except* for one arm: a below-threshold head that is a pulled seed may be the child's
**carve-out** (`Prem`) instead of settled.  `candSettled_of_premFree` kills that arm — §1 is used
exactly once, there — and `noLoose_of_recur` composes it with `floor_of_run_candSettled` at a
`recur` return.  Full vs capped stays explicit: the full branch needs no `LoopBInv`
(`prem_empty_drained`); the capped branch needs §1's mint floor; the leaf's cap form stays
`A4.NoLoose.base_noLoose_cap` and is not re-derived here.

## 4. The remaining gap

`Prem = ∅` is the last leaf for `theoremT`'s value bound and for `NoLoose`, **given**
`LoopBInv`/`ChildLabelFloor` (the per-step label clause the joint induction carries) and, for
`NoLoose`, the seed dichotomy + settled completeness.  `LabelKey` is **not** a leaf — it is false
at engine states; its correct replacement is `StoreTight` + `NoCompleteKey`, which are the same
custody obligation (`KeyCone`'s `keyCone_of_claimC` consumes the latter, this file's §2c the
former), and that obligation is the one genuine residue left in the lane.

No `sorry`/`admit`, no new axiom, `a4_joint` not assumed.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. `Prem = ∅`: the full branch, the capped branch, and the dichotomy -/

/-- **Q12 at the tail output is exactly the mint floor at the tail bound.**  Definitional, and the
point of the section: nothing but the mints' values against `tailBP` stands between the engine and
`Prem = ∅`. -/
theorem prem_tail_iff_noPremGated (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) :
    (∀ x val, ¬ (callOut (tail B S W st)).Premature x val) ↔ NoPremGated B st :=
  ⟨fun h x val hm hlt => h x val ⟨hm, hlt⟩, fun h x val hp => h x val hp.1 hp.2⟩

/-- A mint floor at the tail bound implies `NoPremGated`. -/
theorem noPremGated_of_mintFloor {B : WLab G s} {p : ℕ} {st : RState G s p}
    (h : ∀ m ∈ st.mints, tailBP B st ≤ m.val) : NoPremGated B st :=
  fun x val hm hlt => absurd (h (Mint.mk x val) hm) (not_le.mpr hlt)

/-- **The full (`FIX-EMPTY` drained) branch needs nothing.**  A mint is always its own key
(`iloop_mints_keys`: the BM.23 insert is guarded only by the keep-min), so a drained store means an
empty mint list.  Compare `A4.Structural.full_no_prem`, which is the same fact read through
`premInD_of_run`. -/
theorem prem_empty_drained {t : ℕ} {B : WLab G s} {l : ℕ} {S W : Finset (Fin G.n)} {p : ℕ}
    {st0 stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t B l st0 qs stf)
    (hkey0 : ∀ m ∈ st0.mints, st0.D m.x ≠ none) (hemp : DS.IsEmpty stf.D) :
    ∀ x val, ¬ (callOut (tail B S W stf)).Premature x val := by
  intro x val hp
  exact absurd (hemp x) (iloop_mints_keys t B l hloop hkey0 (Mint.mk x val) hp.1)

/-- **The mint floor at the loop's own bound.**  `iloop_mints_pl` puts the mint key in a residual
group, `iloop_mints_label` identifies its value with the state's label there, and `LoopBInv` floors
that label by the running bound.  This is `theoremT`'s value bound restricted to the mints
themselves. -/
theorem mint_floor_of_loopBInv {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st0 stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t B l st0 qs stf)
    (hpl0 : ∀ m ∈ st0.mints, ∃ j, m.x ∈ st0.pl j)
    (hlab0 : ∀ m ∈ st0.mints, st0.d m.x = m.val)
    (hinv : LoopBInv stf.bp stf) :
    ∀ m ∈ stf.mints, stf.bp ≤ m.val := by
  intro m hm
  obtain ⟨j, hpl⟩ := iloop_mints_pl t B l hloop hpl0 m hm
  have hlab := iloop_mints_label t B l hloop hlab0 m hm
  have hfloor : stf.bp ≤ stf.d m.x := hinv j m.x hpl
  rwa [hlab] at hfloor

/-- **`Prem = ∅` at the tail return, with full vs capped explicit.**  Full: `prem_empty_drained`
(no `LoopBInv`).  Capped: `tailBP = stf.bp` (`nondrained_tailBP`) and the mint floor contradicts
`val < B'`. -/
theorem prem_empty_tail {t : ℕ} {B : WLab G s} {l : ℕ} {S W : Finset (Fin G.n)} {p : ℕ}
    {st0 stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t B l st0 qs stf)
    (hpl0 : ∀ m ∈ st0.mints, ∃ j, m.x ∈ st0.pl j)
    (hlab0 : ∀ m ∈ st0.mints, st0.d m.x = m.val)
    (hkey0 : ∀ m ∈ st0.mints, st0.D m.x ≠ none)
    (hinv : LoopBInv stf.bp stf) :
    ∀ x val, ¬ (callOut (tail B S W stf)).Premature x val := by
  intro x val hp
  by_cases hemp : DS.IsEmpty stf.D
  · exact prem_empty_drained hloop hkey0 hemp x val hp
  · have hB' : (callOut (tail B S W stf)).B' = stf.bp := by
      show tailBP B stf = stf.bp
      exact nondrained_tailBP B stf hemp
    have hlt' : val < stf.bp := hB' ▸ hp.2
    exact absurd (mint_floor_of_loopBInv hloop hpl0 hlab0 hinv (Mint.mk x val) hp.1)
      (not_le.mpr hlt')

/-- **`Prem = ∅` at a `recur` return**, from `LoopBInv` alone: the loop starts at `mkInit`, whose
mint list is empty, so the three carrier hypotheses are vacuous. -/
theorem prem_empty_recur {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t e.B e.l (mkInit e fo piv) qs stf)
    (hinv : LoopBInv stf.bp stf) :
    ∀ x val, ¬ (callOut (tail e.B e.S fo.W stf)).Premature x val :=
  prem_empty_tail (B := e.B) (S := e.S) (W := fo.W) (st0 := mkInit e fo piv) hloop
    (fun m hm => by rw [mkInit_mints] at hm; exact absurd hm List.not_mem_nil)
    (fun m hm => by rw [mkInit_mints] at hm; exact absurd hm List.not_mem_nil)
    (fun m hm => by rw [mkInit_mints] at hm; exact absurd hm List.not_mem_nil)
    hinv

/-- The same in the `NoPremGated` form the identity-cover assembly consumes. -/
theorem noPremGated_of_recur {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t e.B e.l (mkInit e fo piv) qs stf)
    (hinv : LoopBInv stf.bp stf) :
    NoPremGated e.B stf :=
  (prem_tail_iff_noPremGated e.B e.S fo.W stf).mp (prem_empty_recur hloop hinv)

/-- **The identity cover with an empty carve-out, end to end.**  `GatedMint` (identity's residue)
and §1's `Prem = ∅` are opposite-polarity constraints on the same mint list; together they leave
`A4.StepSplitFloor.cover_of_gatedMint_noPrem` with no `Prem` at all — clause (2c),
`U = Ũ(B',S)`. -/
theorem cover_empty_carve_of_gatedMint {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hloop : ILoop t e.B e.l (mkInit e fo piv) qs stf)
    (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (hg : GatedMint e.B e.S fo.W stf)
    (hinv : LoopBInv stf.bp stf) :
    Utilde (tailBP e.B stf) (e.S : Set (Fin G.n)) ⊆
      (callOut (tail e.B e.S fo.W stf)).U :=
  cover_of_gatedMint_noPrem t hfp rfl hloop hchildren hg (noPremGated_of_recur hloop hinv)

/-! ## 2. `LabelKey`: not an invariant, and what it stands for

`A4.StepSplitFloor.LabelKey B st := ∀ y, st.d y < B → ∃ v, st.D y = some v ∧ v < B`. -/

/-! ### 2a. The exact decompositions -/

/-- **`LabelKey` = presence + agreement.**  A low label must (i) have a key at all and (ii) every
value stored there must be low.  The two halves are refuted by *different* channels (the pull
removes keys; a non-re-keying child leaves a stale-high value), so this is the honest split. -/
theorem labelKey_iff_present_agree {B : WLab G s} {p : ℕ} {st : RState G s p} :
    LabelKey B st ↔
      (∀ y, st.d y < B → st.D y ≠ none) ∧
        (∀ y, st.d y < B → ∀ v, st.D y = some v → v < B) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro y hlt
      obtain ⟨v, hv, _⟩ := h y hlt
      rw [hv]
      exact Option.some_ne_none v
    · intro y hlt v hv
      obtain ⟨v', hv', hlt'⟩ := h y hlt
      have hvv : v = v' := by
        rw [hv] at hv'
        exact Option.some.inj hv'
      rw [hvv]
      exact hlt'
  · rintro ⟨hpres, hagree⟩ y hlt
    cases hD : st.D y with
    | none => exact absurd hD (hpres y hlt)
    | some v => exact ⟨v, rfl, hagree y hlt v hD⟩

/-- **`LabelKey` = live ∧ settled.**  The split by the settlement log: the `live` half is what a
pre-pull state can satisfy, and the `settled` half is what ★BM.15 and custody falsify. -/
theorem labelKey_iff_split {B : WLab G s} {p : ℕ} {st : RState G s p} :
    LabelKey B st ↔
      (∀ y, y ∉ settledSet st.evts → st.d y < B → ∃ v, st.D y = some v ∧ v < B) ∧
        (∀ y ∈ settledSet st.evts, st.d y < B → ∃ v, st.D y = some v ∧ v < B) := by
  constructor
  · intro h
    exact ⟨fun y _ hlt => h y hlt, fun y _ hlt => h y hlt⟩
  · rintro ⟨hlive, hsett⟩ y hlt
    by_cases hy : y ∈ settledSet st.evts
    · exact hsett y hy hlt
    · exact hlive y hy hlt

/-! ### 2b. `LabelKey` is refuted at a genuine engine state: the pull remainder

`A4.NonDrainedBp.Counterexample`: `stN` keys `v0` at `lam0`, the pull at separator `lam1` extracts
`v0` and deletes its key (`pullRun`'s `D' = deleteSet D S'`, never re-inserted), the child re-keys
nothing, and `istep_stN` is a real `IStep`.  So `stN'.d v0 = lam0 < lam1` with `stN'.D v0 = none`. -/

/-- The counterexample state's store has no value at the pulled vertex. -/
theorem stN'_D_v0 : Counterexample.stN'.D Counterexample.v0 = none := by
  show DS.merge (DS.deleteSet Counterexample.stN.D {Counterexample.v0}) DS.empty
    Counterexample.v0 = none
  rw [DS.merge_eq, DS.deleteSet_eq, if_pos (Finset.mem_singleton_self _)]
  rfl

/-- **The live agreement fails after a genuine pull-containing `IStep`.** -/
theorem counterexample_not_labelKeyLive :
    ¬ (∀ y, y ∉ settledSet Counterexample.stN'.evts →
        Counterexample.stN'.d y < Counterexample.lam1 →
          ∃ v, Counterexample.stN'.D y = some v ∧ v < Counterexample.lam1) := by
  intro h
  have huns : Counterexample.v0 ∉ settledSet Counterexample.stN'.evts := by
    rw [show Counterexample.stN'.evts =
      ([] : List (SettlementEvent Counterexample.Gcx)) from rfl]
    simp [settledSet]
  have hlt : Counterexample.stN'.d Counterexample.v0 < Counterexample.lam1 :=
    Counterexample.coe_nil_lt_coe_e0
  obtain ⟨v, hv, _⟩ := h Counterexample.v0 huns hlt
  rw [stN'_D_v0] at hv
  cases hv

/-- **`LabelKey` is not an invariant of the engine.**  A genuine `IStep`
(`Counterexample.istep_stN`) produces a state on which it fails.  `LabelKey` is a *pre-pull*
precondition — which is exactly how `A4.StepSplitFloor.hcover_of_labelKey` consumes it at `st`. -/
theorem labelKey_refuted_at_engine_state :
    IStep (G := Counterexample.Gcx) (s := Counterexample.v0) 2 Counterexample.lam1 1
        Counterexample.stN Counterexample.stN' Counterexample.cN Counterexample.foN ∧
      ¬ LabelKey (G := Counterexample.Gcx) (s := Counterexample.v0)
        Counterexample.lam1 Counterexample.stN' := by
  refine ⟨Counterexample.istep_stN, ?_⟩
  intro h
  exact counterexample_not_labelKeyLive ((labelKey_iff_split (B := Counterexample.lam1)).mp h).1

/-! ### 2c. What the store laws *do* give (the direction `hcover` can consume) -/

/-- **Every pulled key's label is below the separator** — `belowKeys ⊆ {y | st.d y < B}`.  Entry
honesty (`d ≤ val`) supplies it; the converse is `LabelKey`, and that is the whole gap. -/
theorem belowKeys_label_lt {D : DS G s} {d : Labels G s} {B : WLab G s}
    (hoh : ∀ y val, D y = some val → d y ≤ val) {y : Fin G.n} (hy : y ∈ belowKeys D B) :
    d y < B := by
  obtain ⟨v, hv, hlt⟩ := mem_belowKeys.mp hy
  exact lt_of_le_of_lt (hoh y v hv) hlt

/-- **★BM.15 is inert on label/store agreement.**  The deletion rewrites no stored value and
removes keys, so agreement after it is agreement *at the surviving keys*: the deletion can neither
create nor repair it.  The value-side counterpart of `A4.FixStale.ge_deleteSet_iff`, and the sense
in which the key-custody residue is *distinct from BM.15*. -/
theorem labelAgree_deleteSet_iff {D : DS G s} (T : Finset (Fin G.n)) (d : Labels G s)
    (B : WLab G s) :
    (∀ y, d y < B → ∀ v, DS.deleteSet D T y = some v → v < B) ↔
      (∀ y, y ∉ T → d y < B → ∀ v, D y = some v → v < B) := by
  constructor
  · intro h y hyT hlt v hv
    exact h y hlt v (by rwa [DS.deleteSet_of_notMem D T y hyT])
  · intro h y hlt v hv
    by_cases hyT : y ∈ T
    · rw [DS.deleteSet_eq, if_pos hyT] at hv
      cases hv
    · rw [DS.deleteSet_eq, if_neg hyT] at hv
      exact h y hyT hlt v hv

/-- **The BM.14 keep-min preserves agreement** when both sources have it. -/
theorem labelAgree_merge {D₁ D₂ : DS G s} {d : Labels G s} {B : WLab G s}
    (h₁ : ∀ y, d y < B → ∀ v, D₁ y = some v → v < B)
    (h₂ : ∀ y, d y < B → ∀ v, D₂ y = some v → v < B) :
    ∀ y, d y < B → ∀ v, DS.merge D₁ D₂ y = some v → v < B := by
  intro y hlt v hv
  rw [DS.merge_eq] at hv
  cases hD₁ : D₁ y with
  | none =>
    rw [hD₁, DS.mergeVal_none_left] at hv
    exact h₂ y hlt v hv
  | some μ =>
    cases hD₂ : D₂ y with
    | none =>
      rw [hD₁, hD₂, DS.mergeVal_none_right] at hv
      have hveq : v = μ := (Option.some.inj hv).symm
      rw [hveq]
      exact h₁ y hlt μ hD₁
    | some ν =>
      rw [hD₁, hD₂, DS.mergeVal_some] at hv
      have hveq : v = min μ ν := (Option.some.inj hv).symm
      rw [hveq]
      exact lt_of_le_of_lt (min_le_left μ ν) (h₁ y hlt μ hD₁)

/-- **The child's below-bound value survives the merge**: a key the child stores below `B` has a
merged value below `B`, whatever the parent held.  This is the exact mechanism by which a `Run`
child that *re-keys* a vertex repairs the parent's stale-high entry — hence the residue is only
about keys the child did **not** re-key. -/
theorem merge_value_lt {D₁ Dp : DS G s} {y : Fin G.n} {B v : WLab G s}
    (hy : Dp y = some v) (hlt : v < B) : ∃ w, DS.merge D₁ Dp y = some w ∧ w < B := by
  rw [DS.merge_eq, hy]
  cases hD₁ : D₁ y with
  | none =>
    rw [DS.mergeVal_none_left]
    exact ⟨v, rfl, hlt⟩
  | some μ =>
    rw [DS.mergeVal_some]
    exact ⟨min μ v, rfl, lt_of_le_of_lt (min_le_right μ v) hlt⟩

/-! ### 2d. The exact remaining premise -/

/-- **`StoreTight`** — the exact premise `LabelKey` stands for, on the carrier the engine can carry
it on: off the settled set, a label below the bound has a store value below the bound.  Two
differences from `LabelKey`, both load-bearing: settled keys are excluded (★BM.15 deletes them, so
no induction can carry that half — §2b is exactly that failure), and it recurs at the child at the
child's own bound, so the induction on `l` can carry it. -/
def StoreTight (B : WLab G s) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ y, y ∉ settledSet st.evts → st.d y < B → ∃ v, st.D y = some v ∧ v < B

/-- **The child-side instance** `StoreTight`'s induction needs: the child's own agreement at its own
returned bound, off its own settlement set.  The only cross-call clause the step requires (the
merge's below-bound values come from it via `merge_value_lt`), and strictly weaker than
`A4.LoopBInv.MintPreFloor`/`ChildLabelFloor`: those constrain the *labels* of selected keys, this
the *store values* of every unsettled low key — no group, no selection, no `Prem`. -/
def ChildStoreTight {p : ℕ} (st : RState G s p) (fo' : CallOut G s) : Prop :=
  ∀ y, y ∉ settledSet fo'.evts → fo'.d' y < fo'.B' → ∃ v, fo'.D y = some v ∧ v < fo'.B'

/-- **The sharpened premise the engine's own `expand` supports.**  BM.12 hands the next child only a
group's *pivot*, so `hcover` needs agreement at pivots — never at an arbitrary low vertex. -/
def PivotKey (B : WLab G s) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ j, st.piv j ∈ st.pl j → st.d (st.piv j) < B →
    ∃ v, st.D (st.piv j) = some v ∧ v < B

/-- `LabelKey` supplies `PivotKey` (its carrier is global, so no group fact is needed). -/
theorem pivotKey_of_labelKey {B : WLab G s} {p : ℕ} {st : RState G s p}
    (h : LabelKey B st) : PivotKey B st :=
  fun _j _hpiv hlt => h _ hlt

/-- **A low group member puts the pivot low** (the pivot is its group's `argmin`, `IStep`'s `hsel`
and `Run.recur`'s `hpiv`), so `PivotKey` at pivots covers the low-member case `hcover` actually
meets. -/
theorem pivotKey_of_group_low {B : WLab G s} {p : ℕ} {st : RState G s p}
    (h : PivotKey B st) (hmin : ∀ j, ∀ y ∈ st.pl j, st.d (st.piv j) ≤ st.d y) :
    ∀ j, (∃ y ∈ st.pl j, st.d y < B) → st.piv j ∈ st.pl j →
      ∃ v, st.D (st.piv j) = some v ∧ v < B := by
  intro j hlow hpiv
  exact h j hpiv (lt_of_le_of_lt (hmin j _ hlow.choose_spec.1) hlow.choose_spec.2)

/-! ## 3. `NoLoose` from §1 (with full vs cap explicit)

`A4.NoLoose.noLoose_of_candSettled` turns `CandSettled` into the floor.
`candSettled_of_premFree` is the missing bridge: the pull/child route settles a below-threshold
head **or** it lands in the child's carve-out, and §1 kills the second arm. -/

/-- **The seed dichotomy + `Prem = ∅` ⇒ `CandSettled`.**  `hdich` is the dichotomy the pull/child
route delivers (`A4.ReturnClauses`' settled-or-carved split); `hprem` is §1.  This is the *only*
place `Prem = ∅` enters the floor. -/
theorem candSettled_of_premFree {R : WLab G s} {out : CallOut G s}
    (hdich : ∀ e₀, G.src e₀ ∈ settledSet out.evts → ext (out.d' (G.src e₀)) e₀ < R →
      G.dst e₀ ∈ settledSet out.evts ∨ ∃ x val, out.Premature x val)
    (hprem : ∀ x val, ¬ out.Premature x val) :
    CandSettled R out.d' out.evts :=
  fun e₀ hu hlt => by
    rcases hdich e₀ hu hlt with hs | ⟨x, val, hpx⟩
    · exact hs
    · exact absurd hpx (hprem x val)

/-- **`NoLoose` at a call**, from settled completeness, soundness, the dichotomy and §1. -/
theorem noLoose_of_premFree {R : WLab G s} {out : CallOut G s}
    (hset : ∀ v ∈ settledSet out.evts, Complete out.d' v) (hsound : Sound out.d')
    (hdich : ∀ e₀, G.src e₀ ∈ settledSet out.evts → ext (out.d' (G.src e₀)) e₀ < R →
      G.dst e₀ ∈ settledSet out.evts ∨ ∃ x val, out.Premature x val)
    (hprem : ∀ x val, ¬ out.Premature x val) :
    NoLoose R out.d' out.evts :=
  noLoose_of_candSettled hset (candSettled_of_premFree hdich hprem)

/-- **The dichotomy's concrete instance: `Prem = ∅` settles a pulled seed.**  This is
`A4.ConeClosure.istep_key_settled_of_belowBody` — a parent key whose *stored body* is below the
separator and whose canonical label is below the child's bound is settled by the child **or** is
the child's carve-out — with §1 killing the second arm.  So the "settled-or-carved" split that
`A4.NoLoose` names as its second residue collapses to "settled" as soon as the child is
Prem-free, and `candSettled_of_premFree` is its headline. -/
theorem seed_settled_of_premFree {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (hstep : IStep t B l st st' c fo') (hconcl : Lemma37Concl (Full t) c fo')
    (hsound : Sound st.d) {y : Fin G.n}
    (hyD : ∃ v, st.D y = some v ∧ v < c.B) (hyB : st.d y < c.B)
    (hlt : dis (s := s) y < fo'.B')
    (hprem : ∀ x val, ¬ fo'.Premature x val) :
    y ∈ settledSet fo'.evts := by
  rcases istep_key_settled_of_belowBody hstep hconcl hsound hyD hyB hlt with hs | ⟨val, hp⟩
  · exact hs
  · exact absurd hp (hprem y val)

/-- **The floor at a `recur` return**, from §1's `Prem = ∅` and the seed dichotomy.  This is the
`Floor e out` shape `A4.BelowSeparator`/`A4.DrainedClauses` consume: the residue named is the
dichotomy, not a new floor invariant. -/
theorem floor_of_recur_premFree {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t e.B e.l (mkInit e fo piv) qs stf)
    (hinv : LoopBInv stf.bp stf)
    (hset : ∀ ev ∈ (callOut (tail e.B e.S fo.W stf)).evts,
      Complete (callOut (tail e.B e.S fo.W stf)).d' ev.v)
    (hsound : Sound (callOut (tail e.B e.S fo.W stf)).d')
    (hdich : ∀ e₀,
      G.src e₀ ∈ settledSet (callOut (tail e.B e.S fo.W stf)).evts →
        ext ((callOut (tail e.B e.S fo.W stf)).d' (G.src e₀)) e₀ < e.B →
          G.dst e₀ ∈ settledSet (callOut (tail e.B e.S fo.W stf)).evts ∨
            ∃ x val, (callOut (tail e.B e.S fo.W stf)).Premature x val) :
    Floor e (callOut (tail e.B e.S fo.W stf)) :=
  floor_of_run_candSettled (t := t) hset hsound
    (candSettled_of_premFree hdich (prem_empty_recur hloop hinv))

/-! ## 4. Key custody: `NoCompleteKey` and its two faces -/

/-- **Custody survives ★BM.15** (the deletion only drops keys) — the mirror of `FixStale.ge_deleteSet`
for the custody clause `A4.ConeClosure`'s `keyCone_of_claimC` consumes. -/
theorem noCompleteKey_deleteSet {d : Labels G s} {D : DS G s} (h : NoCompleteKey d D)
    (T : Finset (Fin G.n)) : NoCompleteKey d (DS.deleteSet D T) := by
  intro y val hy
  by_cases hyT : y ∈ T
  · rw [DS.deleteSet_mem D T y hyT] at hy
    cases hy
  · rw [DS.deleteSet_of_notMem D T y hyT] at hy
    exact h y val hy

/-- **Custody in store-value form.**  Under a keyed store (`value = label`) custody is exactly "no
stored value is its key's canonical label" — the store holds only *strictly heavier*, tentative
walks.  With label soundness (`dis ≤ d`) this is what makes `Complete` decidable at a key at all,
and it is the form in which `StoreTight`'s value half and `NoCompleteKey` meet: both say the store
never presents a canonical walk as its own value. -/
theorem noCompleteKey_iff_val_not_canonical {d : Labels G s} {D : DS G s}
    (hk : ∀ y val, D y = some val → d y = val) :
    NoCompleteKey d D ↔ ∀ y val, D y = some val → val ≠ dis (s := s) y := by
  constructor
  · intro h y val hv hEq
    have hcomp : Complete d y := by
      show d y = dis (s := s) y
      rw [hk y val hv]
      exact hEq
    exact h y val hv hcomp
  · intro h y val hv hcomp
    have hEq : val = dis (s := s) y := by
      rw [← hk y val hv]
      exact hcomp
    exact h y val hv hEq

/-- **Custody refutes `LabelKey`'s settled half.**  A key never carries a complete label
(`NoCompleteKey`), and a settled vertex is complete (`ChildFloor`'s clause 1) — so a settled vertex
below the threshold cannot be a key, which is exactly what `LabelKey`'s settled half asks for. -/
theorem not_labelKeySettled_of_custody {B : WLab G s} {p : ℕ} {st : RState G s p}
    (hkey : NoCompleteKey st.d st.D)
    (hset : ∀ y ∈ settledSet st.evts, Complete st.d y) {y : Fin G.n}
    (hy : y ∈ settledSet st.evts) (hlt : st.d y < B) :
    ¬ (∀ y ∈ settledSet st.evts, st.d y < B → ∃ v, st.D y = some v ∧ v < B) := by
  intro h
  obtain ⟨v, hv, _⟩ := h y hy hlt
  exact hkey y v hv (hset y hy)

/-- **`LabelKey` + custody ⇒ every settled vertex sits at or above the threshold.**  This is the
precise content of `LabelKey` on the settled carrier: it asserts that nothing the pull removed from
`𝒟` still has a label below the bound — true at a *pre-pull* state, false after the pull
(`labelKey_refuted_at_engine_state`).  So `LabelKey` is not a leaf of the induction; the leaf is the
live agreement (`StoreTight`) plus custody (`NoCompleteKey`). -/
theorem settled_ge_of_labelKey_custody {B : WLab G s} {p : ℕ} {st : RState G s p}
    (hkey : NoCompleteKey st.d st.D)
    (hset : ∀ y ∈ settledSet st.evts, Complete st.d y) (hL : LabelKey B st) :
    ∀ y ∈ settledSet st.evts, B ≤ st.d y := by
  intro y hy
  by_contra hge
  have hlt : st.d y < B := lt_of_not_ge hge
  obtain ⟨v, hv, _⟩ := hL y hlt
  exact hkey y v hv (hset y hy)

/-! ## Signature and axiom audit -/

#check @prem_tail_iff_noPremGated
#check @prem_empty_drained
#check @mint_floor_of_loopBInv
#check @prem_empty_tail
#check @prem_empty_recur
#check @noPremGated_of_recur
#check @cover_empty_carve_of_gatedMint
#check @labelKey_iff_present_agree
#check @labelKey_iff_split
#check @labelKey_refuted_at_engine_state
#check @belowKeys_label_lt
#check @labelAgree_deleteSet_iff
#check @labelAgree_merge
#check @merge_value_lt
#check @StoreTight
#check @ChildStoreTight
#check @PivotKey
#check @pivotKey_of_group_low
#check @candSettled_of_premFree
#check @noLoose_of_premFree
#check @seed_settled_of_premFree
#check @floor_of_recur_premFree
#check @noCompleteKey_deleteSet
#check @noCompleteKey_iff_val_not_canonical
#check @not_labelKeySettled_of_custody
#check @settled_ge_of_labelKey_custody

#print axioms prem_empty_drained
#print axioms mint_floor_of_loopBInv
#print axioms prem_empty_tail
#print axioms prem_empty_recur
#print axioms noPremGated_of_recur
#print axioms cover_empty_carve_of_gatedMint
#print axioms labelKey_iff_present_agree
#print axioms labelKey_iff_split
#print axioms stN'_D_v0
#print axioms counterexample_not_labelKeyLive
#print axioms labelKey_refuted_at_engine_state
#print axioms belowKeys_label_lt
#print axioms labelAgree_deleteSet_iff
#print axioms labelAgree_merge
#print axioms merge_value_lt
#print axioms candSettled_of_premFree
#print axioms noLoose_of_premFree
#print axioms seed_settled_of_premFree
#print axioms floor_of_recur_premFree
#print axioms noCompleteKey_deleteSet
#print axioms noCompleteKey_iff_val_not_canonical
#print axioms not_labelKeySettled_of_custody
#print axioms settled_ge_of_labelKey_custody

end DMSY
end Frontier

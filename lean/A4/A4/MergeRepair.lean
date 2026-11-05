import A4.KeyLabFloor

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.MergeRepair — evaluating the BM.14 re-keying repair

`A4.KeyLabFloor` proved that the corrected engine's `LabFloor` is not an invariant: after a pull
remainder, the child returns a *smaller* label for a parent key while `D2 = DS.merge D1 fo'.D`
keeps the parent's stale larger **value**, so two-sided key-label honesty (`Keyed`/`KeyLabEq`)
fails.  It then proposed, as the "minimal semantic repair", to re-key the merged store from the
child's labels:

    D2 := fun y => (DS.merge D1 fo'.D y).map (fun _ => fo'.d' y)

This file settles whether that is a semantic correction.  **It is not**, and the reasons are
structural, not a matter of taste.

## 0. What BM.14 is in the corrected algorithm text

Read from the lane's frozen algorithm text (`c-hd-proof/paper/background/
PRIOR_B1_UNVERIFIED_DRAFT.md`, §S2.1/S2.2), the store semantics are:

* **BM.14** `D.Merge(D_i)` — "`Merge(D')`: Insert(y, val_{D'}(y)) for every key y of D'", i.e. the
  keep-min on stored **values** that `DS.merge` already implements.  There is no re-keying.
* **(V1)** `val(y) ⪰ d[y]` for every key y at every time — **one-sided**, and the only global
  key/value law.  It is preserved by keep-min, because labels never increase.
* A key is **certified** iff it is complete and `val(y) = d[y]`; (R2)/(J3) need *some* certified
  key on each canonical path, never `val = d` at every key.  Two-sided identity appears in the
  text exactly once — **(K0)**, the `l = 0` base case ("each changed label is immediately
  inserted"), which is *derivable* there and is not claimed at `l > 0`.
* **(R3)** is what excludes `KeyLabFloor`'s bad state for real: `keys(D) ⊆ Ũ \ U` and
  `B' ⪯ dis(y) ⪯ d[y] ⪯ val(y) ≺ B`.  It is maintained by **★BM.15 FIX-STALE** ("`for u ∈ U_i:
  D.Delete(u)`"), which this package's repair restored into the engine itself: `A4.Semantics.IStep`
  now reads `D2 = DS.deleteSet (DS.merge D1 fo'.D) (settledFinset fo')`, and
  `MergePolicy.parent` (BM.14 alone) is retained only as the **historical** pre-repair clause the
  negative regressions contrast against.

So the paper's merge is the one that is already implemented, and the paper's invariant is not
`LabFloor` but (V1) + certified-key existence.  That matters below.

## 1. The three candidate readings are two (§1–§2)

`IStepWith` (defined in `A4.Semantics`, next to `IStep`) parameterizes **only** the BM.14 clause
of `IStep`, and with ★BM.15 restored the engine *is* the `fixStale` instance by `Iff.rfl`
(`istepWith_fixStale_iff`).  `MergePolicy.parent` is no longer the engine's clause; it is
documented as historical and used only to state what the omission admitted.
Three policies are named:

* `MergePolicy.parent` — BM.14 as written: keep-min of the two *stored values*.
* `MergePolicy.childLabel` — the proposed repair: same key set, value replaced by `fo'.d'`.
* `MergePolicy.fixStale` — ★BM.15: merge, then delete the child's settled set.

"Child label" and "minimum label" are **not distinct readings** (`childLabel_eq_mergeVal`): at
every key the re-keyed value *is* `min (stored value) (current label)`, and the engine's own
monotone labels + the child's own keyedness make the current label the minimum.  So there are two
policies to choose between, and a "min-merge on labels" is the proposal, not a third option.

## 2. What the proposal buys, exactly (§3)

`keyed_childLabel` is unconditional: the re-keyed store is keyed by construction.  Hence
`keyed_istepWith_childLabel` derives `Keyed st'.d st'.D` from **no** hypotheses at all — no
`Keyed st.d st.D`, no child keyedness, no label monotonicity, and in particular no `KeyedCarry`.
`keyedCarry_fails_independentOf_policy` states the precise reason the last of those is a
*dissolution* and not a proof: `KeyedCarry` mentions only `st.D`, `fo'.D`, `fo'.d'`, so no merge
policy can make it true — `Counterexample.carry_fails` refutes it for every policy and every parent
store, including this one.

## 3. What it costs — the decisive part (§4)

`LabFloor`'s key half is `∀ y val, D y = some val → bp ≤ d y`.  The quantifier body does not
mention `val`, so the statement is a statement about the **key set**:

    keyHalf_congr_keys : (∀ y, D y = none ↔ D' y = none) → (key half at D ↔ key half at D')

`MergePolicy.childLabel_none_iff` says the re-keying preserves the key set exactly, so

    childLabel_keyHalf_iff : key half at the re-keyed store ↔ key half at DS.merge

— **the repair is provably inert on the very predicate it was introduced to restore**, at every
state, for every child.  And it is not merely inert: it *destroys* the one floor the engine does
prove.  At `KeyLabFloor`'s own counterexample state (the repaired state `Counterexample.stKR`, same
labels `dL`, same bound `foK.B' = lam2`, only the store re-keyed) the re-keyed store is
`v1 ↦ lam1` while `bp = lam2`, so

* `childLabel_keyed` : `Keyed` holds (the gain), and
* `childLabel_not_ge` / `childLabel_not_loopBoundInv` : `Ge stKR.bp stKR.D` and `LoopBoundInv stKR`
  are **false** (no mints are recorded here, so the two coincide) —

`Ge`/`LoopBoundInv` being exactly what `A4.Transitive.loopBoundInv_istep` proves for the unrepaired
merge and what `keyLabFloor_istep` consumes alongside `Keyed`.  So the pair `(Keyed, Ge)` is
unsatisfiable at that state: the repair trades the failure `val ≠ d y` for the failure
`val = d y < bp`, and `LabFloor`'s key half is false in both.  `childLabel_no_help` bundles this.
Consequence for `BpChain`/identity-cover: **none** — `bpChain_of_chainLabFloor` (and every
`A4.IdentityCover`/`A4.LowKeyClosure` route) consumes `LabFloor` or a value floor, and the repaired
engine supplies neither at a genuine step output.  The failure is not cosmetic either: the repaired
state's only key carries a label below the running bound, which is the (J2) hazard
`KeyLabFloor.stK'_seed_hazard` records — and the next iteration pulls it (`PullSpec` with
`|keys| ≤ pullCap` returns the whole key set at separator `B`), handing `SeedLabFloor` a seed it
cannot clear.

Also changed by the proposal, and not hideable: (i) stored values now drop below the separator of
the pull that produced them, so the paper's **S5 merge precondition** ("every stored value of `D_i`
is `≺ B_i` and every value remaining in `D` is `⪰ B_i`") fails on the *parent* side, and (R3)'s
`B' ⪯ val` fails with it; (ii) the pull's `(PP)` equality survives (values stay distinct), but
*which* keys a later pull returns changes, so the engine's execution tree changes — this is a
different algorithm, not a re-annotated one; (iii) cost is unchanged asymptotically (a linear
re-key over the merged keys sits inside S5's linear Merge), so the cost clauses are *not* the
obstruction.  (i) and the `Ge` failure are.

## 4. The sound repair is the deletion, and it is a `Semantics.lean` change (§5)

`fixStale` keeps the merge and deletes the child's settled set.  Its key set *does* change
(`MergePolicy.fixStale_none_iff`), which is the only lever that can move a key-set statement — and at the
counterexample it empties the store (`Counterexample.fixStale_eq_empty`), so `Keyed`, `Ge` and the key half
all hold **vacuously** and the (J2) seed hazard is gone (`fixStale_repairs`, a verified
`IStepWith MergePolicy.fixStale` whose output satisfies `LabFloor`).  That is ★BM.15, and it is
now **in the engine**: `A4.Semantics.IStep`'s BM.14 clause reads
(`D2 = DS.deleteSet (DS.merge D1 fo'.D) (settledFinset fo')`, where `settledFinset fo'` is the child's
settled vertices as a `Finset` — `deleteSet` takes a `Finset`, not a `Set`), not a new hypothesis about
children.

What restoring it cost, precisely: the returned store no longer contains the child's settled
vertices, so (a) `Lemma 3.8*`(c)'s re-settlement bound `T_X` loses the duplicate-settlement channel
it was counting — the stale-key channel is now removed
(`A4.FixStale.istepFS_next_seeds_avoid_settled`), leaving the cross-sibling channel (`A4.Size`'s
Lemma 3.8\*(c), untouched) and the `Prem`/Q12 mints, so
`A4.ReturnClauses`' clause (2c) holds at the shrunk key set with `T_X` charged against the mints
(the `FixStale` regression re-states it there); (b) `IStep`'s `D2` clause changed, hence every file that
pattern-matches it (`Transitive`, `LoopBInv`, `KeyLabFloor`, `ValueBpChain`, `LowKeyClosure`,
`ReturnClauses`, `BpMonotonicity`, `IdentityCover`, `Structural`, `ExecutionFrame`, `Cascade`,
`IStepTrace`) had to be re-elaborated — the monotonicity lever is
`A4.Semantics.deleteSet_some_imp` (a deletion drops keys and rewrites no value); and (c)
nothing else — the merge, the sweeps, the mints, the tail, `pullRun` are untouched.

## 5. Verdict

* The proposed `map` is **not** a semantic correction; it is a new hypothesis on the *store*, and
  provably inert on `LabFloor`'s key half (`childLabel_keyHalf_iff`, for all states and children).
* `KeyedCarry` cannot be "proved" by any merge change (`keyedCarry_fails_independentOf_policy`);
  its failure at a pull remainder is a fact about the child and the parent's surviving key set,
  and the re-keying removes the need for it rather than establishing it.
* `BpChain` does **not** resume from this repair.  Neither identity-cover route gets closer.
* The engine-vs-text gap is BM.15, and repairing it was a `Semantics.lean` edit; the frozen text
  itself lists BM.15 as ★ required ("without BM.15 the U_i overlap").  `fixStale_repairs` is the
  proof that the deletion kills this exact counterexample, and `A4.FixStale` carries the
  engine-level regressions (mirror `Keyed`/`LoopBoundInv` results at `IStepFS`, the clause (2c)
  statement at the shrunk key set, and the negative pin: `MergePolicy.parent` still admits this
  counterexample's step while `IStep` forbids it).
* `a4_joint` assembly cannot resume on the assertion that `LabFloor` is an invariant.  Either
  `Semantics.lean` restores BM.15, or the return clauses must be restated in the paper's
  certified-key form ((V1) + (J2)/(J3)), which needs no two-sided honesty anywhere.

No `sorry`/`admit`, no new axiom, no peer file modified.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. A merge policy for BM.14 (`IStep` with one clause varied)

`MergePolicy`, `MergePolicy.parent`, `MergePolicy.fixStale` and `IStepWith` live in
`A4.Semantics` (the engine owns its BM.14 clause).  The policy evaluated here — the proposed
re-keying — is defined below. -/

/-- The proposed repair: keep the merged key set, re-key every key at the child's returned label. -/
noncomputable def MergePolicy.childLabel (D₁ : DS G s) (fo : CallOut G s) : DS G s :=
  fun y => (DS.merge D₁ fo.D y).map (fun _ => fo.d' y)

open Classical in
/-- **The parameterization is conservative, in the direction that now matters**: with ★BM.15
restored, the engine's `IStep` *is* the `fixStale` instance, definitionally (`Iff.rfl`).
`MergePolicy.parent` — BM.14 as written, without BM.15 — is the **historical** pre-repair clause:
it is no longer the engine's, and the negative regressions at the end of `A4.FixStale` pin exactly
that (`parent` admits the `Counterexample` step, `IStep`/`IStepFS` forbid it). -/
theorem istepWith_fixStale_iff {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} :
    IStepWith (MergePolicy.fixStale (G := G) (s := s)) t B l st st' c fo' ↔
      IStep t B l st st' c fo' :=
  Iff.rfl

/-! ## 2. "Child label" = "minimum label"; both differ from "parent value" -/

namespace MergePolicy

/-- The re-keyed store's key set is the merge's key set: `Option.map` never changes `none`ness. -/
theorem childLabel_none_iff (D₁ : DS G s) (fo : CallOut G s) (y : Fin G.n) :
    childLabel D₁ fo y = none ↔ DS.merge D₁ fo.D y = none := by
  unfold childLabel
  cases DS.merge D₁ fo.D y <;> simp

/-- The re-keyed store *is* a keep-min against the current label at every **key** of the merged
store, whenever the label sits below the stored value — which the engine's monotone labels plus the
child's own keyedness supply.  So "choose the child label" and "min-merge on labels" are the same
policy; "parent value" is the other one.  (The restriction to keys is essential: `insert` at a
vertex the merge dropped would *create* a key, which re-keying never does.) -/
theorem childLabel_eq_mergeVal (D₁ : DS G s) (fo : CallOut G s)
    (h : ∀ y v, DS.merge D₁ fo.D y = some v → fo.d' y ≤ v) {y : Fin G.n}
    (hne : DS.merge D₁ fo.D y ≠ none) :
    childLabel D₁ fo y = DS.mergeVal (DS.merge D₁ fo.D y) (some (fo.d' y)) := by
  unfold childLabel
  cases hm : DS.merge D₁ fo.D y with
  | none => exact absurd hm hne
  | some v =>
    rw [Option.map_some, DS.mergeVal_some, min_eq_right (h y v hm)]

/-- ★BM.15's key set: the merge's keys, minus the child's settled set.  This is the only policy of
the three that can change a key-set statement. -/
theorem fixStale_none_iff (D₁ : DS G s) (fo : CallOut G s) (y : Fin G.n) :
    fixStale D₁ fo y = none ↔ DS.merge D₁ fo.D y = none ∨ y ∈ settledSet fo.evts := by
  have hnot : ¬ y ∈ settledFinset fo ↔ ¬ y ∈ settledSet fo.evts := not_congr mem_settledFinset
  unfold fixStale DS.deleteSet
  by_cases hy : y ∈ settledFinset fo
  · rw [if_pos hy]
    exact ⟨fun _ => Or.inr (mem_settledFinset.mp hy), fun _ => rfl⟩
  · rw [if_neg hy]
    exact ⟨fun h => Or.inl h, fun h => h.elim id fun h' => absurd h' (hnot.mp hy)⟩

end MergePolicy

/-! ## 3. What the re-keying buys: keyedness, unconditionally, and nothing else -/

/-- **The re-keyed store is keyed by construction** — no hypotheses, no `KeyedCarry`, no child
keyedness, no label monotonicity. -/
theorem keyed_childLabel (D₁ : DS G s) (fo : CallOut G s) :
    Keyed fo.d' (MergePolicy.childLabel D₁ fo) := by
  intro y val hy
  unfold MergePolicy.childLabel at hy
  cases hm : DS.merge D₁ fo.D y with
  | none => rw [hm] at hy; exact absurd hy (by simp)
  | some v =>
    rw [hm, Option.map_some] at hy
    exact (Option.some.inj hy).symm

/-- **One iteration preserves keyedness under the re-keying policy, with no premises at all** — the
mirror of `A4.KeyLabFloor.keyed_istep`, whose `hcarry`/`hchild`/`hle` parameters are all gone.
`KeyedCarry` names no merge (see `keyedCarry_fails_independentOf_policy`), so the re-keying cannot
*prove* it; it dissolves the need for it, which is the only thing a merge change can do. -/
theorem keyed_istepWith_childLabel {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStepWith (MergePolicy.childLabel (G := G) (s := s)) t B l st st' c fo') :
    Keyed st'.d st'.D := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hM : Keyed fo'.d' D2 := by
    rw [hmerge]
    exact keyed_childLabel D1 fo'
  have hsweep' : Keyed d3 D3 := by
    conv => lhs; rw [show d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 from congrArg Prod.fst hsweep]
    conv => rhs; rw [show D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 from congrArg Prod.snd hsweep]
    exact keyed_sweepEvts B Bi fo'.evts _ _ hM
  exact keyed_fold_insert J.toList sel d3 D3 hsweep'

/-! ## 4. What it costs: the key half is invariant, and the value floor dies -/

/-- `LabFloor`'s key half reads only the **key set**: the quantifier body does not mention `val`. -/
theorem keyHalf_iff_keys {bp : WLab G s} {d : Labels G s} {D : DS G s} :
    (∀ y val, D y = some val → bp ≤ d y) ↔ (∀ y, D y ≠ none → bp ≤ d y) := by
  constructor
  · intro h y hy
    obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hy
    exact h y v hv
  · intro h y val hy
    exact h y (by rw [hy]; exact Option.some_ne_none val)

/-- **Store surgery on a preserved key set cannot change the key half of `LabFloor`.**  This is the
general obstruction: any BM.14 policy that keeps the merge's keys — re-keying, keep-min, any value
rewrite — leaves the key half exactly as true or false as it was. -/
theorem keyHalf_congr_keys {bp : WLab G s} {d : Labels G s} {D D' : DS G s}
    (h : ∀ y, D y = none ↔ D' y = none) :
    (∀ y val, D y = some val → bp ≤ d y) ↔ (∀ y val, D' y = some val → bp ≤ d y) := by
  rw [keyHalf_iff_keys, keyHalf_iff_keys]
  exact forall_congr' fun y => by rw [Ne, Ne, h y]

/-- The proposed repair is **inert on the key half**, for every state and every child. -/
theorem childLabel_keyHalf_iff (bp : WLab G s) (d : Labels G s) (D₁ : DS G s)
    (fo : CallOut G s) :
    (∀ y val, MergePolicy.childLabel D₁ fo y = some val → bp ≤ d y) ↔
      (∀ y val, DS.merge D₁ fo.D y = some val → bp ≤ d y) :=
  keyHalf_congr_keys (MergePolicy.childLabel_none_iff D₁ fo)

namespace Counterexample

/-- The proposed repair applied to the counterexample's merge. -/
noncomputable def D2R : DS Gcx v0 := MergePolicy.childLabel (DS.deleteSet st.D {v0}) foK

/-- The merge value at the failing key, before re-keying. -/
theorem merge_v1 : DS.merge (DS.deleteSet st.D {v0}) foK.D v1 = some lam2 := by
  rw [foK_D]
  exact stK'_D_v1

/-- After re-keying, the surviving key carries the child's label `lam1`. -/
theorem D2R_v1 : D2R v1 = some lam1 := by
  unfold D2R MergePolicy.childLabel
  rw [merge_v1, Option.map_some, foK_d', dL_v1]

/-- The repaired state: same labels, same bound, the re-keyed store. -/
noncomputable def stKR : RState Gcx v0 0 where
  d := foK.d'
  D := D2R
  evts := st.evts ++ foK.evts
  bp := foK.B'
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

theorem stKR_bp : stKR.bp = lam2 := foK_B'

theorem stKR_d_v1 : stKR.d v1 = lam1 := dL_v1

/-- **The gain**: `Keyed` holds at the repaired state. -/
theorem childLabel_keyed : Keyed stKR.d stKR.D := keyed_childLabel _ _

/-- **The cost**: the value floor is now false — `v1` is stored at `lam1` while `bp = lam2`, so the
one floor `A4.Transitive.loopBoundInv_istep` proves for the unrepaired merge is destroyed. -/
theorem childLabel_not_ge : ¬ Ge stKR.bp stKR.D := by
  intro h
  have h1 : stKR.bp ≤ lam1 := h v1 lam1 D2R_v1
  rw [stKR_bp] at h1
  exact absurd h1 (not_le.mpr coe_e0_lt_coe_e0_e1)

/-- **`LabFloor` is still false** at the repaired state — the repair did not restore it. -/
theorem childLabel_not_keyHalf :
    ¬ ∀ y val, stKR.D y = some val → stKR.bp ≤ stKR.d y := by
  intro h
  have h1 := h v1 lam1 D2R_v1
  rw [stKR_bp, stKR_d_v1] at h1
  exact absurd h1 (not_le.mpr coe_e0_lt_coe_e0_e1)

theorem childLabel_not_labFloor : ¬ LabFloor stKR := fun h => childLabel_not_keyHalf h.1

/-- The repaired iteration exists: the same pull, the same child, the same sweep (identity here) —
only BM.14 differs.  So the repaired engine admits the counterexample's step, and the obstruction
is not an artefact of an unrepresentative state. -/
theorem istepR_key : IStepWith (MergePolicy.childLabel (G := Gcx) (s := v0)) 1 ⊤ 1 st stKR childC foK := by
  refine ⟨{v0}, lam2, DS.deleteSet st.D {v0}, (fun j => j.elim0), ∅, (fun j => j.elim0),
    D2R, foK.d', D2R, pull_stK, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CallEntry.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · show ({v0} : Finset (Fin Gcx.n)) = expand st.d st.pl st.piv {v0} lam2
      rw [expand_st]
    · show (1 - 1 : ℕ) = 0
      rfl
  · exact (sweepEvts_foK D2R).symm
  · intro j
    exact j.elim0
  · ext j
    exact ⟨fun h => absurd h (Finset.notMem_empty j), fun _ => j.elim0⟩
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [RState.mk.injEq]
    refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · simp [stKR]
    · funext j
      exact (if_neg (Finset.notMem_empty j)).symm
    · simp [stKR]

/-- The two hypotheses `keyLabFloor_istep` consumes — `Keyed` and the value floor — are jointly
unsatisfiable at a genuine step output of the repaired engine. -/
theorem childLabel_keyed_ge_unsat :
    ¬ (Keyed stKR.d stKR.D ∧ Ge stKR.bp stKR.D) :=
  fun h => childLabel_not_ge h.2

/-- `LoopBoundInv` — the `keep-min` invariant `A4.Transitive`/`A4.ReturnClauses`/`A4.LowKeyClosure`
all consume — is false at the repaired state too: the state records no mint, so the floor cannot be
discharged through the Q12 carve-out. -/
theorem childLabel_not_loopBoundInv : ¬ LoopBoundInv stKR := by
  intro h
  rcases h v1 lam1 D2R_v1 with hle | hm
  · rw [stKR_bp] at hle
    exact absurd hle (not_le.mpr coe_e0_lt_coe_e0_e1)
  · exact absurd hm (by simp [stKR])

/-- **The repair's full verdict at the counterexample, in one statement.**  The re-keyed store is
keyed, the step is a genuine `IStepWith childLabel`, the *key half of `LabFloor` is still false*
(the general `childLabel_keyHalf_iff` says it must be), and the value floor — the engine's own
proved invariant — is now false too.  So `(Keyed, Ge)`, exactly the pair `keyLabFloor_istep`
consumes, is unsatisfiable here: no `BpChain`, no identity cover, and the (J2) seed hazard
(`stK'_seed_hazard`) survives untouched. -/
theorem childLabel_no_help :
    Keyed stKR.d stKR.D ∧
      IStepWith (MergePolicy.childLabel (G := Gcx) (s := v0)) 1 ⊤ 1 st stKR childC foK ∧
      ¬ Ge stKR.bp stKR.D ∧
      ¬ (∀ y val, stKR.D y = some val → stKR.bp ≤ stKR.d y) ∧ ¬ LabFloor stKR :=
  ⟨childLabel_keyed, istepR_key, childLabel_not_ge, childLabel_not_keyHalf,
    childLabel_not_labFloor⟩

/-- **`KeyedCarry` is not a statement about BM.14.**  It constrains the parent's store, the child's
store and the child's labels — no `D2`, no policy.  So its failure here is refuted for *every* merge
policy and *every* parent store at once: re-keying does not prove the premise the engine cannot
prove, it removes the need for it. -/
theorem keyedCarry_fails_independentOf_policy (M : MergePolicy Gcx v0) (D₁ : DS Gcx v0) :
    ¬ (∀ y val, st.D y = some val → foK.D y = none → foK.d' y = val) :=
  carry_fails

end Counterexample

/-! ## 5. The sound repair: ★BM.15 (FIX-STALE), a `Semantics.lean` change -/

/-- BM.15 removes exactly the child's settled set: the `keys(D) ⊆ Ũ \ U` half of the paper's (R3),
which no key-preserving policy can touch (`keyHalf_congr_keys`). -/
theorem fixStale_no_key_in_U (D₁ : DS G s) (fo : CallOut G s) {y : Fin G.n}
    (hy : y ∈ settledSet fo.evts) : MergePolicy.fixStale D₁ fo y = none := by
  unfold MergePolicy.fixStale DS.deleteSet
  exact if_pos (mem_settledFinset.mpr hy)

namespace Counterexample

/-- The child settled both vertices of `Gcx`. -/
theorem settledSet_foK : settledSet foK.evts = Set.univ := by
  ext x
  refine ⟨fun _ => Set.mem_univ x, fun _ => ?_⟩
  rw [foK_evts]
  rcases eq_v0_or_v1 x with rfl | rfl
  · exact ⟨⟨.basePull, v0⟩, List.mem_cons_self, rfl⟩
  · exact ⟨⟨.basePull, v1⟩, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩

/-- **BM.15 empties the counterexample's store**: both surviving keys are settled by the child, so
the deletion removes exactly the stale one. -/
theorem fixStale_eq_empty :
    MergePolicy.fixStale (DS.deleteSet st.D {v0}) foK = DS.empty := by
  funext y
  rw [fixStale_no_key_in_U _ _ (by rw [settledSet_foK]; exact Set.mem_univ y)]
  rfl

/-- The state after a BM.15-repaired iteration. -/
noncomputable def stKF : RState Gcx v0 0 where
  d := foK.d'
  D := DS.empty
  evts := st.evts ++ foK.evts
  bp := foK.B'
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

/-- The repaired iteration (identical to `istep_key` except that BM.14 now deletes `U_i`). -/
theorem istepF_key :
    IStepWith (MergePolicy.fixStale (G := Gcx) (s := v0)) 1 ⊤ 1 st stKF childC foK := by
  refine ⟨{v0}, lam2, DS.deleteSet st.D {v0}, (fun j => j.elim0), ∅, (fun j => j.elim0),
    DS.empty, foK.d', DS.empty, pull_stK, ?_, fixStale_eq_empty.symm, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CallEntry.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · show ({v0} : Finset (Fin Gcx.n)) = expand st.d st.pl st.piv {v0} lam2
      rw [expand_st]
    · show (1 - 1 : ℕ) = 0
      rfl
  · exact (sweepEvts_foK DS.empty).symm
  · intro j
    exact j.elim0
  · ext j
    exact ⟨fun h => absurd h (Finset.notMem_empty j), fun _ => j.elim0⟩
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [RState.mk.injEq]
    refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · simp [stKF]
    · funext j
      exact (if_neg (Finset.notMem_empty j)).symm
    · simp [stKF]

theorem stKF_ge : Ge stKF.bp stKF.D := by
  intro y val hy
  rw [show stKF.D y = none from rfl] at hy
  exact absurd hy (by simp)

theorem stKF_keyHalf : ∀ y val, stKF.D y = some val → stKF.bp ≤ stKF.d y := by
  intro y val hy
  rw [show stKF.D y = none from rfl] at hy
  exact absurd hy (by simp)

/-- **The deletion repairs the state**: the invariant `LabFloor` holds at the BM.15 output (both
floors vacuous — the store is empty), so the seed hazard is gone and the next iteration cannot pull
a stale key.  This is what the re-keying could not do (`childLabel_no_help`). -/
theorem fixStale_repairs :
    IStepWith (MergePolicy.fixStale (G := Gcx) (s := v0)) 1 ⊤ 1 st stKF childC foK ∧
      Keyed stKF.d stKF.D ∧ Ge stKF.bp stKF.D ∧ LabFloor stKF :=
  ⟨istepF_key, fun y val hy => by
      rw [show stKF.D y = none from rfl] at hy
      exact absurd hy (by simp),
    stKF_ge, ⟨stKF_keyHalf, fun j => j.elim0⟩⟩

end Counterexample

/-! ## 6. Signatures and axiom audit -/

#check @IStepWith
#check @istepWith_fixStale_iff
#check @MergePolicy.parent
#check @MergePolicy.childLabel
#check @MergePolicy.fixStale
#check @MergePolicy.childLabel_eq_mergeVal
#check @keyed_childLabel
#check @keyed_istepWith_childLabel
#check @Counterexample.keyedCarry_fails_independentOf_policy
#check @keyHalf_congr_keys
#check @childLabel_keyHalf_iff
#check @fixStale_no_key_in_U
#check @Counterexample.childLabel_keyed_ge_unsat
#check @Counterexample.childLabel_not_loopBoundInv
#check @Counterexample.childLabel_no_help
#check @Counterexample.fixStale_repairs

#print axioms istepWith_fixStale_iff
#print axioms keyed_childLabel
#print axioms keyed_istepWith_childLabel
#print axioms childLabel_keyHalf_iff
#print axioms Counterexample.childLabel_not_loopBoundInv
#print axioms Counterexample.childLabel_keyed_ge_unsat
#print axioms Counterexample.childLabel_no_help
#print axioms Counterexample.fixStale_repairs

end DMSY
end Frontier

import A4.MergeRepair

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.FixStale — ★BM.15 (FIX-STALE) restored on the corrected engine

`A4.MergeRepair` evaluated the BM.14 re-keying repair and rejected it; it also built the
★BM.15 policy (`MergePolicy.fixStale`) and repaired `A4.KeyLabFloor`'s counterexample with it.
The patch that repair owed has since **landed in the engine**: `A4.Semantics.IStep`'s BM.14 clause
is now the frozen text's `D.Merge(D_i); for u ∈ U_i: D.Delete(u)`, and
`MergePolicy.parent` (BM.14 alone) is kept only as the *historical* clause
(`MergeRepair.istepWith_fixStale_iff`; negative pins in §6 below).  This file records why the
deletion works, and carries the engine-level regressions:

1. **`IStepFS`** — the `fixStale` instance of `IStepWith`, i.e. the engine (`Iff.rfl`, `istepFS_def`).
   Nothing else in the iteration moves.
2. **Why the deletion works where no value policy can** (`fixStale_keyHalf_iff`,
   `fixStale_ge_iff`): `Ge`, the key half of `LabFloor` and `Keyed` are all ∀-over-**keys**
   predicates.  A store surgery that only *drops keys* and never rewrites a stored value
   preserves them on the surviving keys (`ge_deleteSet_iff`, `keyHalf_deleteSet_iff`) — so
   ★BM.15 can only *remove* failures, never create one.  Re-keying rewrites values at keys and
   therefore *destroyed* `Ge` (`MergeRepair.Counterexample.childLabel_not_ge`); this is not a
   matter of taste but of the quantifier shape (`MergeRepair.keyHalf_congr_keys`).
3. **(J2) and the `T_X` channel** (`istepFS_no_settled_key`, `istepFS_next_seeds_avoid_settled`):
   no vertex the child settled is a key of the step's output, hence no *later* pull out of that
   store and no BM.12 expansion off the residual groups can hand the next child a vertex already
   settled — the stale-entry duplicate channel `T_X` used to count.  The one residue is the
   frozen text's own (k3) gate (`SweepsSpare`, named and documented below).
4. **Regressions (§5–§6)**: `keyed_istepFS` (mirror of `KeyLabFloor.keyed_istep` with the
   `KeyedCarry` hypothesis restricted off the settled keys), `loopBoundInv_istepFS` (mirror of
   `Transitive.loopBoundInv_istep` through `fixStale_ge`), `clause2c_shrunk_keys` ((2c) at the
   shrunk key set, `T_X := 0`, `Prem` unchanged), and the negative pins — the unrepaired
   `MergePolicy.parent` clause admits the `KeyLabFloor` counterexample and re-frontiers a settled
   vertex where `IStep`/`IStepFS` forbid both.

## The verdict on the engine omission (the patch that `A4.Semantics` now carries)

The frozen algorithm text (`c-hd-proof/paper/background/PRIOR_B1_UNVERIFIED_DRAFT.md`) is
unambiguous and BM.15 is a ★ line (S2.1 table; §S2.4 item 3: *"Disjointness/interval structure
(R8) is derived from the characterization Step 3, which needs (J2): no key of D is ever in U —
this is where FIX-STALE (BM.15) is used (k1)"*; errata E1: *"settled U_i keep stale D entries, so
U_i overlap and Line-24 insertions repeat; the time analysis is invalid as written | FIX-STALE |
... 239 overlaps in 200 graphs, 0 after the fix"*).  So:

* **BM.15 is required**, and it is required by *both* candidate contracts.  The "certified-key form"
  (V1) + (R2) drops only the **value identity** `val(y) = d[y]`; the certified-frontier clause is
  existential per path and tolerates stale keys.  What it does **not** drop is `(J2)`,
  `keys(D) ∩ U = ∅` — and `(J2)`'s (k1) case *is* BM.15.  A form that drops `(J2)` too is not
  restatable: it loses (R3)'s `B' ⪯ d[y]`, (R4)'s dichotomy, (R7), the S5 pull precondition
  ("every stored value of `D_i` is `≺ B_i`"), and with them the `|keys(D)|` bound and every
  `Σ_i |U_i|` charge of Lemma 3.9.
* **Duplicate settlements are not a property of the V5 engine; they are the omission.**
  `CORRECTED_PROOF` §5 measures duplicates on the *cap-on / cap-off* axis ("bit-identical with and
  without it"), not on the *delete-on / delete-off* axis, and the audit's own E1 measurement is
  0 after FIX-STALE.  So `T_X` (`Lemma R`, *sketch grade*) describes the unrepaired engine;
  restoring BM.15 retires it and restores the paper's `T_X = 0` / disjoint `U_i`.

What does **not** change: `Prem` (the Q12 carve-out) is about the final iteration's *line-29
mints*, which BM.15 never touches, so Lemma 3.7\*(2b)/(2c) survive verbatim; `W'` (BM.26) is
filtered against the call's own `U`, which already accumulates the children's settlements.  The
settlement accumulator becomes a **set** in effect (`U_i` disjoint, `T_X = 0`), so `(E3)`'s
event-counting guard is unchanged in form and tighter in value.

No `sorry`/`admit`, no new axiom.  (This file was written against the unpatched engine; the
`Semantics.lean` patch — the `IStep` clause, `settledFinset`/`mem_settledFinset`,
`MergePolicy`/`IStepWith`, and `deleteSet_some_imp` — plus the consumer re-elaborations landed
afterwards, so items 2–4 above now describe the engine rather than a variant.)
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The BM.15 iteration: `IStep` with the frozen text's BM.14–15 -/

/-- **★BM.15 (FIX-STALE) as the engine's iteration.**  `IStep` differs from this in exactly one
conjunct: `D2 = DS.merge D1 fo'.D` instead of `D2 = fixStale D1 fo'`, i.e. the frozen text's
`BM.14 D.Merge(D_i); BM.15 for u ∈ U_i: D.Delete(u)`.  The order matters and is faithful: the
deletion happens **before** the BM.19–21 sweep, so a settled vertex may re-enter only through a
*new gated* relaxation. -/
abbrev IStepFS (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p)
    (c : CallEntry G s) (fo' : CallOut G s) : Prop :=
  IStepWith (MergePolicy.fixStale (G := G) (s := s)) t B l st st' c fo'

/-- `IStepFS` is the `fixStale` instance of `IStepWith` — and with ★BM.15 in the engine that
instance *is* `A4.Semantics.IStep` (`MergeRepair.istepWith_fixStale_iff`, `Iff.rfl`), while
`MergePolicy.parent` is the historical pre-repair clause.  So every theorem below is a theorem
about the engine's own iteration. -/
theorem istepFS_def {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} :
    IStepFS t B l st st' c fo' ↔
      IStepWith (MergePolicy.fixStale (G := G) (s := s)) t B l st st' c fo' :=
  Iff.rfl

/-! ## 2. Why the deletion can only help: the floors are key-set predicates -/

/-- **★BM.15 never damages a value floor.**  `Ge` quantifies over keys, so dropping keys (and
keeping every surviving value verbatim) preserves it.  Contrast the re-keying, which kept the key
set and rewrote values and thereby made `Ge` *false* at the counterexample
(`MergeRepair.Counterexample.childLabel_not_ge`). -/
theorem ge_deleteSet {K : WLab G s} {D : DS G s} (h : Ge K D) (T : Finset (Fin G.n)) :
    Ge K (DS.deleteSet D T) := by
  intro y val hy
  by_cases hyT : y ∈ T
  · rw [DS.deleteSet_mem D T y hyT] at hy
    exact absurd hy.symm (Option.some_ne_none val)
  · rw [DS.deleteSet_of_notMem D T y hyT] at hy
    exact h y val hy

/-- **The exact repair power of a key deletion, for `Ge`.**  The floor after the deletion is the
floor on the keys *outside* the deleted set: nothing else moves.  This is the general reason a
key-set surgery is the only one that can repair a key-set predicate
(`MergeRepair.keyHalf_congr_keys`: a key-preserving policy is provably inert). -/
theorem ge_deleteSet_iff (K : WLab G s) (D : DS G s) (T : Finset (Fin G.n)) :
    Ge K (DS.deleteSet D T) ↔ ∀ y val, D y = some val → y ∉ T → K ≤ val := by
  constructor
  · intro h y val hy hyT
    exact h y val (by rw [DS.deleteSet_of_notMem D T y hyT]; exact hy)
  · intro h y val hy
    by_cases hyT : y ∈ T
    · rw [DS.deleteSet_mem D T y hyT] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    · rw [DS.deleteSet_of_notMem D T y hyT] at hy
      exact h y val hy hyT

/-- `LabFloor`'s key half is a ∀-over-keys predicate too: the same restriction law. -/
theorem keyHalf_deleteSet_iff (bp : WLab G s) (d : Labels G s) (D : DS G s)
    (T : Finset (Fin G.n)) :
    (∀ y val, DS.deleteSet D T y = some val → bp ≤ d y) ↔
      ∀ y val, D y = some val → y ∉ T → bp ≤ d y := by
  constructor
  · intro h y val hy hyT
    exact h y val (by rw [DS.deleteSet_of_notMem D T y hyT]; exact hy)
  · intro h y val hy
    by_cases hyT : y ∈ T
    · rw [DS.deleteSet_mem D T y hyT] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    · rw [DS.deleteSet_of_notMem D T y hyT] at hy
      exact h y val hy hyT

/-- **BM.15 at BM.14, in one statement.**  The key half of `LabFloor` holds *after* ★BM.15 iff it
holds on the merge output's keys outside the child's settled set.  Since the settled set is
exactly the set of vertices the child improved (`settledSet fo'.evts`), the deletion repairs
precisely the stale-key failures — `A4.KeyLabFloor`'s counterexample class — and touches nothing
else.  No value policy can produce this (`MergeRepair.childLabel_keyHalf_iff`: re-keying is
inert on the key half). -/
theorem fixStale_keyHalf_iff (bp : WLab G s) (d : Labels G s) (D₁ : DS G s)
    (fo : CallOut G s) :
    (∀ y val, MergePolicy.fixStale D₁ fo y = some val → bp ≤ d y) ↔
      ∀ y val, DS.merge D₁ fo.D y = some val → y ∉ settledSet fo.evts → bp ≤ d y := by
  unfold MergePolicy.fixStale
  rw [keyHalf_deleteSet_iff (G := G) (s := s) bp d (DS.merge D₁ fo.D) (settledFinset fo)]
  constructor
  · intro h y val hy hySet
    exact h y val hy fun hyF => hySet (mem_settledFinset.mp hyF)
  · intro h y val hy hyF
    exact h y val hy fun hySet => hyF (mem_settledFinset.mpr hySet)

/-- **`Ge` survives ★BM.15 monotonically**: whatever value floor the merge output carried, the
repaired output carries.  So no `BpChain`/`LoopBoundInv` clause that reads a value floor is
*broken* by the repair — they are inherited, and `Ge`'s failure at a genuine `IStep` output
(`A4.KeyLabFloor` counterexample) is not a floor failure at all but a **key-label** failure. -/
theorem fixStale_ge (K : WLab G s) (D₁ : DS G s) (fo : CallOut G s) :
    Ge K (DS.merge D₁ fo.D) → Ge K (MergePolicy.fixStale D₁ fo) := by
  intro h
  unfold MergePolicy.fixStale
  exact ge_deleteSet h _

/-- The same law in restriction form, at BM.14. -/
theorem fixStale_ge_iff (K : WLab G s) (D₁ : DS G s) (fo : CallOut G s) :
    Ge K (MergePolicy.fixStale D₁ fo) ↔
      ∀ y val, DS.merge D₁ fo.D y = some val → y ∉ settledSet fo.evts → K ≤ val := by
  unfold MergePolicy.fixStale
  rw [ge_deleteSet_iff (G := G) (s := s) K (DS.merge D₁ fo.D) (settledFinset fo)]
  constructor
  · intro h y val hy hySet
    exact h y val hy fun hyF => hySet (mem_settledFinset.mp hyF)
  · intro h y val hy hyF
    exact h y val hy fun hySet => hyF (mem_settledFinset.mpr hySet)

/-- **No settled vertex is a key of the merged store after ★BM.15** — the general engine-level
statement of what `MergeRepair.Counterexample.fixStale_eq_empty` witnesses at one state: the child
settled both vertices, so the deletion empties the store.  `A4.KeyLabFloor`'s stale
`v1 ↦ lam2`-over-`lam1` key cannot survive any ★BM.15 step, at any state, for any child. -/
theorem fixStale_no_settled_key (D₁ : DS G s) (fo : CallOut G s) {y : Fin G.n}
    (hy : y ∈ settledSet fo.evts) : MergePolicy.fixStale D₁ fo y = none :=
  fixStale_no_key_in_U D₁ fo hy

/-! ## 3. The counterexample, at the engine-level name -/

/-- **★BM.15 kills the `A4.KeyLabFloor` counterexample.**  Restated at `IStepFS`: the repaired
iteration is a genuine step and its output satisfies `Keyed`, `Ge` and `LabFloor` — the pair
`(Keyed, Ge)` that `keyLabFloor_istep` consumes is *satisfiable* here, where the re-keying made it
unsatisfiable (`MergeRepair.Counterexample.childLabel_keyed_ge_unsat`).  Since the deletion's
effect on those predicates is *only* through the key set (§2), this instance is not special: it is
the class. -/
theorem fixStale_kills_counterexample :
    IStepFS 1 ⊤ 1 Counterexample.st Counterexample.stKF Counterexample.childC Counterexample.foK ∧
      Keyed Counterexample.stKF.d Counterexample.stKF.D ∧
      Ge Counterexample.stKF.bp Counterexample.stKF.D ∧ LabFloor Counterexample.stKF :=
  Counterexample.fixStale_repairs

/-! ## 4. (J2) and the `T_X` channel: what the deletion closes and what it does not -/

/-- **(k3) as an engine-level premise**: the BM.19–21 / BM.27–28 sweeps never *re-create* a key at
a vertex that is already settled and was deleted at BM.15.  This is the one residue of the
deletion repair, and it is arithmetic, not semantics: a settled vertex `w` is complete, so
`dis(w) ≺ B'_i ⪯ B_i ⪯ cand` (`B_i` is a pull separator; `cand ⪰ B_i` by the (E2) gate), while an
insertion at `w` needs `cand ⪯ d[w] = dis(w)`.  Contradiction — hence no insert, hence no key.
The conclusion is stated as a predicate on the sweep *function* so the hypothesis is
witness-free; it is not vacuous (`sweepsSpare_nil`). -/
def SweepsSpare (B lo : WLab G s) (evts : List (SettlementEvent G)) (T : Finset (Fin G.n)) : Prop :=
  ∀ (d : Labels G s) (D : DS G s) (y : Fin G.n), y ∈ T → D y = none →
    (sweepEvts B lo evts d D).2 y = none

/-- `SweepsSpare` is not vacuous by construction: the empty sweep spares everything. -/
theorem sweepsSpare_nil (B lo : WLab G s) (T : Finset (Fin G.n)) :
    SweepsSpare (G := G) (s := s) B lo [] T := by
  intro d D y _ hD
  exact hD

/-- The BM.23/BM.18 mint fold only *adds* keys, at `sel j ∈ resid j`, and `resid` is the residual
group with the settled members already removed (`IStep`'s own `resid` clause).  So a key the
deletion removed stays removed. -/
theorem fold_insert_spares {ι : Type} (js : List ι) (f : ι → Fin G.n) (lam : ι → WLab G s)
    {y : Fin G.n} (hy : ∀ j ∈ js, f j ≠ y) (D : DS G s) (hD : D y = none) :
    (js.foldl (fun D j => DS.insert D (f j) (lam j)) D) y = none := by
  induction js generalizing D with
  | nil => exact hD
  | cons j rest ih =>
    simp only [List.foldl_cons]
    refine ih (fun j' hj' => hy j' (List.mem_cons_of_mem _ hj')) _ ?_
    show DS.insert D (f j) (lam j) y = none
    rw [DS.insert_of_ne D (f j) (lam j) (Ne.symm (hy j List.mem_cons_self))]
    exact hD

/-- **★BM.15 + (k3) ⟹ no settled vertex is a key of the iteration's output.**  This is the frozen
text's `(J2)` at the iteration boundary (`keys(D) ⊆ A \ U`), the clause that item 3 of §S2.4 and
(k1) of §S2.4 Step 4 identify as *the* use of FIX-STALE.  Note what is **not** used: no value
identity, no `KeyedCarry`, no child honesty beyond the deletion itself. -/
theorem istepFS_no_settled_key {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStepFS t B l st st' c fo')
    (hspare : ∀ lo : WLab G s, SweepsSpare B lo fo'.evts (settledFinset fo'))
    {y : Fin G.n} (hy : y ∈ settledSet fo'.evts) : st'.D y = none := by
  classical
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  -- ★BM.15: the settled vertex is not a key of `D2`
  have hD2 : D2 y = none := by
    rw [show D2 = MergePolicy.fixStale D1 fo' from hmerge]
    exact fixStale_no_settled_key D1 fo' hy
  -- (k3): the sweep spares it
  have hD3 : D3 y = none := by
    rw [show D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 from congrArg Prod.snd hsweep]
    exact hspare Bi fo'.d' D2 y (mem_settledFinset.mpr hy) hD2
  -- BM.18/BM.23: mints land only on residual members, which exclude the settled set
  refine fold_insert_spares J.toList sel (fun j => d3 (sel j)) (fun j hj => ?_) D3 hD3
  have hjJ : j ∈ J := Finset.mem_toList.mp hj
  have hselj := (hsel j hjJ).1
  rw [hresid j] at hselj
  have hnot : sel j ∉ settledSet fo'.evts := (Finset.mem_filter.mp hselj).2
  intro hcontra
  exact hnot (hcontra ▸ hy)

/-- **The `T_X` channel, closed.**  `pullRun` returns *exactly* the store's keys below the
separator (`S' = belowKeys D x`), and BM.12 expands only out of the residual groups — which
`IStep` already filters against the settled set.  So **neither seed source of the next child can
contain a vertex this iteration settled**: no stale-entry re-frontiering, no duplicate settlement
through the pull channel.  `T_X`'s duplicate excess is not a property to be bounded here; it is
zero, which is what retires `Lemma R` and restores the paper's disjoint-union Lemma 3.8\*(c) and
the `Σ_i |U_i| ≤ |U|` charges of Lemma 3.9\*. -/
theorem istepFS_next_seeds_avoid_settled {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStepFS t B l st st' c fo')
    (hspare : ∀ lo : WLab G s, SweepsSpare B lo fo'.evts (settledFinset fo'))
    {cap : ℕ} {Bd x : WLab G s} {S' : Finset (Fin G.n)} {D' : DS G s}
    (hpull : pullRun cap st'.D Bd S' x D') :
    (∀ y, y ∈ S' → y ∉ settledSet fo'.evts) ∧
      ∀ (j : Fin p) (y : Fin G.n), y ∈ st'.pl j → y ∉ settledSet fo'.evts := by
  classical
  refine ⟨fun y hyS hySet => ?_, fun j y hy => ?_⟩
  · have hpulled : ∃ v, st'.D y = some v ∧ v < x := (pullRun_pulled hpull).mp hyS
    obtain ⟨v, hv, _⟩ := hpulled
    rw [istepFS_no_settled_key h hspare hySet] at hv
    exact absurd hv.symm (Option.some_ne_none v)
  · obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, _hpull, _hc, _hmerge, _hsweep, hresid, _hJ,
      _hsel, hst'⟩ := h
    subst hst'
    have hy' : y ∈ resid j := hy
    rw [hresid j] at hy'
    exact (Finset.mem_filter.mp hy').2

/-! ## 5. Regressions for the restored engine (★BM.15 in `Semantics.IStep`)

With BM.15 in the engine, `IStepFS` is no longer a *variant* to be contrasted with `IStep` — it is
the same relation (`istepWith_fixStale_iff`) — and the mirror theorems below are stated at
`IStepFS` because that name carries the historical intent ("the repaired iteration").  The
negative pins at the end are what keeps the pair honest: they show the *unrepaired* clause
(`MergePolicy.parent`) admitting exactly what the repaired one forbids. -/

/-- **Keyedness after a deletion is exactly keyedness on the surviving keys** — the mirror of
`A4.Semantics.deleteSet_some_imp` for the two-sided predicate (`Keyed d D` is `∀ y val, D y = some
val → val = d y`, whose body *does* mention `val`; the direction that matters is the restriction,
because BM.15 shrinks the key set before the predicate is checked). -/
theorem keyed_deleteSet_iff (d : Labels G s) (M : DS G s) (T : Finset (Fin G.n)) :
    Keyed d (DS.deleteSet M T) ↔ ∀ y val, M y = some val → y ∉ T → val = d y := by
  constructor
  · intro h y val hy hyT
    exact h y val (by rw [DS.deleteSet_of_notMem M T y hyT]; exact hy)
  · intro h y val hy
    by_cases hyT : y ∈ T
    · rw [DS.deleteSet_mem M T y hyT] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    · rw [DS.deleteSet_of_notMem M T y hyT] at hy
      exact h y val hy hyT

/-- **The merge seam, restricted off the child's settled set.**  `A4.KeyLabFloor.keyed_merge` needs
`KeyedCarry` at *every* parent key.  After ★BM.15 the settled keys are deleted, so the carry is only
needed where it can still be observed — this is the whole content of "no `KeyedCarry` hypothesis on
settled keys". -/
theorem keyed_merge_off_settled {D₁ D₂ : DS G s} {d₁ d₂ : Labels G s} {T : Finset (Fin G.n)}
    (h₁ : Keyed d₁ D₁) (h₂ : Keyed d₂ D₂)
    (hle : ∀ y, d₂ y ≤ d₁ y)
    (hcarry : ∀ y val, D₁ y = some val → D₂ y = none → y ∉ T → d₂ y = val) :
    ∀ y val, DS.merge D₁ D₂ y = some val → y ∉ T → val = d₂ y := by
  intro y val hy hyT
  rw [DS.merge_eq] at hy
  cases hd₁ : D₁ y with
  | none =>
    cases hd₂ : D₂ y with
    | none =>
      rw [hd₁, hd₂, DS.mergeVal_none_left] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    | some ν =>
      rw [hd₁, hd₂, DS.mergeVal_none_left] at hy
      exact (Option.some.inj hy).symm.trans (h₂ y ν hd₂)
  | some μ =>
    cases hd₂ : D₂ y with
    | none =>
      rw [hd₁, hd₂, DS.mergeVal_none_right] at hy
      exact (Option.some.inj hy).symm.trans (hcarry y μ hd₁ hd₂ hyT).symm
    | some ν =>
      rw [hd₁, hd₂, DS.mergeVal_some] at hy
      have hνμ : ν ≤ μ := by rw [h₂ y ν hd₂, h₁ y μ hd₁]; exact hle y
      rw [min_eq_right hνμ] at hy
      exact (Option.some.inj hy).symm.trans (h₂ y ν hd₂)

/-- **Mirror of `A4.KeyLabFloor.keyed_istep` at the repaired engine, with no `KeyedCarry` on
settled keys.**  The `hcarry` hypothesis carries the extra `y ∉ settledSet fo'.evts`: a parent key
the child settled is deleted at BM.15 and never re-read, so its stale value cannot break keyedness.
This is the direct gain of the engine patch — `KeyLabFloor`'s induction had to assume the premise
at *every* remainder key, which is false (`Counterexample.carry_fails`). -/
theorem keyed_istepFS {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStepFS t B l st st' c fo')
    (hpar : Keyed st.d st.D) (hchild : Keyed fo'.d' fo'.D)
    (hle : ∀ y, fo'.d' y ≤ st.d y)
    (hcarry : ∀ y val, st.D y = some val → fo'.D y = none → y ∉ settledSet fo'.evts →
      fo'.d' y = val) :
    Keyed st'.d st'.D := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hD1eq : D1 = DS.deleteSet st.D Si := hpull.2.1
  have hD1 : Keyed st.d D1 := by
    rw [hD1eq]; exact keyed_deleteSet hpar Si
  have hM : Keyed fo'.d' D2 := by
    rw [hmerge]
    refine (keyed_deleteSet_iff fo'.d' (DS.merge D1 fo'.D) (settledFinset fo')).mpr ?_
    refine keyed_merge_off_settled hD1 hchild hle ?_
    intro y val hy hy' hyT
    have hyD : st.D y = some val := by
      by_cases hyS : y ∈ Si
      · rw [hD1eq, DS.deleteSet_mem st.D Si y hyS] at hy
        exact absurd hy.symm (Option.some_ne_none val)
      · rw [hD1eq, DS.deleteSet_of_notMem st.D Si y hyS] at hy
        exact hy
    exact hcarry y val hyD hy' (fun hset => hyT (mem_settledFinset.mpr hset))
  have hsweep' : Keyed d3 D3 := by
    conv => lhs; rw [show d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 from congrArg Prod.fst hsweep]
    conv => rhs; rw [show D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 from congrArg Prod.snd hsweep]
    exact keyed_sweepEvts B Bi fo'.evts _ _ hM
  exact keyed_fold_insert J.toList sel d3 D3 hsweep'

/-- **Mirror of `A4.Transitive.loopBoundInv_istep` at the repaired engine**, with the merged floor
transported across BM.15 by `fixStale_ge`.  `LoopBoundInv` is the invariant `A4.ReturnClauses`,
`A4.LowKeyClosure` and `A4.ValueBpChain` all consume; BM.15 only drops keys, so the floor is
inherited and no clause changes shape. -/
theorem loopBoundInv_istepFS (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStepFS t B l st st' c fo')
    (hble : fo'.B' ≤ c.B)
    (hchild : ∀ y val, fo'.D y = some val → fo'.B' ≤ val) (hinv : LoopBoundInv st) :
    LoopBoundInv st' := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hK : fo'.B' ≤ Bi := by
    rw [hc] at hble
    exact hble
  have hD2 : Ge fo'.B' D2 := by
    rw [hmerge]
    exact fixStale_ge fo'.B' D1 fo'
      (ge_merge (ge_of_le hK (fun y val hy => pullRun_floor hpull hy)) hchild)
  have hD3 : GOrM fo'.B' D3 (J.toList.map fun j => Mint.mk (sel j) (d3 (sel j))) := by
    have hd3 : D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 := by rw [← hsweep]
    rw [hd3]
    exact gOrM_sweepEvts fo'.evts fo'.d' D2
      (fun y val hy => Or.inl (hD2 y val hy)) hK
  refine gOrM_fold_insert J.toList sel (fun j => d3 (sel j))
    (J.toList.map fun j => Mint.mk (sel j) (d3 (sel j))) D3 hD3
    (fun j hj => List.mem_map_of_mem hj)

/-- **(2c) at the shrunk key set, with `T_X := 0` and `Prem` unchanged.**  The three facts
`A4.ReturnClauses`' clause (2c) reduction reads at a step output, in the repaired engine:

1. **`keys(𝒟) ∩ U_i = ∅`** — the child's settled vertices are not keys of the return store.  This
   is `T_X`'s stale-key channel *emptied*: the duplicate settlement it used to count cannot be
   routed through `𝒟`, so `T_X` is charged against the mints alone.
2. **`U` is still the append** — no settlement is removed or rewritten by BM.15.
3. **`Prem` is untouched** — the premature account is exactly the final iteration's line-29 mints
   against `B'`, and BM.15 edits only the `𝒟` clause, so clause (2b)/(2c) keep their form.

(The `SweepsSpare` (k3) residue is a hypothesis here exactly as in `istepFS_no_settled_key`: a
*gated* re-insert at a settled vertex is excluded by arithmetic, not by the clause.) -/
theorem clause2c_shrunk_keys {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStepFS t B l st st' c fo')
    (hspare : ∀ lo : WLab G s, SweepsSpare B lo fo'.evts (settledFinset fo')) :
    (∀ y, y ∈ settledSet fo'.evts → st'.D y = none) ∧
      (∀ x, x ∈ settledSet (callOut st').evts ↔ x ∈ settledSet st.evts ∨
        x ∈ settledSet fo'.evts) ∧
      (∀ x val, (callOut st').Premature x val ↔
        Mint.mk x val ∈ st'.mints ∧ val < fo'.B') := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  refine ⟨fun y hy => istepFS_no_settled_key (t := t) (B := B) (l := l) (st := st) (st' := _)
    (c := c) (fo' := fo')
    ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel, rfl⟩
    hspare hy, ?_, ?_⟩
  · intro x
    show x ∈ settledSet (st.evts ++ fo'.evts) ↔ _
    rw [settledSet_append, Set.mem_union]
  · intro x val
    exact Iff.rfl

/-! ## 6. Negative pins: what the unrepaired clause admits and the repaired one forbids -/

/-- **The `KeyLabFloor` counterexample is a real step of the *unrepaired* engine**: the
`MergePolicy.parent` instance of `IStepWith` at the bad state `stK'`.  Nothing is retracted — the
state, the pull, the child `Run` and the failing `LabFloor` are `A4.KeyLabFloor`'s — only the
step's BM.14 clause is the historical one. -/
theorem parent_step_admits_counterexample :
    IStepWith (MergePolicy.parent (G := Counterexample.Gcx) (s := Counterexample.v0)) 1 ⊤ 1
      Counterexample.st Counterexample.stK' Counterexample.childC Counterexample.foK :=
  Counterexample.istep_key

/-- **…and it is not a step of the engine.**  BM.15 deletes `v1` (the child settled it and never
re-keyed it), so no derivation of `IStep` can land in `stK'`, whose store still keys `v1`.  This is
the omission `A4.KeyLabFloor` measured, closed. -/
theorem not_istep_key :
    ¬ IStep (G := Counterexample.Gcx) (s := Counterexample.v0) 1 ⊤ 1
      Counterexample.st Counterexample.stK' Counterexample.childC Counterexample.foK := by
  classical
  intro h
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  have hsett : Counterexample.v1 ∈ settledFinset Counterexample.foK := by
    rw [mem_settledFinset, Counterexample.settledSet_foK]
    exact Set.mem_univ _
  have hD2 : D2 Counterexample.v1 = none := by
    rw [hmerge]
    exact DS.deleteSet_mem _ _ _ hsett
  have hBi : Bi = Counterexample.lam2 :=
    (congrArg CallEntry.B hc).symm
  have hD3 : D3 Counterexample.v1 = none := by
    have hD3eq : D3 =
        (sweepEvts ⊤ Bi Counterexample.foK.evts Counterexample.foK.d' D2).2 :=
      congrArg Prod.snd hsweep
    rw [hD3eq, hBi, Counterexample.foK_d', Counterexample.sweepEvts_foK]
    exact hD2
  have hJempty : J = ∅ := by
    rw [hJ]
    ext j
    exact ⟨fun hj => absurd hj (Finset.notMem_empty j),
      fun hj => absurd hj (Finset.notMem_empty j)⟩
  have hD : Counterexample.stK'.D Counterexample.v1 = none := by
    have hDeq : Counterexample.stK'.D
        = J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3 :=
      congrArg RState.D hst'
    have hJnil : J.toList = [] := by
      rw [hJempty]; simp
    rw [hDeq, hJnil]
    exact hD3
  rw [Counterexample.stK'_D_v1] at hD
  exact absurd hD (by simp)

/-- **The unrepaired engine re-frontiers a settled vertex.**  `stK'.D` keys `v1`, which `foK`
settled (`settledSet foK.evts = univ`), and the whole store is below `⊤` — so the very next pull
hands `v1` back as a seed.  This is `T_X`'s duplicate channel, alive exactly where BM.15 is absent,
and it is what `istepFS_next_seeds_avoid_settled` rules out for the repaired engine. -/
theorem pullRun_stK' :
    pullRun 1 Counterexample.stK'.D ⊤ ({Counterexample.v1} : Finset (Fin Counterexample.Gcx.n)) ⊤
      (DS.deleteSet Counterexample.stK'.D {Counterexample.v1}) := by
  refine ⟨?_, rfl, le_top, Or.inl rfl,
    Or.inr ⟨Counterexample.v1, Counterexample.lam2, Counterexample.stK'_D_v1, WithTop.coe_lt_top _⟩,
    by rw [Finset.card_singleton]⟩
  ext y
  constructor
  · intro hy
    have hy' : y = Counterexample.v1 := by simpa using hy
    subst hy'
    exact mem_belowKeys.mpr
      ⟨Counterexample.lam2, Counterexample.stK'_D_v1, WithTop.coe_lt_top _⟩
  · intro hy
    obtain ⟨v, hv, -⟩ := (mem_belowKeys (D := Counterexample.stK'.D) (x := ⊤)).mp hy
    simpa using Counterexample.stK'_sole_key hv

/-- **`istepFS_next_seeds_avoid_settled` fails for `MergePolicy.parent`.**  The repaired-engine
statement is *not* a theorem of the unrepaired clause: at the counterexample the next pull's seed
set is `{v1}`, a settled vertex.  Together with `parent_step_admits_counterexample` /
`not_istep_key` this pins the engine patch as a real semantic change, not a re-annotation. -/
theorem next_seeds_avoid_settled_fails_parent :
    ¬ (∀ (st st' : RState Counterexample.Gcx Counterexample.v0 0)
        (c : CallEntry Counterexample.Gcx Counterexample.v0) (fo' : CallOut Counterexample.Gcx Counterexample.v0),
        IStepWith (MergePolicy.parent (G := Counterexample.Gcx) (s := Counterexample.v0)) 1 ⊤ 1
          st st' c fo' →
        ∀ (cap : ℕ) (Bd x : WLab Counterexample.Gcx Counterexample.v0)
          (S' : Finset (Fin Counterexample.Gcx.n)) (D' : DS Counterexample.Gcx Counterexample.v0),
          pullRun cap st'.D Bd S' x D' → ∀ y, y ∈ S' → y ∉ settledSet fo'.evts) := by
  intro hall
  have hseed := hall Counterexample.st Counterexample.stK' Counterexample.childC Counterexample.foK
    Counterexample.istep_key 1 ⊤ ⊤ {Counterexample.v1}
    (DS.deleteSet Counterexample.stK'.D {Counterexample.v1}) pullRun_stK'
    Counterexample.v1 (Finset.mem_singleton_self _)
  exact hseed (by rw [Counterexample.settledSet_foK]; exact Set.mem_univ _)

/-! ## 7. Signatures and axiom audit -/

#check @IStepFS
#check @istepFS_def
#check @ge_deleteSet
#check @ge_deleteSet_iff
#check @keyHalf_deleteSet_iff
#check @fixStale_keyHalf_iff
#check @fixStale_ge
#check @fixStale_ge_iff
#check @fixStale_no_settled_key
#check @fixStale_kills_counterexample
#check @SweepsSpare
#check @sweepsSpare_nil
#check @fold_insert_spares
#check @istepFS_no_settled_key
#check @istepFS_next_seeds_avoid_settled
#check @keyed_deleteSet_iff
#check @keyed_merge_off_settled
#check @keyed_istepFS
#check @loopBoundInv_istepFS
#check @clause2c_shrunk_keys
#check @parent_step_admits_counterexample
#check @not_istep_key
#check @pullRun_stK'
#check @next_seeds_avoid_settled_fails_parent

#print axioms istepFS_def
#print axioms ge_deleteSet
#print axioms ge_deleteSet_iff
#print axioms keyHalf_deleteSet_iff
#print axioms fixStale_keyHalf_iff
#print axioms fixStale_ge
#print axioms fixStale_no_settled_key
#print axioms fixStale_kills_counterexample
#print axioms fold_insert_spares
#print axioms istepFS_no_settled_key
#print axioms istepFS_next_seeds_avoid_settled
#print axioms keyed_deleteSet_iff
#print axioms keyed_merge_off_settled
#print axioms keyed_istepFS
#print axioms loopBoundInv_istepFS
#print axioms clause2c_shrunk_keys
#print axioms parent_step_admits_counterexample
#print axioms not_istep_key
#print axioms pullRun_stK'
#print axioms next_seeds_avoid_settled_fails_parent

end DMSY
end Frontier

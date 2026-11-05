import A4.DrainedClauses
import A4.KeyLabFloor
import A4.LoopBInv

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.NonDrainedBp — `BpChain` at a **non-drained** return

Work package **A4**.  `A4.DrainedClauses` closed clause (2a) `progress` at a return whose loop
exited with `𝒟` drained, and left non-drained exits open.  `A4.KeyLabFloor` localised the
obstruction at the BM.14 merge (`DS.merge` is value-only, the labels are the child's whole
function) and named the repair premise `KeyedCarry` — "a parent key the child did not re-key
keeps its label".  This file proves the non-drained chain, and shows `KeyedCarry` is **not** the
premise the proof needs: the premise is strictly weaker, it is a *label* statement, and it is the
existing `ChildLabelFloor` clause with its carrier widened from the residual pivot groups to
`𝒟`'s keys.

## 1. The invariant is a key-**label** floor, not keyedness

`A4.ValueBpChain` reduced `BpChain` to `LabFloor` (key-label floor + `LoopBInv`) and
`A4.KeyLabFloor` showed the key half is not an invariant of the V5 engine by refuting
`KeyedCarry`.  But the key half `LabKeyFloor bp d D := ∀ y val, D y = some val → bp ≤ d y` does
not need `Keyed` (value = label): every store operation is either *keyed* (a relaxation writes
the label and the key together, a mint inserts at the current label) or *inert* (the pull, the
BM.15 deletion, an unreached key).  For the keyed operations the value **is** the label, so the
floor holds at it; for a key the parent keeps and the child never re-keyed, the value is stale
and the label is the child's, so the floor must be supplied about the **label alone**.

That is the whole difference, and it is what makes the seam provable: a stale *high* value beside
a lowered label is harmless as long as the lowered label still clears the running bound.  So the
premise needed is

  `ChildKeyLabelFloor st fo' := ∀ y val, st.D y = some val → y ∉ settledSet fo'.evts →
     fo'.B' ≤ fo'.d' y`

— verbatim `A4.LoopBInv.ChildLabelFloor` with `y ∈ st.pl j` replaced by `y ∈ DS.keys st.D`, the
same gate (`fo'.B'`, cap-safe) and the same exclusion (BM.15 removes the settled ones).  No
`KeyedCarry`, no re-keying of the merged store, no `PullSpec` change: the pulled keys are not
where the hazard lives.

## 2. What is proved

* `labKeyFloor_merge_delete`, `sweepEvts_labKeyFloor`, `labKeyFloor_fold_insert` — the three
  store laws (§2–§3): the merge/delete seam consumes `ChildKeyFloor` at the child's own keys and
  `ChildKeyLabelFloor` at the parent's; the (E2) sweep never writes below its gate `Bi ≥ fo'.B'`;
  the BM.23 mint fold inserts at the *current* label, where `LoopBInv` holds.
* `labKeyFloor_istep` — **one iteration preserves the key-label floor** (§4), from those three
  laws and `LoopBInv fo'.B' st'`.  `IStep`-level: no reachability, no drainedness.
* `iloop_bpChain_nondrained`, `recur_bpChain_nondrained` — the loop threads the two state
  invariants (§5) and `BpChain` follows from two premise families, kept separate: the uniform
  per-step clause bundle `StepClauses` (§1) and the per-child `SeedChildLabFloor` (spelled
  exactly as `A4.BpMonotonicity`/`A4.KeyLabFloor` leave it — the capped-leaf `dMin` half).
  The seed half and the child half of the chain therefore rest on different premises; this file
  supplies the former.
* `nondrained_tailBP` — at a non-drained exit the returned bound is the **last child's** `B'`
  (BM.24a's other branch), so `BpChain` is exactly what clause (2a) needs there.

## 3. Reachable states vs arbitrary `IStep` states

`A4.BpMonotonicity` §3's counterexamples (`istep_bot`, `valueForm_fails`) are `IStep`-only
states, and `A4.KeyLabFloor` §4's is a `MergePolicy.parent` step — not an output of the engine's
`IStep` (`A4.FixStale.not_istep_key`).  Everything here is stated at `IStep` (hence at every
reachable run) and consumes no reachability hypothesis, so it applies to every run, drained or
not.  The distinction pays off at the *satisfiability* of `ChildKeyLabelFloor`: §6 shows `IStep`
alone cannot give it (an `IStep` state may carry an unsound label), §7 shows a genuine `Run`
child *does* — `run_walk`'s `Sound` is the exact ingredient `IStep` lacks — leaving the residue
`Prem = ∅` at the child (Theorem-T-strength, as for `LoopBInv`/`ChildLabelFloor`) plus the cone
closure `hcone`, which is a statement about reachability and so is out of reach of any `PullSpec`
clause.

No `sorry`, no `admit`, no new axiom.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The invariant and the single cross-call clause -/

/-- **Key-label floor**: at every key of `𝒟`, the state's label clears the state's running
bound.  This is the key half of `A4.ValueBpChain.LabFloor`, stated at `(bp, d, D)` rather than at
a state so it can be threaded through the store operations.  It is *label*-flavoured on purpose:
`Keyed` (value = label) is not an invariant of the engine, but this is (`labKeyFloor_istep`). -/
def LabKeyFloor (bp : WLab G s) (d : Labels G s) (D : DS G s) : Prop :=
  ∀ y val, D y = some val → bp ≤ d y

/-- The state-level form, the key half of `LabFloor`. -/
def LabKeyInv {p : ℕ} (st : RState G s p) : Prop := LabKeyFloor st.bp st.d st.D

/-- `Keyed` + the value floor give the key-label floor outright — the bridge
`A4.KeyLabFloor.keyLabFloor_of_keyed_ge` at the `(bp, d, D)` triple. -/
theorem labKeyFloor_of_keyed_ge {bp : WLab G s} {d : Labels G s} {D : DS G s}
    (hk : Keyed d D) (hge : ∀ y val, D y = some val → bp ≤ val) : LabKeyFloor bp d D := by
  intro y val hy
  rw [← hk y val hy]
  exact hge y val hy

/-- **The cross-call clause the non-drained chain needs**: a parent key that survives the
iteration (the child did not settle it) carries a post-child label clearing the child's returned
bound.  This is `A4.LoopBInv.ChildLabelFloor` with its carrier widened from the residual pivot
groups to `𝒟`'s keys — the only edit to the interface this file needs. -/
def ChildKeyLabelFloor {p : ℕ} (st : RState G s p) (fo' : CallOut G s) : Prop :=
  ∀ y val, st.D y = some val → y ∉ settledSet fo'.evts → fo'.B' ≤ fo'.d' y

/-- **The child's own key-label floor**: clause (2b) at the child's returned store, read at the
labels (Prem-free).  This is the join induction's IH on the child call, and it is what the merge
keeps when the child *did* re-key the vertex. -/
def ChildKeyFloor (fo' : CallOut G s) : Prop :=
  ∀ y val, fo'.D y = some val → fo'.B' ≤ fo'.d' y

/-- **The per-step child clauses**: one bundle, quantified over every `IStep` at level `t` the way
`A4.LoopBInv.LabelFloorHyp` and `A4.BpMonotonicity.StepSeedFloor` are, so the loop induction never
has to name an iteration's child.  `hble` is the child's bound law (`run_le_bound`), the second
and third are this file's, the fourth is the lane's existing `ChildLabelFloor`. -/
def StepClauses (t : ℕ) : Prop :=
  ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p) (c : CallEntry G s)
    (fo' : CallOut G s), IStep t B l st st' c fo' →
    fo'.B' ≤ c.B ∧ ChildKeyLabelFloor st fo' ∧ ChildKeyFloor fo' ∧ ChildLabelFloor st fo'

/-! ## 2. The merge seam (§2 of the module docstring)

`A4.KeyLabFloor.keyed_merge` had to conclude `Keyed` at the merged store, which needs value =
label at the parent's surviving keys.  The floor version needs only the label, so the same seam
is discharged by `ChildKeyLabelFloor` and the child's own `ChildKeyFloor` — the merge's two
sources, one clause each. -/

/-- **The BM.14 merge + ★BM.15 deletion preserves the key-label floor.**  Two sources: a key the
child re-keyed takes the child's value *and* the child's label (`hchild`); a key the child left
alone keeps the parent's value and must clear the bound at its label (`hcarry`).  The deletion
`T = settledFinset fo'` removes keys, so it cannot create a violation (`y ∉ T` is all it
contributes). -/
theorem labKeyFloor_merge_delete {bp : WLab G s} {dp : Labels G s} {D₁ Dp D₀ : DS G s}
    {S' T : Finset (Fin G.n)} (hD₁ : D₁ = DS.deleteSet D₀ S')
    (hchild : ∀ y val, Dp y = some val → bp ≤ dp y)
    (hcarry : ∀ y val, D₀ y = some val → Dp y = none → y ∉ T → bp ≤ dp y) :
    LabKeyFloor bp dp (DS.deleteSet (DS.merge D₁ Dp) T) := by
  intro y val hy
  have hyT : y ∉ T := by
    intro hyT
    rw [DS.deleteSet_mem (DS.merge D₁ Dp) T y hyT] at hy
    exact absurd hy.symm (Option.some_ne_none val)
  have hm : DS.merge D₁ Dp y = some val := by
    rw [DS.deleteSet_of_notMem (DS.merge D₁ Dp) T y hyT] at hy
    exact hy
  rw [DS.merge_eq] at hm
  cases hdp : Dp y with
  | some ν => exact hchild y ν hdp
  | none =>
    cases hD₁y : D₁ y with
    | none =>
      rw [hD₁y, DS.mergeVal_none_left, hdp] at hm
      exact absurd hm.symm (Option.some_ne_none val)
    | some μ =>
      have hval : val = μ := by
        rw [hD₁y, hdp, DS.mergeVal_none_right] at hm
        exact (Option.some.inj hm).symm
      have hD₀ : D₀ y = some val := by
        rw [hD₁, DS.deleteSet_eq] at hD₁y
        by_cases hyS : y ∈ S'
        · rw [if_pos hyS] at hD₁y
          exact absurd hD₁y (by simp)
        · rw [if_neg hyS] at hD₁y
          rw [hval]
          exact hD₁y
      exact hcarry y val hD₀ hdp hyT

/-! ## 3. The (E2) sweep and the mint fold

`A4.LoopBInv.sweepEvts_label_cases` gives the gate fact (`unchanged ∨ ≥ lo`); what the key floor
additionally needs is that the sweep's *store* moves only where its label moves — then the
untouched keys are covered by the input floor and the touched ones by the gate. -/

/-- One gated relaxation preserves the key-label floor, provided the gate's lower bound clears
it: an accepted relaxation writes `cand ≥ lo ≥ bp` as the label at `dst` (and keys `dst` at that
value), every other key keeps both its value and its label. -/
theorem relaxGate_labKeyFloor {B lo bp : WLab G s} {d : Labels G s} {D : DS G s} {e : Fin G.m}
    (h : LabKeyFloor bp d D) (hlo : bp ≤ lo) :
    LabKeyFloor bp (relaxGate B lo d D e).1 (relaxGate B lo d D e).2 := by
  intro y val hy
  unfold relaxGate at hy ⊢
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos hc] at hy ⊢
    by_cases hdst : y = G.dst e
    · subst hdst
      show bp ≤ (Function.update d (G.dst e) (ext (d (G.src e)) e)) (G.dst e)
      rw [Function.update_self]
      exact hlo.trans hc.1
    · show bp ≤ (Function.update d (G.dst e) (ext (d (G.src e)) e)) y
      rw [Function.update_of_ne hdst]
      have hy' : DS.insert D (G.dst e) (ext (d (G.src e)) e) y = some val := hy
      rw [DS.insert_of_ne D (G.dst e) _ hdst] at hy'
      exact h y val hy'
  · rw [if_neg hc] at hy ⊢
    exact h y val hy

/-- The gate sweep over one settled vertex's out-edges. -/
theorem sweepGate_labKeyFloor (B lo bp : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) :
    ∀ (d : Labels G s) (D : DS G s), LabKeyFloor bp d D → bp ≤ lo →
      LabKeyFloor bp (sweepGate B lo u es d D).1 (sweepGate B lo u es d D).2 := by
  induction es with
  | nil => intro d D h _; exact h
  | cons e es ih =>
    intro d D h hlo
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (relaxGate_labKeyFloor h hlo) hlo
    · rw [if_neg hs, if_neg hs]
      exact ih d D h hlo

/-- The settlement-log sweep (`IStep`'s `sweepEvts B Bi fo'.evts fo'.d' D2`). -/
theorem sweepEvts_labKeyFloor (B lo bp : WLab G s) (evts : List (SettlementEvent G)) :
    ∀ (d : Labels G s) (D : DS G s), LabKeyFloor bp d D → bp ≤ lo →
      LabKeyFloor bp (sweepEvts B lo evts d D).1 (sweepEvts B lo evts d D).2 := by
  induction evts with
  | nil => intro d D h _; exact h
  | cons ev hd ih =>
    intro d D h hlo
    exact ih _ _ (sweepGate_labKeyFloor B lo bp ev.v (List.finRange G.m) d D h hlo) hlo

/-- **The BM.23 mint fold preserves the key-label floor.**  `DS.insert` at `(sel j, d3 (sel j))`
moves no label, so the untouched keys keep the sweep's floor and the mint's own key is floored by
`LoopBInv st'` (`sel j ∈ resid j = st'.pl j`).  This is why the mint needs no value premise. -/
theorem labKeyFloor_fold_insert {ι : Type} (js : List ι) (f : ι → Fin G.n) (bp : WLab G s)
    (d : Labels G s) (D : DS G s) (h : LabKeyFloor bp d D) (hs : ∀ j ∈ js, bp ≤ d (f j)) :
    LabKeyFloor bp d (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D) := by
  induction js generalizing D with
  | nil => exact h
  | cons j0 js ih =>
    rw [List.foldl_cons]
    refine ih (DS.insert D (f j0) (d (f j0))) ?_ (fun j hj => hs j (List.mem_cons_of_mem _ hj))
    intro y val hy
    by_cases hyj : y = f j0
    · subst hyj
      exact hs j0 List.mem_cons_self
    · exact h y val (by rwa [DS.insert_of_ne D (f j0) _ hyj] at hy)

/-! ## 4. One iteration preserves the key-label floor -/

/-- **`IStep` preserves the key half of `LabFloor`.**  Premises: the child's bound law, the two
cross-call clauses of §1, and `LoopBInv` at the step's output (which
`A4.LoopBInv.istep_bInv_of_le` supplies from the same bound law plus the lane's existing
`ChildLabelFloor`).  `Keyed`-at-the-output is *not* required, and neither is `KeyedCarry`. -/
theorem labKeyFloor_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hble : fo'.B' ≤ c.B) (hkey : ChildKeyLabelFloor st fo') (hck : ChildKeyFloor fo')
    (hgrp : LoopBInv fo'.B' st') : LabKeyInv st' := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hble' : fo'.B' ≤ Bi := by rw [hc] at hble; exact hble
  -- (a) the merge seam, at the pull remainder
  have hfl : LabKeyFloor fo'.B' fo'.d' D2 := by
    rw [hmerge]
    refine labKeyFloor_merge_delete (D₀ := st.D) (S' := Si) hpull.2.1
      (fun y val hy => hck y val hy) ?_
    intro y val hy hy' hyT
    exact hkey y val hy (fun hmem => hyT (mem_settledFinset.mpr hmem))
  -- (b) the (E2) sweep, gated at `Bi ≥ fo'.B'`
  have hsw : LabKeyFloor fo'.B' d3 D3 := by
    have h0 := sweepEvts_labKeyFloor B Bi fo'.B' fo'.evts fo'.d' D2 hfl hble'
    rwa [← hsweep] at h0
  -- (c) the BM.23 mint fold
  refine labKeyFloor_fold_insert J.toList sel fo'.B' d3 D3 hsw ?_
  intro j hj
  exact hgrp j (sel j) (hsel j (Finset.mem_toList.mp hj)).1

/-! ## 5. The loop: the invariant threads, and `BpChain` follows -/

/-- `mkInit` satisfies the key floor: the only keys are the pivot seeds, each stored at its own
entry label, and `initBp` is below every one of them. -/
theorem labKeyInv_init (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n) :
    LabKeyInv (mkInit e fo piv) := by
  intro y val hy
  have hval : val = fo.d' y := initD'_fresh _ _ _ _ hy
  obtain ⟨j, hj⟩ := initD'_keys fo.d' piv DS.empty
    (fun y val hy => absurd hy (Ne.symm (Option.some_ne_none val))) y val hy
  have h1 : (mkInit e fo piv).bp ≤ fo.d' (piv j) := initBp_le _ _ _ _
  have h2 : (mkInit e fo piv).d y = fo.d' y := rfl
  rw [h2, hj]
  exact h1

/-- The key floor is `A4.ValueBpChain.LabFloor`'s first conjunct, so the seed label floor of
`A4.ValueBpChain` applies verbatim once `LoopBInv` is in hand. -/
theorem labFloor_of_labKeyInv {p : ℕ} {st : RState G s p} (hk : LabKeyInv st)
    (hg : LoopBInv st.bp st) : LabFloor st :=
  ⟨hk, hg⟩

/-- **The loop threads the invariant and delivers `BpChain`.**  `IStep` only ever consumes the
*state* invariants (`LabKeyInv`, `LoopBInv`) plus the uniform per-step child clauses, so the
induction carries them; the `BpChain` link at each step is the seed label floor composed with the
child's own (R5)-shape floor — the single premise `SeedChildLabFloor`, unchanged. -/
theorem iloop_bpChain_nondrained (t : ℕ) (B : WLab G s) (l : ℕ)
    (hsc : StepClauses (G := G) (s := s) t) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf → LabKeyInv st → LoopBInv st.bp st →
      (∀ q ∈ qs, SeedChildLabFloor q.1 q.2) → BpChain st.bp qs := by
  intro p st stf qs hloop
  induction hloop with
  | exit _ => intro _ _ _; exact trivial
  | step hne hgq hstep hrest ih =>
    intro hk hl hseed
    obtain ⟨hble, hkey, hck, hgrp⟩ := hsc B l _ _ _ _ hstep
    have hfloor := labFloor_of_labKeyInv hk hl
    have hseedFloor := seedLabFloor_of_labFloor hstep hfloor
    have hcons := List.forall_mem_cons.mp hseed
    have hinv := istep_bInv_of_le t B l hstep hble hgrp
    refine ⟨?_, ?_⟩
    · rw [← istep_bp hstep]
      exact istep_bp_mono_lab hstep hseedFloor hcons.1
    · rw [← istep_bp hstep]
      exact ih (labKeyFloor_istep hstep hble hkey hck hinv) hinv hcons.2

/-- **`BpChain` at a non-drained `l > 0` spine**, from the loop's own initial state: this is the
statement `A4.ReturnClauses`' `LoopProg` needs, with no drainedness hypothesis (compare
`A4.DrainedClauses.callOut_tail_progress_of_drained`, which needs `𝒟` drained and no chain). -/
theorem recur_bpChain_nondrained (t : ℕ) (e : CallEntry G s) (fo : FPOut G s)
    (piv : Fin fo.p → Fin G.n) (st0 stf : RState G s fo.p)
    (qs : List (CallEntry G s × CallOut G s))
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
    (hst0 : st0 = mkInit e fo piv) (hloop : ILoop t e.B e.l st0 qs stf)
    (hsc : StepClauses (G := G) (s := s) t)
    (hseed : ∀ q ∈ qs, SeedChildLabFloor q.1 q.2) : BpChain st0.bp qs := by
  subst hst0
  exact iloop_bpChain_nondrained t e.B e.l hsc hloop (labKeyInv_init e fo piv)
    (loopBInv_init e fo piv hpiv) hseed

/-- **At a non-drained exit the returned bound is the last child's.**  BM.24a has two branches;
`A4.DrainedClauses` used the drained one (`tailBP = B`), this is the other.  So the `BpChain` of
`recur_bpChain_nondrained` is exactly what clause (2a) `progress` consumes at a non-drained
return — the loop's settlements are floored by the chain, not by the call's own bound. -/
theorem nondrained_tailBP (B : WLab G s) {p : ℕ} (st : RState G s p) (hne : ¬ DS.IsEmpty st.D) :
    tailBP B st = st.bp :=
  tailBP_of_not_isEmpty B st hne


/-! ## 6. The premise is *necessary*, not merely sufficient

`labKeyFloor_istep` takes `ChildKeyLabelFloor`.  This section shows that clause cannot be dropped:
on the lane's `Gcx` there is a genuine `IStep` whose every *other* premise holds (the child's
bound law, the child's own key floor, `LoopBInv` at the output) and whose output violates the key
floor.  The step is the non-drained hazard in its smallest form — `v0` is pulled at separator
`lam1`, so `v1` is a **pull remainder** key (value `lam2`), the child (whose store is empty, so it
re-keys nothing) lowers `v1`'s label to `lam0` = `↑[]`, and the BM.14 merge keeps the parent's
`lam2` beside that label.  ★BM.15 does not delete `v1` — the child settled nothing.

What the child is *not* allowed to be is a genuine `Run`: the state is an `IStep` state, and this
file's `BpChain` therefore rests on `ChildKeyLabelFloor` being a clause about the child call —
exactly the status `A4.LoopBInv.ChildLabelFloor` already has (see its `not_bInv_of_premature`). -/

namespace Counterexample

/-- The hazard state: `v1` keyed at `lam2` with the label `lam2` (the key floor holds here). -/
noncomputable def stN : RState Gcx v0 0 where
  d := fun v => if v = v1 then lam2 else lam0
  D := DS.insert (DS.insert DS.empty v0 lam0) v1 lam2
  evts := []
  bp := lam0
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

theorem stN_D_v0 : stN.D v0 = some lam0 := by
  show DS.insert (DS.insert DS.empty v0 lam0) v1 lam2 v0 = some lam0
  rw [DS.insert_of_ne _ v1 lam2 (by decide : v0 ≠ v1)]
  exact insert_none_key DS.empty v0 lam0 rfl

theorem stN_D_v1 : stN.D v1 = some lam2 := by
  show DS.insert (DS.insert DS.empty v0 lam0) v1 lam2 v1 = some lam2
  exact insert_none_key _ v1 lam2
    (insert_none_other DS.empty v0 v1 lam0 (by decide) rfl)

/-- The child's return: bound `lam1`, empty store, every label `lam0` — it re-keys nothing. -/
noncomputable def foN : CallOut Gcx v0 where
  B' := lam1
  evts := []
  D := DS.empty
  d' := fun _ => lam0
  mints := []
  pfin := 0
  Pfin := fun j => j.elim0

/-- The entry the iteration produces. -/
noncomputable def cN : CallEntry Gcx v0 where
  B := lam1
  S := {v0}
  l := 0
  d := stN.d

/-- The state after the iteration: `v1` survives at `lam2` with the label `lam0`. -/
noncomputable def stN' : RState Gcx v0 0 where
  d := foN.d'
  D := DS.merge (DS.deleteSet stN.D {v0}) DS.empty
  evts := []
  bp := lam1
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

theorem belowKeys_stN : belowKeys (G := Gcx) (s := v0) stN.D lam1 = {v0} := by
  ext y
  rw [mem_belowKeys, Finset.mem_singleton]
  constructor
  · rintro ⟨v, hv, hlt⟩
    rcases eq_v0_or_v1 y with rfl | rfl
    · rfl
    · rw [stN_D_v1] at hv
      rw [← Option.some.inj hv] at hlt
      exact absurd hlt (not_lt.mpr coe_e0_lt_coe_e0_e1.le)
  · intro hy
    subst hy
    exact ⟨lam0, stN_D_v0, coe_nil_lt_coe_e0⟩

/-- The pull at separator `lam1` (the call bound): `v0` is pulled, `v1` is the remainder. -/
theorem pull_stN : pullRun (G := Gcx) (s := v0) (pullCap 2 1) stN.D lam1 {v0} lam1
    (DS.deleteSet stN.D {v0}) := by
  refine ⟨belowKeys_stN.symm, rfl, le_rfl, Or.inl rfl,
    Or.inr ⟨v0, lam0, stN_D_v0, coe_nil_lt_coe_e0⟩, ?_⟩
  show ({v0} : Finset (Fin Gcx.n)).card ≤ pullCap 2 1
  rw [Finset.card_singleton]
  decide

theorem expand_stN : expand (s := v0) stN.d stN.pl stN.piv {v0} lam1 = {v0} := by
  rw [expand, biUnion_fin0, Finset.union_empty]

theorem stN'_D_v1 : stN'.D v1 = some lam2 := by
  show DS.merge (DS.deleteSet stN.D {v0}) DS.empty v1 = some lam2
  rw [DS.merge_eq, DS.deleteSet_of_notMem stN.D {v0} v1 (by decide), stN_D_v1]
  rfl

/-- **The step.**  A genuine `IStep`: pull, BM.12 expansion (vacuous), BM.14 merge, ★BM.15
deletion (a no-op — the child settled nothing), the (E2) sweep (no events), no mints. -/
theorem istep_stN : IStep (G := Gcx) (s := v0) 2 lam1 1 stN stN' cN foN := by
  refine ⟨{v0}, lam1, DS.deleteSet stN.D {v0}, (fun j => j.elim0), ∅,
    (fun j => j.elim0), DS.merge (DS.deleteSet stN.D {v0}) DS.empty, foN.d',
    DS.merge (DS.deleteSet stN.D {v0}) DS.empty, pull_stN, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [CallEntry.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · show ({v0} : Finset (Fin Gcx.n)) = expand stN.d stN.pl stN.piv {v0} lam1
      rw [expand_stN]
    · show (1 - 1 : ℕ) = 0
      rfl
  · intro j
    exact j.elim0
  · ext j
    exact ⟨fun h => absurd h (Finset.notMem_empty j), fun _ => j.elim0⟩
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [RState.mk.injEq]
    refine ⟨rfl, ?_, rfl, rfl, funext fun j => j.elim0, funext fun j => j.elim0, ?_⟩
    · show DS.merge (DS.deleteSet stN.D {v0}) DS.empty =
        List.foldl (fun D j => DS.insert D ((fun j => j.elim0) j) (foN.d' ((fun j => j.elim0) j)))
          (DS.merge (DS.deleteSet stN.D {v0}) DS.empty) (∅ : Finset (Fin 0)).toList
      rw [show ((∅ : Finset (Fin 0)).toList) = [] from by simp]
      rfl
    · simp [stN']

/-- **`ChildKeyLabelFloor` is exactly the missing premise.**  Every other premise of
`labKeyFloor_istep` holds at this step, and the conclusion fails: `v1` keeps the parent's `lam2`
beside the child's `lam0`, below the new running bound `lam1`.  So no engine-internal argument can
replace the clause, and no `PullSpec` clause about the separator can either — the failing key is
the pull *remainder*, never pulled. -/
theorem childKeyLabelFloor_necessary :
    IStep (G := Gcx) (s := v0) 2 lam1 1 stN stN' cN foN ∧ foN.B' ≤ cN.B ∧
      ChildKeyFloor foN ∧ LoopBInv foN.B' stN' ∧ ¬ LabKeyInv stN' ∧
      ¬ ChildKeyLabelFloor stN foN := by
  refine ⟨istep_stN, le_rfl, ?_, ?_, ?_, ?_⟩
  · intro y val hy
    exact absurd hy.symm (Option.some_ne_none val)
  · intro j
    exact j.elim0
  · intro h
    have h1 : stN'.bp ≤ stN'.d v1 := h v1 lam2 stN'_D_v1
    have h2 : stN'.d v1 = lam0 := rfl
    rw [h2] at h1
    exact absurd h1 (not_le.mpr coe_nil_lt_coe_e0)
  · intro h
    have h1 : foN.B' ≤ foN.d' v1 := h v1 lam2 stN_D_v1 (by simp [settledSet, foN])
    show False
    exact absurd h1 (not_le.mpr coe_nil_lt_coe_e0)

end Counterexample


/-! ## 7. Where the clause stands for a genuine `Run` child

§6 shows `ChildKeyLabelFloor` is not `IStep`-internal.  It is, however, *derivable* at a real `Run`
child, and the derivation names exactly what `IStep` lacks: **label soundness**.  `IStep` never
constrains `fo'.d'` (its witnesses use only `fo'.D`, `fo'.evts`, `fo'.B'`; `A4.BpMonotonicity` §3
made that precise), so an `IStep` state can carry an unsound label — §6's witness does
(`lam0 < dis v1 = lam1`).  A `Run` cannot: `run_walk` gives `WalkInv out.d'`, hence
`Sound out.d' = ∀ y, dis y ≤ d' y` (`WalkInv.sound`).

With soundness in hand, clause (2c)'s identity closes the clause for every vertex of the child's
`Ũ`, and Prem-freeness removes the carve-out.  Two residues remain, both named:

1. **`Prem = ∅` at the child** (Theorem T's statement, `A0.Lemma37.TheoremT`) — the same
   Theorem-T-strength residue `A4.LoopBInv`'s `LoopBInv`/`ChildLabelFloor` already carry
   (`not_bInv_of_premature`).
2. **Cone closure** `hcone`: a vertex below the child's returned bound is reachable from the
   child's *seed set*.  Clause (2c) is stated at `Ũ(B, S)` — the child's own cone — while a
   parent key need only be reachable from the top-level source; `hcone` is the gap between those
   two cones.  It is a statement about **reachability**, not about labels or stores, which is why
   no `PullSpec` (or separator) clause can supply it. -/

/-- **`ChildKeyLabelFloor` at a genuine `Run` child**, from its `Lemma37Concl`, its label
soundness, Prem-freeness and the cone closure.  The `st.D` hypothesis of the clause is a carrier
restriction only — nothing in the proof reads the parent's store. -/
theorem childKeyLabelFloor_of_concl {t : ℕ} {c : CallEntry G s} {fo' : CallOut G s} {p : ℕ}
    (st : RState G s p) (hconcl : Lemma37Concl (Full t) c fo') (hw : WalkInv fo'.d')
    (hprem : ∀ x val, ¬ fo'.Premature x val)
    (hcone : ∀ y, dis (s := s) y < fo'.B' → ∃ x ∈ c.S, OnPath (s := s) x y) :
    ChildKeyLabelFloor st fo' := by
  intro y val _ hns
  by_contra hle
  have hlt : fo'.d' y < fo'.B' := lt_of_not_ge hle
  have hdis : dis (s := s) y < fo'.B' := (hw.sound y).trans_lt hlt
  have hyU : y ∈ Utilde fo'.B' (c.S : Set (Fin G.n)) := ⟨hdis, hcone y hdis⟩
  have hyK : y ∉ fo'.carveKeys c.S := by
    intro hk
    obtain ⟨⟨v, hv⟩, _⟩ := hk
    exact hprem y v hv
  have hyU' : y ∈ (fo'.U : Set (Fin G.n)) := by
    rw [hconcl.identity]
    exact ⟨hyU, hyK⟩
  exact hns hyU'

/-- The same, transported to `A4.BpMonotonicity`'s label-floor shape: at a non-drained child the
`SeedChildLabFloor` half is *not* what this file consumes (that stays `A4.KeyLabFloor`'
`bpChain_of_full_children` regime); this records that the two halves of the non-drained chain rest
on different premises — the seed half on `ChildKeyLabelFloor` (above), the child half on (R5). -/
theorem childKeyLabelFloor_of_run {t : ℕ} {e c : CallEntry G s} {fo' : CallOut G s} {p : ℕ}
    (st : RState G s p) (hrun : Run t c fo') (hd : WalkInv c.d)
    (hconcl : Lemma37Concl (Full t) c fo') (hprem : ∀ x val, ¬ fo'.Premature x val)
    (hcone : ∀ y, dis (s := s) y < fo'.B' → ∃ x ∈ c.S, OnPath (s := s) x y) :
    ChildKeyLabelFloor st fo' :=
  childKeyLabelFloor_of_concl st hconcl (run_walk t hrun hd) hprem hcone

/-! ## 8. Signature and axiom audit -/

#check @labKeyFloor_istep
#check @iloop_bpChain_nondrained
#check @recur_bpChain_nondrained
#check @nondrained_tailBP
#check @childKeyLabelFloor_of_run
#check @labKeyFloor_merge_delete
#check @sweepEvts_labKeyFloor

#print axioms labKeyFloor_merge_delete
#print axioms sweepEvts_labKeyFloor
#print axioms labKeyFloor_fold_insert
#print axioms labKeyFloor_istep
#print axioms labKeyInv_init
#print axioms iloop_bpChain_nondrained
#print axioms recur_bpChain_nondrained
#print axioms nondrained_tailBP
#print axioms Counterexample.istep_stN
#print axioms Counterexample.childKeyLabelFloor_necessary
#print axioms childKeyLabelFloor_of_concl
#print axioms childKeyLabelFloor_of_run

end DMSY
end Frontier

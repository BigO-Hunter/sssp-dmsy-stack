import A4.ValueBpChain

/-!
# Frontier.DMSY.KeyLabFloor — the key half of `LabFloor`, its one cross-call premise, and the
counterexample that kills it

`A4.ValueBpChain` reduces `BpChain` to `LabFloor` (`A4.ValueBpChain.LabFloor` = key-label floor +
`LoopBInv`) and names the bridge `KeyLabEq` ("a key's stored value *is* its label") as *not
derivable*, by exhibiting the single state `Counterexample.stv` where the value floor holds and
the key label floor fails.  That refutation is a *state*, not a mechanism, and it is off the
engine's own data (`stv` keys `v1` at `lam2` with the unrelated label `lam0`).  This file settles
the question the lane needs answered:

> can the key half of `LabFloor` be *derived* — carried as a step invariant — from the engine's
> own insert/merge/pull semantics, or is it blocked by a specific semantic seam?

## §1–§2 The mechanical half **is** derivable, and keyedness (not the floor) is the invariant

Every *store* operation of the engine writes a label and the key that carries it in one breath:
`relaxGate` writes `Function.update d dst cand` and `DS.insert D dst cand` together
(`relaxGate_write_key`), and the same holds for the settlement sweep, for `seedIns` (insert at the
*current* label) and for the line-29 mint fold.  Hence

  `Keyed d D := ∀ y val, D y = some val → val = d y`

is preserved by every layer *inside* a call (`keyed_deleteSet`, `keyed_relaxGate`,
`keyed_sweepEvts`, `keyed_seedIns`, `keyed_fold_insert`) — with **no** honesty or floor hypothesis,
because keyedness *implies* the one-sided honesty `d y ≤ val` that the keep-min reasoning consumes.
Keyedness is exactly what `LabFloor`'s key half needs: with `Keyed` and the value floor (which
`A4.Transitive` does prove: `LoopBoundInv` + `MintFloor` ⟹ `Ge`) the label floor is
`bp ≤ val = d y` (`keyLabFloor_of_keyed_ge`).  So the key half is neither a distance fact nor a
completeness fact and needs no `LiveFloor`: it is "keyedness + the value floor".

## §3 The single seam: the call boundary, where `DS.merge` is value-only and the labels wholesale

One iteration's store is `sweepEvts … (DS.merge D1 fo'.D) …`, while one iteration's labels are
`d3` = the *child's whole label function* `fo'.d'` (swept).  The child's labels enter at *every*
vertex; the child's store enters only at the child's *keys*.  So keyedness survives an iteration
iff the two agree on the parent's surviving keys — the single premise

  `KeyedCarry st fo' := ∀ y val, st.D y = some val → fo'.D y = none → fo'.d' y = val`

("a parent key the child did not re-key keeps its label").  `keyed_merge` proves this is
*precisely* the merge's need, in its sharp form: it is stated for an arbitrary `D₁`, so a
pulled-away key's label is irrelevant, as it must be.  `keyed_istep` threads it through a step and
`keyLabFloor_istep` delivers the key half of `LabFloor st'` from `Keyed` + `KeyedCarry` + the
value floor `Ge st'.bp st'.D`.

## §4 `KeyedCarry` is **false**, and the child behind the failure is a genuine `Run`

On the lane's own `Gcx` (`0 → 1`, self-loop at `1`): the state
`st = ⟨d = {v0 ↦ lam0, v1 ↦ lam2}, D = {v0 ↦ lam0, v1 ↦ lam2}, bp = lam0⟩` satisfies
`LabFloor st` **and** `Keyed st.d st.D` **and** `LoopBoundInv st` **and** `MintFloor st`.  The pull
at separator `lam2` takes only `v0` (a key at value `= x` is not `< x`), so `v1` **is** a parent
remainder key the child does not re-key.  The child `foK` is the return of a **real `Run`**
(`child_run` = `Run.base` over `leafRun`, a real `baseRun` whose two loop iterations pull `v0`,
relax `v1 ↦ lam1` and pull `v1`): a *full* leaf (`D_final = ∅`, `B'⁺ = c.B = lam2`, no mints,
Prem-free), returning `v1 ↦ lam1` — a sound walk label (`child_label_sound`) strictly **below** its
own returned bound (`child_label_lt_bound`).  The step is a real **pre-repair** step — the
`MergePolicy.parent` instance of `IStepWith`, i.e. BM.14 without ★BM.15 (`istep_key`; the engine's
own `IStep` no longer admits it, see `A4.FixStale`'s negative pin) — and then

* the **value** floor at `st'` holds (`stK'_ge`: `st'.D = {v1 ↦ lam2}`, `bp = lam2`);
* the **group** half holds (`stK'_loopBInv`, `p = 0`);
* the **key** half fails: `lam2 ≤ st'.d v1 = lam1` is false (`stK'_not_keyLabFloor`), so
  `LabFloor st'` is false (`stK'_not_labFloor`).

The immediate chain link still holds at that step (`st.bp = lam0 ≤ lam2 = st'.bp`), so the damage
is one step removed and is not cosmetic: `stK'_seed_hazard` records that the surviving key — the
*only* key `st'` holds (`stK'_sole_key`) — carries a label `lam1` strictly below the running bound
`lam2`, so the next iteration that pulls it hands `SeedLabFloor` a seed it cannot clear.  That is
the (J2)-second-conjunct hazard of the paper's B-monotonicity argument, in the one place the
engine holds no label/value identity.

So the child is as accurate as a walk label at `v1` can be; no strengthening of the child's *own*
clauses repairs the seam, because the failure is the parent keeping a **stale high value** at a
vertex the child *improved*, and `DS.merge` has no way to carry the label.  `KeyedCarry` fails
there (`carry_fails`), and with it the whole induction: `labFloor_not_istep` is the one-statement
form — stated for the **unrepaired** BM.14 clause (`MergePolicy.parent`), which is what it
documents.  The repaired engine (`IStep`, ★BM.15) deletes the settled key instead, so this state
is not one of its outputs (`A4.FixStale.not_istep_key`) and the omission this section measures is
closed there.

## §5 `SeedChildLabFloor`: `B' = c.B` gives it outright; `dMin` cannot give the capped case

`seedChildLabFloor_of_bound_eq` proves (R5) from `co.B' = c.B` + `CallPre.inRange` + nonempty `S`,
and the engine's two sources of `B' = c.B` are packaged: a drained base leaf (Lemma 3.1\*'s
dichotomy, `seedChildLabFloor_base_of_full'`) and a drained loop store at `l > 0`
(BM.24a, `callOut_Bp_of_loop_empty`).  That is the scope in which `BpChain` is available:
`bpChain_of_full_children` (seed label floors from `LabFloor` + (R5) from `B' = c.B`).  The
*capped* (partial) case — the one `ValueBpChain` defers to `dMin` — cannot be closed there:
`v5Cap` is a **min** (`v5Cap_le_pull`), so the cap only *lowers* the returned bound, while (R5)
needs an **upper** bound on a seed's label, and every `dMin` fact is a *lower* bound at a *key*
(`dMin_le_of_mem`).  `seedChildLabFloor_mono` is the monotonicity kernel ("(R5) is monotone in the
bound upwards, so only lowering it can destroy witnesses"), and `capped_leaf_no_seedBound` is an
explicit pair with the value floor at the returned store and `B'` strictly below *every* seed's
label, i.e. the capped shape on which no `dMin` consequence yields (R5).  (That pair is a
`CallOut`-level shape; it is not asserted to be a `baseRun` output.)

## §6 Verdict

Under `A4.ValueBpChain`'s own invariant, **no**: `LabFloor` is not an invariant of the V5 engine
(§4), so `bpChain_of_chainLabFloor` cannot be fed by the engine and `BpChain` is not derivable
from it.  Under the *corrected* invariant `Keyed` (+ the value floor), the engine supports the
chain's label half through `keyLabFloor_istep` — but only under `KeyedCarry`, which is a statement
about the call boundary that the engine's own semantics do not make: `Run.recur` gives the child
only the parent's *labels* (`c = ⟨B_i, …, l-1, st.d⟩`) and merges back only the child's *store*
(`DS.merge D1 fo'.D`), so a `Run` cannot be constrained by the parent's key set.

**Minimal semantic repair** (one change, at the merge): make the store carry the label it is read
with, i.e. re-key the merged store from the current labels —
`D2 := fun y => (DS.merge D1 fo'.D y).map (fun _ => fo'.d' y)` — or, equivalently, require
`fo'.d' y = st.d y ∨ fo'.D y ≠ none` for every parent key `y` (the child must return, at its own
new label, any parent key whose label it moved).  Under that discipline `KeyedCarry` holds by
construction for the remainder keys and `keyed_istep` closes; on this engine the unrepaired merge
is the only place where a label and the value it belongs to can part company across a call.
Two-sided insert honesty *at the separator alone* is not enough: the failing key is a **pull
remainder**, never inserted at the step's separator — it must be re-keyed at the **merge**.

No `sorry`/`admit`, no new axiom (`#print axioms` at the end: `propext`, `Classical.choice`,
`Quot.sound` only), `a4_joint` not assumed, no peer file modified.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. Store keyedness, and where the engine maintains it -/

/-- **Store keyedness**: a key's stored value *is* its label.  `A4.Structural`'s honesty gives the
one-sided `d y ≤ val`; this is the other direction — the bridge `A4.ValueBpChain.KeyLabEq` names
as missing, stated at the `(d, D)` pair rather than at a state. -/
def Keyed (d : Labels G s) (D : DS G s) : Prop := ∀ y val, D y = some val → val = d y

/-- Keyedness implies one-sided honesty (the keep-min reasoning's input). -/
theorem Keyed.honest {d : Labels G s} {D : DS G s} (h : Keyed d D) :
    ∀ y val, D y = some val → d y ≤ val :=
  fun y val hy => le_of_eq (h y val hy).symm

/-- `Delete` preserves keyedness (labels are untouched). -/
theorem keyed_deleteSet {d : Labels G s} {D : DS G s} (h : Keyed d D)
    (T : Finset (Fin G.n)) : Keyed d (DS.deleteSet D T) := by
  intro y val hy
  by_cases hyT : y ∈ T
  · rw [DS.deleteSet_mem D T y hyT] at hy
    exact absurd hy.symm (Option.some_ne_none val)
  · rw [DS.deleteSet_of_notMem D T y hyT] at hy
    exact h y val hy

/-- **The engine's insert law**: an (E2)-gated relaxation that moves a label *also* keys the
vertex at exactly the new label.  Nothing else in the engine writes `d`. -/
theorem relaxGate_write_key {B lo : WLab G s} {d : Labels G s} {D : DS G s} {e : Fin G.m}
    (hd : ∀ y val, D y = some val → d y ≤ val) {y : Fin G.n}
    (hch : (relaxGate B lo d D e).1 y ≠ d y) :
    (relaxGate B lo d D e).2 y = some ((relaxGate B lo d D e).1 y) := by
  simp only [relaxGate] at hch ⊢
  by_cases h : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · simp only [if_pos h] at hch ⊢
    have hy : y = G.dst e := by
      by_contra hne
      exact hch (by rw [Function.update_of_ne hne])
    subst hy
    rw [Function.update_self]
    rw [DS.insert_self]
    cases hD : D (G.dst e) with
    | none => simp [DS.mergeVal_none_left]
    | some μ =>
      rw [DS.mergeVal_some]
      have hμ : ext (d (G.src e)) e ≤ μ := h.2.2.trans (hd _ μ hD)
      rw [min_eq_right hμ]
  · simp only [if_neg h] at hch
    exact absurd rfl hch

/-- Keyedness is preserved by one gated relaxation. -/
theorem keyed_relaxGate {B lo : WLab G s} {d : Labels G s} {D : DS G s} {e : Fin G.m}
    (hk : Keyed d D) : Keyed (relaxGate B lo d D e).1 (relaxGate B lo d D e).2 := by
  intro y val hy
  simp only [relaxGate] at hy ⊢
  by_cases h : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · simp only [if_pos h] at hy ⊢
    by_cases hyy : y = G.dst e
    · subst hyy
      rw [DS.insert_self] at hy
      rw [Function.update_self]
      cases hD : D (G.dst e) with
      | none =>
        rw [hD, DS.mergeVal_none_left] at hy
        exact (Option.some.inj hy).symm
      | some μ =>
        rw [hD, DS.mergeVal_some] at hy
        have hμ : ext (d (G.src e)) e ≤ μ := h.2.2.trans (le_of_eq (hk _ μ hD).symm)
        rw [min_eq_right hμ] at hy
        exact (Option.some.inj hy).symm
    · rw [DS.insert_of_ne D (G.dst e) _ hyy] at hy
      rw [Function.update_of_ne hyy]
      exact hk y val hy
  · simp only [if_neg h] at hy ⊢
    exact hk y val hy

/-- Keyedness is preserved by the settlement sweep. -/
theorem keyed_sweepGate (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) :
    ∀ (d : Labels G s) (D : DS G s), Keyed d D →
      Keyed (sweepGate B lo u es d D).1 (sweepGate B lo u es d D).2 := by
  induction es with
  | nil => intro d D hk; exact hk
  | cons e es ih =>
    intro d D hk
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (keyed_relaxGate hk)
    · rw [if_neg hs, if_neg hs]
      exact ih d D hk

/-- Keyedness is preserved across a whole settlement log (the step's own sweep). -/
theorem keyed_sweepEvts (B lo : WLab G s) (evts : List (SettlementEvent G)) :
    ∀ (d : Labels G s) (D : DS G s), Keyed d D →
      Keyed (sweepEvts B lo evts d D).1 (sweepEvts B lo evts d D).2 := by
  induction evts with
  | nil => intro d D hk; exact hk
  | cons ev evts ih =>
    intro d D hk
    exact ih _ _ (keyed_sweepGate B lo ev.v (List.finRange G.m) d D hk)

/-- An insert at the *current* label preserves keyedness (`seedIns`, the mint fold). -/
theorem keyed_insert_label {d : Labels G s} {D : DS G s} (hk : Keyed d D) (x : Fin G.n) :
    Keyed d (DS.insert D x (d x)) := by
  intro y val hy
  by_cases hyx : y = x
  · subst hyx
    rw [DS.insert_self] at hy
    cases hD : D y with
    | none => rw [hD] at hy; exact (Option.some.inj hy).symm
    | some μ =>
      rw [hD, DS.mergeVal_some] at hy
      have hμ : μ = d y := hk y μ hD
      rw [min_eq_right (le_of_eq hμ.symm)] at hy
      exact (Option.some.inj hy).symm
  · rw [DS.insert_of_ne D x (d x) hyx] at hy
    exact hk y val hy

/-- `seedIns` preserves keyedness (labels are untouched; every insert is at the current label). -/
theorem keyed_seedIns (bp B : WLab G s) (S : Finset (Fin G.n)) :
    ∀ (d : Labels G s) (D : DS G s), Keyed d D →
      Keyed (seedIns bp B S d D).1 (seedIns bp B S d D).2 := by
  intro d D hk
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => exact hk
  | cons x xs ih =>
    rw [List.foldl_cons]
    by_cases hg : bp ≤ d x ∧ d x < B
    · rw [if_pos hg]
      exact ih d (DS.insert D x (d x)) (keyed_insert_label hk x)
    · rw [if_neg hg]
      exact ih d D hk

/-- The line-29 mint fold preserves keyedness. -/
theorem keyed_fold_insert {ι : Type} (js : List ι) (f : ι → Fin G.n) (d : Labels G s) :
    ∀ (D : DS G s), Keyed d D →
      Keyed d (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D) := by
  induction js with
  | nil => intro D hk; exact hk
  | cons j0 js ih =>
    intro D hk
    rw [List.foldl_cons]
    exact ih _ (keyed_insert_label hk (f j0))

/-- **The merge seam.**  `DS.merge` keeps the smaller *value*; the labels after the merge are the
child's.  Keyedness therefore survives the merge exactly when the child re-keyed every parent key
whose label it moved — `hcarry`.  Stated for an arbitrary `D₁`, which is the sharp form inside an
iteration: `D₁` is the pull remainder, so a *pulled* key's label is irrelevant (the key is gone).
The third hypothesis is the engine's label monotonicity (`A4.Structural.run_le`). -/
theorem keyed_merge {D₁ : DS G s} {D₂ : DS G s} {d₁ d₂ : Labels G s}
    (h₁ : Keyed d₁ D₁) (h₂ : Keyed d₂ D₂)
    (hle : ∀ y, d₂ y ≤ d₁ y)
    (hcarry : ∀ y val, D₁ y = some val → D₂ y = none → d₂ y = val) :
    Keyed d₂ (DS.merge D₁ D₂) := by
  intro y val hy
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
      exact (Option.some.inj hy).symm.trans (hcarry y μ hd₁ hd₂).symm
    | some ν =>
      rw [hd₁, hd₂, DS.mergeVal_some] at hy
      have hνμ : ν ≤ μ := by rw [h₂ y ν hd₂, h₁ y μ hd₁]; exact hle y
      rw [min_eq_right hνμ] at hy
      exact (Option.some.inj hy).symm.trans (h₂ y ν hd₂)

/-! ## 2. The key half from keyedness + the value floor -/

/-- **The key half of `LabFloor`, from keyedness and the value floor.**  `Ge` is what
`A4.Transitive` proves for a step output (`LoopBoundInv` + `MintFloor`), so this is the whole
logical distance between the value form and the label form. -/
theorem keyLabFloor_of_keyed_ge {p : ℕ} {st : RState G s p}
    (hk : Keyed st.d st.D) (hge : Ge st.bp st.D) :
    ∀ y val, st.D y = some val → st.bp ≤ st.d y := by
  intro y val hy
  rw [← hk y val hy]
  exact hge y val hy

/-! ## 3. Threading keyedness through one iteration -/

/-- **One iteration preserves keyedness**, given the child's keyedness, the engine's label
monotonicity and the single cross-call premise `KeyedCarry`. -/
theorem keyed_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hpar : Keyed st.d st.D) (hchild : Keyed fo'.d' fo'.D)
    (hle : ∀ y, fo'.d' y ≤ st.d y)
    (hcarry : ∀ y val, st.D y = some val → fo'.D y = none → fo'.d' y = val) :
    Keyed st'.d st'.D := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  have hD1eq : D1 = DS.deleteSet st.D Si := hpull.2.1
  have hD1 : Keyed st.d D1 := by
    rw [hD1eq]; exact keyed_deleteSet hpar Si
  have hM : Keyed fo'.d' (DS.merge D1 fo'.D) :=
    keyed_merge hD1 hchild hle (fun y val hy hy' => by
      have hyD : st.D y = some val := by
        by_cases hyS : y ∈ Si
        · rw [hD1eq, DS.deleteSet_mem st.D Si y hyS] at hy
          exact absurd hy.symm (Option.some_ne_none val)
        · rw [hD1eq, DS.deleteSet_of_notMem st.D Si y hyS] at hy
          exact hy
      exact hcarry y val hyD hy')
  have hsweep' : Keyed d3 D3 := by
    conv => lhs; rw [show d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 from congrArg Prod.fst hsweep]
    conv => rhs; rw [show D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 from congrArg Prod.snd hsweep]
    rw [hmerge]
    exact keyed_sweepEvts B Bi fo'.evts _ _ (keyed_deleteSet hM (settledFinset fo'))
  exact keyed_fold_insert J.toList sel d3 D3 hsweep'

/-- **The key half of `LabFloor` after one iteration**, on the exact premises `keyed_istep`
consumes plus the value floor `Ge st'.bp st'.D` (which `A4.Transitive.loopBoundInv_istep` +
`A4.LemmaV.ge_of_loopBoundInv` supply).  This is the best possible closure: §4 shows the
`hcarry` premise is not derivable. -/
theorem keyLabFloor_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hpar : Keyed st.d st.D) (hchild : Keyed fo'.d' fo'.D)
    (hle : ∀ y, fo'.d' y ≤ st.d y)
    (hcarry : ∀ y val, st.D y = some val → fo'.D y = none → fo'.d' y = val)
    (hge : Ge st'.bp st'.D) :
    ∀ y val, st'.D y = some val → st'.bp ≤ st'.d y :=
  keyLabFloor_of_keyed_ge (keyed_istep h hpar hchild hle hcarry) hge


namespace Counterexample


/-! ## The child: a real `baseRun` that completes `v1` -/

theorem st_d_v0 : st.d v0 = lam0 := by
  show (if v0 = v0 then lam0 else lam2) = lam0
  rw [if_pos rfl]

theorem st_d_v1 : st.d v1 = lam2 := by
  show (if v1 = v0 then lam0 else lam2) = lam2
  rw [if_neg (by decide : ¬ (v1 = v0))]

theorem ext_lam0_e0 : ext (lam0 : WLab Gcx v0) e0 = lam1 := by
  simp [lam0, lam1, ext_coe]

theorem ext_lam1_e1 : ext (lam1 : WLab Gcx v0) e1 = lam2 := by
  simp [lam1, lam2, ext_coe]

noncomputable def dL : Labels Gcx v0 := Function.update st.d v1 lam1

theorem dL_v1 : dL v1 = lam1 := by simp [dL]

theorem dL_v0 : dL v0 = lam0 := by
  rw [dL, Function.update_of_ne (by decide : v0 ≠ v1)]
  exact st_d_v0

theorem relaxEdge_e0 (D : DS Gcx v0) : relaxEdge lam2 st.d D e0 = (dL, DS.insert D v1 lam1) := by
  unfold relaxEdge
  rw [src_e0, dst_any, st_d_v0, ext_lam0_e0, st_d_v1]
  rw [if_pos ⟨coe_e0_lt_coe_e0_e1.le, coe_e0_lt_coe_e0_e1⟩]
  rfl

theorem relaxEdge_e1 (D : DS Gcx v0) : relaxEdge lam2 dL D e1 = (dL, D) := by
  unfold relaxEdge
  rw [src_e1, dst_any, dL_v1, ext_lam1_e1]
  rw [if_neg]
  intro h
  exact absurd h.1 (not_le.mpr coe_e0_lt_coe_e0_e1)

theorem sweep_v0 (D : DS Gcx v0) : sweep lam2 v0 (List.finRange Gcx.m) st.d D
    = (dL, DS.insert D v1 lam1) := by
  have h01 : (List.finRange Gcx.m : List (Fin Gcx.m)) = [e0, e1] := by decide
  have h1 : ¬ (Gcx.src e1 = v0) := by rw [src_e1]; decide
  simp only [h01, sweep, h1, if_false, src_e0, relaxEdge_e0, dL, if_true]

theorem sweep_v1 (D : DS Gcx v0) : sweep lam2 v1 (List.finRange Gcx.m) dL D = (dL, D) := by
  have h01 : (List.finRange Gcx.m : List (Fin Gcx.m)) = [e0, e1] := by decide
  have h0 : ¬ (Gcx.src e0 = v1) := by rw [src_e0]; decide
  simp only [h01, sweep, h0, if_false, src_e1, relaxEdge_e1, if_true]

/-! ### The leaf's store -/

noncomputable def leafD0 : DS Gcx v0 := initD ({v0} : Finset (Fin Gcx.n)) st.d
noncomputable def aP0 : DS Gcx v0 := DS.deleteSet leafD0 {v0}
noncomputable def leafD1 : DS Gcx v0 := DS.insert aP0 v1 lam1
noncomputable def aP1 : DS Gcx v0 := DS.deleteSet leafD1 {v1}

theorem leafD0_v0 : leafD0 v0 = some lam0 := by
  show (if v0 ∈ ({v0} : Finset (Fin Gcx.n)) then some (st.d v0) else none) = some lam0
  rw [if_pos (Finset.mem_singleton_self v0), st_d_v0]

theorem leafD0_other {y : Fin Gcx.n} (hy : y ≠ v0) : leafD0 y = none := by
  show (if y ∈ ({v0} : Finset (Fin Gcx.n)) then some (st.d y) else none) = none
  rw [if_neg (by simpa using hy)]

theorem aP0_none (y : Fin Gcx.n) : aP0 y = none := by
  rw [aP0]
  by_cases hy : y ∈ ({v0} : Finset (Fin Gcx.n))
  · rw [DS.deleteSet_mem leafD0 {v0} y hy]
  · rw [DS.deleteSet_of_notMem leafD0 {v0} y hy]
    exact leafD0_other (by simpa using hy)

theorem leafD1_v1 : leafD1 v1 = some lam1 := by
  rw [leafD1, DS.insert_self, aP0_none, DS.mergeVal_none_left]

theorem leafD1_other {y : Fin Gcx.n} (hy : y ≠ v1) : leafD1 y = none := by
  rw [leafD1, DS.insert_of_ne aP0 v1 lam1 hy, aP0_none]

theorem aP1_none (y : Fin Gcx.n) : aP1 y = none := by
  rw [aP1]
  by_cases hy : y ∈ ({v1} : Finset (Fin Gcx.n))
  · rw [DS.deleteSet_mem leafD1 {v1} y hy]
  · rw [DS.deleteSet_of_notMem leafD1 {v1} y hy]
    exact leafD1_other (by simpa using hy)

theorem aP1_isEmpty : DS.IsEmpty aP1 := aP1_none

/-! ### The leaf's loop -/

noncomputable def leafSt0 : BState Gcx v0 := ⟨st.d, leafD0, [], lam2⟩
noncomputable def leafSt1 : BState Gcx v0 := ⟨dL, leafD1, [⟨.basePull, v0⟩], lam2⟩
noncomputable def leafSt2 : BState Gcx v0 :=
  ⟨dL, aP1, [⟨.basePull, v0⟩, ⟨.basePull, v1⟩], lam2⟩

theorem iter_v0 : iter lam2 v0 lam2 leafSt0 = leafSt1 := by
  simp [iter, leafSt0, leafSt1, aP0, leafD1, sweep_v0]

theorem iter_v1 : iter lam2 v1 lam2 leafSt1 = leafSt2 := by
  simp [iter, leafSt1, leafSt2, aP1, sweep_v1]

theorem leafLoop1 : Loop 1 lam2 (0 + iterCost v1 leafSt1) leafSt1 leafSt2 := by
  have hne1 : ¬ DS.IsEmpty leafD1 := fun h => by
    have h1 := h v1
    rw [leafD1_v1] at h1
    exact absurd h1 (by simp)
  have hexit : Loop 1 lam2 0 (iter lam2 v1 lam2 leafSt1) (iter lam2 v1 lam2 leafSt1) :=
    Loop.exit (Or.inl (by rw [iter_v1]; exact aP1_isEmpty))
  have hpull := Loop.pull (t := 1) (B := lam2) (c := 0) (st := leafSt1)
    (st' := iter lam2 v1 lam2 leafSt1) v1 lam1 lam2 hne1 (by simp [leafSt1])
    leafD1_v1 coe_e0_lt_coe_e0_e1 le_rfl (fun y μ hy hD => by
      simp only [leafSt1] at hD
      rw [leafD1_other hy] at hD
      exact absurd hD (by simp)) (Or.inl rfl) hexit
  rwa [iter_v1] at hpull

theorem leafLoop :
    Loop 1 lam2 ((0 + iterCost v1 leafSt1) + iterCost v0 leafSt0) leafSt0 leafSt2 := by
  have hne0 : ¬ DS.IsEmpty leafD0 := fun h => by
    have h0 := h v0
    rw [leafD0_v0] at h0
    exact absurd h0 (by simp)
  have hinner : Loop 1 lam2 (0 + iterCost v1 leafSt1) (iter lam2 v0 lam2 leafSt0) leafSt2 := by
    rw [iter_v0]; exact leafLoop1
  have hpull := Loop.pull (t := 1) (B := lam2) (c := 0 + iterCost v1 leafSt1) (st := leafSt0)
    (st' := leafSt2) v0 lam0 lam2 hne0 (by decide : ([] : List (SettlementEvent Gcx)).length ≤ 1 ^ 3)
    leafD0_v0 lam0_lt_lam2 le_rfl (fun y μ hy hD => by
      simp only [leafSt0] at hD
      rw [leafD0_other hy] at hD
      exact absurd hD (by simp)) (Or.inl rfl) hinner
  exact hpull

/-! ### The leaf's `baseRun` and its `Run` -/

noncomputable def bout : BaseOut Gcx v0 where
  B'_pull := lam2
  B'_plus := lam2 ⊓ dMin lam2 aP1
  D_final := aP1
  evts := [⟨.basePull, v0⟩, ⟨.basePull, v1⟩]
  d' := dL

theorem bout_B' : bout.B'_plus = lam2 := by
  show lam2 ⊓ dMin lam2 aP1 = lam2
  rw [dMin_eq_of_isEmpty lam2 aP1_isEmpty, inf_idem]

theorem leafBaseRun : baseRun 1 ⟨lam2, ({v0} : Finset (Fin Gcx.n)), st.d, initD {v0} st.d⟩ bout := by
  exact ⟨_, leafSt2, by simpa [leafSt0, leafD0] using leafLoop, by simp [bout, leafSt2]⟩

theorem leafRun : Run 1 ⟨lam2, ({v0} : Finset (Fin Gcx.n)), 0, st.d⟩ (baseOut bout) :=
  Run.base rfl leafBaseRun

/-! ### The parent's step: the merge keeps the stale value and imports the child's label -/

noncomputable def foK : CallOut Gcx v0 := baseOut bout

noncomputable def childC : CallEntry Gcx v0 := ⟨lam2, ({v0} : Finset (Fin Gcx.n)), 0, st.d⟩

noncomputable def D2K : DS Gcx v0 := DS.merge (DS.deleteSet st.D {v0}) aP1

noncomputable def stK' : RState Gcx v0 0 where
  d := foK.d'
  D := D2K
  evts := st.evts ++ foK.evts
  bp := foK.B'
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

theorem foK_B' : foK.B' = lam2 := bout_B'

theorem foK_D : foK.D = aP1 := rfl

theorem foK_d' : foK.d' = dL := rfl

theorem foK_mints : foK.mints = [] := by
  simp [foK, bout, baseOut]

theorem foK_evts : foK.evts = [⟨.basePull, v0⟩, ⟨.basePull, v1⟩] := rfl

/-- The step's gate is `lam2`: settling `v0` recovers `lam1`, which the gate rejects. -/
theorem sweepGate_v0_reject (D : DS Gcx v0) :
    sweepGate ⊤ lam2 v0 (List.finRange Gcx.m) dL D = (dL, D) := by
  have h01 : (List.finRange Gcx.m : List (Fin Gcx.m)) = [e0, e1] := by decide
  have h1 : ¬ (Gcx.src e1 = v0) := by rw [src_e1]; decide
  have h0 : ¬ (lam2 ≤ ext (dL v0) e0) := by
    rw [dL_v0, ext_lam0_e0]
    exact not_le.mpr coe_e0_lt_coe_e0_e1
  simp [h01, sweepGate, h1, src_e0, relaxGate, h0]

theorem sweepGate_v1_reject (D : DS Gcx v0) :
    sweepGate ⊤ lam2 v1 (List.finRange Gcx.m) dL D = (dL, D) := by
  have h01 : (List.finRange Gcx.m : List (Fin Gcx.m)) = [e0, e1] := by decide
  have h0 : ¬ (Gcx.src e0 = v1) := by rw [src_e0]; decide
  have h1 : ¬ (ext (dL v1) e1 ≤ dL v1) := by
    rw [dL_v1, ext_lam1_e1]
    exact not_le.mpr coe_e0_lt_coe_e0_e1
  simp [h01, sweepGate, h0, src_e1, dst_any, relaxGate, h1]

theorem sweepEvts_foK (D : DS Gcx v0) : sweepEvts ⊤ lam2 foK.evts dL D = (dL, D) := by
  have h : sweepEvts ⊤ lam2 [⟨.basePull, v0⟩, ⟨.basePull, v1⟩] dL D = (dL, D) := by
    simp only [sweepEvts, sweepGate_v0_reject, sweepGate_v1_reject]
  simpa [foK, bout, baseOut] using h

theorem pull_stK :
    pullRun (pullCap 1 1) st.D ⊤ ({v0} : Finset (Fin Gcx.n)) lam2 (DS.deleteSet st.D {v0}) := by
  refine ⟨belowKeys_st.symm, rfl, le_top, Or.inr ⟨v1, lam2, D_v1, rfl⟩,
    Or.inr ⟨v0, lam0, D_v0, lam0_lt_lam2⟩, ?_⟩
  rw [Finset.card_singleton]
  show 1 ≤ pullCap 1 1
  decide

theorem istep_key :
    IStepWith (MergePolicy.parent (G := Gcx) (s := v0)) 1 ⊤ 1 st stK' childC foK := by
  refine ⟨{v0}, lam2, DS.deleteSet st.D {v0}, (fun j => j.elim0), ∅, (fun j => j.elim0),
    D2K, foK.d', D2K, pull_stK, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [CallEntry.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · show ({v0} : Finset (Fin Gcx.n)) = expand st.d st.pl st.piv {v0} lam2
      rw [expand_st]
    · show (1 - 1 : ℕ) = 0
      rfl
  · exact (sweepEvts_foK D2K).symm
  · intro j
    exact j.elim0
  · ext j
    exact ⟨fun h => absurd h (Finset.notMem_empty j), fun _ => j.elim0⟩
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [RState.mk.injEq]
    refine ⟨rfl, ?_, rfl, rfl, rfl, ?_, ?_⟩
    · simp [stK', D2K]
    · funext j
      exact (if_neg (Finset.notMem_empty j)).symm
    · simp [stK']

/-! ### The verdict at `stK'`: the value floor holds, the key label floor fails -/

theorem stK'_D_v1 : stK'.D v1 = some lam2 := by
  show DS.merge (DS.deleteSet st.D {v0}) aP1 v1 = some lam2
  rw [DS.merge_eq, DS.deleteSet_of_notMem st.D {v0} v1 (by simp [v0, v1]), aP1_none, D_v1,
    DS.mergeVal_none_right]

theorem stK'_D_v0 : stK'.D v0 = none := by
  show DS.merge (DS.deleteSet st.D {v0}) aP1 v0 = none
  rw [DS.merge_eq, DS.deleteSet_mem st.D {v0} v0 (by simp), aP1_none, DS.mergeVal_none_left]

theorem stK'_d_v1 : stK'.d v1 = lam1 := dL_v1

theorem stK'_d_v0 : stK'.d v0 = lam0 := dL_v0

theorem stK'_bp : stK'.bp = lam2 := foK_B'

theorem stK'_ge : Ge stK'.bp stK'.D := by
  intro y val hy
  rcases eq_v0_or_v1 y with rfl | rfl
  · rw [stK'_D_v0] at hy
    exact absurd hy (by simp)
  · rw [stK'_D_v1] at hy
    rw [stK'_bp]
    exact le_of_eq (Option.some.inj hy)

theorem stK'_not_keyLabFloor : ¬ ∀ y val, stK'.D y = some val → stK'.bp ≤ stK'.d y := by
  intro h
  have h1 := h v1 lam2 stK'_D_v1
  rw [stK'_d_v1, stK'_bp] at h1
  exact absurd h1 (not_le.mpr coe_e0_lt_coe_e0_e1)

/-! ### The parent state satisfies the whole corrected invariant -/

theorem st_keyed : Keyed st.d st.D := by
  intro y val hy
  rcases eq_v0_or_v1 y with rfl | rfl
  · rw [D_v0] at hy
    exact (Option.some.inj hy).symm.trans st_d_v0
  · rw [D_v1] at hy
    exact (Option.some.inj hy).symm.trans st_d_v1

theorem st_ge : Ge st.bp st.D := by
  intro y val hy
  rw [st_keyed y val hy]
  exact coe_nil_le _

theorem st_labFloor : LabFloor st := by
  refine ⟨fun y val hy => ?_, fun j => j.elim0⟩
  rw [← st_keyed y val hy]
  exact st_ge y val hy

theorem st_loopBoundInv : LoopBoundInv st := by
  intro y val hy
  exact Or.inl (st_ge y val hy)

theorem st_mintFloor : MintFloor st := by
  intro m hm
  exact absurd hm (by simp [st])

/-- **`KeyedCarry` fails** at this step: `v1` is a parent key the child did not re-key, and the
child's label there is `lam1`, not the parent's `lam2`. -/
theorem carry_fails :
    ¬ (∀ y val, st.D y = some val → foK.D y = none → foK.d' y = val) := by
  intro h
  have hD : foK.D v1 = none := by
    rw [foK_D]; exact aP1_none v1
  have h1 := h v1 lam2 D_v1 hD
  rw [foK_d', dL_v1] at h1
  exact lam2_ne_lam1 h1.symm

/-- **The child's own label at `v1` sits below its own returned bound** — the label the parent
imports is not stale, it is the child's *improvement*, and importing it is what breaks the
parent's floor. -/
theorem child_label_lt_bound : foK.d' v1 < foK.B' := by
  rw [foK_d', dL_v1, foK_B']
  exact coe_e0_lt_coe_e0_e1

/-- The child's label at `v1` is an honest walk label (it dominates the canonical one), so it is
as accurate as the child's own data allows. -/
theorem child_label_sound : dis (s := v0) v1 ≤ foK.d' v1 := by
  rw [foK_d', dL_v1]
  exact dis_le_walk walk_e0

theorem child_run : Run 1 childC foK := leafRun

/-- The failing key is the step's **only** remaining key, so a later iteration's pull must take
it. -/
theorem stK'_sole_key {y : Fin Gcx.n} {val : WLab Gcx v0} (hy : stK'.D y = some val) :
    y = v1 := by
  rcases eq_v0_or_v1 y with rfl | rfl
  · rw [stK'_D_v0] at hy
    exact absurd hy (by simp)
  · rfl

/-- **The damage, stated as the (J2) hazard**: the surviving key's label sits below the running
bound, so any later iteration that pulls it hands `SeedLabFloor` a seed it cannot clear. -/
theorem stK'_seed_hazard : stK'.D v1 = some lam2 ∧ stK'.d v1 < stK'.bp := by
  refine ⟨stK'_D_v1, ?_⟩
  rw [stK'_d_v1, stK'_bp]
  exact coe_e0_lt_coe_e0_e1

theorem stK'_loopBInv : LoopBInv stK'.bp stK' := fun j => j.elim0

theorem stK'_not_labFloor : ¬ LabFloor stK' := fun h => stK'_not_keyLabFloor h.1

theorem foK_D_isEmpty : DS.IsEmpty foK.D := aP1_isEmpty

theorem foK_premFree : ∀ x val, ¬ foK.Premature x val := fun x val h =>
  absurd h.1 (by simp [foK_mints])

theorem foK_bound_le : foK.B' ≤ childC.B := by
  rw [foK_B']; exact le_rfl

/-- **The counterexample, in one statement.**  The parent's state satisfies the corrected
invariant `LabFloor` (both halves), `Keyed`, `LoopBoundInv` and `MintFloor`; the step's child is a
genuine `Run` (`child_run`), full (`foK.D` empty), Prem-free, obeys the bound law, and returns
`B' = c.B` with a sound (walk) label at the parent's surviving key; the value floor *and* the group
floor survive the step — and `LabFloor` does not. -/
theorem labFloor_not_istep :
    LabFloor st ∧ Keyed st.d st.D ∧ LoopBoundInv st ∧ MintFloor st ∧
      Run 1 childC foK ∧ DS.IsEmpty foK.D ∧ (∀ x val, ¬ foK.Premature x val) ∧
      foK.B' ≤ childC.B ∧ Ge stK'.bp stK'.D ∧ LoopBInv stK'.bp stK' ∧
      IStepWith (MergePolicy.parent (G := Gcx) (s := v0)) 1 ⊤ 1 st stK' childC foK ∧
      ¬ (∀ y val, stK'.D y = some val → stK'.bp ≤ stK'.d y) ∧ ¬ LabFloor stK' :=
  ⟨st_labFloor, st_keyed, st_loopBoundInv, st_mintFloor, child_run, foK_D_isEmpty,
    foK_premFree, foK_bound_le, stK'_ge, stK'_loopBInv, istep_key, stK'_not_keyLabFloor,
    stK'_not_labFloor⟩

end Counterexample


/-! ## 5. `SeedChildLabFloor`: full children give it outright; the cap is the wrong direction -/

/-- **BM.24a at a drained loop store**: a `Run.recur` return whose loop state drained returns the
call's bound. -/
theorem callOut_Bp_of_loop_empty {p : ℕ} {B : WLab G s} {S W : Finset (Fin G.n)}
    {st : RState G s p} (h : DS.IsEmpty st.D) : (callOut (tail B S W st)).B' = B := by
  show tailBP B st = B
  unfold tailBP
  rw [if_pos h]

/-- (R5) from `B' = c.B` and `CallPre.inRange`: every seed sits below the entry bound. -/
theorem seedChildLabFloor_of_bound_eq {c : CallEntry G s} {co : CallOut G s}
    (hpre : CallPre c.B c.S c.d) (hB : co.B' = c.B) (hne : c.S.Nonempty) :
    SeedChildLabFloor c co := by
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, hv, ?_⟩
  rw [hB]
  exact (hpre.inRange v hv).le

/-- **The engine's two sources of `B' = c.B`**, packaged: a drained base leaf (Lemma 3.1\*'s
dichotomy) and a drained loop store at `l > 0` (BM.24a).  A child whose returned bound reaches its
entry bound therefore satisfies (R5) for any nonempty seed set — that is the whole content of
`bpChain_of_full_children`'s last premise. -/
theorem seedChildLabFloor_base_of_full' {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hpre : CallPre c.B c.S c.d) (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hfull : DS.IsEmpty bout.D_final) (hne : c.S.Nonempty) :
    SeedChildLabFloor c (baseOut bout) :=
  seedChildLabFloor_base_of_full hpre hb hfull hne

/-- **`BpChain` in the scope where the engine supports it**: the seed label floors (from
`LabFloor`) plus (R5) for every iteration, where (R5) is discharged by the child's own return
bound reaching its entry bound (`B' = B`) — the full-execution regime of Lemma 3.7\*. -/
theorem bpChain_of_full_children {b : WLab G s}
    {qs : List (CallEntry G s × CallOut G s)} (hcl : ChainLabFloor b qs)
    (hpre : ∀ q ∈ qs, CallPre q.1.B q.1.S q.1.d) (hne : ∀ q ∈ qs, q.1.S.Nonempty)
    (hB : ∀ q ∈ qs, q.2.B' = q.1.B) : BpChain b qs :=
  bpChain_of_chainLabFloor b hcl (fun q hq =>
    seedChildLabFloor_of_bound_eq (hpre q hq) (hB q hq) (hne q hq))

/-- (R5) is monotone in the returned bound *upwards*: a witness at `B'` is a witness at any
larger bound.  So the only way to lose it is to *lower* `B'`. -/
theorem seedChildLabFloor_mono {c : CallEntry G s} {co co' : CallOut G s}
    (hB : co.B' ≤ co'.B') (h : SeedChildLabFloor c co) : SeedChildLabFloor c co' := by
  obtain ⟨v, hv, hle⟩ := h
  exact ⟨v, hv, hle.trans hB⟩

namespace Counterexample

/-- A one-key store carries only its own value. -/
theorem single_key {y : Fin Gcx.n} {val : WLab Gcx v0}
    (h : DS.insert DS.empty v1 lam1 y = some val) : val = lam1 := by
  by_cases hyv : y = v1
  · subst hyv
    rw [DS.insert_self] at h
    rw [show DS.empty v1 = none from rfl, DS.mergeVal_none_left] at h
    exact (Option.some.inj h).symm
  · rw [DS.insert_of_ne DS.empty v1 lam1 hyv] at h
    rw [show DS.empty y = none from rfl] at h
    exact absurd h (by simp)

/-- **The direction obstruction.**  `v5Cap` is a `min`: it can only lower the leaf's returned
bound (`v5Cap_le_pull`, `v5Cap_le_dMin`), while (R5) needs an *upper* bound on a seed's label.
Every `dMin` fact is a *lower* bound at a *key* (`dMin_le_of_mem`).  The pair below has the value
floor at the returned store and the returned bound strictly below *every* seed's label — the
capped-leaf shape on which `dMin` cannot produce an (R5) witness.  (A `CallOut`-level shape; it is
not asserted to be the output of a `baseRun`.) -/
theorem capped_leaf_no_seedBound :
    ∃ (c : CallEntry Gcx v0) (co : CallOut Gcx v0),
      (∀ y val, co.D y = some val → co.B' ≤ val) ∧
      (∀ v ∈ c.S, co.B' < c.d v) ∧
      ¬ SeedChildLabFloor c co := by
  refine ⟨⟨lam2, {v1}, 0, st.d⟩,
    ⟨lam1, [], DS.insert DS.empty v1 lam1, dL, [], 0, fun j => j.elim0⟩, ?_, ?_, ?_⟩
  · intro y val hy
    have h1 : DS.insert DS.empty v1 lam1 y = some val := hy
    rw [single_key h1]
  · intro v hv
    have hv1 : v = v1 := by simpa using hv
    subst hv1
    exact coe_e0_lt_coe_e0_e1
  · rintro ⟨v, hv, hle⟩
    have hv1 : v = v1 := by simpa using hv
    subst hv1
    exact absurd hle (not_le.mpr coe_e0_lt_coe_e0_e1)

end Counterexample

/-! ## 6. Signatures and axiom audit -/

#check @Keyed
#check @keyed_merge
#check @keyed_istep
#check @keyLabFloor_istep
#check @keyLabFloor_of_keyed_ge
#check @Counterexample.labFloor_not_istep
#check @Counterexample.carry_fails
#check @Counterexample.child_run
#check @Counterexample.labFloor_not_istep
#check @bpChain_of_full_children
#check @Counterexample.capped_leaf_no_seedBound

#print axioms keyed_merge
#print axioms keyed_istep
#print axioms keyLabFloor_istep
#print axioms Counterexample.labFloor_not_istep
#print axioms bpChain_of_full_children
#print axioms Counterexample.capped_leaf_no_seedBound

end DMSY
end Frontier

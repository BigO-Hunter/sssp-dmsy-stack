import A4.BpMonotonicity
import A4.LowKeyClosure

/-!
# Frontier.DMSY.LiveFloor — the live (distance) floor: base case, transfer set, and why it does
not survive an iteration

`A4.BpMonotonicity` isolates `LiveFloor` as the engine-level invariant that discharges the seed
half of `BpChain` (`iloop_bpChain_of_liveFloor`), and leaves two open items: discharge it at
`mkInit`, and preserve it across `IStep`.  This file closes the first, characterises the second
exactly, and settles it negatively — the invariant is **not** preserved, not even with the
`Prem`-free bound law — with a fully explicit `IStep` refutation.

(Import note: until the `ChildFloor` clash was fixed, `A4.BpMonotonicity` and
`A4.LowKeyClosure` could not be imported together — both `BpMonotonicity` and `BelowSeparator`
defined `Frontier.DMSY.ChildFloor`, with different meanings.  The (R5) clause in
`BpMonotonicity` is now `SeedChildFloor`, so this file imports both, and §4 below is stated in
`Mint`/`Premature` language only because the Q12 bridge belongs to `A4.ValueBpChain`.)

## 1. The base case is a theorem (`liveFloor_init`)

At `mkInit e fo piv` the structure is `initD' fo.d' piv` (keys `= piv j`), the groups are
`fo.P`, and `bp = initBp fo.d' piv e.B = min(B, min_j fo.d' (piv j))`.  Both halves reduce to
one fact about the FindPivots output: **every gate-set member is complete**,
`fo.d' y = dis y` for `y ∈ fo.P j` (`pivot_complete`).  Its proof is the search drain
(`A2.complete_of_drain`): the gate set is `⊆ e.S`, seeds sit below `e.B` by `CallPre.inRange`,
so a gate member lies in `Ũ(e.B, e.S)` — and the drained search completes every member of `Ũ`.
`CallPre.claimC` is what makes the *entry* labels of that cone usable (`fInv_init` is built from
it); the completeness itself is the drain's `hall`.

## 2. `LiveFloor` is strictly stronger than the floors the engine owns

`loopBInv_of_liveFloor` and `ge_of_liveFloor`: `LiveFloor` implies both of the engine's own
floors (label floor at the groups, value floor at the keys).  `labelFloor_not_dis` records the
order-theoretic kernel of the converse failure: `bp ≤ d y` (label) together with
`dis y ≤ d y` (soundness) and `d y ≤ val` (honesty) says nothing about `dis y` — both engine
bounds face *away* from `dis`.  So no value/label hypothesis — `LoopBInv`, `LoopBoundInv`,
`MintPreFloor`, or a Prem-free bound law — can ever produce `LiveFloor`.

## 3. Preservation is false (`liveFloor_not_preserved`) — an explicit `IStep`

`Gcx` is two vertices and two edges: `e0 : 0 → 1` and the self-loop `e1 : 1 → 1`.  The entry
state `st` keys both vertices (`0 ↦ []`, `1 ↦ [e0, e1]`) at `bp = ↑[]`; `LiveFloor st` holds
because every distance is `≥ ↑[]` (`coe_nil_le`).  The step pulls at separator `lam2 = ↑[e0,e1]`
(vertex `0` goes to the child, vertex `1`'s key survives since its value is not `<` the
separator — `belowKeys_st`, `pull_st`), and the child returns `fo.B' = lam2` with an **empty** `D`
and **no mints** — Prem-free, and `fo.B' ≤ c.B` with equality.  At `st'` the surviving key
`1 ↦ lam2` sits at `dis 1 ≤ ↑[e0] < lam2 = st'.bp`, so `LiveFloor` fails
(`st'_not_liveFloor`).  The failing vertex is a **stale key**: its stored label is a walk the
canonical path does not use, so the label over-estimates the distance by a whole edge.  No
hypothesis about values, mints or `Prem` sees this — `fo.D` is empty and `fo.mints = []`.

Distribution over the three sources of a live vertex at `st'`: the failing key is a *parent
**remainder*** (it survived the pull, `deleteSet` spares it), not a child key and not a mint.  So
a preservation theorem would need three distance floors — the child's returned keys (the
induction hypothesis at the child), the residual group members / mint keys (`sel j ∈ resid j`),
and the parent remainders above the pull separator.  §3 refutes the third, and the first two are
not implied by anything the engine owns (§2).  `st'_labelFloor` shows the failing state *does*
satisfy the label floor, so the gap is exactly label-vs-distance, not a missing engine fact.

## 4. The `BpChain` route, and `A4.LowKeyClosure`'s residual

The stale-key vertex is the same object `LowKeyClosure` isolates on the return side: its
`KeyFloorLow` (`keyFloorLow_iff_noStaleKey`) is "no unsettled cone member carries a key at value
`≥ B′`".  Two results connect the files (stated here in `Mint`/`Premature` language, since
`LiveFloor.lean` cannot import `LowKeyClosure`):

* `mints_key_le` — a recorded line-29 mint's key survives at value `≤` the mint's value (values
  only decrease: `mergeVal`/`insert` keep the minimum).  So the "recorded low mint *and* stale
  high key" vertex that `LowKeyClosure` §4 leaves as slack **cannot exist**;
* `mint_iff_keyBelow` — hence, at any step output, the **mint disjunct of `ExitJoint` is
  equivalent to the value floor at that vertex's key** (`A4.ValueBpChain.keyFloorLow_of_exitJoint_mint`
  and its converse carry this across to `LowKeyClosure`'s `ExitJoint`/`KeyFloorLow`):
  `(∃ m ∈ st.mints, m.x = x ∧ m.val < st.bp) ↔ (∃ val, st.D x = some val ∧ val < st.bp)`.
  The mint disjunct is not a statement about mints — it is `KeyFloorLow` in other notation, so
  both files are blocked at one and the same leaf, and it is *not* the leaf `BpChain` needs
  (which is `dis`, not values).

No `sorry`/`admit`, no new axiom, `a4_joint` not assumed.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 0. A generic minimum-walk fact -/

/-- The empty walk is the least label: `↑[] ≤ b` for every `b`. -/
theorem coe_nil_le {G : Graph} {s : Fin G.n} (b : WLab G s) :
    ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) ≤ b := by
  cases b using WithTop.recTopCoe with
  | top => exact le_top
  | coe w =>
    rw [WithTop.coe_le_coe]
    cases w with
    | nil => exact le_rfl
    | cons a as =>
      exact (lt_append (s := s) (P := ([] : List (Fin G.m))) (R := a :: as) (by simp)).le

/-! ## 1. The base case: `LiveFloor` at `mkInit` -/

/-- The drained search completes every member of the FindPivots cone. -/
theorem pivot_complete {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) {y : Fin G.n}
    (hy : y ∈ Utilde e.B (e.S : Set (Fin G.n))) : Complete fo.d' y := by
  obtain ⟨hpre, Y, c, lps, hYsub, hYne, hcap, hloop, hd', -⟩ := hfp
  rw [hd']
  exact complete_of_drain (loop_fInv hloop (fInv_init hpre)) (loop_end_empty hloop) y hy

/-- A gate-set member of a `fpRun` output lies in `Ũ(e.B, e.S)`. -/
theorem mem_utilde_of_groups {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo) {j : Fin fo.p} {y : Fin G.n}
    (hy : y ∈ fo.P j) : y ∈ Utilde e.B (e.S : Set (Fin G.n)) := by
  obtain ⟨hpre, Y, c, lps, hYsub, hYne, hcap, hloop, hd', hW, hp, hP, hQ⟩ := hfp
  rw [hP] at hy
  exact mem_utilde_of_mem hpre (hYsub hy)

/-- **`LiveFloor` at `mkInit`** (the audit item's base case).  Keys are the pivots
(`initD'_keys`), whose labels are complete (`pivot_complete`); group members dominate their own
pivot (`hpiv`) and are complete too; `bp = initBp ≤ fo.d' (piv j)`. -/
theorem liveFloor_init {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y) :
    LiveFloor (mkInit e fo piv) := by
  constructor
  · intro y v hy
    obtain ⟨j, hj⟩ := initD'_keys fo.d' piv DS.empty
      (fun y val hy => absurd hy (Ne.symm (Option.some_ne_none val))) y v hy
    have hc : Complete fo.d' (piv j) :=
      pivot_complete hfp (mem_utilde_of_groups hfp (hpiv j).1)
    rw [hj, ← hc]
    exact initBp_le fo.d' piv e.B j
  · intro j y hy
    have hc : Complete fo.d' y := pivot_complete hfp (mem_utilde_of_groups hfp hy)
    rw [← hc]
    exact (initBp_le fo.d' piv e.B j).trans ((hpiv j).2 y hy)

/-! ## 2. `LiveFloor` implies the floors the engine owns, and no floor implies it back -/

/-- `LiveFloor` implies the label floor at the residual groups (the content of `LoopBInv`). -/
theorem loopBInv_of_liveFloor {p : ℕ} {st : RState G s p} (hlive : LiveFloor st)
    (hsound : Sound st.d) : ∀ j y, y ∈ st.pl j → st.bp ≤ st.d y :=
  fun j y hy => (hlive.2 j y hy).trans (hsound y)

/-- `LiveFloor` implies the value floor at the keys (`Ge` / `LoopBoundInv`'s first branch),
given one-sided honesty `d y ≤ val`. -/
theorem ge_of_liveFloor {p : ℕ} {st : RState G s p} (hlive : LiveFloor st)
    (hsound : Sound st.d) (hhon : ∀ y val, st.D y = some val → st.d y ≤ val) :
    ∀ y val, st.D y = some val → st.bp ≤ val :=
  fun y val hy => (hlive.1 y val hy).trans ((hsound y).trans (hhon y val hy))

/-- **The order-theoretic kernel**: a value floor (`v ≤ l` from honesty, `b ≤ l` from a label
floor) is not a distance floor (`b ≤ di`), because both engine bounds sit on the *far* side of
`dis` (`di ≤ d ≤ v`). -/
theorem labelFloor_not_dis : ∃ b di d v : ℕ, b ≤ d ∧ di ≤ d ∧ d ≤ v ∧ ¬ b ≤ di :=
  ⟨3, 1, 5, 7, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-! ## 3. Preservation is false: the explicit `IStep` counterexample -/

namespace Counterexample

/-- Two vertices, two edges: `e0 : 0 → 1` and the self-loop `e1 : 1 → 1`.  Vertex `1` then has
two labels (`[e0]` and `[e0, e1]`) with `↑[e0] < ↑[e0, e1]` by `lt_append`; that gap is the
stale key. -/
def Gcx : Graph where
  n := 2
  m := 2
  src := fun e => if e = ⟨0, by decide⟩ then ⟨0, by decide⟩ else ⟨1, by decide⟩
  dst := fun _ => ⟨1, by decide⟩
  w := fun _ => 0

/-- The source. -/
def v0 : Fin Gcx.n := ⟨0, by decide⟩

/-- The far vertex. -/
def v1 : Fin Gcx.n := ⟨1, by decide⟩

/-- `0 → 1`. -/
def e0 : Fin Gcx.m := ⟨0, by decide⟩

/-- The self-loop at `1`. -/
def e1 : Fin Gcx.m := ⟨1, by decide⟩

theorem src_e0 : Gcx.src e0 = v0 := rfl

theorem src_e1 : Gcx.src e1 = v1 := by
  show (if e1 = e0 then v0 else v1) = v1
  rw [if_neg (by decide)]

theorem dst_any (e : Fin Gcx.m) : Gcx.dst e = v1 :=
  Fin.ext rfl

/-- The one-edge walk to `v1`. -/
theorem walk_e0 : Gcx.IsWalk v0 v1 [e0] := by
  have h := Graph.IsWalk.single (G := Gcx) (e := e0)
  rwa [src_e0, dst_any] at h

/-- The two-edge walk to `v1`. -/
theorem walk_e0_e1 : Gcx.IsWalk v0 v1 [e0, e1] := by
  have h1 := Graph.IsWalk.single (G := Gcx) (e := e0)
  rw [src_e0, dst_any] at h1
  have h2 : Gcx.IsWalk v1 v1 [e1] := by
    have hn : Gcx.IsWalk (Gcx.dst e1) v1 [] := by rw [dst_any]; exact Graph.IsWalk.nil v1
    have hh := Graph.IsWalk.cons (G := Gcx) (e := e1) hn
    rwa [src_e1] at hh
  have hn2 : Gcx.IsWalk (Gcx.dst e0) v1 [e1] := by rw [dst_any]; exact h2
  have hh := Graph.IsWalk.cons (G := Gcx) (e := e0) hn2
  rwa [src_e0] at hh

/-- The stale label strictly dominates the other one: `↑[e0] < ↑[e0, e1]`. -/
theorem coe_e0_lt_coe_e0_e1 :
    ((toW ([e0] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0)
      < ((toW ([e0, e1] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0) := by
  have h := lt_append (s := v0) (P := [e0]) (R := [e1]) (by simp)
  simpa using h

/-- `↑[] < ↑[e0, e1]`. -/
theorem coe_nil_lt_coe_e0_e1 :
    ((toW ([] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0)
      < ((toW ([e0, e1] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0) := by
  have h := lt_append (s := v0) (P := ([] : List (Fin Gcx.m))) (R := [e0, e1]) (by simp)
  simpa using h

/-- `↑[] < ↑[e0]`. -/
theorem coe_nil_lt_coe_e0 :
    ((toW ([] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0)
      < ((toW ([e0] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0) := by
  have h := lt_append (s := v0) (P := ([] : List (Fin Gcx.m))) (R := [e0]) (by simp)
  simpa using h

/-- The canonical label of `v1` sits strictly below the stale label. -/
theorem dis_v1_lt : dis (s := v0) v1
    < ((toW ([e0, e1] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0) :=
  (dis_le_walk walk_e0).trans_lt coe_e0_lt_coe_e0_e1

/-- The one-edge entry walk, as a label. -/
def lam1 : WLab Gcx v0 := ((toW ([e0] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0)

/-- The stale two-edge label, as a label. -/
def lam2 : WLab Gcx v0 := ((toW ([e0, e1] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0)

/-- The empty label. -/
def lam0 : WLab Gcx v0 := ((toW ([] : List (Fin Gcx.m)) : WalkOrd Gcx v0) : WLab Gcx v0)

theorem lam2_ne_lam1 : lam2 ≠ lam1 := by
  intro h
  have h2 : lam1 < lam2 := coe_e0_lt_coe_e0_e1
  rw [h] at h2
  exact lt_irrefl lam1 h2

/-- The loop's initial state at the counterexample: both vertices keyed, running bound `↑[]`. -/
noncomputable def st : RState Gcx v0 0 where
  d := fun v => if v = v0 then lam0 else lam2
  D := DS.insert (DS.insert DS.empty v0 lam0) v1 lam2
  evts := []
  bp := lam0
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

theorem insert_none_key (D : DS Gcx v0) (y : Fin Gcx.n) (lam : WLab Gcx v0)
    (hD : D y = none) : DS.insert D y lam y = some lam := by
  rw [DS.insert_self, hD, DS.mergeVal_none_left]

theorem insert_none_other (D : DS Gcx v0) (y z : Fin Gcx.n) (lam : WLab Gcx v0)
    (hzy : z ≠ y) (hD : D z = none) : DS.insert D y lam z = none := by
  rw [DS.insert_of_ne D y lam hzy]; exact hD

theorem D_v0 : st.D v0 = some lam0 := by
  show DS.insert (DS.insert DS.empty v0 lam0) v1 lam2 v0 = some lam0
  rw [DS.insert_of_ne _ v1 lam2 (by decide : v0 ≠ v1)]
  exact insert_none_key DS.empty v0 lam0 rfl

theorem D_v1 : st.D v1 = some lam2 := by
  show DS.insert (DS.insert DS.empty v0 lam0) v1 lam2 v1 = some lam2
  exact insert_none_key _ v1 lam2 (insert_none_other DS.empty v0 v1 lam0 (by decide) rfl)

/-- The child's return: bound `lam2`, empty structure, no mints — Prem-free. -/
noncomputable def fo : CallOut Gcx v0 where
  B' := lam2
  evts := []
  D := DS.empty
  d' := st.d
  mints := []
  pfin := 0
  Pfin := fun j => j.elim0

/-- The state after the iteration. -/
noncomputable def st' : RState Gcx v0 0 where
  d := st.d
  D := DS.merge (DS.deleteSet st.D {v0}) DS.empty
  evts := []
  bp := lam2
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

/-- The call entry the iteration produces. -/
noncomputable def c : CallEntry Gcx v0 where
  B := lam2
  S := {v0}
  l := 0
  d := st.d

theorem st_liveFloor : LiveFloor st := by
  constructor
  · intro y v hy
    exact coe_nil_le _
  · intro j y hy
    exact j.elim0

theorem expand_st : expand (s := v0) st.d st.pl st.piv ({v0} : Finset (Fin Gcx.n)) lam2
    = {v0} := by
  rw [expand, biUnion_fin0, Finset.union_empty]

theorem dis_v1_lt_lam2 : dis (s := v0) v1 < lam2 := dis_v1_lt

theorem merge_empty_right (D : DS Gcx v0) (y : Fin Gcx.n) :
    DS.merge D DS.empty y = D y := by
  show DS.mergeVal (D y) (DS.empty y) = D y
  rw [show DS.empty y = none from rfl]
  cases D y with
  | none => rfl
  | some a => rw [DS.mergeVal_none_right]

theorem st'_D_v1 : st'.D v1 = some lam2 := by
  show DS.merge (DS.deleteSet st.D {v0}) DS.empty v1 = some lam2
  rw [merge_empty_right]
  rw [DS.deleteSet_of_notMem st.D {v0} v1 (by
    show v1 ∉ ({v0} : Finset (Fin Gcx.n))
    simp [v0, v1])]
  exact D_v1

theorem st'_not_liveFloor : ¬ LiveFloor st' := by
  intro h
  have h1 : st'.bp ≤ dis (s := v0) v1 := h.1 v1 lam2 st'_D_v1
  have h2 : dis (s := v0) v1 < st'.bp := by
    show dis (s := v0) v1 < lam2
    exact dis_v1_lt_lam2
  exact absurd h1 (not_le.mpr h2)

/-- The two vertices of `Gcx` exhaust `Fin Gcx.n`. -/
theorem eq_v0_or_v1 (y : Fin Gcx.n) : y = v0 ∨ y = v1 := by
  have h2 : y.1 < 2 := y.isLt
  rcases Nat.lt_succ_iff_lt_or_eq.mp h2 with h | h
  · left; exact Fin.ext (by show y.1 = 0; omega)
  · right; exact Fin.ext (by show y.1 = (1 : ℕ); exact h)

/-- The pull's separator set at `lam2`: exactly the `lam0` key. -/
theorem belowKeys_st : belowKeys (G := Gcx) (s := v0) st.D lam2 = {v0} := by
  ext y
  rw [mem_belowKeys, Finset.mem_singleton]
  constructor
  · rintro ⟨v, hv, hlt⟩
    rcases eq_v0_or_v1 y with rfl | rfl
    · rfl
    · rw [D_v1] at hv
      rw [← Option.some.inj hv] at hlt
      exact absurd hlt (lt_irrefl lam2)
  · rintro rfl
    exact ⟨lam0, D_v0, by simpa [lam0, lam2] using coe_nil_lt_coe_e0_e1⟩

theorem lam0_lt_lam2 : lam0 < lam2 := by
  simpa [lam0, lam2] using coe_nil_lt_coe_e0_e1

theorem pull_st : pullRun (G := Gcx) (s := v0) (pullCap 2 1) st.D ⊤ {v0} lam2
    (DS.deleteSet st.D {v0}) := by
  refine ⟨belowKeys_st.symm, rfl, le_top, Or.inr ⟨v1, lam2, D_v1, rfl⟩,
    Or.inr ⟨v0, lam0, D_v0, lam0_lt_lam2⟩, ?_⟩
  rw [Finset.card_singleton]
  show 1 ≤ pullCap 2 1
  decide

/-- **One genuine `IStep` whose entry satisfies `LiveFloor` and whose exit does not.**  The child
is Prem-free (`fo.D = ∅`, `fo.mints = []`) and the bound law `fo.B' ≤ c.B` holds with equality. -/
theorem istep_st : IStep (G := Gcx) (s := v0) 2 ⊤ 1 st st' c fo := by
  refine ⟨{v0}, lam2, DS.deleteSet st.D {v0}, (fun j => j.elim0), ∅, (fun j => j.elim0),
    DS.merge (DS.deleteSet st.D {v0}) DS.empty, fo.d', DS.merge (DS.deleteSet st.D {v0}) DS.empty,
    pull_st, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · rw [CallEntry.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl⟩
    · show ({v0} : Finset (Fin Gcx.n)) = expand st.d st.pl st.piv {v0} lam2
      rw [expand_st]
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
    · simp [st']
    · simp [st', st, fo]
    · funext j
      exact j.elim0
    · simp [st']

theorem fo_bound_le : fo.B' ≤ c.B := le_rfl

theorem fo_premFree : ∀ x val, ¬ fo.Premature x val := by
  intro x val h
  exact absurd h.1 (by simp [fo])

/-- **Preservation of `LiveFloor` across `IStep` is false** — with the entry invariant, the
Prem-free child, the bound law, and no mints anywhere. -/
theorem liveFloor_not_preserved :
    LiveFloor st ∧ IStep (G := Gcx) (s := v0) 2 ⊤ 1 st st' c fo ∧
      fo.B' ≤ c.B ∧ (∀ x val, ¬ fo.Premature x val) ∧ ¬ LiveFloor st' :=
  ⟨st_liveFloor, istep_st, fo_bound_le, fo_premFree, st'_not_liveFloor⟩

/-- The failing key is a **pull remainder**: `deleteSet` spares it, the child's structure is
empty and its mint list is empty, so no hypothesis on the child's `D` or mints can see it. -/
theorem survivor_key : (DS.deleteSet st.D {v0}) v1 = some lam2 := by
  rw [DS.deleteSet_of_notMem st.D {v0} v1]
  · exact D_v1
  · show v1 ∉ ({v0} : Finset (Fin Gcx.n))
    simp [v0, v1]

theorem fo_D_empty : fo.D = DS.empty := rfl

theorem fo_mints_empty : fo.mints = [] := rfl

theorem st'_D_v0 : st'.D v0 = none := by
  show DS.merge (DS.deleteSet st.D {v0}) DS.empty v0 = none
  rw [merge_empty_right]
  exact DS.deleteSet_mem st.D {v0} v0 (by
    show v0 ∈ ({v0} : Finset (Fin Gcx.n))
    simp)

/-- The label floor *does* hold at the failing state — so `LiveFloor` is strictly stronger than
every label/value floor the engine owns. -/
theorem st'_labelFloor : ∀ y val, st'.D y = some val → st'.bp ≤ st'.d y := by
  intro y val hy
  rcases eq_v0_or_v1 y with rfl | rfl
  · rw [st'_D_v0] at hy
    exact absurd hy.symm (Option.some_ne_none val)
  · show lam2 ≤ st'.d v1
    simp only [st', st]
    rw [if_neg (by decide : v1 ≠ v0)]

end Counterexample

/-! ## 4. Line-29 mints: a recorded mint's key survives at or below the mint's value

`st'.D` is `D3` with one ungated insert per group of `J` at the *current label* `d3 (sel j)`.
`DS.insert` keeps the minimum, so a mint's key is present at a value `≤` the mint's value
whatever `D3` held (and later inserts only lower it).  This is the fact that removes
`LowKeyClosure` §4's "stale high key *and* recorded low mint" slack. -/

/-- Inserts never remove a key. -/
theorem fold_keys_mono {ι : Type} (js : List ι) (f : ι → Fin G.n) (g : ι → WLab G s)
    (D0 : DS G s) {z : Fin G.n} (h : D0 z ≠ none) :
    (js.foldl (fun D j => DS.insert D (f j) (g j)) D0) z ≠ none := by
  induction js generalizing D0 with
  | nil => exact h
  | cons j0 js ih =>
    rw [List.foldl_cons]
    exact ih _ (DS.keys_insert_le D0 (f j0) (g j0) h)

/-- A key inserted somewhere in the fold is a key at the end. -/
theorem fold_key_present {ι : Type} (js : List ι) (f : ι → Fin G.n) (g : ι → WLab G s)
    (D0 : DS G s) {j : ι} (hj : j ∈ js) :
    (js.foldl (fun D j => DS.insert D (f j) (g j)) D0) (f j) ≠ none := by
  induction js generalizing D0 with
  | nil => exact absurd hj (List.not_mem_nil)
  | cons j0 js ih =>
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hj with rfl | hj'
    · exact fold_keys_mono js f g _ (DS.mem_keys_insert D0 (f j) (g j))
    · exact ih _ hj'

/-- A pointwise upper bound at a key survives further inserts once the key is present: an insert
at the key keeps the minimum, an insert elsewhere leaves the slot alone. -/
theorem fold_preserves_of_some {ι : Type} (js : List ι) (f : ι → Fin G.n)
    (g : ι → WLab G s) (D0 : DS G s) {z : Fin G.n} {K : WLab G s}
    (h : ∃ v0, D0 z = some v0 ∧ v0 ≤ K) :
    ∀ v, (js.foldl (fun D j => DS.insert D (f j) (g j)) D0) z = some v → v ≤ K := by
  induction js generalizing D0 with
  | nil =>
    intro v hv
    obtain ⟨v0, hv0, hle⟩ := h
    rw [show List.foldl (fun D j => DS.insert D (f j) (g j)) D0 [] z = D0 z from rfl] at hv
    rw [hv0] at hv
    rw [← Option.some.inj hv]
    exact hle
  | cons j0 js ih =>
    rw [List.foldl_cons]
    refine ih _ ?_
    by_cases hz : z = f j0
    · subst hz
      obtain ⟨v0, hv0, hle⟩ := h
      refine ⟨min v0 (g j0), ?_, (min_le_left _ _).trans hle⟩
      rw [DS.insert_self, hv0, DS.mergeVal_some]
    · obtain ⟨v0, hv0, hle⟩ := h
      refine ⟨v0, ?_, hle⟩
      show DS.insert D0 (f j0) (g j0) z = some v0
      rw [DS.insert_of_ne D0 (f j0) (g j0) hz]
      exact hv0

/-- The value at a key inserted during the fold is at most the inserted value. -/
theorem fold_mem_le {ι : Type} (js : List ι) (f : ι → Fin G.n) (g : ι → WLab G s)
    (D0 : DS G s) {j : ι} (hj : j ∈ js) :
    ∀ v, (js.foldl (fun D j => DS.insert D (f j) (g j)) D0) (f j) = some v → v ≤ g j := by
  obtain ⟨pre, post, rfl⟩ := List.mem_iff_append.mp hj
  rw [List.foldl_append, List.foldl_cons]
  refine fold_preserves_of_some (z := f j) (K := g j) post f g _ ?_
  cases hD : (pre.foldl (fun D j => DS.insert D (f j) (g j)) D0) (f j) with
  | none =>
    refine ⟨g j, ?_, le_rfl⟩
    rw [DS.insert_self, hD, DS.mergeVal_none_left]
  | some μ =>
    refine ⟨min μ (g j), ?_, min_le_right _ _⟩
    rw [DS.insert_self, hD, DS.mergeVal_some]

/-- **A recorded line-29 mint's key survives at a value `≤` the mint's value.** -/
theorem mints_key_le {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    {m : Mint G s} (hm : m ∈ st'.mints) :
    ∃ v, st'.D m.x = some v ∧ v ≤ m.val := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  rw [List.mem_map] at hm
  obtain ⟨j, hj, rfl⟩ := hm
  have hp : (J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3) (sel j)
      ≠ none := fold_key_present J.toList sel (fun j => d3 (sel j)) D3 hj
  obtain ⟨v, hv⟩ := Option.ne_none_iff_exists'.mp hp
  exact ⟨v, hv, fold_mem_le J.toList sel (fun j => d3 (sel j)) D3 hj v hv⟩

/-- **A key below the running bound is a recorded mint** (`LoopBoundInv`'s escape): this is the
value half of the `Prem`-free statement, stated at a loop state. -/
theorem below_key_is_mint {p : ℕ} {st : RState G s p} (hinv : LoopBoundInv st)
    {x : Fin G.n} {val : WLab G s} (hx : st.D x = some val) (hlt : val < st.bp) :
    Mint.mk x val ∈ st.mints := by
  rcases hinv x val hx with h | h
  · exact absurd h (not_le.mpr hlt)
  · exact h

/-- **The mint disjunct is the value floor at keys, not a separate obligation.**  At a step
output, "there is a recorded mint at `x` below the running bound" and "`x`'s key carries a value
below the running bound" are the *same* statement (`←` is `LoopBoundInv` alone, `→` is
`mints_key_le`).  So `LowKeyClosure`'s `ExitJoint` mint disjunct and its `KeyFloorLow` are two
notations for one leaf. -/
theorem mint_iff_keyBelow {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hinv : LoopBoundInv st') (x : Fin G.n) :
    (∃ m ∈ st'.mints, m.x = x ∧ m.val < st'.bp) ↔
      ∃ val, st'.D x = some val ∧ val < st'.bp := by
  constructor
  · rintro ⟨m, hm, rfl, hlt⟩
    obtain ⟨v, hv, hle⟩ := mints_key_le h hm
    exact ⟨v, hv, hle.trans_lt hlt⟩
  · rintro ⟨val, hv, hlt⟩
    exact ⟨Mint.mk x val, below_key_is_mint hinv hv hlt, rfl, hlt⟩

/-- **The `Prem`-free value floor follows from the mint floor** (the direction `BpChain` and the
identity cover actually need): if no recorded mint sits below the running bound, no key does. -/
theorem keyFloor_of_mintFloor {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hinv : LoopBoundInv st') (hmint : ∀ m ∈ st'.mints, st'.bp ≤ m.val) :
    ∀ y val, st'.D y = some val → st'.bp ≤ val := by
  intro y val hv
  by_contra hlt
  obtain ⟨m, hm, -, hlt'⟩ :=
    (mint_iff_keyBelow h hinv y).mpr ⟨val, hv, not_le.mp hlt⟩
  exact absurd (hmint m hm) (not_le.mpr hlt')

/-! ## Signatures and axiom audit -/

#check @liveFloor_init
#check @loopBInv_of_liveFloor
#check @ge_of_liveFloor
#check @labelFloor_not_dis
#check @Counterexample.liveFloor_not_preserved
#check @Counterexample.st'_labelFloor
#check @Counterexample.survivor_key
#check @Counterexample.istep_st
#check @mints_key_le
#check @below_key_is_mint
#check @mint_iff_keyBelow
#check @keyFloor_of_mintFloor

#print axioms liveFloor_init
#print axioms Counterexample.liveFloor_not_preserved
#print axioms mints_key_le
#print axioms mint_iff_keyBelow

end DMSY
end Frontier

import A4.Transitive
import A4.LemmaV

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.LoopBInv — the return-side loop invariant, the mint bound, and the leaf split

`A4.JointAssembly` assembles the **entry side** of the joint chain (`Reach` ⟹ `Lemma37Hyp`,
`ChildFloor` ⟹ `ChildStep`).  The return side was left open.  The single numeric fact
`theoremT` consumes is a *value* bound, `out.B' ≤ m.val` for every final mint `m`, and the joint
review located it in one loop invariant:

```
LoopBInv B st  :=  ∀ j, ∀ y ∈ st.pl j, st.bp ≤ st.d y
```

## What is proved here (standard axioms only)

* `sweepEvts_label_cases` — the engine fact this needs: a sweep either leaves a label alone or
  writes a value `≥ lo`.  With `lo = Bi ≥ fo'.B'` (the child's bound law) this transports a
  label floor at `fo'.d'` to `st'.d` across the parent's own sweep.
* `istep_bInv` — one iteration preserves `LoopBInv`.  **Signature = the review's target plus one
  premise**: `hchild`, `hinv`, `hcb` are kept verbatim, and `hfloor : ChildLabelFloor st fo'` is
  the single surviving clause.  `hchild` supplies the child's bound law
  (`fo'.B' ≤ c.B`, `run_le_bound`); `hinv` and `hcb` are *not* consumed — preservation is a pure
  label-floor statement, and `Lemma37Concl` carries no label-side clause (`bound` is about
  `fo'.D`, `progress` about `fo'.U`, `identity` about `out.U`).  That `hinv` alone is not enough
  is `not_bInv_of_premature`.
* `iloop_bInv`, `iloop_mintFloor` — `LoopBInv` (and the mint floor it induces) thread through
  `ILoop`.
* `istep_mintFloor`, `tail_mintFloor`, `recur_mintFloor`, `run_mintFloor` — **`Run t e out →
  out.B' ≤ m.val`**, the Theorem-T value bound, by the review's exact route (`sel j ∈ resid j =
  st'.pl j`, `st'.bp = fo'.B'`, `tailBP`, mint keys re-keyed by the fold).
* `MintPreFloor`, `istep_mintFloor_of_pre`, `iloop_mintFloor_of_pre`, `run_mintFloor_of_pre` —
  **the minimal corrected invariant**: the bound above needs only the *selected* keys
  (`st'.mints`), not every residual group member, to sit at `≥ fo'.B'` before the sweep.  This
  is strictly weaker than `LoopBInv` and is the form `a4_joint` should carry.
* `baseOut_gate`, `childLabelFloor_base_gate` — **the full/cap split of the premise at a base
  leaf**: the gate is the leaf's returned bound `B'⁺ ≤ c.B`, and it coincides with `c.B` exactly
  on full leaves.  Nothing here is stated at `c.B` unconditionally.
* `not_bInv_of_premature`, `not_bInv_of_loop_premature` — `LoopBInv` is **not free**: a state
  with a `Premature` entry (Q12: a final-iteration line-29 mint below `B'`) violates it at its
  own mint key, since `premShape` gives `d' x ≤ val < B' = bp`.  So the naked invariant is
  Theorem-T-strength and cannot be assumed away.

## The leaf constraint (`A4.LeafFloor`) — the precise semantics this proof depends on

(That peer file is cited, not imported: its facts are restated here as `baseOut_gate` /
`childLabelFloor_base_gate` on the `baseRun`/`Lemma31Concl` interface, so this file builds
independently of it.)

`A4.LeafFloor` shows the sibling clause `ChildFloor`'s refusal floor *fails on capped base
exits*: its gate is the child's **entry** bound `c.B`, and a cap-limited leaf abandons the band
`(B'⁺, c.B)` with stale labels.  This file's premise is deliberately **not** that clause:

* `ChildLabelFloor st fo'` is gated at `fo'.B'` — the child's **returned** bound (= `B'⁺` at a
  base leaf), never at `c.B`.  `baseOut_gate` records that a base leaf's returned bound is
  `B'⁺ ≤ c.B`, and `childLabelFloor_base_gate` records that the two gates coincide **exactly on
  full leaves** (`bout.D_final` drained, `LeafFloor.childFloor_base_of_full`'s regime) and that
  the returned-bound gate is the weaker one on capped exits.  So the capped branch cannot break
  this premise the way it breaks the refusal floor; no unconditional `c.B`-gated statement is
  made anywhere in this file.
* `ChildLabelFloor` is still **not** discharged here, and it is not free even at a full leaf:
  a vertex complete with `dis y < B'⁺` whose canonical path avoids the child's seed set is
  unsettled with its label below `B'⁺` (`CallPre.claimC` at the child's entry is exactly what
  allows this).  That is why it stays a premise — pointwise in the step (`LabelFloorHyp`), or in
  its minimal mint-key form (`MintPreHyp`) — and never a restated final theorem.
* The leaf side needs `CallPre` (`claimC`, `inRange`) in addition to `Lemma31Concl`.  The two
  gate lemmas (`baseOut_gate`, `childLabelFloor_base_gate`) are stated on exactly that interface
  — `CallPre` + `baseRun` + the drain hypothesis — so the joint induction knows the base case's
  recipe is `LeafFloor.childFloor_base_of_full` for the refusal floor **plus** a separate
  `ChildLabelFloor`/`MintPreFloor` argument, which this file does not attempt.

## Direction warning (the review's flag)

`hsel`'s selection **minimality** gives `d3 (sel j) ≤ d3 y` for `y ∈ resid j` — the *wrong*
direction for `LoopBInv`, which needs `bp ≤ d3 y`.  Minimality is used only in the correct
direction here (`LoopBInv` at the post state applied to the mint key, `istep_mintFloor`), and is
never used to manufacture a floor.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The invariant, the surviving clause, and its minimal form -/

/-- **`LoopBInv`** — every member of every residual pivot group carries a label at least the
running return bound.  At a loop exit the residual groups are `CallOut.Pfin`, so this bounds the
final mints' values (the `theoremT` seam). -/
def LoopBInv (B : WLab G s) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ j, ∀ y ∈ st.pl j, st.bp ≤ st.d y

/-- **The clause `LoopBInv`'s preservation still needs** — the label-side companion of clause
(2b): off the child's settled set, the child's returned labels dominate its **returned** bound.
Gated at `fo'.B'` (not at `c.B`): that is the cap-safe form (`baseOut_gate`,
`childLabelFloor_base_gate`). -/
def ChildLabelFloor {p : ℕ} (st : RState G s p) (fo' : CallOut G s) : Prop :=
  ∀ j, ∀ y ∈ st.pl j, y ∉ settledSet fo'.evts → fo'.B' ≤ fo'.d' y

/-- The step-uniform form of `ChildLabelFloor`. -/
def LabelFloorHyp (t : ℕ) : Prop :=
  ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p) (c : CallEntry G s)
    (fo' : CallOut G s), IStep t B l st st' c fo' → ChildLabelFloor st fo'

/-- **The minimal corrected invariant** for `theoremT`: the final re-selection's keys (the mints
themselves) sit at or above the child's bound *before* the parent's sweep.  Strictly weaker than
`LoopBInv` — it constrains only the selected keys, not every residual member — and it is
cap-safe by construction (gate `fo'.B'`). -/
def MintPreFloor {p : ℕ} (st' : RState G s p) (fo' : CallOut G s) : Prop :=
  ∀ m ∈ st'.mints, fo'.B' ≤ fo'.d' m.x

/-- The step-uniform form of `MintPreFloor`. -/
def MintPreHyp (t : ℕ) : Prop :=
  ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p) (c : CallEntry G s)
    (fo' : CallOut G s), IStep t B l st st' c fo' → MintPreFloor st' fo'

/-! ## The engine fact: a sweep never writes below its gate -/

/-- One (E2)-gated relaxation either leaves a label alone or writes a candidate `≥ lo`. -/
theorem relaxGate_label_cases (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (y : Fin G.n) :
    (relaxGate B lo d D e).1 y = d y ∨ lo ≤ (relaxGate B lo d D e).1 y := by
  unfold relaxGate
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos hc]
    by_cases hy : y = G.dst e
    · subst hy
      refine Or.inr ?_
      show lo ≤ (Function.update d (G.dst e) (ext (d (G.src e)) e)) (G.dst e)
      rw [Function.update_self]
      exact hc.1
    · refine Or.inl ?_
      show (Function.update d (G.dst e) (ext (d (G.src e)) e)) y = d y
      rw [Function.update_of_ne hy]
  · rw [if_neg hc]
    exact Or.inl rfl

/-- The gate sweep over one vertex's out-edges: labels are unchanged or `≥ lo`. -/
theorem sweepGate_label_cases (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) :
    ∀ (d : Labels G s) (D : DS G s) (y : Fin G.n),
      (sweepGate B lo u es d D).1 y = d y ∨ lo ≤ (sweepGate B lo u es d D).1 y := by
  induction es with
  | nil => intro d D y; exact Or.inl rfl
  | cons e es ih =>
    intro d D y
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      rcases ih (relaxGate B lo d D e).1 (relaxGate B lo d D e).2 y with h | h
      · rcases relaxGate_label_cases B lo d D e y with h' | h'
        · exact Or.inl (h.trans h')
        · exact Or.inr (by rw [h]; exact h')
      · exact Or.inr h
    · rw [if_neg hs, if_neg hs]
      exact ih d D y

/-- The settlement-log sweep: labels are unchanged or `≥ lo`.  Instantiating `lo = Bi` and
`fo'.B' ≤ c.B = Bi` transports `ChildLabelFloor` to `st'.d`. -/
theorem sweepEvts_label_cases (B lo : WLab G s) (evts : List (SettlementEvent G)) :
    ∀ (d : Labels G s) (D : DS G s) (y : Fin G.n),
      (sweepEvts B lo evts d D).1 y = d y ∨ lo ≤ (sweepEvts B lo evts d D).1 y := by
  induction evts with
  | nil => intro d D y; exact Or.inl rfl
  | cons ev evts ih =>
    intro d D y
    show (sweepEvts B lo evts (sweepGate B lo ev.v (List.finRange G.m) d D).1
      (sweepGate B lo ev.v (List.finRange G.m) d D).2).1 y = d y ∨
      lo ≤ (sweepEvts B lo evts (sweepGate B lo ev.v (List.finRange G.m) d D).1
        (sweepGate B lo ev.v (List.finRange G.m) d D).2).1 y
    rcases ih (sweepGate B lo ev.v (List.finRange G.m) d D).1
      (sweepGate B lo ev.v (List.finRange G.m) d D).2 y with h | h
    · rcases sweepGate_label_cases B lo ev.v (List.finRange G.m) d D y with h' | h'
      · exact Or.inl (h.trans h')
      · exact Or.inr (by rw [h]; exact h')
    · exact Or.inr h

/-! ## The invariant at the loop's initial state -/

/-- `mkInit` satisfies `LoopBInv`: `bp = initBp = min(B, min_j d[piv_j])` and each pivot is its
group's minimum (`Run.recur`'s `hpiv`).  The one place the run's pivot minimality enters. -/
theorem loopBInv_init (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y) :
    LoopBInv e.B (mkInit e fo piv) := by
  intro j y hy
  exact (initBp_le fo.d' piv e.B j).trans ((hpiv j).2 y hy)

/-! ## One iteration, then the loop -/

open Classical in
/-- **One iteration preserves `LoopBInv`**, with the child's bound law as data
(`hble : fo'.B' ≤ c.B`, which `hchild : Run t c fo'` supplies via `run_le_bound`).  A residual
member of group `j` lies in `st.pl j` and outside `settledSet fo'.evts`; `hfloor` puts it at
`≥ fo'.B'` after the child, and the parent's sweep gate is `Bi = c.B ≥ fo'.B'`. -/
theorem istep_bInv_of_le (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hble : fo'.B' ≤ c.B) (hfloor : ChildLabelFloor st fo') : LoopBInv B st' := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  have hd : st'.d = d3 := by rw [hst']
  have hbp : st'.bp = fo'.B' := by rw [hst']
  have hplEq : ∀ j, st'.pl j = resid j := by intro j; rw [hst']
  have hBi : fo'.B' ≤ Bi := by
    rw [hc] at hble
    simpa using hble
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := by rw [← hsweep]
  intro j y hy
  rw [hbp, hd, hd3]
  have h1 : y ∈ resid j := by
    rw [← hplEq j]
    exact hy
  rw [hresid j] at h1
  obtain ⟨hpl, hclean⟩ := Finset.mem_filter.mp h1
  rcases sweepEvts_label_cases B Bi fo'.evts fo'.d' D2 y with hcases | hcases
  · rw [hcases]
    exact hfloor j y hpl hclean
  · exact hBi.trans hcases

/-- **`istep_bInv` — the review's target signature, verbatim.**  `hchild` supplies the bound law;
`hfloor` is the one surviving clause.  `hinv` and `hcb` are retained for signature parity and
are not consumed: preservation is a pure label-floor statement, and `Lemma37Concl` carries no
label-side clause (`bound` is about `fo'.D`, `progress` about `fo'.U`, `identity` about `out.U`).
The fact that `hinv` is *not* enough is exactly `not_bInv_of_premature`. -/
theorem istep_bInv (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hchild : Run t c fo') (hinv : LoopBInv B st) (hcb : Lemma37Concl (Full t) c fo')
    (hfloor : ChildLabelFloor st fo') : LoopBInv B st' :=
  istep_bInv_of_le t B l h (run_le_bound t hchild) hfloor

/-- **`LoopBInv` threads through the whole loop** under one per-step `ChildLabelFloor` and the
children's bound law (the hypothesis shape `iloop_bp_le`/`loopBoundInv_loop` use). -/
theorem iloop_bInv (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, q.2.B' ≤ q.1.B) →
      (∀ (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
        IStep t B l st₁ st₂ c fo' → ChildLabelFloor st₁ fo') →
      LoopBInv B st → LoopBInv B stf := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ _ hinv => hinv
  | step hne hg hstep hrest ih =>
    intro hble hfloor hinv
    exact ih (fun q hq => hble q (List.mem_cons_of_mem _ hq)) hfloor
      (istep_bInv_of_le t B l hstep (hble _ List.mem_cons_self) (hfloor _ _ _ _ hstep))

/-! ## The mint floor — Theorem T's value half -/

/-- The loop state's own mints are its group members at their own labels: `mints` is
`J.toList.map (⟨sel j, d3 (sel j)⟩)`, `pl` is `resid`, and `sel j ∈ resid j` (`hsel`). -/
theorem istep_mint_shape (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    ∀ m ∈ st'.mints, (∃ j, m.x ∈ st'.pl j) ∧ st'.d m.x = m.val := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  have hd : st'.d = d3 := by rw [hst']
  have hplEq : ∀ j, st'.pl j = resid j := by intro j; rw [hst']
  have hmints : st'.mints = J.toList.map (fun j => Mint.mk (sel j) (d3 (sel j))) := by rw [hst']
  intro m hm
  rw [hmints] at hm
  obtain ⟨j, hj, hjm⟩ := List.mem_map.mp hm
  rw [← hjm]
  exact ⟨⟨j, by rw [hplEq j]; exact (hsel j (Finset.mem_toList.mp hj)).1⟩, by rw [hd]⟩

/-- **One iteration's final mints are floored by its own bound**, given `LoopBInv` at the
*post* state — the review's route: `sel j ∈ resid j = st'.pl j`, and `st'.bp = fo'.B'` (the
`IStep` equation), so `LoopBInv` gives `st'.bp ≤ st'.d (sel j) = m.val`.  Selection *minimality*
is not used (it points the wrong way); the post-state invariant supplies the floor. -/
theorem istep_mintFloor (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hinv : LoopBInv B st') : ∀ m ∈ st'.mints, st'.bp ≤ m.val := by
  have hshape := istep_mint_shape t B l h
  intro m hm
  obtain ⟨⟨j, hj⟩, hlab⟩ := hshape m hm
  rw [← hlab]
  exact hinv j m.x hj

/-- **The minimal form**: the mint bound follows from `MintPreFloor` — the selected keys sit at
`≥ fo'.B'` *before* the parent's sweep — plus the child's bound law.  Strictly weaker than
`LoopBInv`: nothing is said about residual members the final iteration did not re-select. -/
theorem istep_mintFloor_of_pre (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hble : fo'.B' ≤ c.B) (hpre : MintPreFloor st' fo') :
    ∀ m ∈ st'.mints, st'.bp ≤ m.val := by
  have hshape := istep_mint_shape t B l h
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  have hbp : st'.bp = fo'.B' := by rw [hst']
  have hd : st'.d = d3 := by rw [hst']
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := by rw [← hsweep]
  have hBi : fo'.B' ≤ Bi := by
    rw [hc] at hble
    simpa using hble
  intro m hm
  rw [hbp]
  have hfloor : fo'.B' ≤ fo'.d' m.x := hpre m hm
  have hval : d3 m.x = m.val := by
    rw [← hd]
    exact (hshape m hm).2
  rcases sweepEvts_label_cases B Bi fo'.evts fo'.d' D2 m.x with hcases | hcases
  · rw [← hval, hd3, hcases]
    exact hfloor
  · rw [← hval, hd3]
    exact hBi.trans hcases

/-- The loop-level mint floor from `LoopBInv` (floor at the initial state's mints). -/
theorem iloop_mintFloor (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, q.2.B' ≤ q.1.B) →
      (∀ (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
        IStep t B l st₁ st₂ c fo' → ChildLabelFloor st₁ fo') →
      LoopBInv B st → (∀ m ∈ st.mints, st.bp ≤ m.val) →
      ∀ m ∈ stf.mints, stf.bp ≤ m.val := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ _ _ hm => hm
  | step hne hg hstep hrest ih =>
    intro hble hfloor hinv h0
    have hinv' := istep_bInv_of_le t B l hstep (hble _ List.mem_cons_self)
      (hfloor _ _ _ _ hstep)
    exact ih (fun q hq => hble q (List.mem_cons_of_mem _ hq)) hfloor hinv'
      (istep_mintFloor t B l hstep hinv')

/-- The loop-level mint floor from the **minimal** premise `MintPreFloor`. -/
theorem iloop_mintFloor_of_pre (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, q.2.B' ≤ q.1.B) →
      (∀ (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
        IStep t B l st₁ st₂ c fo' → MintPreFloor st₂ fo') →
      (∀ m ∈ st.mints, st.bp ≤ m.val) → ∀ m ∈ stf.mints, stf.bp ≤ m.val := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ _ hm => hm
  | step hne hg hstep hrest ih =>
    intro hble hpre h0
    exact ih (fun q hq => hble q (List.mem_cons_of_mem _ hq)) hpre
      (istep_mintFloor_of_pre t B l hstep (hble _ List.mem_cons_self)
        (hpre _ _ _ _ hstep))

/-- **The tail's return mint bound** (`out.B' ≤ m.val`): the tail keeps the state's mints, a
minted key is still keyed by `𝒟` (`hkey`, `iloop_mints_keys`), so `tailBP = st.bp` and the
state-level floor carries over.  This is the `tailBP` step of the review's route. -/
theorem tail_mintFloor (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hmint : ∀ m ∈ st.mints, st.bp ≤ m.val) (hkey : ∀ m ∈ st.mints, st.D m.x ≠ none) :
    ∀ m ∈ (callOut (tail B S W st)).mints, (callOut (tail B S W st)).B' ≤ m.val := by
  intro m hm
  have hemp : ¬ DS.IsEmpty st.D := fun h => hkey m hm (h m.x)
  show tailBP B st ≤ m.val
  rw [tailBP_of_not_isEmpty B st hemp]
  exact hmint m hm

/-- **`recur_mintFloor` — `out.B' ≤ m.val` at exactly the shape `Run.recur` returns**, from the
`LoopBInv` route.  Every premise is a `Run.recur` field or `LabelFloorHyp`. -/
theorem recur_mintFloor (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
    (hst0 : st0 = mkInit e fo piv) (hloop : ILoop t e.B e.l st0 qs stf)
    (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (hfloor : LabelFloorHyp (G := G) (s := s) t) :
    ∀ m ∈ (callOut (tail e.B e.S fo.W stf)).mints,
      (callOut (tail e.B e.S fo.W stf)).B' ≤ m.val := by
  have hfloor' : ∀ (st₁ st₂ : RState G s fo.p) (c : CallEntry G s) (fo' : CallOut G s),
      IStep t e.B e.l st₁ st₂ c fo' → ChildLabelFloor st₁ fo' :=
    fun st₁ st₂ c fo' hstep => hfloor e.B e.l st₁ st₂ c fo' hstep
  have hinv0 : LoopBInv e.B st0 := by
    rw [hst0]
    exact loopBInv_init e fo piv hpiv
  have hmint0 : ∀ m ∈ st0.mints, st0.bp ≤ m.val := by
    rw [hst0, mkInit_mints]
    exact fun m hm => absurd hm List.not_mem_nil
  have hble : ∀ q ∈ qs, q.2.B' ≤ q.1.B := fun q hq => run_le_bound t (hchildren q hq)
  have hinv : LoopBInv e.B stf := iloop_bInv t e.B e.l hloop hble hfloor' hinv0
  have hmint : ∀ m ∈ stf.mints, stf.bp ≤ m.val :=
    iloop_mintFloor t e.B e.l hloop hble hfloor' hinv0 hmint0
  have hkey : ∀ m ∈ stf.mints, stf.D m.x ≠ none := by
    refine iloop_mints_keys t e.B e.l hloop ?_
    rw [hst0, mkInit_mints]
    exact fun m hm => absurd hm List.not_mem_nil
  exact tail_mintFloor e.B e.S fo.W stf hmint hkey

/-- **The same `recur` bound from the minimal premise `MintPreFloor`** (no `LoopBInv`). -/
theorem recur_mintFloor_of_pre (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hst0 : st0 = mkInit e fo piv) (hloop : ILoop t e.B e.l st0 qs stf)
    (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (hpre : MintPreHyp (G := G) (s := s) t) :
    ∀ m ∈ (callOut (tail e.B e.S fo.W stf)).mints,
      (callOut (tail e.B e.S fo.W stf)).B' ≤ m.val := by
  have hpre' : ∀ (st₁ st₂ : RState G s fo.p) (c : CallEntry G s) (fo' : CallOut G s),
      IStep t e.B e.l st₁ st₂ c fo' → MintPreFloor st₂ fo' :=
    fun st₁ st₂ c fo' hstep => hpre e.B e.l st₁ st₂ c fo' hstep
  have hmint0 : ∀ m ∈ st0.mints, st0.bp ≤ m.val := by
    rw [hst0, mkInit_mints]
    exact fun m hm => absurd hm List.not_mem_nil
  have hble : ∀ q ∈ qs, q.2.B' ≤ q.1.B := fun q hq => run_le_bound t (hchildren q hq)
  have hmint : ∀ m ∈ stf.mints, stf.bp ≤ m.val :=
    iloop_mintFloor_of_pre t e.B e.l hloop hble hpre' hmint0
  have hkey : ∀ m ∈ stf.mints, stf.D m.x ≠ none := by
    refine iloop_mints_keys t e.B e.l hloop ?_
    rw [hst0, mkInit_mints]
    exact fun m hm => absurd hm List.not_mem_nil
  exact tail_mintFloor e.B e.S fo.W stf hmint hkey

/-- **Theorem T's value bound at every `Run` return**: `out.B' ≤ m.val` for every final mint,
from the label floor. -/
theorem run_mintFloor (t : ℕ) (hfloor : LabelFloorHyp (G := G) (s := s) t) :
    ∀ {e : CallEntry G s} {out : CallOut G s},
      Run t e out → ∀ m ∈ out.mints, out.B' ≤ m.val := by
  intro e out h
  induction h with
  | base hl hb =>
    intro m hm
    exact absurd hm List.not_mem_nil
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro m hm
    exact recur_mintFloor t hfp hpiv hst0 hloop hchildren
      hfloor m hm

/-- **Theorem T's value bound from the minimal premise** (`MintPreFloor`, no `LoopBInv`). -/
theorem run_mintFloor_of_pre (t : ℕ) (hpre : MintPreHyp (G := G) (s := s) t) :
    ∀ {e : CallEntry G s} {out : CallOut G s},
      Run t e out → ∀ m ∈ out.mints, out.B' ≤ m.val := by
  intro e out h
  induction h with
  | base hl hb =>
    intro m hm
    exact absurd hm List.not_mem_nil
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    intro m hm
    exact recur_mintFloor_of_pre t hst0 hloop hchildren
      hpre m hm

/-! ## The leaves: the gate is the returned bound, so the cap cannot bite it

`A4.LeafFloor` refutes the *refusal* floor `ChildFloor` on capped base exits: its gate is the
child's entry bound `c.B`, and a cap-limited leaf abandons `(B'⁺, c.B)` with stale labels.  The
premise this file uses is gated at the leaf's **returned** bound instead; the two gates agree
exactly on full leaves.  Nothing unconditional below is stated at `c.B`. -/

/-- A base leaf's returned bound is `B'⁺`, and `B'⁺ ≤ c.B` (the V5 cap law). -/
theorem baseOut_gate {t : ℕ} {c : CallEntry G s} {bout : BaseOut G s}
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout) :
    (baseOut bout).B' = bout.B'_plus ∧ bout.B'_plus ≤ c.B := by
  refine ⟨rfl, ?_⟩
  obtain ⟨_cst, st, _hloop, hr⟩ := hb
  subst hr
  exact v5Cap_le_bound _ _ _

/-- **The full/cap split of the premise at a base leaf.**  On a **full** leaf
(`bout.D_final` drained — `LeafFloor.childFloor_base_of_full`'s regime, where Lemma 3.1\*'s
dichotomy gives `B'⁺ = c.B`) the returned-bound gate *is* the `c.B` gate; on a capped exit the
returned-bound gate is the strictly weaker (or equal) one, which is why `LeafFloor`'s capped
counterexample does not refute `ChildLabelFloor`.  Both directions are recorded so the joint
induction can choose the branch explicitly rather than assume the unconditional `c.B` form. -/
theorem childLabelFloor_base_gate {p : ℕ} (st : RState G s p) {t : ℕ} {c : CallEntry G s}
    {bout : BaseOut G s} (hpre : CallPre c.B c.S c.d)
    (hb : baseRun t ⟨c.B, c.S, c.d, initD c.S c.d⟩ bout)
    (hfull : DS.IsEmpty bout.D_final) :
    ChildLabelFloor st (baseOut bout) ↔
      ∀ j, ∀ y ∈ st.pl j, y ∉ settledSet bout.evts → c.B ≤ bout.d' y := by
  have hlem := baseRun_lemma31 (⟨hpre, rfl⟩ : ReachBase ⟨c.B, c.S, c.d, initD c.S c.d⟩) hb
  have hB' : (baseOut bout).B' = c.B := by
    show bout.B'_plus = c.B
    exact hlem.dichotomy.mpr hfull
  constructor
  · intro h j y hpl huns
    have := h j y hpl huns
    rwa [hB'] at this
  · intro h j y hpl huns
    rw [hB']
    exact h j y hpl huns

/-! ## The failure direction: `LoopBInv` is Theorem-T-strength, not free -/

/-- **`LoopBInv` fails on any state whose own mint set holds a sub-`bp` entry**: the mint key is
a group member (`hpl`) whose label is the minted value (`hlab`), so `LoopBInv` would force
`bp ≤ val`, contradicting `val < bp`. -/
theorem not_bInv_of_low_mint {p : ℕ} {st : RState G s p} (B : WLab G s)
    (hlab : ∀ m ∈ st.mints, st.d m.x = m.val)
    (hpl : ∀ m ∈ st.mints, ∃ j, m.x ∈ st.pl j)
    (m : Mint G s) (hm : m ∈ st.mints) (hlt : m.val < st.bp) : ¬ LoopBInv B st := by
  intro hinv
  obtain ⟨j, hj⟩ := hpl m hm
  have h := hinv j m.x hj
  rw [hlab m hm] at h
  exact absurd h (not_le.mpr hlt)

/-- The `CallOut.Premature` form (the Q12 carve-out): a premature entry of the state's own
return record refutes `LoopBInv`. -/
theorem not_bInv_of_premature {p : ℕ} {st : RState G s p} (B : WLab G s)
    (hlab : ∀ m ∈ st.mints, st.d m.x = m.val)
    (hpl : ∀ m ∈ st.mints, ∃ j, m.x ∈ st.pl j)
    {x : Fin G.n} {val : WLab G s} (hprem : (callOut st).Premature x val) :
    ¬ LoopBInv B st :=
  not_bInv_of_low_mint B hlab hpl (Mint.mk x val) hprem.1 hprem.2

/-- Loop level: any loop state reached from `mkInit` (empty mint list, so vacuous) that returns
with a `Premature` entry violates `LoopBInv`. -/
theorem iloop_not_bInv_of_premature (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ m ∈ st.mints, st.d m.x = m.val) → (∀ m ∈ st.mints, ∃ j, m.x ∈ st.pl j) →
      ∀ {x : Fin G.n} {val : WLab G s}, (callOut stf).Premature x val →
        ¬ LoopBInv B stf := by
  intro p st stf qs h hlab hpl x val hprem
  exact not_bInv_of_premature B (iloop_mints_label t B l h hlab)
    (iloop_mints_pl t B l h hpl) hprem

/-- **The concrete instance**: a `recur` loop started at `mkInit` that returns with a
`Premature` entry cannot satisfy `LoopBInv`.  Hence `LoopBInv` is not derivable from the
semantics without a floor premise, and its truth at a return is Theorem-T-strength
(`Prem = ∅`). -/
theorem not_bInv_of_loop_premature (t : ℕ) (e : CallEntry G s) (fo : FPOut G s)
    (piv : Fin fo.p → Fin G.n) {qs : List (CallEntry G s × CallOut G s)}
    {stf : RState G s fo.p} (hloop : ILoop t e.B e.l (mkInit e fo piv) qs stf)
    {x : Fin G.n} {val : WLab G s} (hprem : (callOut stf).Premature x val) :
    ¬ LoopBInv e.B stf :=
  iloop_not_bInv_of_premature t e.B e.l hloop
    (fun m hm => absurd hm (by rw [mkInit_mints]; exact List.not_mem_nil))
    (fun m hm => absurd hm (by rw [mkInit_mints]; exact List.not_mem_nil)) hprem

/-! ## Exact signatures and axiom audit -/

#check @LoopBInv
#check @ChildLabelFloor
#check @LabelFloorHyp
#check @MintPreFloor
#check @MintPreHyp
#check @istep_bInv
#check @iloop_bInv
#check @istep_mintFloor
#check @istep_mintFloor_of_pre
#check @tail_mintFloor
#check @recur_mintFloor
#check @run_mintFloor
#check @run_mintFloor_of_pre
#check @childLabelFloor_base_gate
#check @not_bInv_of_loop_premature

#print axioms istep_bInv
#print axioms run_mintFloor
#print axioms run_mintFloor_of_pre
#print axioms childLabelFloor_base_gate
#print axioms not_bInv_of_loop_premature

end DMSY
end Frontier

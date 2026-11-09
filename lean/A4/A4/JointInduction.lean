import A4.Main
import A4.PremLabelKey
import A4.MintPreFloor
import A4.ReachInv

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.JointInduction — the §8.1 first-violation induction, transcribed and wired

## 1. Transcription of the hand proof (`research/CORRECTED_PROOF.md` §4.4, §8; audit `PROOF.md` §3–§9)

**What is inducted on.**  Not execution steps and not mint depth: the induction is on the
**settlement-event index** — the position of a settlement batch in the call's settlement log
`U` (`CallOut.evts` here).  `§4.4` is explicit: *"a first-violation induction on settlement
batches (PROOF.md §3)"*, and `§8.1` names its content: Lemma W (window), Lemma V (no sub-`B'`
values), Lemma Rep (custody), the `W'` drop lemma + co-settlement corollary, the refusal-floor
lemma.  The "first violation" is the **first** batch whose settlements are not complete; every
earlier batch is assumed complete (IH) and the goal is a contradiction.

**The two conjuncts, and why they are joint.**  Write
`C(ev) := Complete d[ev]` (the settlement is canonical) and
`F(σ) := dB[𝒟 ∪ P̂] ≥ β` (the bound floor at the program point σ with governing bound β).
The audit's cycle per batch is

    (IH: all earlier settlements complete)  →  F at the filter/return  →  current batch complete
    (current batch complete)               →  F at the next filter/return

i.e. completeness of settlements implies the floor (`§4.4`: *"bound invariant (Theorem T) ⟸ no
stale (incomplete) settlements"*) and the floor implies the next batch's completeness
(`§4.4`: *"completeness of W′/pulls ⟸ bound invariant at the filter"*).  Neither half is
provable alone — that is the circularity the first-violation ordering breaks.  In Lean
vocabulary the pair is `Lemma37Concl.settleComplete` (2a) and `NoPrem` (Theorem T), which is why
`Main.lean`'s two `sorry`s are one proof.

**Case split per batch** (the audit's local obligations, each with a unit here that reduces it):

| §8.1 piece | content | this tree |
|---|---|---|
| Lemma W | no live `𝒟` value `< β` at an event with governing bound β | `A4.LiveFloor`, `A4.KeyLabFloor` |
| Lemma V | no sub-`B'` value at returns/filters | `A4.LemmaV`, `A4.PremLabelKey` (`prem_empty_tail`) |
| Lemma Rep | custody of a batch across the merge/delete seams | `A4.CustodyInduction` (`freshCompleteKey_*`) |
| `W'` drop + co-settlement | a dropped re-frontiering settles or is carved out | `A4.FixStale`, `A4.Cascade` |
| refusal floor | a refused relaxation is already canonical | `A1.utilde_of_relax`, `A4.NoLoose` |
| Lemma d2 | the current `W'` batch is complete | `A4.BelowSeparator` (`ChildFloor`), `A4.SettleSweep` |
| base pulls | pull-minimality + refusal floor (`§4.1(c)`) | `A1.BaseInv`, `baseRun_lemma31` |

**Where the transcription lands in Lean.**  Per iteration (`IStep`), the invariant that must be
carried is exactly `LoopBInv` (labels of residual pivot-group members `≥` the running bound)
*plus* the floor package that produces it.  `LoopBInv`'s preservation (`istep_bInv`) needs
`ChildLabelFloor st fo'`; §2 below is that premise's exact producer: the child's **store**
accuracy (`ChildStoreTight`) plus the child's bound clause with `NoPrem` — i.e. Lemma V at the
child boundary, applied through the merge.  The residual after this file is therefore a single
named obligation, `StepFloor`, and it is Lemma W's content at a step, not a new assumption.

Credit: the induction is DMSY's / the audit's hand proof (arXiv:2602.07868v1 + `PROOF.md`);
this file only transcribes it and proves the wiring lemmas it names.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1b. Wave plan and carrier correction (2026-11-08, after `BaseCustody`)

The recur wave's three carriers, in dependency order, each with the §8.1 case it serves:

1. **`ChildFloor`** (Lemma d2 — settlement completeness at one iteration).  `JointAssembly.
   istepTrace_childStep` reduces the per-step premise to `ChildFloor` + `ChildStoreTight`, and
   `BelowSeparator.childStep_of_floor` consumes it.  **Carrier correction:** `ChildLabelFloor` /
   `LabelFloorHyp` as a *uniform* step premise is refuted — `MintPreFloor.not_childLabelFloor_base`
   refutes the floor whenever a residual group member is abandoned below the child's returned
   bound (Q12's child-interior channel), and `MintPreFloor.base_leaf_counterexample` is a
   formalized leaf where the floor's invariant `NoAbandonedBelow` fails under `CallPre` +
   `baseRun_lemma31` alone.  So the wave must carry the floor **group-restricted, inside the joint
   induction itself** (the audit's first-violation ordering supplies it exactly where the
   parent's invariant maintains it) — never as a free-standing hypothesis.
2. **`LoopBInv`** (Lemma V — no sub-`B'` values at returns/filters).  Via the group-restricted
   floor above: `istep_bInv` + `prem_empty_recur` give the value bound and Theorem T's recur half.
3. **`StepSplit`** (coverage / (J6), clause (1)'s loop invariant).  `LoopFrontier.
   child_frontier_of_lInv` consumes it; it is the entry-side premise `lemma37Hyp_of_reach` needs.

Then `hrecur` assembles by `jointChain_of_steps`, and both `Main` seams reduce to it.

**Child-entry premise.**  The base-side premise of `jointChain_of_steps_of_baseC` (entry custody,
`A4.BaseCustody`) is discharged by the recur wave's invariants per the redirect — **not** by
`Custody`: the child's store is fresh over inherited labels, so custody does not thread through
`ChildOf` (obstruction named in `A4.BaseCustody`'s docstring).  The `containR` counterexample
sketch for child base returns (same docstring) was **not** formalized — budget; the sketch stands
as recorded, and formalizing it would be a statement-level finding for the repo owner.
-/

/-! ## 2. The crux: `ChildLabelFloor` from store accuracy + the child's bound clause

`A4.LoopBInv` reduced Theorem T to `ChildLabelFloor st fo'` (every residual group member the
child did **not** settle carries a child-returned label `≥ fo'.B'`).  `MintPreFloor` showed that
at a leaf this is *not* a consequence of the leaf interface — a low label need not have a low
key.  The missing link is the store-accuracy direction `ChildStoreTight` (`A4.PremLabelKey` §2d):
a low *label* off the settled set has a low *stored value*.  Combined with the child's clause
(2b) — every stored value is `≥ fo'.B'` except the carve-out — and `NoPrem` (Theorem T, the
other half of the same induction), the floor follows.  This is Lemma V at the child boundary,
read through the store rather than through the labels. -/

/-- **Lemma V at the child boundary.**  Store accuracy (`ChildStoreTight`) + the child's bound
clause (2b) + carve-out emptiness (`NoPrem`) give `ChildLabelFloor`: every residual group member
the child left unsettled sits at or above the child's returned bound.

The two halves of the joint induction meet exactly here: (2b) is `Lemma37Concl.bound` and
`NoPrem` is Theorem T, and neither suffices alone (`bound` bounds *values*, the floor needs
*labels*, and labels only decrease — hence the store-accuracy premise).

**Caveat, so nobody carries a false invariant.**  The *global* form of `ChildStoreTight` is not
an engine invariant: at a drained leaf a vertex can be unsettled with a low label and no key at
all (`A4.MintPreFloor.base_leaf_counterexample`), so the form the induction can carry is the
group-restricted one — which is `ChildLabelFloor` itself.  The bridge below is therefore the
*reason* the floor needs accuracy (the two §8.1 halves cannot be split), not an independent
reduction of it. -/
theorem childLabelFloor_of_storeTight {p : ℕ} {st : RState G s p} {fo' : CallOut G s}
    (hbound : ∀ y val, fo'.D y = some val → fo'.B' ≤ val ∨ fo'.Premature y val)
    (hnoPrem : ∀ x val, ¬ fo'.Premature x val)
    (htight : ChildStoreTight st fo') :
    ChildLabelFloor st fo' := by
  intro j y _hy hns
  by_contra hle
  have hlt : fo'.d' y < fo'.B' := lt_of_not_ge hle
  obtain ⟨v, hv, hvlt⟩ := htight y hns hlt
  rcases hbound y v hv with hge | hprem
  · exact absurd hvlt (not_lt_of_ge hge)
  · exact hnoPrem y v hprem

/-- The same at any state, without the group hypothesis (the `LoopBInv`-free form). -/
theorem childLabelFloor_of_childBound {p : ℕ} {B : WLab G s} {st : RState G s p}
    {fo' : CallOut G s}
    (hbound : ∀ y val, fo'.D y = some val → fo'.B' ≤ val ∨ fo'.Premature y val)
    (hnoPrem : ∀ x val, ¬ fo'.Premature x val)
    (htight : ChildStoreTight st fo')
    (hmono : ∀ y, fo'.d' y ≤ st.d y) :
    ChildLabelFloor st fo' := by
  intro j y _hy hns
  by_contra hle
  have hlt : fo'.d' y < fo'.B' := lt_of_not_ge hle
  obtain ⟨v, hv, hvlt⟩ := htight y hns hlt
  rcases hbound y v hv with hge | hprem
  · exact absurd hvlt (not_lt_of_ge hge)
  · exact hnoPrem y v hprem

/-! ## 3. The joint invariant, and Theorem T's two halves from it -/

/-- The joint invariant at a return: the full Lemma 3.7\* conclusion together with carve-out
emptiness (Theorem T).  This is `Main.JointChain`'s body, named so the induction hypothesis can
be stated as a lemma about children. -/
def JointInv (t : ℕ) (e : CallEntry G s) (out : CallOut G s) : Prop :=
  Lemma37Concl (Full t) e out ∧ NoPrem e out

theorem JointInv.concl {t : ℕ} {e : CallEntry G s} {out : CallOut G s} (h : JointInv t e out) :
    Lemma37Concl (Full t) e out := h.1

theorem JointInv.noPrem {t : ℕ} {e : CallEntry G s} {out : CallOut G s} (h : JointInv t e out) :
    NoPrem e out := h.2

/-- `JointInv` is `JointChain`'s body, so the joint chain is its closure over reachable runs. -/
theorem jointChain_iff (t : ℕ) :
    JointChain (G := G) (s := s) t ↔
      ∀ (e : CallEntry G s) (out : CallOut G s),
        Reach t e → Lemma37Hyp t e → Run t e out → JointInv t e out :=
  Iff.rfl

/-- **The value bound is the whole of Theorem T** at a return: a mint's value below `B'` is a
premature entry, and (2b) puts every mint key in the returned `𝒟`. -/
theorem noPrem_of_mintValueBound (t : ℕ) {e : CallEntry G s} {out : CallOut G s}
    (hrun : Run t e out) (hb : ∀ m ∈ out.mints, out.B' ≤ m.val) :
    ∀ x val, ¬ out.Premature x val := by
  intro x val hp
  exact absurd hp.2 (not_lt_of_ge (hb (Mint.mk x val) hp.1))

/-- **Theorem T's recur half from the child-side floor** (the §8.1 induction's second clause):
a per-step `ChildStoreTight` + child bound/`NoPrem` package yields `ChildLabelFloor` at each
iteration, hence `LoopBInv` at the loop exit, hence no premature mint at the return.  The
remaining premise is `StepFloor` below. -/
theorem noPrem_recur_of_stepFloor (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t e.B e.l (mkInit e fo piv) qs stf)
    (hfloor : LoopBInv stf.bp stf) :
    ∀ x val, ¬ (callOut (tail e.B e.S fo.W stf)).Premature x val :=
  prem_empty_recur (piv := piv) hloop hfloor

/-! ## 3b. The induction itself: `JointChain` from the two per-node obligations

`JointChain` quantifies over reachable entries, so the induction is a structural recursion on the
`Run` derivation with the reachability/hypothesis package carried as a *hypothesis of the motive*:
at a `recur` node the children's `Reach` comes from `Reach.sub` + `childOf_of_recur`, and their
`Lemma37Hyp` from `A4.JointAssembly.lemma37Hyp_of_reach` (which is where the two entry-side
premises `ChildStep`-uniform and `StepSplit` enter — they are the same premises `a4_joint` needs
and are *not* consequences of `Run`).  The motive is level-split (`0 < e.l → Lemma37Hyp t e`)
because a reachable entry can be a level-`0` child, where `Lemma37Hyp` is false and the base
obligation applies instead; `JointChain`'s own statement only ever asks for the `0 < e.l` case,
so the split loses nothing. -/

/-- **`JointChain` from the two per-node obligations.**  `hbase` is Lemma 3.1\*'s return at a
level-`0` entry; `hrecur` is §8.1's first-violation step at a `recur` node, taking the induction
hypothesis at every child.  With these (plus the two entry-side premises `A4.JointAssembly`
already isolates) both `Main.lean` seams follow. -/
theorem jointChain_of_steps (t : ℕ) (ht : 2 ≤ t)
    (hcs : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st₁ st₂ : RState G s p)
      (c : CallEntry G s) (fo' : CallOut G s), IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo')
    (hsplit : ∀ (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)), StepSplit t B l S)
    (hbase : ∀ {e : CallEntry G s} {bout : BaseOut G s}, Reach t e → e.l = 0 →
      baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout → JointInv t e (baseOut bout))
    (hrecur : ∀ {e : CallEntry G s} {fo : FPOut G s} {piv : Fin fo.p → Fin G.n}
      {st0 stf : RState G s fo.p} {qs : List (CallEntry G s × CallOut G s)}
      (_hl : 0 < e.l) (_hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
      (_hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
      (_hst0 : st0 = mkInit e fo piv) (_hloop : ILoop t e.B e.l st0 qs stf)
      (_hchildren : ∀ q ∈ qs, Run t q.1 q.2),
      (∀ q ∈ qs, JointInv t q.1 q.2) → Lemma37Hyp t e →
        JointInv t e (callOut (tail e.B e.S fo.W stf))) :
    JointChain (G := G) (s := s) t := by
  have key : ∀ {e : CallEntry G s} {out : CallOut G s}, Run t e out → Reach t e →
      (0 < e.l → Lemma37Hyp t e) → JointInv t e out := by
    intro e out hrun
    induction hrun with
    | base hl hb =>
      intro hre hhyp
      exact hbase hre hl hb
    | recur hl hfp hpiv hst0 hloop hchildren ih =>
      intro hre hhyp
      refine hrecur hl hfp hpiv hst0 hloop hchildren (fun q hq => ?_) (hhyp hl)
      refine ih q hq (Reach.sub hre (childOf_of_recur t hl hfp hpiv hst0 hloop hchildren hq))
        (fun hpos => ?_)
      exact lemma37Hyp_of_reach t ht hcs hsplit
        (Reach.sub hre (childOf_of_recur t hl hfp hpiv hst0 hloop hchildren hq)) hpos
  intro e out hre hyp hrun
  exact key hrun hre (fun _ => hyp)

/-! ## 3c. Wave slice (1): Theorem T from the group-restricted floor

The wave's target, stated exactly.  `LabelFloorHyp` — the per-step `ChildLabelFloor`, i.e. the
floor **exactly at the parent's residual groups** (the `PremLabelKey` reading) — gives the value
bound at every run (`LoopBInv.run_mintFloor`), and the value bound is the whole of Theorem T
(`noPrem_of_mintValueBound`).  No reachability is needed: the value bound holds for every run.

**Scoping of the first instance (this slice's finding).**  The instance cannot be taken at an
arbitrary leaf — `MintPreFloor.not_childLabelFloor_base` refutes the floor there whenever a
residual group member is abandoned below the child's returned bound, and
`base_leaf_counterexample` formalizes a leaf where the floor's invariant fails outright — and at
the **top-level base call** there are no steps at all, so `hrecur` is never invoked on one.  The
first real instance is therefore at a **recur step of a reachable run**, and its missing producer
is exactly the parent-side linkage `MintPreFloor`'s closing note names: `resid j ⊆ expand … S_i B_i`
(every residual group member lies in the child's seed expansion, hence settles unless it is the
carve-out).  That linkage is the wall; this theorem pins what it buys when it lands. -/

/-- **Theorem T from the group-restricted floor.**  Byte-identical `@TheoremT` statement; the
premise is the wave's target (`LabelFloorHyp`, the floor at the parent's residual groups).  As a
*uniform* statement the premise is refuted (`MintPreFloor.not_childLabelFloor_base`,
`base_leaf_counterexample`), so this is the target of the wave, not its completion. -/
theorem theoremT_of_labelFloorHyp (t : ℕ) (hfloor : LabelFloorHyp (G := G) (s := s) t) :
    @TheoremT G s (@Reach G s t) (@Run G s t) := by
  intro e out _hre hrun x val hp
  exact noPrem_of_mintValueBound t hrun
    (run_mintFloor (G := G) (s := s) t hfloor hrun) x val hp

/-- **The linkage, one half of it, from `expand`'s own definition** (`A4.Semantics`): if group
`j`'s pivot is pulled (`piv j ∈ Si`) and `j` is live (`piv j ∈ pl j`), then every member of the
group whose label is below the child's separator `Bi` **is** in the child's seed set. -/
theorem mem_expand_of_group_low {d : Labels G s} {p : ℕ} {pl : Fin p → Finset (Fin G.n)}
    {piv : Fin p → Fin G.n} {Si : Finset (Fin G.n)} {Bi : WLab G s} {j : Fin p} {y : Fin G.n}
    (hpiv : piv j ∈ Si ∧ piv j ∈ pl j) (hy : y ∈ pl j) (hlt : d y < Bi) :
    y ∈ expand d pl piv Si Bi := by
  rw [expand]
  refine Finset.mem_union_right _ ?_
  exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j,
    (by rw [if_pos hpiv]; exact Finset.mem_filter.mpr ⟨hy, hlt⟩)⟩

/-! ## 3d. Scoping note: the wall, after reading A2/A3 (2026-11-08)

The contract vocabulary **does** expose the membership half of the linkage: `IStep`'s child entry
is `c = ⟨Bi, expand st.d st.pl st.piv Si Bi, l - 1, st.d⟩` (`Semantics` BM.12), and `expand`'s
definition puts every group member with `d v < Bi` into `c.S` whenever the group's pivot is
pulled — `mem_expand_of_group_low` above is that one-liner.  A3's `pullRun` supplies `Si =
belowKeys st.D Bi` (`pullRun_pulled`) and the separator law.

**The wall moved, and is now located exactly.**  Two halves remain, and neither is definitional:

1. **The pivot-pulled side needs the pre-state fact** `piv j ∈ Si ∧ piv j ∈ pl j` for the group
   the floor quantifies over — i.e. the floor's groups must be the ones *this* iteration expands,
   which is the correspondence between `ChildLabelFloor st fo'`'s `j` and the step's own `Si`
   (`JointAssembly.istepTrace_child_d`-style bookkeeping).
2. **The pivot-not-pulled side has no expansion**: members of `pl j` with `piv j ∉ Si` are not in
   `c.S` at all, and their non-abandonment must come from the bound monotonicity / sweep-gate
   content (Lemma W's window), not from `expand`.

So the route to `LabelFloorHyp` is: (half 1, above) + (half 2, Lemma W) + the child's
`Lemma37Concl.identity` (y ∈ c.S settles unless carve-out) + `NoPrem` — i.e. exactly the audit's
joint first-violation induction, now with each ingredient's producer named.  This confirms the
carrier correction: nothing here yields the floor as a free-standing hypothesis.

Half 1's membership lemma (`y ∈ pl j → d y < Bi → y ∈ expand …`, pivot-pulled) was drafted and
is a one-liner from `expand`'s own definition (`rw [expand]`, then `Finset.mem_biUnion` + the
group's filter), but was **not landed**: its compile verification was cut off by host pressure
and an unverified lemma is worse than no lemma.  It is the first line of the next session. -/

/-! ### 3d.1. Half 1 landed: the step's own expansion, unpacked -/

/-- **The `IStep` unpacking**: a step determines its pull witnesses, and the child entry's seed
set is the step's own expansion.  This is the mechanical `obtain` the half-1 instantiation needs,
pinned as a lemma so callers do not repeat the seventeen-field destructure. -/
theorem istep_unpack {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    ∃ Si : Finset (Fin G.n), ∃ Bi : WLab G s, ∃ D1 : DS G s,
      pullRun (pullCap t l) st.D B Si Bi D1 ∧
        c = ⟨Bi, expand st.d st.pl st.piv Si Bi, l - 1, st.d⟩ := by
  obtain ⟨Si, Bi, D1, -, -, -, -, -, -, hpull, hc, -, -, -, -, -, -⟩ := h
  exact ⟨Si, Bi, D1, hpull, hc⟩

/-- **Half 1, at the unpacked components**: a residual-group member whose label is below the
separator and whose group's pivot is pulled is in the child's seeds.  This is
`mem_expand_of_group_low` instantiated at the step's own `pl`/`piv`/`Si`/`Bi` through the child
entry's defining equation. -/
theorem seed_of_expand_mem {d : Labels G s} {p : ℕ} {pl : Fin p → Finset (Fin G.n)}
    {piv : Fin p → Fin G.n} {Si : Finset (Fin G.n)} {Bi : WLab G s} {c : CallEntry G s}
    {l : ℕ} (hc : c = ⟨Bi, expand d pl piv Si Bi, l - 1, d⟩)
    {j : Fin p} {y : Fin G.n} (hpiv : piv j ∈ Si) (hmem : piv j ∈ pl j)
    (hypl : y ∈ pl j) (hlt : d y < Bi) :
    y ∈ c.S := by
  rw [hc]
  exact mem_expand_of_group_low ⟨hpiv, hmem⟩ hypl hlt

/-! ### 3d.2. Half 2 scoped: the wall is the audit's window argument itself

`istep_bInv`/`istep_bInv_of_le` (`A4.LoopBInv`) maintain `LoopBInv` from `ChildLabelFloor st fo'`
— so half 2 cannot be derived *from* them (that is the circle).  What the sweep gate actually
gives (`sweepEvts_label_cases`) is "a label is *unchanged* or `≥ lo`": a not-expanded group
member whose label was already low keeps its low label through the step, so the window must come
from `LoopBInv B st` **at the pre-state** plus `BpChain` — and comparing `st.bp ≤ st'.bp` is the
per-call `B'` monotonicity that `CORRECTED_PROOF` §8 item 5 flags as unproved even at sketch
grade (`A4.ReturnClauses`: "`BpChain` is the one genuinely inductive premise here").  So half 2
is not a lemma in `A4.BpMonotonicity`/`A4.ValueBpChain` — it **is** the audit's Lemma W window
argument applied at post-sweep labels, i.e. the last genuinely open mathematical content on the
base-side path.  Scope for its proof: carry `BpChain` (or the equivalent `bp ≤ st'.bp` per step)
plus `LoopBInv B st` and read the unchanged-label case through `sweepEvts_label_cases`; the
changed-label case is floored by the gate (`lo = Bi = c.B ≥ st'.bp` needs `BpChain`). 
**DETERMINATION (wave slice 2, 2026-11-08): outcome (b) — PARTIAL; per-step monotonicity is
AVAILABLE under two sourced hypotheses.**  `BpMonotonicity.istep_bp_mono` gives `st.bp ≤ st'.bp`
per `IStep` from `SeedFloor st.bp c` + `SeedChildFloor c fo'`, and
`BpMonotonicity.istep_bp_mono_of_liveFloor` sources the first from `LiveFloor st`
(`istep_seedFloor`).  Half 2's assembly is therefore: carry `LiveFloor st` + `SeedChildFloor
c fo'` (the seed-restricted cousins of `LoopBInv`/`ChildLabelFloor`), take `st.bp ≤ st'.bp` from
`istep_bp_mono_of_liveFloor`, read the unchanged-label case through `sweepEvts_label_cases` with
`LoopBInv B st`, and floor the changed-label case by the gate (`lo = Bi = c.B ≥ st'.bp` via the
monotonicity).  Still missing for `LabelFloorHyp`: the assembly itself, plus the sources of
`LiveFloor`/`SeedChildFloor` at reachable steps.

**DETERMINATION 2 (sourcing): `LiveFloor` is (c) — refuted in-tree; `SeedChildFloor` is (a) at
full leaves, unsourced at capped returns.**  `LiveFloor.st'_not_liveFloor` is a formalized `¬
LiveFloor st'` at a genuine step, so the `istep_bp_mono_of_liveFloor` route is dead at general
steps.  `SeedChildFloor c co` (`∃ v ∈ c.S, dis v ≤ co.B'`, paper (R5)) **is** discharged in the
full-leaf regime: `KeyLabFloor.seedChildLabFloor_of_bound_eq` gives it from `B' = c.B` +
`CallPre.inRange`; no producer is named at capped returns.  Net: half 2's monotonicity is
available exactly where the child's returned bound equals the separator (full leaves); the
capped case is `CORRECTED_PROOF` §8-item-5 class — either prove `BpChain` at capped exits as its
own slice, or carry `SeedFloor`/`SeedChildFloor` as the named premises (the containR/2≤t
pattern; recommendation for the repo owner recorded here).

**PERSISTENCE LEMMA SCOPED (2026-11-08): moved wall, two parts.**  (i) At a base leaf the sweep
is A1's **ungated** `relaxEdge`/`sweep` (accept = `cand ≤ d dst ∧ cand < B`), so a *touched*
member's label can drop arbitrarily far below the running bound — the persistence statement
holds only for **untouched** vertices (`bout.d' y = st.d y`); the gated form
(`sweepEvts_label_cases`: unchanged or `≥ lo`) belongs to the recur-side `RState` sweep, not to
the leaf.  (ii) The separator law `c.B ≤ st.d y` for residual members is **unsourced**:
`LoopBInv B st` floors members at `st.bp ≤ c.B` (wrong direction), and `st.bp = c.B` needs the
full-leaf dichotomy *at the pre-child state* — `LoopBInv`'s own maintenance again.  Half 2 at
full leaves waits on: untouched-member persistence (easy, from `sweep`'s equations) + the
separator law at `bp = B` (a `LoopBInv`-maintenance half).  Both named, neither landed.

**FULL-LEAF CASE SCOPED (2026-11-08): the (R5)→group lift is real, not a one-liner.**
`SeedChildFloor` (one seed's `dis ≤ B'`) does not lift to `ChildLabelFloor st (baseOut bout)`
(∀ residual member y ∉ U: `B'⁺ ≤ bout.d' y`) by existence: the quantifier is over every group
member, and the leaf only *lowers* labels (`bout.d' y ≤ st.d y`), so `LoopBInv B st`'s
`st.bp ≤ st.d y` points the wrong way.  The true route is gated-persistence: the leaf's sweeps
are (E2)-gated, so an untouched member keeps `st.d y`, and `B'⁺ = c.B` (dichotomy) plus the
separator law must give `c.B ≤ st.d y` for group members — which is half of `LoopBInv`'s
maintenance again (the changed case), while touched members need the gate `≥ lo`.  So the
full-leaf case is *half 2 applied once more*, not a consequence of (R5); it waits on the same
`BpChain`-at-capped/gated-exits input as the capped case.  Recommendation unchanged (two-out),
now with the sharpened note that both regimes reduce to the same missing input: **label
persistence under gated sweeps below the running bound**.
-/

/-- **Part (i), standalone**: a vertex that is not the destination of a relaxation keeps its
label (`relaxEdge`'s accept branch writes only the head). -/
theorem relaxEdge_untouched_label {B : WLab G s} {d : Labels G s} {D : DS G s} {e : Fin G.m}
    {y : Fin G.n} (hd : G.dst e ≠ y) : (relaxEdge B d D e).1 y = d y := by
  unfold relaxEdge
  split
  · dsimp only
    exact Function.update_of_ne (Ne.symm hd) (ext (d (G.src e)) e) d
  · rfl

/-- **Part (i) — untouched-member persistence for A1's ungated sweep**: a vertex that is the
destination of no swept edge keeps its label.  **Regime-split receipt:** at base leaves this is
the *only* persistence half available — A1's sweep is ungated (accept = `cand ≤ d dst ∧ cand
< B`), so a *touched* member's label can drop arbitrarily far below the running bound; the gated
form (unchanged-or-`≥ lo`) is the recur-side `RState` sweep's (`sweepEvts_label_cases`). -/
theorem sweep_untouched_label (B : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) :
    ∀ (d : Labels G s) (D : DS G s) (y : Fin G.n),
      (∀ e ∈ es, G.dst e ≠ y) → (sweep B u es d D).1 y = d y := by
  induction es with
  | nil => intro d D y _; rfl
  | cons e es ih =>
    intro d D y htouch
    rw [sweep]
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      have hd : G.dst e ≠ y := htouch e List.mem_cons_self
      rw [ih (relaxEdge B d D e).1 (relaxEdge B d D e).2 y
        (fun e' he' => htouch e' (List.mem_cons_of_mem e he')),
        relaxEdge_untouched_label hd]
    · rw [if_neg hs, if_neg hs]
      exact ih d D y (fun e' he' => htouch e' (List.mem_cons_of_mem e he'))

/-! ## 4. The residual, stated once

`StepFloor` is everything §8.1's Lemma W/V package delivers at one iteration, in the form
`A4.LoopBInv.istep_bInv` consumes.  `A4.PremLabelKey`'s leaf analysis (`MintPreFloor`) shows it
is **not** a consequence of `CallPre + baseRun_lemma31`; it comes from the parent's
`pullRun`/`expand`/`FPContract` residual linkage (`resid j ⊆ expand … S_i B_i`).  Naming it here
means the induction's shape is complete and one obligation is left, not six. -/

/-- The per-step floor the joint induction carries (§8.1 Lemma V at an iteration boundary). -/
def StepFloor (t : ℕ) : Prop :=
  ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p) (c : CallEntry G s)
    (fo' : CallOut G s), IStep t B l st st' c fo' → ChildLabelFloor st fo'

end DMSY
end Frontier

/-! ## 5. Axiom audit -/

#print axioms Frontier.DMSY.relaxEdge_untouched_label
#print axioms Frontier.DMSY.sweep_untouched_label
#print axioms Frontier.DMSY.istep_unpack
#print axioms Frontier.DMSY.seed_of_expand_mem
#print axioms Frontier.DMSY.mem_expand_of_group_low
#print axioms Frontier.DMSY.jointChain_of_steps
#print axioms Frontier.DMSY.childLabelFloor_of_storeTight
#print axioms Frontier.DMSY.childLabelFloor_of_childBound
#print axioms Frontier.DMSY.noPrem_of_mintValueBound
#print axioms Frontier.DMSY.noPrem_recur_of_stepFloor

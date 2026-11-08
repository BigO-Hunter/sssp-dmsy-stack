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
*labels*, and labels only decrease — hence the store-accuracy premise). -/
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

#print axioms Frontier.DMSY.jointChain_of_steps
#print axioms Frontier.DMSY.childLabelFloor_of_storeTight
#print axioms Frontier.DMSY.childLabelFloor_of_childBound
#print axioms Frontier.DMSY.noPrem_of_mintValueBound
#print axioms Frontier.DMSY.noPrem_recur_of_stepFloor

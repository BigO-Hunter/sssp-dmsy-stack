import A4.BaseContain
import A4.ReturnClauses

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.BaseCustody — `containR` at a level-`0` return, down to entry custody

`A4.BaseContain` left `containR` as the single base-side gap.  This file closes it **modulo one
named premise**, and identifies that premise exactly.

## The mechanism

`A4.ReturnClauses.callOut_tail_containR` proves `containR` at a tail from `Custody` — "a live
label is settled or queued" (`CustodyL`).  The same argument works at a level-`0` return, and the
base loop **preserves** custody: its sweeps only write a label through an accepted relaxation,
and an accepted relaxation inserts (`relaxEdge`'s accept branch is `DS.insert` at the head).  So
this file mirrors `A4.ReturnClauses`'s gated-sweep custody lemmas for A1's **ungated** engine —
`relaxEdge_custody`, `sweep_custody`, `iter_custody`, `loop_custody` — and reads the invariant at
the exit (`base_custody_of_entry`), then `base_containR_of_entryCustody`.

## What is left, and why it is load-bearing

Custody must hold at the loop's **initial** state `⟨e.d, initD e.S e.d, [], e.B⟩`, where it reads:
*every finite entry label is a seed*.  That is true at the top-level base call (the top entry's
labels are `initLabels`, `⊤` off `{s}` = `e.S`), and for child entries it is the same `Custody`
the recur side already maintains (`A4.ReturnClauses.tail_custody`) — so it belongs to the
`Reach`-strengthening the joint chain carries, not to A1.  It is **not** derivable from
`CallPre + baseRun_lemma31`: a non-seed vertex can carry a finite entry label, be refused by
every sweep of this call, and end up the tight relaxation target of a settled vertex whose label
later dropped — written-never, keyed-never, yet `Relaxed` at the return.  (Sketch-grade; not
formalized here.)  So `hbase` reduces to **one** premise — entry custody — which is the honest
state; it is not hypothesis-free.

Credit: Lemma 3.1\*/3.7\*, Theorem T and the joint induction are DMSY's / the audit's
(arXiv:2602.07868v1, `PROOF.md` §§3–9); this file is the custody slice of formalizing them.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Custody through A1's ungated engine -/

/-- **`relaxEdge` preserves custody**: it writes a label only through the accept branch, whose
insert touches exactly the written head. -/
theorem relaxEdge_custody {B : WLab G s} {d : Labels G s} {D : DS G s} {Z : Set (Fin G.n)}
    (h : ∀ v, d v ≠ ⊤ → v ∈ Z ∨ D v ≠ none) (e : Fin G.m) :
    ∀ v, (relaxEdge B d D e).1 v ≠ ⊤ → v ∈ Z ∨ (relaxEdge B d D e).2 v ≠ none := by
  unfold relaxEdge
  by_cases hc : ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B
  · rw [if_pos hc]
    intro v hv
    dsimp only at hv ⊢
    by_cases hve : v = G.dst e
    · subst hve
      refine Or.inr ?_
      rw [DS.insert_self]
      exact DS.mergeVal_ne_none _ _
    · rw [Function.update_of_ne hve] at hv
      rw [DS.insert_of_ne D (G.dst e) _ hve]
      exact h v hv
  · rw [if_neg hc]
    intro v hv
    dsimp only at hv ⊢
    exact h v hv

/-- **`sweep` preserves custody.** -/
theorem sweep_custody (B : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) :
    ∀ (d : Labels G s) (D : DS G s) (Z : Set (Fin G.n)),
      (∀ v, d v ≠ ⊤ → v ∈ Z ∨ D v ≠ none) →
      ∀ v, (sweep B u es d D).1 v ≠ ⊤ → v ∈ Z ∨ (sweep B u es d D).2 v ≠ none := by
  induction es with
  | nil => intro d D Z h v hv; exact h v hv
  | cons e es ih =>
    intro d D Z h v hv
    rw [sweep] at hv ⊢
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs] at hv ⊢
      exact ih (relaxEdge B d D e).1 (relaxEdge B d D e).2 Z (relaxEdge_custody h e) v hv
    · rw [if_neg hs, if_neg hs] at hv ⊢
      exact ih d D Z h v hv

/-- **One iteration preserves custody**: the sweep writes only through accepted relaxations, and
the settlement log only grows. -/
theorem iter_custody (B : WLab G s) (u : Fin G.n) (x : WLab G s) (st : BState G s)
    (h : CustodyL (G := G) (s := s) st.d st.D st.evts) :
    CustodyL (G := G) (s := s) (iter B u x st).d (iter B u x st).D (iter B u x st).evts := by
  have hz : ∀ v, st.d v ≠ ⊤ →
      v ∈ (settledSet st.evts ∪ ({u} : Set (Fin G.n))) ∨ (DS.deleteSet st.D {u}) v ≠ none := by
    intro v hv
    rcases h v hv with hs | hk
    · exact Or.inl (Set.mem_union_left _ hs)
    · by_cases hvu : v = u
      · exact Or.inl (by rw [hvu]; simp)
      · exact Or.inr (by rw [DS.deleteSet_of_notMem st.D {u} v (by simpa using hvu)]; exact hk)
  intro v hv
  rw [iter] at hv ⊢
  rcases sweep_custody B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})
    (settledSet st.evts ∪ ({u} : Set (Fin G.n))) hz v hv with hs | hk
  · refine Or.inl ?_
    rw [settledSet_append_singleton]
    rcases hs with hs | hs
    · exact Set.mem_union_left _ hs
    · exact Set.mem_union_right _ hs
  · exact Or.inr hk

/-- **Custody threads through the whole loop.** -/
theorem loop_custody (t : ℕ) (B : WLab G s) :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' →
      CustodyL (G := G) (s := s) st.d st.D st.evts →
      CustodyL (G := G) (s := s) st'.d st'.D st'.evts := by
  intro c st st' h
  induction h with
  | exit h => exact fun hinv => hinv
  | @pull _ _ _ u lam x _ _ _ _ _ _ _ _ ih =>
    exact fun hinv => ih (iter_custody B u x _ hinv)

/-- **Custody at a level-`0` return, from custody at the entry state.**  The return record is the
exit state (`baseOut` projects `d' = st.d`, `D = st.D`, `evts = st.evts`). -/
theorem base_custody_of_entry {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout)
    (hc : CustodyL (G := G) (s := s) e.d (initD e.S e.d) []) :
    CustodyL (G := G) (s := s) (baseOut bout).d' (baseOut bout).D (baseOut bout).evts := by
  obtain ⟨c, st, hloop, hr⟩ := hb
  subst hr
  exact loop_custody t e.B hloop hc

/-- **`containR` at a level-`0` return**, from entry custody.  Same shape as
`A4.ReturnClauses.callOut_tail_containR`; the bound hypothesis is not needed. -/
theorem base_containR_of_entryCustody {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout)
    (hc : CustodyL (G := G) (s := s) e.d (initD e.S e.d) []) :
    ∀ v, v ∈ Relaxed (baseOut bout).d' e.B (baseOut bout).U →
      (baseOut bout).B' ≤ (baseOut bout).d' v → v ∈ DS.keys (baseOut bout).D := by
  intro v hrel _
  obtain ⟨hvU, hfin⟩ := hrel
  obtain ⟨e₀, -, -, -, hlt⟩ := hfin
  have hne : (baseOut bout).d' v ≠ ⊤ :=
    ne_top_of_lt (lt_of_lt_of_le hlt le_top)
  rcases base_custody_of_entry hb hc v hne with hs | hk
  · exact absurd hs hvU
  · exact hk

/-! ## The package: `hbase` down to entry custody -/

/-- **The level-`0` return obligation, modulo entry custody alone.**  Every clause of
`Lemma37Concl` plus `NoPrem` is now supplied by A1, `BaseReturn` and `BaseContain`; the single
remaining premise is custody at the loop's initial state — *every finite entry label is a seed* —
which holds at the top-level base call and is inherited at children from the recur side's
`Custody` (`A4.ReturnClauses.tail_custody`). -/
theorem jointInv_base_of_entryCustody {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout)
    (hc : CustodyL (G := G) (s := s) e.d (initD e.S e.d) []) :
    JointInv t e (baseOut bout) :=
  jointInv_base_of_package hre hb (base_containS hb)
    (base_containR_of_entryCustody hb hc)

/-- **The induction with `hbase` discharged down to entry custody.**  `hre` now returns the entry
contract *and* the entry-custody premise, which is the one base-side fact the `Reach`-strengthening
must carry (free at the top, inherited from the recur side's `Custody` at children). -/
theorem jointChain_of_steps_of_baseC (t : ℕ) (ht : 2 ≤ t)
    (hcs : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st₁ st₂ : RState G s p)
      (c : CallEntry G s) (fo' : CallOut G s), IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo')
    (hsplit : ∀ (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)), StepSplit t B l S)
    (hre : ∀ {e : CallEntry G s}, Reach t e → e.l = 0 →
      ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩ ∧ CustodyL (G := G) (s := s) e.d (initD e.S e.d) [])
    (hrecur : ∀ {e : CallEntry G s} {fo : FPOut G s} {piv : Fin fo.p → Fin G.n}
      {st0 stf : RState G s fo.p} {qs : List (CallEntry G s × CallOut G s)}
      (_hl : 0 < e.l) (_hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
      (_hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
      (_hst0 : st0 = mkInit e fo piv) (_hloop : ILoop t e.B e.l st0 qs stf)
      (_hchildren : ∀ q ∈ qs, Run t q.1 q.2),
      (∀ q ∈ qs, JointInv t q.1 q.2) → Lemma37Hyp t e →
        JointInv t e (callOut (tail e.B e.S fo.W stf))) :
    JointChain (G := G) (s := s) t :=
  jointChain_of_steps t ht hcs hsplit
    (fun {_ _} hreach hl hb =>
      jointInv_base_of_entryCustody (hre hreach hl).1 hb (hre hreach hl).2)
    hrecur

end DMSY
end Frontier

/-! ## Axiom audit -/

#print axioms Frontier.DMSY.relaxEdge_custody
#print axioms Frontier.DMSY.sweep_custody
#print axioms Frontier.DMSY.iter_custody
#print axioms Frontier.DMSY.loop_custody
#print axioms Frontier.DMSY.base_custody_of_entry
#print axioms Frontier.DMSY.base_containR_of_entryCustody
#print axioms Frontier.DMSY.jointInv_base_of_entryCustody
#print axioms Frontier.DMSY.jointChain_of_steps_of_baseC

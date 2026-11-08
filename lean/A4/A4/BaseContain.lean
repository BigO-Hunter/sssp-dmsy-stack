import A4.BaseReturn

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.BaseContain — `containS` at a level-`0` return (the pull remainder)

`A4.BaseReturn` left two clauses of `Lemma37Concl` un-delivered at a level-`0` return:
`containS` (this file) and `containR` (still open).

**The mechanism, in the engine's own terms.**  Algorithm 4 starts with `𝒟 = initD S d`, i.e.
every seed keyed (`initD_keys`); an iteration deletes exactly the vertex it settles
(`iter`'s `DS.deleteSet st.D {u}`) and its sweep only *inserts* (`relaxEdge` → `DS.insert`).
Hence a seed leaves `𝒟` only by being settled, which is precisely
`S ∖ settledSet evts ⊆ keys 𝒟`.  So the clause is a `Loop` induction, and it needs exactly one
engine fact: **the sweep never drops a key** (`sweep_ne_none`, from `relaxEdge_ne_none` + A0's
`DS.insert` monotonicity) — here in A1's *ungated* form, which A1 does not state.

## `containR` is not in this file

The remaining clause wants: a relaxed out-neighbour `v` of a settled vertex, at `d v < B`, is
keyed.  `BInv.frontier` gives only a *path witness* (`∃ y ∈ keys 𝒟, OnPath y v`), never
`v ∈ keys 𝒟`; and the fact that actually decides it is label **provenance** — `v`'s label is the
value of an accepted relaxation at some settled vertex, which inserted `v` and never deleted it
(`v` unsettled ⇒ never a pull-min).  A1's `BInv` carries `fresh` (stored value = current label)
but no provenance field, so `containR` needs one more loop invariant, not another consequence of
`BInv`.  Recorded rather than assumed.

Credit: Lemma 3.1\*/3.7\* and the joint induction are DMSY's / the audit's (arXiv:2602.07868v1,
`PROOF.md` §§3–9).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The sweep never drops a key (A1's ungated engine) -/

/-- **`relaxEdge` never drops a key**: it either leaves `𝒟` alone or inserts at the head
(`insert_ne_none` is A4's `Main.insert_ne_none`, i.e. A0's `DS.insert` monotonicity). -/
theorem relaxEdge_ne_none (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (x : Fin G.n) (hx : D x ≠ none) : (relaxEdge B d D e).2 x ≠ none := by
  unfold relaxEdge
  by_cases h : ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B
  · rw [if_pos h]
    exact insert_ne_none D (G.dst e) (ext (d (G.src e)) e) x hx
  · rw [if_neg h]
    exact hx

/-- **`sweep` never drops a key.** -/
theorem sweep_ne_none (B : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) :
    ∀ (d : Labels G s) (D : DS G s) (x : Fin G.n), D x ≠ none →
      (sweep B u es d D).2 x ≠ none := by
  induction es with
  | nil => intro d D x hx; exact hx
  | cons e es ih =>
    intro d D x hx
    rw [sweep]
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ x (relaxEdge_ne_none B d D e x hx)
    · rw [if_neg hs, if_neg hs]
      exact ih d D x hx

/-- One iteration settles `u` and keeps every other key. -/
theorem iter_ne_none (B : WLab G s) (u : Fin G.n) (x : WLab G s) (st : BState G s)
    (y : Fin G.n) (hy : st.D y ≠ none) (hyu : y ≠ u) : (iter B u x st).D y ≠ none := by
  show (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).2 y ≠ none
  refine sweep_ne_none B u _ _ _ y ?_
  rw [DS.deleteSet_of_notMem st.D {u} y]
  · exact hy
  · simpa using hyu

/-! ## The loop invariant and the clause -/

/-- The settlement log only grows: `settledSet (a ++ [ev]) = settledSet a ∪ {ev.v}`. -/
theorem settledSet_append_singleton (a : List (SettlementEvent G)) (ev : SettlementEvent G) :
    settledSet (a ++ [ev]) = settledSet a ∪ ({ev.v} : Set (Fin G.n)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨ev', hev', hv⟩ := hx
    rcases List.mem_append.mp hev' with hev' | hev'
    · exact Set.mem_union_left _ ⟨ev', hev', hv⟩
    · rw [List.mem_singleton] at hev'
      exact Set.mem_union_right _ (by rw [← hv, hev']; rfl)
  · intro hx
    rcases hx with hx | hx
    · obtain ⟨ev', hev', hv⟩ := hx
      exact ⟨ev', List.mem_append_left _ hev', hv⟩
    · rw [Set.mem_singleton_iff] at hx
      exact ⟨ev, List.mem_append_right _ (List.mem_singleton_self ev), by rw [hx]⟩

/-- **`LoopInvS`** — the pull remainder: a seed that is not settled is still keyed. -/
def LoopInvS (S : Finset (Fin G.n)) (st : BState G s) : Prop :=
  ((S : Set (Fin G.n)) \ settledSet st.evts) ⊆ DS.keys st.D

/-- **The invariant is preserved by one iteration**: the only key deleted is the settled `u`,
and a seed outside the new settlement set is outside the old one and is not `u`. -/
theorem loopInvS_iter {B : WLab G s} {S : Finset (Fin G.n)} {st : BState G s}
    {u : Fin G.n} {x : WLab G s} (h : LoopInvS (s := s) S st) :
    LoopInvS (s := s) S (iter B u x st) := by
  intro y hy
  obtain ⟨hyS, hyns⟩ := hy
  rw [iter] at hyns ⊢
  have hyns' : y ∉ settledSet st.evts := by
    intro hc
    exact hyns (by rw [settledSet_append_singleton]; exact Set.mem_union_left _ hc)
  have hyu : y ≠ u := by
    intro heq
    exact hyns (by
      rw [settledSet_append_singleton]
      exact Set.mem_union_right _ (by rw [heq]; rfl))
  exact iter_ne_none B u x st y (h ⟨hyS, hyns'⟩) hyu

/-- **`LoopInvS` holds through the whole loop.** -/
theorem loop_loopInvS (t : ℕ) (B : WLab G s) (S : Finset (Fin G.n)) :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' →
      LoopInvS (s := s) S st → LoopInvS (s := s) S st' := by
  intro c st st' h
  induction h with
  | exit h => exact fun hinv => hinv
  | pull u lam x hne hg hu hxgt hxle hxrest hxeq hrest ih =>
    intro hinv
    exact ih (loopInvS_iter (s := s) hinv)

/-- **`containS` at a level-`0` return**: `S ∖ (U ∪ K) ⊆ keys 𝒟_final`.  The carve-out is empty
at a base return, and `U = settledSet bout.evts`, so this is `LoopInvS` read at the exit. -/
theorem base_containS {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    ((e.S : Set (Fin G.n)) \
      ((baseOut bout).U ∪ (baseOut bout).carveKeys e.S)) ⊆ DS.keys (baseOut bout).D := by
  obtain ⟨c, st, hloop, hr⟩ := hb
  subst hr
  intro y hy
  obtain ⟨hyS, hyns⟩ := hy
  have hyns' : y ∉ settledSet st.evts := by
    intro hc
    exact hyns (Set.mem_union_left _ hc)
  have hinit : LoopInvS (s := s) e.S ⟨e.d, initD e.S e.d, [], e.B⟩ := by
    intro z hz
    obtain ⟨hzS, -⟩ := hz
    show (if z ∈ e.S then some (e.d z) else none) ≠ none
    rw [if_pos (Finset.mem_coe.mp hzS)]
    exact Option.some_ne_none (e.d z)
  exact loop_loopInvS t e.B e.S hloop hinit ⟨hyS, hyns'⟩


/-- **The induction with `containS` discharged**: `jointChain_of_steps_of_base` minus its
`containS` hypothesis, leaving `containR` as the single base-side gap. -/
theorem jointChain_of_steps_of_baseS (t : ℕ) (ht : 2 ≤ t)
    (hcs : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st₁ st₂ : RState G s p)
      (c : CallEntry G s) (fo' : CallOut G s), IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo')
    (hsplit : ∀ (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)), StepSplit t B l S)
    (hre : ∀ {e : CallEntry G s}, Reach t e → e.l = 0 →
      ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hcontainR : ∀ {e : CallEntry G s} {bout : BaseOut G s},
      baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout → ∀ v,
        v ∈ Relaxed (baseOut bout).d' e.B (baseOut bout).U →
          (baseOut bout).B' ≤ (baseOut bout).d' v → v ∈ DS.keys (baseOut bout).D)
    (hrecur : ∀ {e : CallEntry G s} {fo : FPOut G s} {piv : Fin fo.p → Fin G.n}
      {st0 stf : RState G s fo.p} {qs : List (CallEntry G s × CallOut G s)}
      (_hl : 0 < e.l) (_hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
      (_hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
      (_hst0 : st0 = mkInit e fo piv) (_hloop : ILoop t e.B e.l st0 qs stf)
      (_hchildren : ∀ q ∈ qs, Run t q.1 q.2),
      (∀ q ∈ qs, JointInv t q.1 q.2) → Lemma37Hyp t e →
        JointInv t e (callOut (tail e.B e.S fo.W stf))) :
    JointChain (G := G) (s := s) t :=
  jointChain_of_steps_of_base t ht hcs hsplit hre
    (fun hb => base_containS hb) hcontainR hrecur

/-! ## The size step is available exactly at `t ≥ 2` — the `t ∈ {0,1}` verdict

`jointChain_of_steps` needs `2 ≤ t` for one reason only: the child entry's `memCap` clause,
i.e. the size step `pullCap t l + fpCap t ≤ memCap t (l−1)` (`Structural.pullCap_add_fpCap_le_memCap`,
which takes `ht : 2 ≤ t`).  The child-seed bound `childOf_seed_size` gives
`|S_child| ≤ pullCap t l + fpCap t` and `Lemma37Hyp` asks `|S_child| ≤ memCap t (l−1)`.

**The deficit is exactly `fpCap t`.**  `memCap t (l−1) = t²·2^((l−1)t)` and
`pullCap t l = t·2^((l−1)t)`, so the inequality is equivalent to
`fpCap t ≤ t(t−1)·2^((l−1)t)`.  With `fpCap t = max 1 (t/3) ≥ 1` and `t(t−1) = 0` for
`t ∈ {0,1}`, the right side is `0` — so both low values fail, by exactly the singleton term:

* `t = 1`: `2^(l−1) + 1 > 2^(l−1)` (`ReachHyp.pullCap_add_fpCap_gt_memCap_at_one`),
* `t = 0`: `pullCap 0 l = 0`, `memCap 0 (l−1) = 0`, `fpCap 0 = 1` (`sizeStep_fails_at_zero`).

`pullCap_add_fpCap_le_memCap_iff` makes this exact: the size step holds **iff** `2 ≤ t`.  So
`a4_joint : ∀ t` cannot be closed through the child-size route at `t ∈ {0,1}` — not because the
statement is false (Theorem T is not in doubt at small `t`) but because this artifact's only
child-size bound overshoots `memCap` there by exactly `fpCap t`.  Two ways out, both
**repo-owner decisions** (the pinned statement is unchanged here): (a) sharpen
`childOf_seed_size` to `|S_child| ≤ pullCap t l`, dropping the FindPivots singleton — that would
close `t = 1` if A2's contracts support it; or (b) put `2 ≤ t` in `a4_joint`'s antecedent,
which is the parameter regime the paper's complexity discussion already assumes. -/

/-- `fpCap 0 = 1`: the FindPivots singleton does not vanish at `t = 0`. -/
theorem fpCap_zero : fpCap 0 = 1 := rfl

/-- **The size step fails at `t = 0`** by exactly the `fpCap` term. -/
theorem sizeStep_fails_at_zero (l : ℕ) : memCap 0 (l - 1) < pullCap 0 l + fpCap 0 := by
  unfold memCap pullCap fpCap
  simp

/-- **The child-size step is available exactly at `t ≥ 2`.**  The `2 ≤ t` in
`jointChain_of_steps` is therefore not slack: it is the precise parameter regime in which this
artifact's child-seed bound meets `Lemma37Hyp`'s size clause. -/
theorem pullCap_add_fpCap_le_memCap_iff (t : ℕ) :
    (∀ l : ℕ, pullCap t l + fpCap t ≤ memCap t (l - 1)) ↔ 2 ≤ t := by
  constructor
  · intro h
    by_contra hlt
    have ht1 : t ≤ 1 := by omega
    have h1 := h 1
    have ht01 : t = 0 ∨ t = 1 := by omega
    rcases ht01 with rfl | rfl <;> simp [pullCap, memCap, fpCap] at h1
  · intro ht l
    exact pullCap_add_fpCap_le_memCap (t := t) (l := l) ht

end DMSY
end Frontier

/-! ## Axiom audit -/

#print axioms Frontier.DMSY.fpCap_zero
#print axioms Frontier.DMSY.sizeStep_fails_at_zero
#print axioms Frontier.DMSY.pullCap_add_fpCap_le_memCap_iff
#print axioms Frontier.DMSY.base_containS
#print axioms Frontier.DMSY.jointChain_of_steps_of_baseS

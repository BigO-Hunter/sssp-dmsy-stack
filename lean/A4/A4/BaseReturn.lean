import A4.JointInduction
import A4.ReachHyp
import A4.WDrop

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.BaseReturn — the level-`0` return obligation of the joint induction

`A4.JointInduction.jointChain_of_steps` reduced both `Main` seams to two per-node obligations.
This file attacks the first: `hbase`, the `Lemma37Concl ∧ NoPrem` package at a **level-`0`**
(reachable base) return, i.e. Lemma 3.1\*'s return re-read as Lemma 3.7\*'s clauses with
`Prem = ∅` (base returns mint nothing).

## What is proved here

Nine of `Lemma37Concl`'s eleven clauses are **closed at a level-`0` return** from A1 alone
(`baseRun_lemma31` / `loop_bInv` at the `ReachBase` the entry contract supplies):

* (2a) `progress`, `settleComplete`, `uSubset` — A1's `Lemma31Concl` verbatim;
* (2b) `bound` — A1's cap law `B'⁺ ≤ dMin B 𝒟_final` read per key (`dMin_le_of_mem`), with the
  carve-out disjunct dead (`Premature` needs a mint, and base returns mint nothing);
* (2b) `premInD`, `premShape`, `fullImmune` — vacuous, for the same reason;
* (2c) `identity` — A1's settlement identity with `carveKeys = ∅` (`carveKeys_empty`), so
  `U = Ũ(B', S) ∖ ∅`;
* (1) `frontier` — `BInv.frontier` is stated at `(settledSet st.evts, keys st.D)`, which *is*
  the return record's `(U, keys D)` (A1's `loop_bInv` at the exit), so `base_frontier` is a
  three-line read of the loop invariant;
* Theorem T's half (`NoPrem`) — `base_no_prem`.

## What is not, and why

Two clauses at a level-`0` return are **not** consequences of `CallPre + baseRun_lemma31`:

* (3) `containS` — `S ∖ (U ∪ K) ⊆ keys 𝒟_final`: the seeds the leaf did not settle are still
  queued.  This needs the pull chain's remainder law (`PullSpec.pulled`/`rest` composed along
  `Loop`), which A1 does not expose as a `baseRun`-level statement.
* (3) `containR` — every `v ∈ R(B, U)` with `d' v ≥ B'` is keyed: the boundary closure of the
  leaf's out-neighbours.  `boundaryClosure_of_CallPre` gives the *canonical-path* form; the
  keyed form needs the same `Y` the frontier clause needs.

So `jointInv_base_of_package` takes exactly those two, and
`jointChain_of_steps_of_base` re-states the induction with `hbase` discharged down to them.

Credit: Lemma 3.1\*/3.7\* and the joint induction are DMSY's / the audit's (arXiv:2602.07868v1,
`PROOF.md` §§3–9); this file is the base-return slice of formalizing it.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The clauses A1 does deliver, clause by clause -/

/-- (2a) Progress at a level-`0` return. -/
theorem base_progress {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    ∀ x ∈ (baseOut bout).U, dis (s := s) x < (baseOut bout).B' :=
  (baseRun_lemma31 hre hb).progress

/-- (2a) Every settlement of a level-`0` return is complete. -/
theorem base_settleComplete {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    ∀ ev ∈ (baseOut bout).evts, Complete (baseOut bout).d' ev.v :=
  (baseRun_lemma31 hre hb).settleComplete

/-- (2a) `U ⊆ Ũ(B', S)` at a level-`0` return (in fact equality, from A1's identity). -/
theorem base_uSubset {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    (baseOut bout).U ⊆ Utilde (baseOut bout).B' (e.S : Set (Fin G.n)) :=
  (baseRun_lemma31 hre hb).identity.le

/-- (2c) The settlement identity at a level-`0` return, with an empty carve-out. -/
theorem base_identity {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    (baseOut bout).U =
      Utilde (baseOut bout).B' (e.S : Set (Fin G.n)) \ (baseOut bout).carveKeys e.S := by
  rw [carveKeys_empty (base_no_prem t hb) e.S, Set.sdiff_empty]
  exact (baseRun_lemma31 hre hb).identity

/-- (2b) The bound clause at a level-`0` return, in the carve-out form `Lemma37Concl` asks for.
The `Premature` disjunct is dead because a base return mints nothing. -/
theorem base_bound {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    ∀ y val, (baseOut bout).D y = some val →
      (baseOut bout).B' ≤ val ∨ (baseOut bout).Premature y val := by
  intro y val hy
  refine Or.inl ?_
  exact ((baseRun_lemma31 hre hb).bound.trans (dMin_le_of_mem e.B hy))

/-- (2b) The carve-out contents at a level-`0` return: nothing is premature. -/
theorem base_premEmpty {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    (∀ x val, ¬ (baseOut bout).Premature x val) ∧
      (∀ x val, (baseOut bout).Premature x val → (baseOut bout).D x = some val) ∧
      (∀ x val, (baseOut bout).Premature x val →
        x ∉ (baseOut bout).U ∧ (∃ j, x ∈ (baseOut bout).Pfin j) ∧
          (baseOut bout).d' x ≤ val ∧ PremShape (baseOut bout).d' x val) :=
  ⟨base_no_prem t hb, fun _ _ hp => absurd hp (base_no_prem t hb _ _),
    fun _ _ hp => absurd hp (base_no_prem t hb _ _)⟩

/-- (2b) `fullImmune` at a level-`0` return: vacuous. -/
theorem base_fullImmune {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    Full t e (baseOut bout) → ∀ x val, ¬ (baseOut bout).Premature x val :=
  fun _ => base_no_prem t hb

/-- (1) **The frontier clause at a level-`0` return.**  A1's `BInv.frontier` is stated at
`(settledSet st.evts, keys st.D)` for `Ũ(e.B, S)` — verbatim the return record's fields
(`baseOut` projects `d' = st.d`, `U = settledSet st.evts`, `D = st.D`), so the clause is A1's
loop invariant read at the exit. -/
theorem base_frontier {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    IsFrontier (baseOut bout).d' (Utilde e.B (e.S : Set (Fin G.n)))
      (baseOut bout).U (DS.keys (baseOut bout).D) := by
  obtain ⟨c, st, hloop, hr⟩ := hb
  subst hr
  exact (loop_bInv hloop (bInv_init hre)).frontier

/-! ## The package: `hbase` down to the two clauses A1 does not deliver -/

/-- **The level-`0` return obligation, modulo the two un-delivered clauses.**  Everything
`Lemma37Concl` asks at a base return is supplied except `containS` and `containR` — the pull
remainder and the keyed boundary closure. -/
theorem jointInv_base_of_package {t : ℕ} {e : CallEntry G s} {bout : BaseOut G s}
    (hre : ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout)
    (hcontainS : ((e.S : Set (Fin G.n)) \
      ((baseOut bout).U ∪ (baseOut bout).carveKeys e.S)) ⊆ DS.keys (baseOut bout).D)
    (hcontainR : ∀ v, v ∈ Relaxed (baseOut bout).d' e.B (baseOut bout).U →
      (baseOut bout).B' ≤ (baseOut bout).d' v → v ∈ DS.keys (baseOut bout).D) :
    JointInv t e (baseOut bout) := by
  refine ⟨⟨base_frontier hre hb, base_progress hre hb, base_settleComplete hre hb,
    base_uSubset hre hb, base_bound hre hb,
    (base_premEmpty hb).2.1, (base_premEmpty hb).2.2, base_fullImmune hb,
    base_identity hre hb, hcontainS, hcontainR⟩, base_no_prem t hb⟩

/-- **The induction with `hbase` discharged to the two remaining clauses.** -/
theorem jointChain_of_steps_of_base (t : ℕ) (ht : 2 ≤ t)
    (hcs : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st₁ st₂ : RState G s p)
      (c : CallEntry G s) (fo' : CallOut G s), IStep t B l st₁ st₂ c fo' → ChildStep B st₁ st₂ fo')
    (hsplit : ∀ (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)), StepSplit t B l S)
    (hre : ∀ {e : CallEntry G s}, Reach t e → e.l = 0 →
      ReachBase ⟨e.B, e.S, e.d, initD e.S e.d⟩)
    (hcontainS : ∀ {e : CallEntry G s} {bout : BaseOut G s},
      baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout →
        ((e.S : Set (Fin G.n)) \
          ((baseOut bout).U ∪ (baseOut bout).carveKeys e.S)) ⊆ DS.keys (baseOut bout).D)
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
  jointChain_of_steps t ht hcs hsplit
    (fun hreach hl hb =>
      jointInv_base_of_package (hre hreach hl) hb (hcontainS hb) (hcontainR hb))
    hrecur

/-! ## The `t < 2` boundary — a correction, checked

A previous note in this repository's history (and in `SORRY_SEAM_REPORT.md`) claimed
`JointChain t` is *vacuous* for `t < 2`, "since `Lemma37Hyp` is unsatisfiable".  **That is
false and this section records why**, because it would have been used to justify stopping at
`2 ≤ t`.

`lTop t n = (log₂ n + (t−1)) / max t 1`, so at `t = 0` the top entry has `l = log₂ n`, which is
usually positive.  `memCap 0 l = 0`, so `Lemma37Hyp 0` fails **at the top** (its size clause asks
`1 ≤ 0`) — that much is true (`lemma37Hyp_zero_top_false`).  But `JointChain` quantifies over
every reachable entry, including *children*, and a level-`0` child of the top with `S = ∅`
satisfies `memCap 0 0 = 0` and `JointChain`'s other premises.  So `JointChain 0` is **not**
vacuously true; it needs the induction, whose child-size step is exactly what fails.

At `t = 1` nothing is vacuous at all: `memCap 1 l = 2^l ≥ 1`, so `Lemma37Hyp 1` is satisfiable,
and the child-size step is unavailable in the sharp form
(`ReachHyp.pullCap_add_fpCap_gt_memCap_at_one`: `memCap 1 (l-1) < pullCap 1 l + fpCap 1`).

Consequence, stated precisely: `jointChain_of_steps`/`jointChain_of_steps_of_base` establish
`JointChain t` for **`2 ≤ t`**; the `t ∈ {0,1}` cases of `a4_joint`'s `∀ t` remain open, and
they are open on the *size* step (Lemma 3.5's `|S_child| ≤ memCap t (l−1)`), not on vacuity.
The top entry's case at `t = 0` is discharged below. -/

/-- `Lemma37Hyp 0` fails at the top entry: `memCap 0 l = 0` but `|{s}| = 1`. -/
theorem lemma37Hyp_zero_top_false :
    ¬ Lemma37Hyp (G := G) (s := s) 0
      ⟨(⊤ : WLab G s), {s}, lTop 0 G.n, initLabels G s⟩ := by
  intro h
  have hsize : ({s} : Finset (Fin G.n)).card ≤ memCap 0 (lTop 0 G.n) := h.2.2
  rw [reachHyp_memCap_zero, Finset.card_singleton] at hsize
  omega

end DMSY
end Frontier

/-! ## Axiom audit -/

#print axioms Frontier.DMSY.lemma37Hyp_zero_top_false
#print axioms Frontier.DMSY.base_frontier
#print axioms Frontier.DMSY.base_progress
#print axioms Frontier.DMSY.base_settleComplete
#print axioms Frontier.DMSY.base_uSubset
#print axioms Frontier.DMSY.base_identity
#print axioms Frontier.DMSY.base_bound
#print axioms Frontier.DMSY.base_premEmpty
#print axioms Frontier.DMSY.base_fullImmune
#print axioms Frontier.DMSY.jointInv_base_of_package
#print axioms Frontier.DMSY.jointChain_of_steps_of_base

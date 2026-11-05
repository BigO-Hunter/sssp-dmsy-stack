import A4.Semantics

/-!
# Frontier.DMSY.WDrop — the W′ drop lemma (audit PROOF.md §8, Lemma d2)

Work package **A4 (BMSSP recursion)**.  The **W′ drop lemma** — "Lemma W (W' drop lemma)" of the
task brief; the audit's *frontier-order lemma* `d2`, `PROOF.md` §8 (distinct from the audit's
Lemma W = the §4 window; both ride the same joint first-violation induction, CORRECTED_PROOF
§8.1):

> When the bound invariant holds, the W′ filter drops incomplete vertices: if `d[x] < B'` and
> `x` is not complete, then `x` cannot be in `W'` (the call-local boundary set).

The proof is the audit's one-vertex contradiction, made explicit here: an incomplete `v` with
`d[v] < B'` would visit a complete boundary vertex `y ∈ 𝒟 ∪ P̂` at value
`≥ d_B[𝒟 ∪ P̂] ≥ B'` (the bound invariant, read at complete vertices where value = label =
`dis y`), but `OnPath y v` gives `dis y ≤ dis v ≤ d[v] < B' ≤ dis y`.  The **first-violation
induction** of the audit (PROOF.md §3) is not re-run here: it is exactly what discharges the two
hypotheses below *at a reachable run's filter moment* — the bound floor is the audit's Lemma V
("no sub-`B'` value at returns/filters") and the closure is its Lemma Rep / reachable-state
closure (CORRECTED_PROOF §2.3, "every incomplete-but-relevant vertex is reachable from a
complete vertex in `𝒟 ∪ P̂`").  Those discharge steps live behind `A4.Main`'s `a4_joint` seam
and are deliberately untouched here.

Instance note: on *this* formalization's engine the lemma's completeness half is nearly free —
`A2.fpRun_pull_invariant` gives `W = Ũ(B, S) ∖ behind Y` complete at the FindPivots output
labels (the search runs to exhaustion), so the audit's hard case (incomplete failed-search
residue in `W`) cannot arise; the `WalkInv` plumbing through `Run` it names exists
(`A4.Structural.run_walk`, and `reach_sound`/`reach_entry_sound` deliver it at every reachable
entry).  The statement below is the audit-grade shape: sound labels + bound floor + closure,
with the closure's entry-level discharge at `boundaryClosure_of_CallPre` below.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The two invariants the drop step consumes -/

/-- **Bound invariant at complete boundary vertices** (the audit's `d_B[𝒟 ∪ P̂] ≥ B'`, read where
it is consumed): every *complete* vertex of the call-local boundary `Z` (the live `𝒟` keys plus
the pivot set `P̂`) carries value `≥ B'`.  At a complete vertex the value is the canonical label
(`d y = dis y`), which is what the strictness chain reads; the stored-value form of Lemma V
implies this via custody (entry value `≤` the label at custody, PROOF.md §8 ending 1). -/
def BoundFloor (bp : WLab G s) (d : Labels G s) (Z : Set (Fin G.n)) : Prop :=
  ∀ y ∈ Z, Complete d y → bp ≤ d y

/-- **Boundary closure** (reachable-state closure, CORRECTED_PROOF §2.3; the audit's Lemma Rep
at the filter moment): every incomplete vertex below the bound has its canonical path through a
complete boundary vertex — "an incomplete `v` with `d[v] < B'` would visit a complete vertex in
`𝒟 ∪ P`". -/
def BoundaryClosure (bp : WLab G s) (d : Labels G s) (Z : Set (Fin G.n)) : Prop :=
  ∀ v, ¬ Complete d v → d v < bp → ∃ y ∈ Z, Complete d y ∧ OnPath (s := s) y v

/-! ## The drop step -/

/-- **W′ drop lemma.**  Under the bound invariant (and the reachable-state closure), the `W'`
filter drops incomplete vertices: if `d x < B'` and `x` is not complete, then
`x ∉ wPrime bp W evts d`.  Proof (the audit's minimal-counterexample contradiction): an
incomplete `x` below the bound visits a complete boundary vertex `y` with `dis y ≥ B'`, while
`OnPath y x` forces `dis y ≤ dis x ≤ d x < B'`.  The proof discards even the `W'` membership:
under the hypotheses no incomplete sub-bound label exists at all — "the interval that `B'`
would have to enter is empty" (PROOF.md §8 ending 1). -/
theorem wPrime_drop {bp : WLab G s} {d : Labels G s} {Z : Set (Fin G.n)}
    {W : Finset (Fin G.n)} {evts : List (SettlementEvent G)}
    (hsound : Sound d) (hfloor : BoundFloor bp d Z) (hclose : BoundaryClosure bp d Z)
    (x : Fin G.n) (hx : d x < bp) (hnc : ¬ Complete d x) : x ∉ wPrime bp W evts d := by
  intro _
  obtain ⟨y, hyZ, hcy, hvis⟩ := hclose x hnc hx
  -- the visited complete vertex sits at value `≥ B'` …
  have hbp : bp ≤ dis (s := s) y := by
    rw [← hcy]
    exact hfloor y hyZ hcy
  -- … yet its canonical value is ≤ `d x < B'` — contradiction
  exact absurd hx (not_lt.mpr (hbp.trans (hvis.dis_le.trans (hsound x))))

/-- **Membership form** (the shape clause (2a) consumes for `boundaryAppend` events): every `W'`
member is complete at the filter's labels. -/
theorem complete_of_mem_wPrime {bp : WLab G s} {d : Labels G s} {Z : Set (Fin G.n)}
    {W : Finset (Fin G.n)} {evts : List (SettlementEvent G)}
    (hsound : Sound d) (hfloor : BoundFloor bp d Z) (hclose : BoundaryClosure bp d Z)
    {x : Fin G.n} (hx : x ∈ wPrime bp W evts d) : Complete d x := by
  classical
  by_contra hnc
  exact wPrime_drop hsound hfloor hclose x (Finset.mem_filter.mp hx).2.2 hnc hx

/-! ## Discharging the closure hypothesis (the entry-level piece of the audit's Lemma Rep)

The closure hypothesis is not always a residue of the joint induction: at a call whose labels
satisfy the entry contract (Claim C: everything below `B` outside `Ũ(B, S)` is complete) and
whose state carries a frontier `⟨X, Y⟩` for `Ũ(B, S)`, it follows for *every* `bp ≤ B` and
every boundary `Z ⊇ Y`.  The audit's remaining work (maintaining the frontier
`⟨U^acc, 𝒟^acc ∪ P̂⟩` at loop states through the joint chain) reduces to supplying `Y` — the
canonical-path visit itself is entry-level and proved here. -/

/-- **Boundary closure from the entry contract**: an incomplete `v` with `d v < bp ≤ B` lies in
`Ũ(B, S)` (Claim C would make it complete otherwise), so the frontier's `Y`-witness is the
complete vertex its canonical path visits. -/
theorem boundaryClosure_of_callPre {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    {X Y : Set (Fin G.n)} {bp : WLab G s}
    (hclaim : ∀ v, dis (s := s) v < B → v ∉ Utilde B (S : Set (Fin G.n)) → Complete d v)
    (hF : IsFrontier d (Utilde B (S : Set (Fin G.n))) X Y)
    (hsound : Sound d) (hbp : bp ≤ B) {Z : Set (Fin G.n)} (hZY : Y ⊆ Z) :
    BoundaryClosure bp d Z := by
  intro v hnc hlt
  have hdB : dis (s := s) v < B := lt_of_le_of_lt (hsound v) (lt_of_lt_of_le hlt hbp)
  by_cases hv : v ∈ Utilde B (S : Set (Fin G.n))
  · rcases hF v hv with ⟨-, hc⟩ | ⟨y, hy, hc, hvis⟩
    · exact absurd hc hnc
    · exact ⟨y, hZY hy, hc, hvis⟩
  · exact absurd (hclaim v hdB hv) hnc

/-- The `CallPre`-packaged form: a call with entry preconditions and a live frontier `⟨X, Y⟩`
for `Ũ(B, S)` has its `BoundaryClosure` hypothesis of the W′ drop lemma discharged at every
`bp ≤ B`, boundary `Z ⊇ Y`. -/
theorem boundaryClosure_of_CallPre {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    (hpre : CallPre B S d) {X Y : Set (Fin G.n)}
    (hF : IsFrontier d (Utilde B (S : Set (Fin G.n))) X Y)
    {bp : WLab G s} (hbp : bp ≤ B) {Z : Set (Fin G.n)} (hZY : Y ⊆ Z) :
    BoundaryClosure bp d Z :=
  boundaryClosure_of_callPre hpre.claimC hF hpre.walk.sound hbp hZY

end DMSY
end Frontier

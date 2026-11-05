import A4.ReturnClauses

/-!
# Frontier.DMSY.BpMonotonicity — the per-call `B'` monotonicity obligation (audit §8 item 5)

Work package **A4**. `A4.ReturnClauses` proves `progress`/`uSubset` at a loop exit from
`LoopProg`/`LoopSub` plus the running-bound monotonicity `BpChain`, and flags `BpChain` as the
one genuinely inductive premise of the return side (CORRECTED_PROOF §8 item 5, "unproved even at
sketch grade").  This file settles the obligation in three parts.

## 1. The real proof: what monotonicity reduces to (no `BpChain` premise)

`bp` is the **last** child's `B'` (`IStep.bp := fo'.B'`, `istep_bp`), so the obligation is
per-step: `st.bp ≤ fo'.B'` for every iteration.  The paper's derivation (S2.4 Step 3 (B-mono))
factors through two *distance* facts on the child of that step:

* `SeedFloor st.bp c` — every vertex handed to the child sits at distance `≥ st.bp` (the paper's
  (S-a)/(J2)-second conjunct);
* `SeedChildFloor c fo'` — the child's returned bound is at least one seed's distance (the paper's
  (R5), `B' ⪰ min_{x∈S} dis x`).

`istep_bp_mono` composes them; `bpChain_of_chainFloor` + `iloop_chainFloor` thread the seed floor
along `ILoop` and **derive** `BpChain` (`iloop_bpChain_of_floors`) — `BpChain` is not assumed
anywhere in this file and not restated as an axiom.

## 2. How far the engine's own data reaches

`LiveFloor` is the (J2)-second conjunct as an engine-level state invariant, spelled on the two
places a seed comes from: keys of `𝒟` (`pullRun`) and residual pivot-group members (`expand`).
`seedFloor_expand_of_liveFloor` proves the *pulled* seeds and the *group* seeds both clear the
floor, so `LiveFloor` discharges the seed half of §1 (`istep_bp_mono_of_liveFloor`,
`iloop_bpChain_of_liveFloor`).  Both halves are **distance** floors: the value floors the engine
does own (`Transitive.LoopBoundInv`, `LoopBInv`, and `pullRun_floor` for the remainder) do not
imply them, because a stored value only ever over-estimates its vertex's distance
(`d y ≤ val` for a key, `Sound` gives `dis y ≤ d y`) and `LoopBInv`/`LoopBoundInv` floor `st.d`/`val`
from *below*.  So the residue is not bookkeeping: it is the completeness of keyed vertices.

The concrete channels by which `LiveFloor` can be lost are the corrected engine's own two
unguarded/below-gate key sources, and neither is visible to a *return-side* clause:

* a child's `𝒟` merged at BM.14 can carry a key below the running bound — clause (2b) admits
  exactly that through `CallOut.Premature`, so `BoundClause` permits it by design;
* the line-29 re-selection inserts are **ungated**, and `RState.mints` is *replaced* every
  iteration, so an earlier iteration's sub-`bp` mint is an ordinary key of `𝒟` at the next
  iteration and is covered by neither `Premature` nor `BoundClause` — `LoopBoundInv` tolerates it
  (it floors values, not distances) and `Transitive`'s enumeration removes it only *later*, when a
  subsequent pull consumes it (the pull takes every key below its separator).  That next pull is
  precisely iteration `i+1`, whose seed set therefore may hold the low vertex: a drop in `B'` is
  consistent with every clause `Lemma37Concl` states.

## 3. The escape family (kept apart from §1–§2)

`IStep` puts **no constraint whatsoever** on `fo'.B'`: the returned bound occurs only in the
concluding `bp := fo'.B'` component (`fo'.D`, `fo'.evts`, `fo'.d'` are what the step consumes).
`istep_bot` exhibits an `IStep` on the one-vertex, edge-free graph with `st.bp = ⊤` and
`st'.bp = ↑[] < ⊤`, and `istep_does_not_force_mono` concludes that no theorem of the shape
`IStep ⟹ st.bp ≤ st'.bp` can hold.  This is a *non-derivability* result, not an axiom: it is
witnessed by a real `IStep` term, so it stays outside §1's proof obligation and cannot be used
to discharge it.

No `sorry`, `admit`, or new `axiom`; standard axioms only.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The two floors, and monotonicity as a consequence of them -/

/-- **Seed floor** (paper (S-a)/(J2)-second): every vertex of the child call's seed set sits at
distance at least the running return bound. -/
def SeedFloor (bp : WLab G s) (c : CallEntry G s) : Prop :=
  ∀ v ∈ c.S, bp ≤ dis (s := s) v

/-- **Seed child floor** (paper (R5)): the child's returned bound dominates the distance of one
of its own seeds.  This is the clause `Lemma37Concl` does *not* carry; `A4.LoopBInv`'s label
floors are its proof-side ingredients (`B'_child ≥ B'_0 = min_j d[piv_j]`, `piv j ∈ S`).

**Name.**  This was `ChildFloor` until the declaration clash with
`A4.BelowSeparator.ChildFloor` (a *different* notion: the two-clause settled-completeness /
refusal floor `(∀ ev ∈ fo'.evts, Complete fo'.d' ev.v) ∧ ∀ e, G.src e ∈ settledSet fo'.evts → …`)
was found: the two files could not be imported together.  `BelowSeparator` keeps the name (it is
the settled/sweep chain that `A4.SettleSweep`/`A4.JointAssembly`/`A4.LeafFloor` all use); this
file's (R5) clause is renamed `SeedChildFloor`. -/
def SeedChildFloor (c : CallEntry G s) (co : CallOut G s) : Prop :=
  ∃ v ∈ c.S, dis (s := s) v ≤ co.B'

/-- **One iteration is monotone in `B'`**, from the two floors. -/
theorem istep_bp_mono {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hseed : SeedFloor st.bp c) (hchild : SeedChildFloor c fo') : st.bp ≤ st'.bp := by
  rw [istep_bp h]
  obtain ⟨v, hv, hle⟩ := hchild
  exact (hseed v hv).trans hle

/-- The seed floor along an iteration sequence (the non-`BpChain` premise: it constrains `𝒟`'s
and the groups' vertices against the *running* bound, never a child's returned `B'`). -/
def ChainFloor : WLab G s → List (CallEntry G s × CallOut G s) → Prop
  | _, [] => True
  | b, q :: qs => SeedFloor b q.1 ∧ ChainFloor q.2.B' qs

/-- **`BpChain` from the seed floors plus the children's own floors.** -/
theorem bpChain_of_chainFloor : ∀ (b : WLab G s) {qs : List (CallEntry G s × CallOut G s)},
    ChainFloor b qs → (∀ q ∈ qs, SeedChildFloor q.1 q.2) → BpChain b qs := by
  intro b qs
  induction qs generalizing b with
  | nil => intro _ _; trivial
  | cons q qs ih =>
    intro hcl hch
    obtain ⟨hseed, hrest⟩ := hcl
    obtain ⟨v, hv, hle⟩ := hch q List.mem_cons_self
    exact ⟨(hseed v hv).trans hle,
      ih q.2.B' hrest (fun q' hq' => hch q' (List.mem_cons_of_mem _ hq'))⟩

/-- The step-uniform seed floor (shape of `A4.LoopBInv`'s `LabelFloorHyp`). -/
def StepSeedFloor (t : ℕ) (B : WLab G s) (l : ℕ) : Prop :=
  ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
    IStep t B l st st' c fo' → SeedFloor st.bp c

/-- **The loop threads the seed floor.** Uniform in the loop state, so one hypothesis about
`IStep` covers every iteration. -/
theorem iloop_chainFloor (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf →
      (∀ (B0 : WLab G s) (l0 : ℕ), StepSeedFloor (G := G) (s := s) t B0 l0) →
      ChainFloor st.bp qs := by
  intro p st stf qs h
  induction h with
  | exit _ => intro _; exact trivial
  | step hne hg hstep hrest ih =>
    intro hfloor
    refine ⟨hfloor B l _ _ _ _ hstep, ?_⟩
    rw [← istep_bp hstep]
    exact ih (fun B0 l0 p0 st0 st0' c fo0 h0 => hfloor B0 l0 st0 st0' c fo0 h0)

/-- **`BpChain` at a loop, derived** — the obligation `A4.ReturnClauses` consumes, with no
`BpChain` premise: seed floors (engine-side, §2) + the children's own floor (R5). -/
theorem iloop_bpChain_of_floors (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf →
      (∀ (B0 : WLab G s) (l0 : ℕ), StepSeedFloor (G := G) (s := s) t B0 l0) →
      (∀ q ∈ qs, SeedChildFloor q.1 q.2) → BpChain st.bp qs := by
  intro p st stf qs hloop hseed hchild
  exact bpChain_of_chainFloor st.bp
    (iloop_chainFloor t B l hloop (fun B0 l0 => hseed B0 l0)) hchild

/-! ## 2. What the engine's own `pullRun`/`expand` data supplies

`Strict.` Seeding has exactly two sources in `IStep` (`expand`): the pulled keys `S_i ⊆ belowKeys`
and the residual group members `{v ∈ Pl j | d v < B_i}`.  `LiveFloor` is the (J2)-second
conjunct spelled per source, in distance form. -/

/-- **Live floor**: the running bound sits below every vertex still live in the loop state — keyed
in `𝒟` and present in a residual pivot group.  This is the invariant the audit item names as
missing; §1 shows it is exactly what `BpChain` needs. -/
def LiveFloor {p : ℕ} (st : RState G s p) : Prop :=
  (∀ (y : Fin G.n) (v : WLab G s), st.D y = some v → st.bp ≤ dis (s := s) y) ∧
    (∀ (j : Fin p) (y : Fin G.n), y ∈ st.pl j → st.bp ≤ dis (s := s) y)

/-- **The seed floor, discharged from the engine's own data.**  Pulled keys come from `𝒟` and
group members from `Pl`. -/
theorem seedFloor_expand_of_liveFloor {cap : ℕ} {p : ℕ} {st : RState G s p}
    {D1 : DS G s} {Si : Finset (Fin G.n)} {Bi Bd : WLab G s} {l : ℕ}
    (hpull : pullRun cap st.D Bd Si Bi D1) (hlive : LiveFloor st) :
    SeedFloor st.bp ⟨Bi, expand st.d st.pl st.piv Si Bi, l, st.d⟩ := by
  obtain ⟨hD, hP⟩ := hlive
  intro v hv
  rw [expand, Finset.mem_union] at hv
  rcases hv with hv | hv
  · obtain ⟨val, hval, -⟩ := (pullRun_pulled hpull).mp hv
    exact hD v val hval
  · obtain ⟨j, -, hmem⟩ := Finset.mem_biUnion.mp hv
    split_ifs at hmem with hc
    · exact hP j v (Finset.mem_filter.mp hmem).1
    · exact absurd hmem (Finset.notMem_empty v)

/-- **The seed floor of one iteration, extracted from the `IStep` witnesses.** -/
theorem istep_seedFloor {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hlive : LiveFloor st) : SeedFloor st.bp c := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, -⟩ := h
  subst hc
  exact seedFloor_expand_of_liveFloor hpull hlive

/-- **One iteration is monotone in `B'`, from the engine's live floor plus the child's floor.** -/
theorem istep_bp_mono_of_liveFloor {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hlive : LiveFloor st) (hchild : SeedChildFloor c fo') :
    st.bp ≤ st'.bp :=
  istep_bp_mono h (istep_seedFloor h hlive) hchild

/-- The step-uniform form of the live floor (shape of `A4.LoopBInv`'s `LabelFloorHyp`). -/
def LiveFloorAt (t : ℕ) (B : WLab G s) (l : ℕ) : Prop :=
  ∀ {p : ℕ} (st st' : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
    IStep t B l st st' c fo' → LiveFloor st

/-- The loop-uniform form. -/
def LiveFloorHyp (t : ℕ) : Prop := ∀ (B : WLab G s) (l : ℕ), LiveFloorAt (G := G) (s := s) t B l

/-- One `IStep`'s seed floor follows from the live floor at that entry. -/
theorem stepSeedFloor_of_liveFloor {t : ℕ} {B : WLab G s} {l : ℕ}
    (hlive : LiveFloorAt (G := G) (s := s) t B l) : StepSeedFloor (G := G) (s := s) t B l :=
  fun _ _ _ _ h => istep_seedFloor h (hlive _ _ _ _ h)

/-- **`BpChain` from the engine's live floor and the children's (R5)-shape floor.** -/
theorem iloop_bpChain_of_liveFloor (t : ℕ) (B : WLab G s) (l : ℕ)
    (hlive : LiveFloorHyp (G := G) (s := s) t) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf → (∀ q ∈ qs, SeedChildFloor q.1 q.2) → BpChain st.bp qs :=
  fun hloop hchild =>
    iloop_bpChain_of_floors t B l hloop
      (fun B0 l0 => stepSeedFloor_of_liveFloor (hlive B0 l0)) hchild

/-! ## 3. The escape family: `IStep` does not force the chain

Everything below is a **non-derivability** exhibit, deliberately outside §1–§2: §1's proof needs
the two floors as *hypotheses*, and this section shows no `IStep`-only argument can replace them.
Nothing here is used by §1–§2. -/

/-- The one-vertex, edge-free graph.  Every label of it is `↑[]` or `⊤`. -/
def G₁ : Graph where
  n := 1
  m := 0
  src := fun e => e.elim0
  dst := fun e => e.elim0
  w := fun e => e.elim0

/-- The unique vertex of `G₁`. -/
def s₁ : Fin G₁.n := ⟨0, by decide⟩

/-- The "no groups, no keys, `bp = ⊤`" loop state of `G₁`. -/
def stBot : RState G₁ s₁ 0 where
  d := fun _ => ⊤
  D := DS.empty
  evts := []
  bp := ⊤
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

/-- The loop state after one iteration of `G₁`'s loop, at running bound `b`. -/
def stAfter (b : WLab G₁ s₁) : RState G₁ s₁ 0 where
  d := fun _ => ⊤
  D := DS.empty
  evts := []
  bp := b
  pl := fun j => j.elim0
  piv := fun j => j.elim0
  mints := []

/-- The child's return record at bound `b`. -/
def foAt (b : WLab G₁ s₁) : CallOut G₁ s₁ where
  B' := b
  evts := []
  D := DS.empty
  d' := fun _ => ⊤
  mints := []
  pfin := 0
  Pfin := fun j => j.elim0

/-- The `Fin 0`-indexed block of `expand` is empty: `G₁` has no pivot groups. -/
theorem biUnion_fin0 {α : Type} [DecidableEq α] (f : Fin 0 → Finset α) :
    (Finset.univ.biUnion f) = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro v hv
  obtain ⟨j, -, -⟩ := Finset.mem_biUnion.mp hv
  exact j.elim0

/-- `expand` adds nothing at `G₁`. -/
theorem expand_G₁ (d : Labels G₁ s₁) (pl : Fin 0 → Finset (Fin G₁.n))
    (piv : Fin 0 → Fin G₁.n) (Si : Finset (Fin G₁.n)) (Bi : WLab G₁ s₁) :
    expand d pl piv Si Bi = Si := by
  rw [expand, biUnion_fin0, Finset.union_empty]

/-- `pullRun` on the empty structure, at separator `⊤`, pulling nothing. -/
theorem pullRun_empty_bot (cap : ℕ) :
    pullRun (G := G₁) (s := s₁) cap DS.empty ⊤ ∅ ⊤ DS.empty := by
  refine ⟨?_, ?_, le_rfl, Or.inl rfl, Or.inl fun y => rfl, by simp⟩
  · ext y
    simp [belowKeys, DS.empty]
  · funext y
    simp [DS.deleteSet, DS.empty]

/-- **An `IStep` whose returned bound is `b`, on the state whose running bound is `⊤`.**  The
child's bound is unconstrained by the step: the witnesses below close for every `b`. -/
theorem istep_bot (t l : ℕ) (b : WLab G₁ s₁) :
    IStep (G := G₁) (s := s₁) t ⊤ l stBot (stAfter b) ⟨⊤, ∅, l - 1, fun _ => ⊤⟩ (foAt b) := by
  refine ⟨∅, ⊤, DS.empty, (fun j => j.elim0), ∅, (fun j => j.elim0), DS.empty,
    (fun _ => ⊤), DS.empty, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact pullRun_empty_bot (pullCap t l)
  · rw [CallEntry.mk.injEq]
    exact ⟨rfl, (expand_G₁ _ _ _ ∅ ⊤).symm, rfl, rfl⟩
  · funext y
    simp [foAt, settledFinset, DS.deleteSet, DS.merge, DS.mergeVal, DS.empty]
  · rfl
  · intro j
    exact j.elim0
  · ext j
    exact j.elim0
  · intro j hj
    exact absurd hj (Finset.notMem_empty j)
  · rw [RState.mk.injEq]
    refine ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · simp [stAfter]
    · rfl
    · funext j
      exact j.elim0
    · funext j
      exact j.elim0
    · simp [stAfter]

/-- The counterexample's drop: `⊤` is strictly above `↑[]`. -/
theorem bot_lt_top_G₁ : ((toW ([] : List (Fin G₁.m)) : WalkOrd G₁ s₁) : WLab G₁ s₁) < ⊤ :=
  WithTop.coe_lt_top _

/-- **The escape theorem.**  No `IStep`-only statement forces the running bound to be
nondecreasing: `stBot` steps to `stAfter ↑[]` while carrying `bp = ⊤`.  This is why §1 must take
`SeedFloor`/`SeedChildFloor` as hypotheses — the step relation alone is silent about `fo'.B'`. -/
theorem istep_does_not_force_mono :
    ¬ (∀ (t : ℕ) (B : WLab G₁ s₁) (l : ℕ) (p : ℕ) (st st' : RState G₁ s₁ p)
        (c : CallEntry G₁ s₁) (fo' : CallOut G₁ s₁), IStep t B l st st' c fo' →
        st.bp ≤ st'.bp) := by
  intro h
  have hdrop := h 0 ⊤ 0 0 stBot (stAfter ((toW ([] : List (Fin G₁.m)) : WalkOrd G₁ s₁) : WLab G₁ s₁))
    ⟨⊤, ∅, 0, fun _ => ⊤⟩ (foAt ((toW ([] : List (Fin G₁.m)) : WalkOrd G₁ s₁) : WLab G₁ s₁))
    (istep_bot 0 0 _)
  exact absurd hdrop (not_le_of_gt bot_lt_top_G₁)

/-- The same drop read on the child's own record: `fo'.B' = ↑[]` while the parent ran at `⊤`. -/
theorem istep_bot_child_bound :
    (foAt ((toW ([] : List (Fin G₁.m)) : WalkOrd G₁ s₁) : WLab G₁ s₁)).B' < ⊤ :=
  bot_lt_top_G₁

end DMSY
end Frontier

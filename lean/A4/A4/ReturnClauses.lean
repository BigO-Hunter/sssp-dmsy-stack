import A4.Main
import A4.MintPreFloor
import A4.Transitive
import A4.WDrop
import A4.Rep
import A4.LemmaV

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.ReturnClauses — the return-side clauses of Lemma 3.7\* at a tail

Work package **A4 (BMSSP recursion)**, the *return side* of the joint chain.  `A4.JointAssembly`
assembles the entry side (`Lemma37Hyp` at every `Reach` entry, the per-iteration `ChildStep`
bundle); this file attacks the clauses `Lemma37Concl` asks for at the one place `Run` produces
them, `out = callOut (tail e.B e.S fo.W stf)`, and separates what the tail's own semantics
proves from what only a loop invariant can supply.

## What is proved here, and against which premise

* **(2b) `bound`** — `callOut_tail_boundClause`: *fully proved*, from `LoopBoundInv stf` (the
  keep-min floor `Transitive.LoopBoundInv`, `A4.Transitive.tail_boundClause`), which the joint
  chain supplies from the children's Prem-free bound laws.  No new premise.
* **(2a) `progress` / `uSubset` at the `W'` boundary** — `progress_wPrime`, `uSubset_wPrime`:
  *unconditional* (sound labels + the FindPivots region `W ⊆ Ũ(B,S)`).
* **(2a) `progress` / `uSubset` over the loop log** — `tail_progress`, `tail_uSubset`: proved
  from the state invariant at the loop exit (`LoopProg`/`LoopSub`) plus the boundary half.
  `istep_progress`/`istep_uSubset`/`iloop_progress`/`iloop_uSubset` show the invariant is
  *preserved* by an iteration from (a) the child's own clause and (b) `BpChain`, the running-bound
  monotonicity `B'`-nondecreasing along the iteration sequence.  `BpChain` is the one genuinely
  inductive premise here; it is **not** a restatement of progress (it constrains the `bp` field
  only) and it is exactly the audit's per-call `B'` monotonicity (CORRECTED_PROOF §8 item 5,
  "unproved even at sketch grade").
* **(3) `containR`** — `callOut_tail_containR`: proved from `Custody` ("every live label is
  either settled or queued in `𝒟`"), which `tail_custody`/`sweepEvts_custody` preserve through
  the tail structurally.  The clause does not even need the tightness witness of `Relaxed`.
* **(3) `containS`** — `callOut_tail_containS`: proved from the settlement identity plus the
  keyed seed re-insert of BM.25 (`seedIns_gate_key`), and label monotonicity at seeds.
* **(2c) `identity`** — `tail_identity`: reduced to its two halves `U ⊆ Ũ(B',S)` (that is
  `uSubset`, proved above) and `Ũ(B',S) ⊆ U ∪ K` (the "no vertex below `B'` is left unsettled or
  carved" content, named `hcover`).  The reduction also uses `U ∩ K = ∅`, which is
  `Structural.premShape_of_run`'s `x ∉ U` half of a Prem entry.

Nothing here assumes `a4_joint`, uses `sorry`/`admit`, or adds an axiom; every premise is a
typed hypothesis of its theorem and is named in the report.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 0. The tail's `W'` boundary set, and the return record's fields

`tail`'s body spells the same `wPrime`/`seedIns` expression three times; naming it once keeps the
clause statements readable.  It is only a name for the engine's own expression (`tailWp_eq`). -/

/-- BM.26's boundary set at a tail: the `W`-members below `B'` not yet settled. -/
noncomputable def tailWp (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    Finset (Fin G.n) :=
  wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1

theorem tailWp_eq (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    tailWp B S W st =
      wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1 := rfl

/-- `seedIns` (BM.25) never touches labels: its label component is its input. -/
theorem seedIns_fst (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s) :
    (seedIns bp B S d D).1 = d := by
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => rfl
  | cons y ys ih =>
    rw [List.foldl_cons]
    by_cases hg : bp ≤ d y ∧ d y < B
    · rw [if_pos hg]
      exact ih d (DS.insert D y (d y))
    · rw [if_neg hg]
      exact ih d D

/-- The boundary set reads the loop's own labels and log. -/
theorem tailWp_reads_state (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    tailWp B S W st = wPrime (tailBP B st) W st.evts st.d := by
  rw [tailWp_eq, seedIns_fst]

/-- The running bound never exceeds the tail's return bound (BM.24a). -/
theorem bp_le_tailBP (B : WLab G s) {p : ℕ} (st : RState G s p) (h : st.bp ≤ B) :
    st.bp ≤ tailBP B st := by
  unfold tailBP
  split_ifs with hemp
  · exact h
  · exact le_rfl

/-- The returned bound is the tail's `tailBP` (BM.24a: `B' = B` on drain). -/
theorem tailOut_B' (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    (callOut (tail B S W st)).B' = tailBP B st := rfl

/-- The returned `𝒟` is the tail's swept structure. -/
theorem tailOut_D (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    (callOut (tail B S W st)).D =
      (sweepEvts B (tailBP B st) (wPrimeEvts (tailWp B S W st))
        (seedIns (tailBP B st) B S st.d st.D).1
        (seedIns (tailBP B st) B S st.d st.D).2).2 := rfl

/-- The returned labels are the tail's swept labels. -/
theorem tailOut_d' (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    (callOut (tail B S W st)).d' =
      (sweepEvts B (tailBP B st) (wPrimeEvts (tailWp B S W st))
        (seedIns (tailBP B st) B S st.d st.D).1
        (seedIns (tailBP B st) B S st.d st.D).2).1 := rfl

/-- The returned settlement log is the loop log followed by the boundary appends. -/
theorem tailOut_evts (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    (callOut (tail B S W st)).evts = st.evts ++ wPrimeEvts (tailWp B S W st) := rfl

/-- The return keeps the loop's final mints (the Q12 carve-out set). -/
theorem tailOut_mints (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    (callOut (tail B S W st)).mints = st.mints := rfl

/-- `U` at the return is the loop's settlements plus the boundary appends. -/
theorem tailOut_U (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    (callOut (tail B S W st)).U = settledSet st.evts ∪ (tailWp B S W st : Set (Fin G.n)) := by
  rw [CallOut.U, tailOut_evts, tailWp_eq, settledSet_append, settledSet_wPrimeEvts]

/-- Membership form of `tailOut_U`. -/
theorem tailOut_U_mem {B : WLab G s} {S W : Finset (Fin G.n)} {p : ℕ} {st : RState G s p}
    {x : Fin G.n} :
    x ∈ (callOut (tail B S W st)).U ↔
      x ∈ settledSet st.evts ∨ x ∈ tailWp B S W st := by
  rw [tailOut_U, Set.mem_union]
  exact ⟨fun h => h.imp id Finset.mem_coe.mp, fun h => h.imp id Finset.mem_coe.mpr⟩

/-! ## 1. The boundary half: `W'` members are complete, below `B'`, and in `Ũ(B',S)`

These are the tail-only facts: `wPrime`'s own filter supplies `d x < B'`, soundness turns it into
`dis x < B'`, and the FindPivots region plants the canonical-path witness. -/

open Classical in
/-- `wPrime`'s three conjuncts. -/
theorem mem_wPrime {bp : WLab G s} {W : Finset (Fin G.n)} {evts : List (SettlementEvent G)}
    {d : Labels G s} {x : Fin G.n} :
    x ∈ wPrime bp W evts d ↔ x ∈ W ∧ x ∉ settledSet evts ∧ d x < bp :=
  Finset.mem_filter

/-- A `W'` member sits below the return bound at the *canonical* label. -/
theorem progress_wPrime {bp : WLab G s} {W : Finset (Fin G.n)} {evts : List (SettlementEvent G)}
    {d : Labels G s} (hsound : Sound d) {x : Fin G.n} (hx : x ∈ wPrime bp W evts d) :
    dis (s := s) x < bp :=
  (hsound x).trans_lt (mem_wPrime.mp hx).2.2

/-- A sound label below a bound makes its vertex reachable (needed for `OnPath`-reflexivity). -/
theorem reachable_of_lt {d : Labels G s} (hsound : Sound d) {b : WLab G s} {v : Fin G.n}
    (h : d v < b) : G.Reachable s v := by
  by_contra hr
  have hle := hsound v
  rw [dis_of_not_reachable hr] at hle
  exact absurd hle (not_le.mpr (lt_of_lt_of_le h le_top))

/-- Narrowing a `Ũ` bound only needs the distance inequality: the visit witness is inherited. -/
theorem utilde_of_lt {B B' : WLab G s} {T : Set (Fin G.n)} {x : Fin G.n}
    (hx : x ∈ Utilde B T) (hlt : dis (s := s) x < B') : x ∈ Utilde B' T :=
  ⟨hlt, hx.2⟩

/-- **`W'` half of `uSubset`**: a boundary append of the tail is in `Ũ(B', S)`, from the
FindPivots region `W ⊆ Ũ(B, S)` and the boundary filter. -/
theorem uSubset_wPrime {B bp : WLab G s} {S W : Finset (Fin G.n)}
    {evts : List (SettlementEvent G)} {d : Labels G s}
    (hW : (W : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))) (hsound : Sound d)
    {x : Fin G.n} (hx : x ∈ wPrime bp W evts d) : x ∈ Utilde bp (S : Set (Fin G.n)) :=
  utilde_of_lt (hW (Finset.mem_coe.mpr (mem_wPrime.mp hx).1)) (progress_wPrime hsound hx)

/-! ## 2. (2a) `progress` and `uSubset` at the return

The boundary half is discharged unconditionally; the loop-log half is the state invariant
`LoopProg` / `LoopSub` at the loop exit, whose *preservation* is §5. -/

/-- The progress invariant at a loop state: every settlement of the loop sits below the running
bound.  (The clause restricted to the loop's own log — §5 derives it.) -/
def LoopProg {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x ∈ settledSet st.evts, dis (s := s) x < st.bp

/-- The subset invariant at a loop state: every settlement of the loop lies in `Ũ(bp, S)`. -/
def LoopSub (S : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x ∈ settledSet st.evts, x ∈ Utilde st.bp (S : Set (Fin G.n))

/-- **(2a) `progress` at the return**, from the loop's own progress invariant: the boundary
appends are handled unconditionally. -/
theorem tail_progress (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hinv : LoopProg st) (hbp : st.bp ≤ B) (hsound : Sound st.d) :
    ∀ x ∈ (callOut (tail B S W st)).U, dis (s := s) x < (callOut (tail B S W st)).B' := by
  intro x hx
  rw [tailOut_B']
  rcases (tailOut_U_mem.mp hx) with h | h
  · exact (hinv x h).trans_le (bp_le_tailBP B st hbp)
  · have h' : x ∈ wPrime (tailBP B st) W st.evts st.d := by rwa [tailWp_reads_state] at h
    exact progress_wPrime hsound h'

/-- **(2a) `U ⊆ Ũ(B', S)` at the return**, from the loop's subset invariant and the FindPivots
region. -/
theorem tail_uSubset (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hinv : LoopSub S st) (hbp : st.bp ≤ B) (hsound : Sound st.d)
    (hW : (W : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))) :
    (callOut (tail B S W st)).U ⊆ Utilde (tailBP B st) (S : Set (Fin G.n)) := by
  intro x hx
  rcases (tailOut_U_mem.mp hx) with h | h
  · have hlt : dis (s := s) x < tailBP B st :=
      (hinv x h).1.trans_le (bp_le_tailBP B st hbp)
    exact utilde_of_lt (hinv x h) hlt
  · have h' : x ∈ wPrime (tailBP B st) W st.evts st.d := by rwa [tailWp_reads_state] at h
    exact uSubset_wPrime hW hsound h'

/-! ## 3. (2b) `bound` — proved

The enumeration is `A4.Transitive.tail_boundClause`'s: `seedIns` and the (E2)-gated `W'` sweep
insert only values `≥ B'`, so a stored value below `B'` must be a final-iteration mint — which is
exactly `CallOut.Premature`.  The premise `LoopBoundInv` is the keep-min floor, *not* a restatement
of the clause: it constrains `stf.D` against `stf.bp`, and `A4.Transitive.loopBoundInv_loop`
derives it from the children's Prem-free bound laws. -/

/-- **Clause (2b) at the return** (`Lemma37Concl.bound`), from the loop-exit bound floor. -/
theorem callOut_tail_boundClause (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) :
    BoundClause (callOut (tail B S W st)) :=
  tail_boundClause B S W st hinv

/-- The strict form: with no low final mint the returned structure clears `B'` outright. -/
theorem callOut_tail_boundClauseStrict (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st)
    (hno : ¬ LowMint (callOut (tail B S W st))) :
    BoundClauseStrict (callOut (tail B S W st)) :=
  tail_boundClauseStrict hinv hno

/-! ## 4. (3) `containR` — proved from custody

`Relaxed` supplies only `d' v < B` and `v ∉ U`; the clause needs `v ∈ keys 𝒟`.  The engine fact
that makes this true is **custody**: every vertex with a live (non-`⊤`) label is either settled or
carries an entry of `𝒟` — labels are only ever written by an accepted relaxation, and an accepted
relaxation inserts.  The hypotheses of Lemma W's window (`A4.Window`) are the same phenomenon on
the bound side; here only the key side is needed, and the tail preserves it structurally. -/

/-- Custody on a `(labels, 𝒟, log)` triple: a live label is settled or queued. -/
def CustodyL (d : Labels G s) (D : DS G s) (evts : List (SettlementEvent G)) : Prop :=
  ∀ v, d v ≠ ⊤ → v ∈ settledSet evts ∨ D v ≠ none

/-- Custody at a loop state. -/
def Custody {p : ℕ} (st : RState G s p) : Prop :=
  CustodyL st.d st.D st.evts

/-- An accepted gated relaxation updates exactly the one label it inserts a key for. -/
theorem relaxGate_custody {B lo : WLab G s} {d : Labels G s} {D : DS G s}
    {Z : Set (Fin G.n)} (h : ∀ v, d v ≠ ⊤ → v ∈ Z ∨ D v ≠ none) {e : Fin G.m} :
    ∀ v, (relaxGate B lo d D e).1 v ≠ ⊤ →
      v ∈ Z ∨ (relaxGate B lo d D e).2 v ≠ none := by
  intro v hv
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · have h1 : (relaxGate B lo d D e).1 = Function.update d (G.dst e) (ext (d (G.src e)) e) := by
      simp only [relaxGate, if_pos hc]
    have h2 : (relaxGate B lo d D e).2 = DS.insert D (G.dst e) (ext (d (G.src e)) e) := by
      simp only [relaxGate, if_pos hc]
    rw [h1] at hv
    rw [h2]
    by_cases hvz : v = G.dst e
    · subst hvz
      refine Or.inr ?_
      rw [DS.insert_self]
      exact DS.mergeVal_ne_none _ _
    · have hupd : Function.update d (G.dst e) (ext (d (G.src e)) e) v = d v :=
        Function.update_of_ne (a := v) (a' := G.dst e) (β := fun _ => WLab G s) hvz
          (ext (d (G.src e)) e) d
      rw [hupd] at hv
      rcases h v hv with hz | hk
      · exact Or.inl hz
      · exact Or.inr (insert_ne_none D (G.dst e) (ext (d (G.src e)) e) v hk)
  · have h1 : (relaxGate B lo d D e).1 = d := by simp only [relaxGate, if_neg hc]
    have h2 : (relaxGate B lo d D e).2 = D := by simp only [relaxGate, if_neg hc]
    rw [h1] at hv
    rw [h2]
    exact h v hv

/-- The gated sweep of one vertex preserves custody. -/
theorem sweepGate_custody {B lo : WLab G s} (u : Fin G.n) (es : List (Fin G.m))
    {Z : Set (Fin G.n)} : ∀ (d : Labels G s) (D : DS G s),
      (∀ v, d v ≠ ⊤ → v ∈ Z ∨ D v ≠ none) → ∀ v, (sweepGate B lo u es d D).1 v ≠ ⊤ →
        v ∈ Z ∨ (sweepGate B lo u es d D).2 v ≠ none := by
  induction es with
  | nil => intro d D h v hv; exact h v hv
  | cons e es ih =>
    intro d D h
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (relaxGate_custody h)
    · rw [if_neg hs, if_neg hs]
      exact ih d D h

/-- Custody survives a whole settlement-log sweep. -/
theorem sweepEvts_custody {B lo : WLab G s} (evts : List (SettlementEvent G))
    {Z : Set (Fin G.n)} : ∀ (d : Labels G s) (D : DS G s),
      (∀ v, d v ≠ ⊤ → v ∈ Z ∨ D v ≠ none) → ∀ v, (sweepEvts B lo evts d D).1 v ≠ ⊤ →
        v ∈ Z ∨ (sweepEvts B lo evts d D).2 v ≠ none := by
  induction evts with
  | nil => intro d D h v hv; exact h v hv
  | cons ev evts ih =>
    intro d D h v hv
    exact ih _ _ (sweepGate_custody ev.v (List.finRange G.m) d D h) v hv

/-- The tail's settlement log: the loop log then the boundary appends. -/
theorem tail_evts_eq (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    (tail B S W st).evts = st.evts ++ wPrimeEvts (tailWp B S W st) := rfl

/-- The tail preserves custody (BM.25 inserts without touching labels, BM.28 inserts through the
gate; both only add keys). -/
theorem tail_custody (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (h : Custody st) : CustodyL (tail B S W st).d (tail B S W st).D (tail B S W st).evts := by
  intro v hv
  have hseed : ∀ u, (seedIns (tailBP B st) B S st.d st.D).1 u ≠ ⊤ →
      u ∈ settledSet st.evts ∨ (seedIns (tailBP B st) B S st.d st.D).2 u ≠ none := by
    intro u hu
    rw [seedIns_d] at hu
    rcases h u hu with hs | hk
    · exact Or.inl hs
    · exact Or.inr (seedIns_ne_none _ _ _ _ _ u hk)
  rcases sweepEvts_custody (B := B) (lo := tailBP B st) (wPrimeEvts (tailWp B S W st))
    (seedIns (tailBP B st) B S st.d st.D).1 (seedIns (tailBP B st) B S st.d st.D).2 hseed v hv
    with hs | hk
  · refine Or.inl ?_
    rw [tail_evts_eq, settledSet_append]
    exact Set.mem_union_left _ hs
  · exact Or.inr hk

/-- **(3) `containR` at the return.**  The `Relaxed` witness gives a finite label, and custody
turns finiteness plus `v ∉ U` into `v ∈ keys 𝒟`; the `B' ≤ d' v` side of the paper's clause is not
needed (custody is already inside the interval). -/
theorem callOut_tail_containR (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hcust : Custody st) :
    ∀ v, v ∈ Relaxed (callOut (tail B S W st)).d' B (callOut (tail B S W st)).U →
      (callOut (tail B S W st)).B' ≤ (callOut (tail B S W st)).d' v →
        v ∈ DS.keys (callOut (tail B S W st)).D := by
  intro v hrel _
  obtain ⟨hvU, hfin⟩ := hrel
  obtain ⟨e, -, -, -, hlt⟩ := hfin
  have hne : (callOut (tail B S W st)).d' v ≠ ⊤ := by
    rw [tailOut_d']
    exact ne_top_of_lt (lt_of_lt_of_le hlt le_top)
  rw [tailOut_d'] at hne
  rcases tail_custody B S W st hcust v hne with hs | hk
  · exact absurd hs hvU
  · rw [tailOut_D]
    exact hk

/-! ## 5. (3) `containS` — proved from the settlement identity

BM.25 re-inserts every seed `x ∈ S` with `B' ≤ d[x] < B` **keyed at `x`**, and the seed gate is
the only alternative to `x` being below `B'`; in that case `x ∈ Ũ(B', S)` and the identity forces
`x ∈ U ∪ K`, which the clause's hypothesis excludes. -/

/-- A fold of BM.25 gated inserts never drops a key. -/
theorem seedFold_ne_none (bp B : WLab G s) : ∀ (xs : List (Fin G.n)) (d : Labels G s)
    (D : DS G s) {x : Fin G.n}, D x ≠ none →
      (xs.foldl (fun (acc : Labels G s × DS G s) y =>
        if bp ≤ acc.1 y ∧ acc.1 y < B then (acc.1, DS.insert acc.2 y (acc.1 y)) else acc)
        (d, D)).2 x ≠ none := by
  intro xs
  induction xs with
  | nil => intro d D x hx; exact hx
  | cons y ys ih =>
    intro d D x hx
    rw [List.foldl_cons]
    by_cases hgy : bp ≤ d y ∧ d y < B
    · rw [if_pos hgy]
      exact ih d (DS.insert D y (d y)) (insert_ne_none D y (d y) x hx)
    · rw [if_neg hgy]
      exact ih d D hx

/-- BM.25 keeps the key of a seed whose own gate passes (labels never change across the fold, so
the seed recognises itself whenever it is reached). -/
theorem seedFold_gate_key (bp B : WLab G s) : ∀ (xs : List (Fin G.n)) (d : Labels G s)
    (D : DS G s) {x : Fin G.n}, x ∈ xs → bp ≤ d x ∧ d x < B →
      (xs.foldl (fun (acc : Labels G s × DS G s) y =>
        if bp ≤ acc.1 y ∧ acc.1 y < B then (acc.1, DS.insert acc.2 y (acc.1 y)) else acc)
        (d, D)).2 x ≠ none := by
  intro xs
  induction xs with
  | nil => intro d D x hx; nomatch hx
  | cons y ys ih =>
    intro d D x hx hg
    rw [List.foldl_cons]
    by_cases hgy : bp ≤ d y ∧ d y < B
    · rw [if_pos hgy]
      by_cases hyx : y = x
      · subst hyx
        exact seedFold_ne_none bp B ys d (DS.insert D y (d y))
          (by rw [DS.insert_self]; exact DS.mergeVal_ne_none _ _)
      · refine ih d (DS.insert D y (d y)) ?_ hg
        rcases List.mem_cons.mp hx with h | h
        · exact absurd h.symm hyx
        · exact h
    · rw [if_neg hgy]
      refine ih d D ?_ hg
      rcases List.mem_cons.mp hx with h | h
      · subst h
        exact absurd hg hgy
      · exact h

/-- A seed whose BM.25 gate passes is a key of the tail's `𝒟`. -/
theorem seedIns_gate_key (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s)
    {x : Fin G.n} (hx : x ∈ S) (hg : bp ≤ d x ∧ d x < B) :
    (seedIns bp B S d D).2 x ≠ none :=
  seedFold_gate_key bp B S.toList d D (Finset.mem_toList.mpr hx) hg

/-- **(3) `containS` at the return.**  A seed that is neither settled nor carved out is either
re-entered keyed by BM.25 (gate passes) or lies below `B'` inside `Ũ(B', S)` — where the
settlement identity forces it into `U` or `K`, contradiction.  The hypothesis `hdB` is the
`CallPre.inRange` side carried to the loop exit (labels only decrease along the run), and `hid` is
clause (2c) itself. -/
theorem callOut_tail_containS (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hsound : Sound st.d) (hdB : ∀ x ∈ S, st.d x < B)
    (hid : (callOut (tail B S W st)).U =
      Utilde (tailBP B st) (S : Set (Fin G.n)) \ (callOut (tail B S W st)).carveKeys S) :
    ((S : Set (Fin G.n)) \ ((callOut (tail B S W st)).U ∪
        (callOut (tail B S W st)).carveKeys S)) ⊆ DS.keys (callOut (tail B S W st)).D := by
  intro x hx
  obtain ⟨hxS, hxUK⟩ := hx
  have hxU : x ∉ (callOut (tail B S W st)).U := fun h => hxUK (Set.mem_union_left _ h)
  have hxK : x ∉ (callOut (tail B S W st)).carveKeys S :=
    fun h => hxUK (Set.mem_union_right _ h)
  have hxS' : x ∈ S := Finset.mem_coe.mp hxS
  rw [DS.keys]
  by_cases hgate : tailBP B st ≤ st.d x
  · have hkey : (seedIns (tailBP B st) B S st.d st.D).2 x ≠ none :=
      seedIns_gate_key _ _ _ _ _ hxS' ⟨hgate, hdB x hxS'⟩
    rw [tailOut_D]
    exact sweepEvts_ne_none _ (tailBP B st) _ _ _ x hkey
  · exfalso
    have hlt : st.d x < tailBP B st := not_le.mp hgate
    have hdis : dis (s := s) x < tailBP B st := (hsound x).trans_lt hlt
    have hreach : G.Reachable s x := by
      by_contra hr
      rw [dis_of_not_reachable hr] at hdis
      exact absurd hdis not_top_lt
    have hmem : x ∈ Utilde (tailBP B st) (S : Set (Fin G.n)) :=
      ⟨hdis, x, hxS, onPath_self hreach⟩
    rw [hid] at hxU
    exact hxU ⟨hmem, hxK⟩

/-! ## 6. (2c) `identity` — the reduction

`U = Ũ(B',S) ∖ K` splits into three facts, two of which are already proved above:
`U ⊆ Ũ(B',S)` (`tail_uSubset`), `U ∩ K = ∅` (`Structural.premShape_of_run`'s `x ∉ U`), and
`Ũ(B',S) ⊆ U ∪ K` — the "nothing below `B'` is left unsettled" content, named `hcover`. -/

/-- The settlement identity from its three halves. -/
theorem tail_identity (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (hsub : (callOut (tail B S W st)).U ⊆ Utilde (tailBP B st) (S : Set (Fin G.n)))
    (hdisj : ∀ x, x ∈ (callOut (tail B S W st)).U →
      x ∉ (callOut (tail B S W st)).carveKeys S)
    (hcover : Utilde (tailBP B st) (S : Set (Fin G.n)) ⊆
      (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S) :
    (callOut (tail B S W st)).U =
      Utilde (tailBP B st) (S : Set (Fin G.n)) \ (callOut (tail B S W st)).carveKeys S := by
  refine Set.Subset.antisymm (fun x hx => ⟨hsub hx, hdisj x hx⟩) ?_
  rintro x ⟨hxU, hxK⟩
  have hun := hcover hxU
  rw [Set.mem_union] at hun
  rcases hun with h | h
  · exact h
  · exact absurd h hxK

/-! ## 7. The loop invariants: one iteration, and the loop

`LoopProg`/`LoopSub` are preserved by an iteration from (a) the child's own clause at the child's
returned bound and (b) the running bound not dropping across the step.  Threading the loop needs
(b) for every pair of consecutive steps, so it is stated once as `BpChain` — the audit's per-call
`B'` monotonicity (CORRECTED_PROOF §8 item 5).  Nothing else about the loop is assumed. -/

/-- **Running-bound monotonicity** along an iteration sequence: the running `B'` never drops from
one iteration's child return to the next. -/
def BpChain : WLab G s → List (CallEntry G s × CallOut G s) → Prop
  | _, [] => True
  | B, q :: qs => B ≤ q.2.B' ∧ BpChain q.2.B' qs

theorem bpChain_cons {B : WLab G s} {q : CallEntry G s × CallOut G s}
    {qs : List (CallEntry G s × CallOut G s)} (h : BpChain B (q :: qs)) :
    B ≤ q.2.B' ∧ BpChain q.2.B' qs := h

/-- Every child's return bound dominates the loop's starting bound. -/
theorem bpChain_le : ∀ (B : WLab G s) {qs : List (CallEntry G s × CallOut G s)},
    BpChain B qs → ∀ q ∈ qs, B ≤ q.2.B' := by
  intro B qs
  induction qs generalizing B with
  | nil => intro _ q hq; nomatch hq
  | cons q0 qs ih =>
    intro h q hq
    obtain ⟨h0, hrest⟩ := h
    rcases List.mem_cons.mp hq with hq | hq
    · subst hq; exact h0
    · exact h0.trans (ih q0.2.B' hrest q hq)

/-- An iteration appends exactly its child's settlements to the log. -/
theorem istep_U_mem {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') (x : Fin G.n) :
    x ∈ settledSet st'.evts ↔ x ∈ settledSet st.evts ∨ x ∈ settledSet fo'.evts := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  rw [settledSet_append, Set.mem_union]

/-- Settlement provenance through the loop: every settlement of the exit log is the loop's own or
one of its children's. -/
theorem iloop_U_mem (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf → ∀ x, x ∈ settledSet stf.evts →
        x ∈ settledSet st.evts ∨ ∃ q ∈ qs, x ∈ settledSet q.2.evts := by
  intro p st stf qs h
  induction h with
  | exit h => intro x hx; exact Or.inl hx
  | step hne hg hstep hrest ih =>
    intro x hx
    rcases ih x hx with h0 | ⟨q, hq, hqx⟩
    · rcases (istep_U_mem hstep x).mp h0 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr ⟨_, List.mem_cons_self, h1⟩
    · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq, hqx⟩

/-- The step's running bound is its child's returned bound (BM.24). -/
theorem istep_bp {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    st'.bp = fo'.B' := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  rw [hst']

/-- One iteration preserves the progress invariant, given the child's own progress clause and the
step's bound monotonicity. -/
theorem istep_progress {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hprog : LoopProg st) (hchild : ∀ x ∈ settledSet fo'.evts, dis (s := s) x < fo'.B')
    (hmono : st.bp ≤ fo'.B') : LoopProg st' := by
  intro x hx
  rw [istep_bp h]
  rw [istep_U_mem h x] at hx
  rcases hx with hx | hx
  · exact (hprog x hx).trans_le hmono
  · exact hchild x hx

/-- One iteration preserves the subset invariant (child's clause + `S` monotonicity + the step's
bound monotonicity). -/
theorem istep_uSubset (S : Finset (Fin G.n)) {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hsub : LoopSub S st)
    (hcS : (c.S : Set (Fin G.n)) ⊆ (S : Set (Fin G.n)))
    (hchild : ∀ x ∈ settledSet fo'.evts, x ∈ Utilde fo'.B' (c.S : Set (Fin G.n)))
    (hmono : st.bp ≤ fo'.B') : LoopSub S st' := by
  intro x hx
  rw [istep_bp h]
  rw [istep_U_mem h x] at hx
  rcases hx with hx | hx
  · have hx' := hsub x hx
    exact utilde_of_lt hx' (hx'.1.trans_le hmono)
  · exact utilde_mono_set hcS (hchild x hx)

/-- The loop threads the progress invariant. -/
theorem iloop_progress (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf →
      (∀ q ∈ qs, ∀ x ∈ settledSet q.2.evts, dis (s := s) x < q.2.B') →
      BpChain st.bp qs → LoopProg st → LoopProg stf := by
  intro p st stf qs h
  induction h with
  | exit h => intro _ _ hinv; exact hinv
  | step hne hg hstep hrest ih =>
    intro hchild hchain hinv
    obtain ⟨h0, hrest_chain⟩ := bpChain_cons hchain
    refine ih (fun q hq => hchild q (List.mem_cons_of_mem _ hq)) ?_
      (istep_progress hstep hinv (hchild _ List.mem_cons_self) h0)
    rw [istep_bp hstep]
    exact hrest_chain

/-- The loop threads the subset invariant. -/
theorem iloop_uSubset (t : ℕ) (B : WLab G s) (l : ℕ) (S : Finset (Fin G.n)) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)},
      ILoop t B l st qs stf →
      (∀ q ∈ qs, (q.1.S : Set (Fin G.n)) ⊆ (S : Set (Fin G.n))) →
      (∀ q ∈ qs, ∀ x ∈ settledSet q.2.evts, x ∈ Utilde q.2.B' (q.1.S : Set (Fin G.n))) →
      BpChain st.bp qs → LoopSub S st → LoopSub S stf := by
  intro p st stf qs h
  induction h with
  | exit h => intro _ _ _ hinv; exact hinv
  | step hne hg hstep hrest ih =>
    intro hcS hchild hchain hinv
    obtain ⟨h0, hrest_chain⟩ := bpChain_cons hchain
    refine ih (fun q hq => hcS q (List.mem_cons_of_mem _ hq))
      (fun q hq => hchild q (List.mem_cons_of_mem _ hq)) ?_
      (istep_uSubset S hstep hinv (hcS _ List.mem_cons_self)
        (hchild _ List.mem_cons_self) h0)
    rw [istep_bp hstep]
    exact hrest_chain

/-- **`progress` from the loop's own data** — the assembled (2a) clause at the return, with the
boundary half discharged by `tail_progress` and the log half by `iloop_progress`. -/
theorem callOut_tail_progress_of_loop (t : ℕ) (B : WLab G s) (S W : Finset (Fin G.n))
    {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t B l st qs stf)
    (hchild : ∀ q ∈ qs, ∀ x ∈ settledSet q.2.evts, dis (s := s) x < q.2.B')
    (hchain : BpChain st.bp qs) (hinit : LoopProg st)
    (hbp : stf.bp ≤ B) (hsound : Sound stf.d) :
    ∀ x ∈ (callOut (tail B S W stf)).U, dis (s := s) x < (callOut (tail B S W stf)).B' :=
  tail_progress B S W stf (iloop_progress t B l hloop hchild hchain hinit) hbp hsound

/-- **`uSubset` from the loop's own data** — the assembled (2a) containment at the return. -/
theorem callOut_tail_uSubset_of_loop (t : ℕ) (B : WLab G s) (S W : Finset (Fin G.n))
    {p : ℕ} {st stf : RState G s p} {qs : List (CallEntry G s × CallOut G s)}
    (hloop : ILoop t B l st qs stf)
    (hcS : ∀ q ∈ qs, (q.1.S : Set (Fin G.n)) ⊆ (S : Set (Fin G.n)))
    (hchild : ∀ q ∈ qs, ∀ x ∈ settledSet q.2.evts,
      x ∈ Utilde q.2.B' (q.1.S : Set (Fin G.n)))
    (hchain : BpChain st.bp qs) (hinit : LoopSub S st)
    (hbp : stf.bp ≤ B) (hsound : Sound stf.d)
    (hW : (W : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))) :
    (callOut (tail B S W stf)).U ⊆ Utilde (tailBP B stf) (S : Set (Fin G.n)) :=
  tail_uSubset B S W stf (iloop_uSubset t B l S hloop hcS hchild hchain hinit) hbp hsound hW

/-! ## 8. The parent seam for `NoAbandonedBelow` (the leaf's missing invariant)

`A4.MintPreFloor` showed the leaf-local mint/label floor is **false** and that the exact missing
invariant is `NoAbandonedBelow` (`∀ y ∉ U, B'⁺ ≤ dis y`), which A1's interface cannot supply.
This section builds the parent side of that seam out of `IStep`'s own `pullRun`/`expand` data:

* `istep_pull_seed` — a key the pull takes is seeded into that iteration's child
  (`Si ⊆ expand`, plus `pullRun_pulled`), so it lands in the child's cone;
* `mem_cone_of_seed` — a seed at a label below the child's bound lies in `Ũ(c.B, c.S)`;
* `istep_seed_settled_or_carved` — the payoff: a *seed* below the child's **returned** bound is
  settled by the child or is one of the child's premature (carve-out) entries.  So the parent
  owns every abandoned vertex up to the carve-out, and nothing more;
* `child_noAbandonedBelow_of_noPrem` — hence the child's `NoAbandonedBelow` follows from the
  parent seam **plus** `Prem = ∅`, keeping the carve-out obligation separate from the conditional
  `run_mintFloor` bound.

**The exact residue** (nothing here is assumed away).  Two pieces are genuinely missing from the
parent's *current* semantics:

1. **Entry accuracy at the boundary key.**  `A4.Structural.istep_cover_accurate` gets a seed out
   of the pull only from `st.D y = some (st.d y)` — the entry is *accurate* — plus
   `st.d y < c.B`; `mem_expand_of_low_member` needs the group's pivot to have been pulled
   (`piv j ∈ Si`, with `piv j ∈ pl j`) and `d y < Bᵢ`.  `IStep`/`ILoop` maintain only one-sided
   honesty (`istep_honest`: `st.d y ≤ val`), never accuracy, so `istep_pull_seed` below states the
   weaker usable form: the *stored value* is below the child's bound (`∃ v, st.D y = some v ∧
   v < c.B`), which `pullRun_pulled` alone turns into seedhood.
2. **`resid` is filtered by settlement only.**  `resid j = (st.pl j).filter (x ∉ settledSet
   fo'.evts)`, so a residual member whose label falls below the running bound can leave the step
   unseeded: `st.pl` is never reset by the pull, and the loop may exit with such a member still
   in `pl`.  That is exactly the `Prem` escape, and `premInD_of_run`/`premShape_of_run` show the
   entry is at least kept in `𝒟`.  So `NoAbandonedBelow` at a leaf is equivalent to the carve-out
   being empty (`child_noAbandonedBelow_of_noPrem`), *not* to a leaf fact — which is why
   `MintPreFloor`'s counterexample does not contradict anything here.

The needed parent invariant, stated exactly, is therefore the pair
`(∀ y, dis y < c.B → ∃ v, st.D y = some v ∧ v < c.B) ∧ (∀ y, dis y < c.B → y ∈ c.S)` for every
child seed below its bound — i.e. accuracy-or-queueing at the boundary keys plus the `Bᵢ < B'⁺`
impossible gap — and it is a **loop invariant**, not a one-step consequence. -/

-- The `resid ⊆ expand` half of the seam already exists in `A4.Structural`:
-- `mem_expand_of_pulled` (pulled ⟹ seeded), `mem_expand_of_low_member` (low group member of a
-- pulled pivot ⟹ seeded) and `istep_cover_accurate` (the composed pull form).  What this file
-- adds below is the *cone/settlement* half they hand off to.

/-- A seed below the child's entry bound lies in the child's canonical cone. -/
theorem mem_cone_of_seed {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    (hsound : Sound d) {y : Fin G.n} (hS : y ∈ S) (hd : d y < B) :
    y ∈ Utilde B (S : Set (Fin G.n)) := by
  have hdis : dis (s := s) y < B := (hsound y).trans_lt hd
  exact ⟨hdis, y, Finset.mem_coe.mpr hS, onPath_self (reachable_of_lt hsound hd)⟩

/-- **The pull's keys are the iteration's seeds**: a `𝒟`-key below the separator is pulled
(`pullRun_pulled`) and hence expanded into the child's seed set. -/
theorem istep_pull_seed {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') {y : Fin G.n}
    (hyD : ∃ v, st.D y = some v ∧ v < c.B) : y ∈ c.S := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  obtain ⟨v, hv, hlt⟩ := hyD
  rw [hc] at hlt ⊢
  exact mem_expand_of_pulled ((pullRun_pulled hpull).mpr ⟨v, hv, hlt⟩)

/-- The child's labels are the parent's step labels. -/
theorem istep_child_d {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') : c.d = st.d := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, _⟩ := h
  rw [hc]

/-- **The parent seam's payoff.**  A child seed below the child's *returned* bound is settled by
the child or is one of the child's premature entries: the child's settlement identity decides it,
so the only escape is the Q12 carve-out. -/
theorem istep_seed_settled_or_carved {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hconcl : Lemma37Concl (Full t) c fo')
    (hsound : Sound st.d) {y : Fin G.n} (hseed : y ∈ c.S) (hd : st.d y < c.B)
    (hlt : dis (s := s) y < fo'.B') :
    y ∈ settledSet fo'.evts ∨ ∃ val, fo'.Premature y val := by
  have hcone : y ∈ Utilde c.B (c.S : Set (Fin G.n)) :=
    mem_cone_of_seed hsound hseed (istep_child_d h ▸ hd)
  have hcone' : y ∈ Utilde fo'.B' (c.S : Set (Fin G.n)) := utilde_of_lt hcone hlt
  by_cases hU : y ∈ fo'.U
  · exact Or.inl hU
  · refine Or.inr ?_
    have hK : y ∈ fo'.carveKeys c.S := by
      by_contra hk
      exact hU (hconcl.identity ▸ ⟨hcone', hk⟩)
    obtain ⟨⟨val, hp⟩, -⟩ := hK
    exact ⟨val, hp⟩

/-- **`NoAbandonedBelow` at a leaf child, from the parent's seam and carve-out emptiness.**  With
the child's cone covering every vertex below its returned bound (the `istep_pull_seed` linkage)
and `Prem = ∅`, nothing is abandoned below `B'⁺` — so `NoAbandonedBelow` is exactly the
`Prem = ∅` obligation, held separate from the conditional mint-value bound `run_mintFloor`. -/
theorem child_noAbandonedBelow_of_noPrem {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {bout : BaseOut G s}
    (h : IStep t B l st st' c (baseOut bout))
    (hconcl : Lemma37Concl (Full t) c (baseOut bout)) (hsound : Sound st.d)
    (hseed : ∀ y, dis (s := s) y < bout.B'_plus → y ∈ c.S)
    (hdB : ∀ y, y ∈ c.S → st.d y < c.B)
    (hnoprem : ∀ x val, ¬ (baseOut bout).Premature x val) :
    NoAbandonedBelow bout := by
  intro y hy
  by_contra hlt
  have hlt' : dis (s := s) y < bout.B'_plus := not_le.mp hlt
  rcases istep_seed_settled_or_carved h hconcl hsound (hseed y hlt') (hdB y (hseed y hlt'))
    hlt' with hs | ⟨val, hp⟩
  · exact hy hs
  · exact hnoprem y val hp

end DMSY
end Frontier

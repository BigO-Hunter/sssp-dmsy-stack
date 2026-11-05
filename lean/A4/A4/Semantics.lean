import A1.BaseCorrect
import A2.FPContract
import A3.PullLoop
import Frontier.DMSY.Interfaces

/-!
# Frontier.DMSY.Semantics — Algorithm 3 (BMSSP*) on the corrected engine (E0)–(E3)

Work package **A4 (BMSSP recursion)**.  The relational big-step judgment `Run t e out`
(CORRECTED_PROOF §2, A0's `A4` signature) of the *corrected* Duan–Mao–Shu–Yin recursion
(Algorithm 3), calling the already-verified subroutines verbatim (IMPLAN §1: import, do not
rebuild):

* **A1** `baseRun` — Algorithm 4 with the (E1) V5 cap (`l = 0` branch);
* **A2** `fpRun` — Algorithm 2 (tree building, member cap `k = fpCap t`);
* **A3** `pullRun` — the D-structure pull (DMSY Lemma 3.4).

The spine is pinned against the line-numbered corrected pseudocode **BM.1–BM.31** of the lane's
frozen algorithm text (c-hd-proof `paper/background/PRIOR_B1_UNVERIFIED_DRAFT.md` §3 = DMSY26
Alg. 3 with the (E0)–(E3) engine deltas), read through CORRECTED_PROOF §2.1/§4.1:

* **(E0)** the BM.7/BM.23 argmins are taken only over nonempty residual groups (the printed
  pseudocode crashes on `argmin ∅`);
* **(E1)** the V5 cap lives at the leaves (A1 owns it; `Engine.v5Cap`) — Algorithm 3 must *not*
  take its `B'` at `d_B[𝒟]` (CORRECTED_PROOF §4.2);
* **(E2)** both sweeps (BM.20 gate `≥ B_i`, BM.28 gate `≥ B'`) relax **only candidates in
  `[gate, B)`** — the prose reading of the line-23 sweep, which closes Q12's sweep channel;
  the child-interior channel survives and is handled by the clause-2 carve-out;
* **(E3)** `U` is the settlement **log** (events, not distinct vertices); BM.9's guard compares
  event counts at the level ceiling `Engine.eventCap t l`.

Semantics deltas pinned here (each load-bearing for the corrected Lemma 3.7\*, documented at its
definition): the BM.22 pivot update is a cost/load-bearing move only (the re-selection takes
`argmin` over the residual group regardless), so the relational semantics keeps the pivot fixed
and pins BM.22 for packages C2/C3; the line-29 re-selection mints are recorded per iteration and
`CallOut.mints` exposes the **final iteration's** — exactly the Q12 premature set of clause (2b).

The engine carries **★BM.15 (FIX-STALE)**: BM.14's merge is followed by the child's settled set
being deleted from `𝒟` (`D2 = DS.deleteSet (DS.merge D1 fo'.D) (settledFinset fo')`).  The
deletion is **required**, not cosmetic — it is what keeps settled keys out of `𝒟`, the frozen
text's (J2) `keys(𝒟) ∩ U = ∅`, whose (k1) case *is* BM.15 (`c-hd-proof` §S2.4 item 3, errata E1).
Without it a settled vertex stays a key of the parent's structure, a later pull hands it back to
the next child, and the `U_i` overlap (`Drain`/`|keys(𝒟)|`/S5's "every stored value of `D_i` is
`≺ B_i`" all fail).

**`T_X`'s duplicate accounting changes with the deletion** (Lemma 3.8\*(c)).  The **stale-key
channel is removed**: no pull key and no BM.12 expansion seed handed to the next child can be a
vertex this iteration's child already settled (`FixStale.istepFS_next_seeds_avoid_settled`), so the
parent's own store stops re-frontiering settled work.  Two channels remain and are *not* touched by
BM.15: the **cross-sibling** re-settlement of a shared vertex (each child's `W'` filter is
call-local and blind to a sibling's settlements — `A4.Size`'s Lemma 3.8\*(c) is stated for exactly
that excess), and the **`Prem`/Q12 mints** (the final iteration's line-29 inserts, `Premature` reads
`CallOut.mints` and `B'` only).  Clause (2b)/(2c) therefore survive verbatim at the shrunk key set,
with `T_X` no longer charged against stale `𝒟` keys.

## The Q9 instance (mandatory negative regression)

`Reach` (below) is the reachable-state closure of CORRECTED_PROOF §2.3: the top entry
`BMSSP*(⊤, {s}, l_top)` from `initLabels`, closed under the engine's own recursive calls.  The
audit's Q9 state (`{s,x,z,v}`, `d[x]` complete, `d[z] = d[v] = ⊤`, call `BMSSP(20, {x})`)
satisfies `Lemma37Hyp` but is **not** `Reach` — no run of the engine produces it.  The lemmas
below quantify over `Reach` only; the Q9 state is the regression that keeps them honest.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Parameters and loop state -/

/-- FindPivots member cap `k` (BM.4/FIX-L13: `3k ≤ t` keeps the BM.12 expansion inside
`|S_i| ≤ t²·2^((l-1)t)`); the paper's `k = ⌈t/log t⌉` is a cost choice of packages C2/C3. -/
def fpCap (t : ℕ) : ℕ := max 1 (t / 3)

/-- The Algorithm-3 iteration-loop state (BM.8–BM.24): labels, the structure `𝒟`, the cumulative
settlement log `U`, the running return bound `B'`, the residual pivot groups `Pl` (BM.17 removes
settled members), the current pivots, and the **current iteration's** line-29 re-selection mints
(replaced every iteration — `CallOut.mints` reports the final iteration's, the Q12 carve-out). -/
structure RState (G : Graph) (s : Fin G.n) (p : ℕ) where
  d : Labels G s
  D : DS G s
  evts : List (SettlementEvent G)
  bp : WLab G s
  pl : Fin p → Finset (Fin G.n)
  piv : Fin p → Fin G.n
  mints : List (Mint G s)

/-- The child's settled vertices as a `Finset` — ★BM.15's deletion set.  `DS.deleteSet` takes a
`Finset` and `settledSet` is a `Set`; the image of the settlement log's vertices is exactly the
frozen text's `U_i`, so a vertex settled twice is deleted once. -/
def settledFinset (fo : CallOut G s) : Finset (Fin G.n) :=
  fo.evts.toFinset.image fun ev => ev.v

theorem mem_settledFinset {fo : CallOut G s} {y : Fin G.n} :
    y ∈ settledFinset fo ↔ y ∈ settledSet fo.evts := by
  unfold settledFinset settledSet
  simp [List.mem_toFinset]

/-- **`DS.deleteSet` only drops keys.**  Every statement quantified as `∀ y val, D y = some val →
Φ y val` — `Ge`, `Keyed`, `LabFloor`'s key half, entry honesty — is preserved by BM.15's
deletion, because the deletion rewrites no stored value: it removes keys and leaves every
surviving value verbatim.  This is the one fact each consumer of the patched BM.14 clause needs,
and the exact opposite of what a value policy (re-keying) does. -/
theorem deleteSet_some_imp {D : DS G s} (T : Finset (Fin G.n)) {Φ : Fin G.n → WLab G s → Prop}
    (h : ∀ y val, D y = some val → Φ y val) :
    ∀ y val, DS.deleteSet D T y = some val → Φ y val := by
  intro y val hy
  by_cases hyT : y ∈ T
  · rw [DS.deleteSet_mem D T y hyT] at hy
    exact absurd hy.symm (Option.some_ne_none val)
  · rw [DS.deleteSet_of_notMem D T y hyT] at hy
    exact h y val hy

/-! ## (E2)-gated sweeps (BM.20 / BM.28) -/

/-- One edge under the (E2) gate: the candidate `d[src] ⊕ e` is relaxed (ties re-accepted,
idempotent store) and inserted **iff** it lies in `[lo, B)` and accepts (`≤ d[dst]`). -/
noncomputable def relaxGate (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) :
    Labels G s × DS G s :=
  let cand := ext (d (G.src e)) e
  if lo ≤ cand ∧ cand < B ∧ cand ≤ d (G.dst e) then
    (Function.update d (G.dst e) cand, DS.insert D (G.dst e) cand)
  else (d, D)

/-- The gated sweep of `u`'s out-edges (edge-index order), mirrors `A1.Sweep.sweep`. -/
noncomputable def sweepGate (B lo : WLab G s) (u : Fin G.n) : List (Fin G.m) →
    Labels G s → DS G s → Labels G s × DS G s
  | [], d, D => (d, D)
  | e :: es, d, D =>
    sweepGate B lo u es (if G.src e = u then (relaxGate B lo d D e).1 else d)
      (if G.src e = u then (relaxGate B lo d D e).2 else D)

/-- The BM.19–21 / BM.27–28 sweep driver: every listed settlement's out-edges, in log order. -/
noncomputable def sweepEvts (B lo : WLab G s) : List (SettlementEvent G) →
    Labels G s → DS G s → Labels G s × DS G s
  | [], d, D => (d, D)
  | ev :: evts, d, D =>
    let a := sweepGate B lo ev.v (List.finRange G.m) d D
    sweepEvts B lo evts a.1 a.2

/-! ## The BM.12 expansion -/

open Classical in
/-- BM.11–12 expansion: for each pulled key that is the *current* pivot of its group `j`, add
the low members `{v ∈ Pl j | d v < B_i}` to the child's seed set. -/
noncomputable def expand (d : Labels G s) {p : ℕ} (pl : Fin p → Finset (Fin G.n))
    (piv : Fin p → Fin G.n) (Si : Finset (Fin G.n)) (Bi : WLab G s) : Finset (Fin G.n) :=
  Si ∪ (Finset.univ.biUnion fun j =>
    if piv j ∈ Si ∧ piv j ∈ pl j then (pl j).filter (fun v => d v < Bi) else ∅)

/-! ## One iteration (BM.10–BM.24) and the BM.9 loop -/

open Classical in
/-- One Algorithm-3 loop iteration producing the recursive call entry `c` and consuming its
return `fo'` (BM.13): pull `(S_i, B_i)` (BM.10; size-capped at `pullCap t l` — Lemma 3.4's
`M = t·2^((l−1)t)`, the pull-size clause feeding the child seed-set bound of the joint
induction), expand (BM.11–12), merge the child's structure (BM.14) and **delete the child's
settled set** (★BM.15 FIX-STALE: a settled vertex must not survive as a key of the parent's
`𝒟`; that removes `T_X`'s stale-key channel, while the cross-sibling channel and the
`Prem` mints remain), sweep the child's settlements with the (E2) gate `[B_i, B)` (BM.19–21),
re-select the pivot of every group whose
pivot the child settled and which still has members (BM.18 + BM.23, (E0)-guarded, **ungated**
inserts = the line-29 mints), then `B' := B'_i`, `U := U + U_i` (BM.24).  The BM.22 pivot update
is cost/load-bearing only and is pinned here by keeping `piv` fixed during the iteration (C2/C3
own the exact text). -/
def IStep (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p)
    (c : CallEntry G s) (fo' : CallOut G s) : Prop :=
  ∃ (Si : Finset (Fin G.n)) (Bi : WLab G s) (D1 : DS G s)
    (resid : Fin p → Finset (Fin G.n)) (J : Finset (Fin p)) (sel : Fin p → Fin G.n)
    (D2 : DS G s) (d3 : Labels G s) (D3 : DS G s),
    pullRun (pullCap t l) st.D B Si Bi D1 ∧
    c = ⟨Bi, expand st.d st.pl st.piv Si Bi, l - 1, st.d⟩ ∧
    D2 = DS.deleteSet (DS.merge D1 fo'.D) (settledFinset fo') ∧
    (d3, D3) = sweepEvts B Bi fo'.evts fo'.d' D2 ∧
    (∀ j, resid j = (st.pl j).filter (fun x => x ∉ settledSet fo'.evts)) ∧
    J = (Finset.univ.filter fun j => st.piv j ∈ settledSet fo'.evts ∧ (resid j).Nonempty) ∧
    (∀ j, j ∈ J → sel j ∈ resid j ∧ ∀ y ∈ resid j, d3 (sel j) ≤ d3 y) ∧
    st' = { d := d3,
            D := J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3,
            evts := st.evts ++ fo'.evts,
            bp := fo'.B',
            pl := resid,
            piv := fun j => if j ∈ J then sel j else st.piv j,
            mints := J.toList.map (fun j => Mint.mk (sel j) (d3 (sel j))) }

/-! ## The BM.14 clause as a **policy**

`IStep` is the engine: BM.14's keep-min merge **and** ★BM.15's deletion of the child's settled
set.  `IStepWith` varies *that one conjunct* and nothing else, which is how the repair was
evaluated: `MergePolicy.parent` is BM.14 without BM.15 (the pre-repair engine, kept for the
negative regressions), `MergePolicy.fixStale` is the frozen text's BM.14+BM.15 and is the
instance the engine *is* (`istepWith_fixStale_iff`, `Iff.rfl`).  A policy that rewrites stored
values (`A4.MergeRepair`'s `MergePolicy.childLabel`) cannot repair a key-quantified floor; only a
key deletion can (`deleteSet_some_imp`). -/

/-- What BM.14 leaves in `𝒟` after a child return: the *policy* under evaluation. -/
abbrev MergePolicy (G : Graph) (s : Fin G.n) := DS G s → CallOut G s → DS G s

/-- BM.14 as written: keep-min of the two stores' values, key sets unioned.  **Historical** — this
is the pre-★BM.15 engine's clause, kept so the repaired engine can be contrasted with it. -/
noncomputable def MergePolicy.parent (D₁ : DS G s) (fo : CallOut G s) : DS G s := DS.merge D₁ fo.D

/-- ★BM.15 (FIX-STALE): merge, then delete the child's settled set — the engine's clause. -/
noncomputable def MergePolicy.fixStale (D₁ : DS G s) (fo : CallOut G s) : DS G s :=
  DS.deleteSet (DS.merge D₁ fo.D) (settledFinset fo)

open Classical in
/-- **`IStep` with the BM.14 clause varied by a policy** — the rest of the iteration (pull, BM.12
expansion, BM.24 sweeps, BM.18/23 residuals, mints) is verbatim `IStep`. -/
def IStepWith (M : MergePolicy G s) (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p)
    (c : CallEntry G s) (fo' : CallOut G s) : Prop :=
  ∃ (Si : Finset (Fin G.n)) (Bi : WLab G s) (D1 : DS G s)
    (resid : Fin p → Finset (Fin G.n)) (J : Finset (Fin p)) (sel : Fin p → Fin G.n)
    (D2 : DS G s) (d3 : Labels G s) (D3 : DS G s),
    pullRun (pullCap t l) st.D B Si Bi D1 ∧
    c = ⟨Bi, expand st.d st.pl st.piv Si Bi, l - 1, st.d⟩ ∧
    D2 = M D1 fo' ∧
    (d3, D3) = sweepEvts B Bi fo'.evts fo'.d' D2 ∧
    (∀ j, resid j = (st.pl j).filter (fun x => x ∉ settledSet fo'.evts)) ∧
    J = (Finset.univ.filter fun j => st.piv j ∈ settledSet fo'.evts ∧ (resid j).Nonempty) ∧
    (∀ j, j ∈ J → sel j ∈ resid j ∧ ∀ y ∈ resid j, d3 (sel j) ≤ d3 y) ∧
    st' = { d := d3,
            D := J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3,
            evts := st.evts ++ fo'.evts,
            bp := fo'.B',
            pl := resid,
            piv := fun j => if j ∈ J then sel j else st.piv j,
            mints := J.toList.map (fun j => Mint.mk (sel j) (d3 (sel j))) }

/-- BM.9's loop (E3): while `|U| ≤ Engine.eventCap t l` (events!) and `𝒟 ≠ ∅`.  The loop
collects the child call records (`q.1` entry, `q.2` return) so that `Run` can require each of
them to be a genuine run — the recursion is well-founded on the level `l`, no mutual
induction needed. -/
inductive ILoop (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ}, RState G s p → List (CallEntry G s × CallOut G s) → RState G s p → Prop
  | exit {p : ℕ} {st : RState G s p}
      (h : DS.IsEmpty st.D ∨ eventCap t l < st.evts.length) :
      ILoop t B l st [] st
  | step {p : ℕ} {st st' st'' : RState G s p}
      {q : CallEntry G s × CallOut G s} {qs : List (CallEntry G s × CallOut G s)}
      (hne : ¬ DS.IsEmpty st.D) (hg : st.evts.length ≤ eventCap t l)
      (hstep : IStep t B l st st' q.1 q.2) (hrest : ILoop t B l st' qs st'') :
      ILoop t B l st (q :: qs) st''

/-! ## Initialization (BM.3–BM.8) and the tail (BM.24a–BM.29) -/

/-- BM.7's pivot seeds (one **ungated** insert per group, (E0)-guarded by the caller). -/
noncomputable def initD' {p : ℕ} (d : Labels G s) (piv : Fin p → Fin G.n) : DS G s :=
  (List.finRange p).foldl (fun D j => DS.insert D (piv j) (d (piv j))) DS.empty

/-- BM.8's initial return bound `B' := min(B, min_j d[piv_j])` (empty min = `B`). -/
noncomputable def initBp {p : ℕ} (d : Labels G s) (piv : Fin p → Fin G.n) (B : WLab G s) :
    WLab G s :=
  (List.ofFn fun j : Fin p => d (piv j)).foldr min B

/-- BM.3–BM.8: the loop's initial state. -/
noncomputable def mkInit (e : CallEntry G s) (fo : FPOut G s)
    (piv : Fin fo.p → Fin G.n) : RState G s fo.p where
  d := fo.d'
  D := initD' fo.d' piv
  evts := []
  bp := initBp fo.d' piv e.B
  pl := fo.P
  piv := piv
  mints := []

open Classical in
/-- **BM.24a (FIX-EMPTY)**: `B' := B` when the loop exits with `𝒟` drained.  Load-bearing for
clauses (2a)/(2c): a return with `𝒟 = ∅` and `B' < B` is jointly unsatisfiable (the empty
frontier side would force `Ũ(B,S) ⊆ U ⊆ Ũ(B',S)`).  On a full execution the dichotomy then
gives `B' = B` and the tail's gates `[B', B)` are empty. -/
noncomputable def tailBP {p : ℕ} (B : WLab G s) (st : RState G s p) : WLab G s :=
  if DS.IsEmpty st.D then B else st.bp

/-- BM.25: re-insert the below-bound seeds `x ∈ S` with `B' ≤ d[x] < B` (gated `≥ B'`). -/
noncomputable def seedIns (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s) :
    Labels G s × DS G s :=
  S.toList.foldl (fun (acc : Labels G s × DS G s) x =>
    if bp ≤ acc.1 x ∧ acc.1 x < B then (acc.1, DS.insert acc.2 x (acc.1 x)) else acc) (d, D)

open Classical in
/-- BM.26's `W'` filter: `W' = {x ∈ W ∖ U | d[x] < B'}` — the boundary appends (E3's second
settlement source).  This is where Q11 bites: the filter is call-local and cannot see a
settlement in a sibling subtree, so `W'` can re-settle a vertex (Lemma 3.8\*(c)'s `T_X`). -/
noncomputable def wPrime (bp : WLab G s) (W : Finset (Fin G.n)) (evts : List (SettlementEvent G))
    (d : Labels G s) : Finset (Fin G.n) :=
  W.filter (fun x => x ∉ settledSet evts ∧ d x < bp)

/-- The boundary-append events of `W'` (E3). -/
noncomputable def wPrimeEvts (Wp : Finset (Fin G.n)) : List (SettlementEvent G) :=
  Wp.toList.map fun x => ⟨.boundaryAppend, x⟩

/-- BM.24a–BM.29 (the tail): fix `B'`, re-insert seeds (BM.25), append `W'` settlements
(BM.26/34), and sweep `W'` with the (E2) gate `[B', B)` (BM.27–28).  BM.29's `W'` delete is
the B1 variant's provable no-op (S2 (R3)); `IStep`'s ★BM.15 deletes only the *loop's* child
settled sets, so the tail's own `W'` keys are kept here (BM.29's delete is a no-op on this engine). -/
noncomputable def tail (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) :
    RState G s p where
  d := (sweepEvts B (tailBP B st) (wPrimeEvts (wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1))
        (seedIns (tailBP B st) B S st.d st.D).1 (seedIns (tailBP B st) B S st.d st.D).2).1
  D := (sweepEvts B (tailBP B st) (wPrimeEvts (wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1))
        (seedIns (tailBP B st) B S st.d st.D).1 (seedIns (tailBP B st) B S st.d st.D).2).2
  evts := st.evts ++ wPrimeEvts (wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1)
  bp := tailBP B st
  pl := st.pl
  piv := st.piv
  mints := st.mints

/-! ## The BMSSP* judgment (A0's `A4` signature) -/

/-- The return record of the `l = 0` case (A1's V5-capped base case; no mints, no groups). -/
def baseOut (bout : BaseOut G s) : CallOut G s where
  B' := bout.B'_plus
  evts := bout.evts
  D := bout.D_final
  d' := bout.d'
  mints := []
  pfin := 0
  Pfin := fun _ => ∅

/-- The return record of the `l > 0` case: the tail's state and the **final iteration's** mints,
with the FindPivots residual groups (clause (2b) reads `x ∈ P_j` from them). -/
def callOut {p : ℕ} (st : RState G s p) : CallOut G s where
  B' := st.bp
  evts := st.evts
  D := st.D
  d' := st.d
  mints := st.mints
  pfin := p
  Pfin := st.pl

/-- **BMSSP\*** (Algorithm 3 on the corrected engine) — A4's cost-free relational big-step
(the cost index is package C3's; the loop carries no cost here).  `l = 0` delegates to A1's
`baseRun` on the Algorithm-4 initialization `initD`; `l > 0` runs FindPivots (A2), the BM.9
loop (whose per-iteration child calls are required to be genuine `Run`s), and the tail. -/
inductive Run (t : ℕ) : CallEntry G s → CallOut G s → Prop
  | base {e : CallEntry G s} {bout : BaseOut G s}
      (hl : e.l = 0) (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
      Run t e (baseOut bout)
  | recur {e : CallEntry G s} {p : ℕ} {fo : FPOut G s} {piv : Fin fo.p → Fin G.n}
      {st0 stf : RState G s fo.p} {qs : List (CallEntry G s × CallOut G s)}
      (hl : 0 < e.l) (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
      (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
      (hst0 : st0 = mkInit e fo piv)
      (hloop : ILoop t e.B e.l st0 qs stf)
      (hchildren : ∀ q ∈ qs, Run t q.1 q.2) :
      Run t e (callOut (tail e.B e.S fo.W stf))

/-- A **full execution** (Lemma 3.7\*'s `Full`): the loop exited with `𝒟` drained.  The tail
only adds keys, so `out.D` is empty exactly on full executions; the final iteration's mints
insert their keys and nothing deletes them after BM.10, so full executions have no mints. -/
def Full (t : ℕ) (e : CallEntry G s) (out : CallOut G s) : Prop :=
  Run t e out ∧ DS.IsEmpty out.D

/-! ## Reachable-state closure (CORRECTED_PROOF §2.3, Q9 fix) -/

/-- `c` is the entry of a recursive call (BM.13) made by `e`'s Algorithm-3 run: the loop of
`e`'s `l > 0` spine iterated through `c`.  The witnesses are **tied to one `recur` derivation**
(wound R2125608361): the `Run` witness is exactly the `recur` conclusion at these components
(`out = callOut (tail e.B e.S fo.W stf)`), and the loop's child returns are required to be
genuine `Run`s — the exact shape `childOf_of_recur` builds.  The untied form admitted a `Run`
witness unrelated to the `ILoop` witness and junk (non-run) child returns, which blocked
`Sound` at every `Reach` entry (`A4.Structural.reach_sound`). -/
def ChildOf (t : ℕ) (e c : CallEntry G s) : Prop :=
  ∃ (out : CallOut G s) (p : ℕ) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n)
    (st0 stf : RState G s fo.p) (qs : List (CallEntry G s × CallOut G s)),
    Run t e out ∧ out = callOut (tail e.B e.S fo.W stf) ∧ 0 < e.l ∧
    fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo ∧
    (∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y) ∧
    st0 = mkInit e fo piv ∧ ILoop t e.B e.l st0 qs stf ∧
    (∀ q ∈ qs, Run t q.1 q.2) ∧ ∃ q ∈ qs, q.1 = c

/-- **Reachable entries** (CORRECTED_PROOF §2.3): the top entry `BMSSP*(⊤, {s}, l_top)` from
`initLabels`, closed under the engine's own recursive calls.  All of A4's lemmas quantify over
`Reach`; the audit's Q9 state is not reachable (see the module docstring). -/
inductive Reach (t : ℕ) : CallEntry G s → Prop
  | top : Reach t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩
  | sub {e c : CallEntry G s} (he : Reach t e) (hc : ChildOf t e c) : Reach t c

/-! ## The totality judgment (task key lemma 2) -/

/-- **Totality judgment** (`forall Reach entry, exists out, Run top out`): every reachable
entry has a return — the engine never gets stuck on reachable entries.  This is the run-
existence step of top-level exactness (`TopExactAt`'s `∃ out, Run top out`), consumed by
`A4.Main.top_exact_at`; the relational semantics admits derivations but does not derive their
existence, so totality is pinned as a judgment (proved or assumed per deployment).  The
top-level corollary is the instance at `⟨⊤, {s}, lTop t G.n, initLabels G s⟩`; its full-
execution flavor (loop exit with `𝒟` drained) is the (E3) guard's delivery, bounded by
`eventCap_lTop` (`eventCap t (lTop t n) > n`) plus the settlement-count certificate. -/
def Total (t : ℕ) : Prop := ∀ (e : CallEntry G s), Reach t e → ∃ out, Run t e out

end DMSY
end Frontier

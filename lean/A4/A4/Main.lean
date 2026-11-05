import A4.Size
import A4.LemmaD
import A4.Window
import A4.ExecutionFrame
import A4.Cascade

/-!
# Frontier.DMSY.Main — the corrected Lemma 3.7* assembly (work package A4)

Work package **A4 (BMSSP recursion)**.  The A0 interface targets `A4Contract` and top-level
exactness, assembled from the semantics (`A4.Semantics`), the structural half
(`A4.Structural`), the transitive proposition (`A4.Transitive`) and the size contract
(`A4.Size`).

Clause-by-clause status at the recursion level (`Lemma37Concl`, CORRECTED_PROOF §3):

| clause | source of the proof | status here |
|---|---|---|
| (1) frontier | framework `IsFrontier.step`/`.split` across pull/expansion/child steps (`istep_child_frontier` is the instantiated split at pulls; the loop-state frontier invariant is the joint chain's remaining half) | joint chain |
| (2a) progress + `U ⊆ Ũ(B', S)` | refusal-floor `A1.utilde_of_relax`, `utilde_subset` | joint chain |
| (2a) settlement completeness | W′ appends settle complete `W` (A2 runs to exhaustion — `A2.fpRun_pull_invariant`) + child IH; persistence `Complete.of_le` | joint chain |
| (2b) bound, modulo Prem | transitive proposition (`A4.Transitive`), Prem-free children | joint chain |
| (2b) Prem shape / membership | mint bookkeeping (`A4.Structural.premInD_of_run/premShape_of_run`) | stated |
| (2b) full immunity | `A4.Structural.full_no_prem` | **proved** |
| (2c) identity `U = Ũ(B',S) ∖ K` | frontier squeeze `IsFrontier.below` + audit's Lemma V | joint chain |
| (3) containment | `Relaxed`/sweep custody (audit's Lemma Rep) | joint chain |

The *joint chain* rows are the audit's joint first-violation induction (CORRECTED_PROOF §8.1:
Lemma W/V/Rep, W′ drop, refusal-floor — "the main body of the Lean work", hand-proved in the
audit, **not machine-checked**).  They are pinned here as one named obligation (`JointChain`)
so the remaining work is a single visible seam.  The **Q9 regression** and the **Q12 carve-out**
are structural in this development: the former is excluded by `Reach`, the latter is carried by
`CallOut.mints`/`Premature` throughout.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The joint obligation (CORRECTED_PROOF §8.1) -/

/-- Carve-out emptiness at one return (Theorem T's per-return clause). -/
def NoPrem (e : CallEntry G s) (out : CallOut G s) : Prop :=
  ∀ x val, ¬ out.Premature x val

/-- **JointChain** — the audit's joint first-violation induction, the one remaining seam of A4:
settlement completeness (2a), the frontier (1), the identity (2c), containment (3), the bound
clause (2b) with Prem-free children, and carve-out emptiness (Theorem T), all at once over
reachable runs.  The audit proves this by a first-violation induction on settlement batches
(PROOF.md §3) from Lemma W (window), Lemma V (no sub-`B'` values at returns/filters), Lemma Rep
(custody), the W′ drop lemma and the refusal-floor lemma (`A1.utilde_of_relax`). -/
def JointChain (t : ℕ) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s),
    Reach t e → Lemma37Hyp t e → Run t e out →
      Lemma37Concl (Full t) e out ∧ NoPrem e out

/-- **A4's main theorem** (task key lemma 1): the corrected Lemma 3.7\* over reachable runs,
with the Q12 carve-out and the Q9 closure, plus Theorem T's carve-out emptiness. -/
theorem a4_joint (t : ℕ) (G : Graph) (s : Fin G.n) : @JointChain G s t := by
  intro e out hre hyp hrun
  sorry -- the audit's joint first-violation induction (CORRECTED_PROOF §8.1)

/-- **Corrected Lemma 3.7\*** (`Lemma37Star`, A0): frontier clause, bound+completeness clause
with the Q12 carve-out, containment clause — over reachable entries (Q9). -/
theorem lemma37Star (t : ℕ) (G : Graph) (s : Fin G.n) :
    @Lemma37Star G s t (@Reach G s t) (@Run G s t) (@Full G s t) := by
  intro e out hre hyp hrun
  exact (a4_joint t G s e out hre hyp hrun).1

/-- **Theorem T** (carve-out emptiness on the V5 engine, A0): `Prem = ∅` at every return of
every reachable run.  Note this quantifies over *all* reachable runs, including `l = 0`
(base runs have `mints = []`, so those cases are free). -/
theorem theoremT (t : ℕ) (G : Graph) (s : Fin G.n) :
    @TheoremT G s (@Reach G s t) (@Run G s t) := by
  intro e out hre hrun x val hp
  sorry -- from `JointChain` + the `Lemma37Hyp` of reachable entries (audit §5, Theorem T)

/-- **A4's interface theorem**: `A4Contract` (A0) — the corrected engine satisfies Lemma 3.7\*
and Theorem T. -/
theorem a4_contract (t : ℕ) (G : Graph) (s : Fin G.n) :
    @A4Contract G s t (@Reach G s t) (@Run G s t) (@Full G s t) :=
  ⟨lemma37Star t G s, theoremT t G s⟩

/-! ## Top-level support: labels stay `⊤` off the reachable set, keys never drop

Two mechanical invariants consumed by top-level exactness (R2125608334):

* `UnreachTop` — a label at a vertex unreachable from `s` stays `⊤`.  This is the minimal form of
  "unreachable vertices stay `⊤` by label soundness": A4 carries no `WalkInv` preservation chain
  for `Run`, but top-level exactness needs only this weak invariant, which every layer preserves
  mechanically (a finite label at `v` is only ever produced along an edge out of a vertex whose
  label was finite, hence reachable).
* key growth — `DS.insert` never drops a key, so a drained returned `𝒟` forces the loop's exit `𝒟`
  to be drained, and FIX-EMPTY then pins `B' = B = ⊤` at the top call. -/

/-- Labels stay `⊤` at vertices unreachable from `s`. -/
def UnreachTop (d : Labels G s) : Prop := ∀ v, ¬ G.Reachable s v → d v = ⊤

/-- The head of an edge whose tail is reachable from `s` is reachable. -/
theorem reachable_dst {e : Fin G.m} (h : G.Reachable s (G.src e)) :
    G.Reachable s (G.dst e) := by
  obtain ⟨p, hp⟩ := h
  exact ⟨p ++ [e], hp.append (IsWalk.single e)⟩

/-- A walk-labelled vertex is reachable; `WalkInv` labels are `⊤` off the reachable set. -/
theorem unreachTop_of_walk {d : Labels G s} (h : WalkInv d) : UnreachTop d := by
  intro v hv
  by_contra hne
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp hne
  exact hv ⟨p, h v p (hp.symm ▸ rfl)⟩

theorem relaxGate_unreach (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (h : UnreachTop d) : UnreachTop (relaxGate B lo d D e).1 := by
  intro v hv
  unfold relaxGate
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos hc]
    by_cases hvz : v = G.dst e
    · subst hvz
      show Function.update d (G.dst e) (ext (d (G.src e)) e) (G.dst e) = ⊤
      rw [Function.update_self]
      by_cases htop : d (G.src e) = ⊤
      · rw [htop, ext_top]
      · have hsrc : G.Reachable s (G.src e) := by
          by_contra hr
          exact htop (h (G.src e) hr)
        exact absurd (reachable_dst hsrc) hv
    · show Function.update d (G.dst e) (ext (d (G.src e)) e) v = ⊤
      rw [Function.update_of_ne hvz]
      exact h v hv
  · rw [if_neg hc]
    exact h v hv

theorem sweepGate_unreach (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (h : UnreachTop d) : UnreachTop (sweepGate B lo u es d D).1 := by
  induction es generalizing d D with
  | nil => exact h
  | cons e es ih =>
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (relaxGate_unreach B lo d D e h)
    · rw [if_neg hs, if_neg hs]
      exact ih d D h

theorem sweepEvts_unreach (B lo : WLab G s) (evts : List (SettlementEvent G)) (d : Labels G s)
    (D : DS G s) (h : UnreachTop d) : UnreachTop (sweepEvts B lo evts d D).1 := by
  induction evts generalizing d D with
  | nil => exact h
  | cons ev evts ih =>
    unfold sweepEvts
    exact ih _ _ (sweepGate_unreach B lo ev.v (List.finRange G.m) d D h)

/-- `seedIns` never touches labels. -/
theorem seedIns_d (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s) :
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

theorem tail_unreach (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (h : UnreachTop st.d) : UnreachTop (tail B S W st).d :=
  sweepEvts_unreach B (tailBP B st) _ _ _ (by rw [seedIns_d]; exact h)

theorem a1_relaxEdge_unreach (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (h : UnreachTop d) : UnreachTop (relaxEdge B d D e).1 := by
  intro v hv
  unfold relaxEdge
  by_cases hc : ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B
  · rw [if_pos hc]
    by_cases hvz : v = G.dst e
    · subst hvz
      show Function.update d (G.dst e) (ext (d (G.src e)) e) (G.dst e) = ⊤
      rw [Function.update_self]
      by_cases htop : d (G.src e) = ⊤
      · rw [htop, ext_top]
      · have hsrc : G.Reachable s (G.src e) := by
          by_contra hr
          exact htop (h (G.src e) hr)
        exact absurd (reachable_dst hsrc) hv
    · show Function.update d (G.dst e) (ext (d (G.src e)) e) v = ⊤
      rw [Function.update_of_ne hvz]
      exact h v hv
  · rw [if_neg hc]
    exact h v hv

theorem a1_sweep_unreach (B : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (h : UnreachTop d) : UnreachTop (sweep B u es d D).1 := by
  induction es generalizing d D with
  | nil => exact h
  | cons e es ih =>
    unfold sweep
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (a1_relaxEdge_unreach B d D e h)
    · rw [if_neg hs, if_neg hs]
      exact ih d D h

theorem a1_loop_unreach (t : ℕ) (B : WLab G s) :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' → UnreachTop st.d → UnreachTop st'.d := by
  intro c st st' h
  induction h with
  | exit h => exact fun hst => hst
  | pull u lam x hne hg hu hxgt hxle hxrest hxeq hrest ih =>
    intro hst
    refine ih ?_
    exact a1_sweep_unreach B u (List.finRange G.m) _ _ hst

theorem baseRun_unreach {t : ℕ} {e : BaseIn G s} {out : BaseOut G s}
    (h : UnreachTop e.d) (hb : baseRun t e out) : UnreachTop out.d' := by
  obtain ⟨c, st, hloop, hr⟩ := hb
  subst hr
  exact a1_loop_unreach t e.B hloop h

/-- One iteration's child call inherits the parent's loop labels (BM.13's `st.d`) —
`A4.Structural.istep_entry_d`. -/
theorem istep_unreach {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hc : UnreachTop fo'.d') : UnreachTop st'.d := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc', hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  show UnreachTop d3
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := congrArg Prod.fst hsweep
  rw [hd3]
  exact sweepEvts_unreach B Bi fo'.evts fo'.d' D2 hc

theorem iloop_unreach (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      UnreachTop st.d → (∀ q ∈ qs, UnreachTop q.1.d → UnreachTop q.2.d') → UnreachTop stf.d := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun hst _ => hst
  | step hne hg hstep hrest ih =>
    intro hst hkids
    refine ih ?_ (fun q hq => hkids q (List.mem_cons_of_mem _ hq))
    exact istep_unreach hstep
      (hkids _ List.mem_cons_self (by rw [istep_entry_d hstep]; exact hst))

/-- `Run` preserves `UnreachTop` on the entry labels (R2125608334's mechanical half). -/
theorem run_unreach (t : ℕ) : ∀ {e : CallEntry G s} {out : CallOut G s},
    Run t e out → UnreachTop e.d → UnreachTop out.d' := by
  intro e out h
  induction h with
  | base hl hb => exact fun hd => baseRun_unreach hd hb
  | recur hl hfp hpiv hst0 hloop _hchildren ih =>
    intro hd
    refine tail_unreach _ _ _ _ ?_
    refine iloop_unreach t _ _ hloop ?_ ?_
    · rw [hst0]
      exact unreachTop_of_walk (fpRun_contract _ _ hfp).1.walk
    · intro q hq hq1
      exact ih q hq hq1

/-- `initLabels` is `⊤` off `{s}`, and `s` is trivially reachable. -/
theorem initLabels_unreach : UnreachTop (initLabels G s) := by
  intro v hv
  by_cases hv' : v = s
  · rw [hv'] at hv
    exact absurd (⟨[], IsWalk.nil s⟩ : G.Reachable s s) hv
  · simp [initLabels, hv']

/-- The source's canonical label is the empty walk. -/
theorem dis_source : dis (s := s) s = ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) := by
  rw [dis_of_reachable (⟨[], IsWalk.nil s⟩ : G.Reachable s s), path_source]

theorem initLabels_source : initLabels G s s = dis (s := s) s := by
  rw [dis_source]
  simp [initLabels]

/-! ## Key growth (a drained returned `𝒟` means a drained loop exit) -/

/-- `DS.insert` never drops a key. -/
theorem insert_ne_none (D : DS G s) (y : Fin G.n) (lam : WLab G s) (x : Fin G.n)
    (hx : D x ≠ none) : (DS.insert D y lam) x ≠ none := by
  by_cases hxy : x = y
  · rw [hxy, DS.insert_self]
    exact DS.mergeVal_ne_none (D y) lam
  · rw [DS.insert_of_ne D y lam hxy]
    exact hx

theorem relaxGate_ne_none (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (x : Fin G.n) (hx : D x ≠ none) : (relaxGate B lo d D e).2 x ≠ none := by
  unfold relaxGate
  by_cases h : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos h]
    exact insert_ne_none D (G.dst e) (ext (d (G.src e)) e) x hx
  · rw [if_neg h]
    exact hx

theorem sweepGate_ne_none (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m)) (d : Labels G s)
    (D : DS G s) (x : Fin G.n) (hx : D x ≠ none) : (sweepGate B lo u es d D).2 x ≠ none := by
  induction es generalizing d D with
  | nil => exact hx
  | cons e es ih =>
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (relaxGate_ne_none B lo d D e x hx)
    · rw [if_neg hs, if_neg hs]
      exact ih d D hx

theorem sweepEvts_ne_none (B lo : WLab G s) (evts : List (SettlementEvent G)) (d : Labels G s)
    (D : DS G s) (x : Fin G.n) (hx : D x ≠ none) : (sweepEvts B lo evts d D).2 x ≠ none := by
  induction evts generalizing d D with
  | nil => exact hx
  | cons ev evts ih =>
    unfold sweepEvts
    exact ih _ _ (sweepGate_ne_none B lo ev.v (List.finRange G.m) d D x hx)

theorem seedIns_ne_none (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s)
    (x : Fin G.n) (hx : D x ≠ none) : (seedIns bp B S d D).2 x ≠ none := by
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => exact hx
  | cons y ys ih =>
    rw [List.foldl_cons]
    by_cases hg : bp ≤ d y ∧ d y < B
    · rw [if_pos hg]
      exact ih d (DS.insert D y (d y)) (insert_ne_none D y (d y) x hx)
    · rw [if_neg hg]
      exact ih d D hx

theorem tail_ne_none (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (x : Fin G.n) (hx : st.D x ≠ none) : (tail B S W st).D x ≠ none :=
  sweepEvts_ne_none B (tailBP B st) _ _ _ x
    (seedIns_ne_none (tailBP B st) B S st.d st.D x hx)

/-! ## Top-entry facts -/

/-- `memCap` is at least 1 for `0 < t` (feeds `Lemma37Hyp`'s member bound at top). -/
theorem one_le_memCap {t l : ℕ} (ht : 0 < t) : 1 ≤ memCap t l := by
  unfold memCap
  have h2 : 0 < t ^ 2 := pow_pos ht 2
  have h3 : 0 < 2 ^ (l * t) := pow_pos (by norm_num) (l * t)
  have h4 : 0 < t ^ 2 * 2 ^ (l * t) := mul_pos h2 h3
  omega

/-- The base input of the top entry is a reachable base input (A1's `ReachBase`): `CallPre` at
`initLabels` (walks, vacuous Claim C below `⊤`, the initial frontier, `d[s] < ⊤`). -/
theorem reachBase_topEntry :
    ReachBase (⟨(⊤ : WLab G s), {s}, initLabels G s, initD {s} (initLabels G s)⟩ : BaseIn G s) := by
  have hfront : IsFrontier (initLabels G s)
      (Utilde (s := s) ⊤ (({s} : Finset (Fin G.n)) : Set (Fin G.n)))
      ∅ (({s} : Finset (Fin G.n)) : Set (Fin G.n)) := by
    rw [Finset.coe_singleton]
    exact isFrontier_init initLabels_source
  have hclaim : ∀ v, dis (s := s) v < (⊤ : WLab G s) →
      v ∉ Utilde (s := s) ⊤ (({s} : Finset (Fin G.n)) : Set (Fin G.n)) →
        Complete (initLabels G s) v := by
    intro v hlt hnot
    have hre : G.Reachable s v := by
      by_contra hr
      rw [dis_of_not_reachable hr] at hlt
      exact absurd hlt (lt_irrefl _)
    rw [Finset.coe_singleton, utilde_top_source] at hnot
    exact absurd hre hnot
  have hinr : ∀ x ∈ ({s} : Finset (Fin G.n)), initLabels G s x < (⊤ : WLab G s) := by
    intro x hx
    have hxs : x = s := by simpa using hx
    rw [hxs]
    show (if s = s then ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) else ⊤) < ⊤
    rw [if_pos rfl]
    exact WithTop.coe_lt_top _
  have hcall : CallPre (⊤ : WLab G s) ({s} : Finset (Fin G.n)) (initLabels G s) :=
    ⟨initLabels_walk, hclaim, hfront, hinr⟩
  exact ⟨hcall, rfl⟩

/-- With no premature mints the carve-out keys are empty. -/
theorem carveKeys_empty {out : CallOut G s} (hn : ∀ x val, ¬ out.Premature x val)
    (S : Finset (Fin G.n)) : out.carveKeys S = (∅ : Set (Fin G.n)) := by
  apply Set.eq_empty_of_forall_notMem
  intro x hx
  obtain ⟨⟨val, hp⟩, _⟩ := hx
  exact absurd hp (hn x val)

/-- At the top entry, a **full** run (loop exit with `𝒟` drained) returns `B' = ⊤` and the exact
settlement identity over every reachable vertex, all settlements complete.  The base case is
Lemma 3.1*'s dichotomy + identity + `settleComplete` (A1); the recursion case is FIX-EMPTY
(`tailBP_of_isEmpty`, with key growth forcing the loop exit `𝒟` drained) + `JointChain`'s identity
and settlement clauses + Theorem T (carve-out emptiness). -/
theorem top_full_facts_gen (t : ℕ) (ht : 2 ≤ t) : ∀ {e : CallEntry G s} {out : CallOut G s},
    Run t e out → Reach t e → e.B = (⊤ : WLab G s) → e.S = {s} → e.d = initLabels G s →
    DS.IsEmpty out.D →
      out.B' = (⊤ : WLab G s) ∧ out.U = {v | G.Reachable s v} ∧
        ∀ ev ∈ out.evts, Complete out.d' ev.v := by
  intro e out h
  induction h with
  | base hl hb =>
    rename_i E bb
    intro hre hB hS hd hempty
    have hrb : ReachBase (⟨E.B, E.S, E.d, initD E.S E.d⟩ : BaseIn G s) := by
      rw [hB, hS, hd]
      exact reachBase_topEntry
    have h31 := baseRun_lemma31 hrb hb
    obtain ⟨c, st, hloop, hr⟩ := hb
    subst hr
    have hD : DS.IsEmpty st.D := hempty
    have hdich := h31.dichotomy.mpr hD
    change (st.x ⊓ dMin E.B st.D) = E.B at hdich
    refine ⟨?_, ?_, h31.settleComplete⟩
    · show st.x ⊓ dMin E.B st.D = (⊤ : WLab G s)
      rw [hdich, hB]
    · have hU : settledSet st.evts = Utilde (st.x ⊓ dMin E.B st.D)
        ((E.S : Finset (Fin G.n)) : Set (Fin G.n)) := h31.identity
      rw [hdich, hB, hS, Finset.coe_singleton, utilde_top_source] at hU
      show settledSet st.evts = _
      exact hU
  | recur hl hfp hpiv hst0 hloop hchildren _ih =>
    rename_i E pp fo piv st0 stf qs
    intro hre hB hS hd hempty
    have hstf : DS.IsEmpty stf.D := by
      intro y
      by_contra hn
      exact absurd (hempty y) (tail_ne_none _ _ _ _ y hn)
    have hbp : (callOut (tail E.B E.S fo.W stf)).B' = (⊤ : WLab G s) := by
      show tailBP E.B stf = ⊤
      rw [hB]
      exact tailBP_of_isEmpty _ _ hstf
    have hhyp : Lemma37Hyp t E := by
      refine ⟨hl, ?_, ?_⟩
      · rw [hB, hS, hd, Finset.coe_singleton]
        exact isFrontier_init initLabels_source
      · rw [hS, Finset.card_singleton]
        exact one_le_memCap (lt_of_lt_of_le (by norm_num) ht)
    have hrun' : Run t E (callOut (tail E.B E.S fo.W stf)) :=
      @Run.recur G s t E pp fo piv st0 stf qs hl hfp hpiv hst0 hloop hchildren
    obtain ⟨hconc, hnoprem⟩ := a4_joint t G s E (callOut (tail E.B E.S fo.W stf)) hre hhyp hrun'
    have hU : (callOut (tail E.B E.S fo.W stf)).U = {v | G.Reachable s v} := by
      rw [hconc.identity, hbp, carveKeys_empty hnoprem E.S, Set.diff_empty,
        hS, Finset.coe_singleton, utilde_top_source]
    exact ⟨hbp, hU, hconc.settleComplete⟩

theorem top_full_facts (t : ℕ) {out : CallOut G s}
    (ht : 2 ≤ t)
    (hre : Reach t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩)
    (hrun : Run t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ out)
    (hempty : DS.IsEmpty out.D) :
    out.B' = (⊤ : WLab G s) ∧ out.U = {v | G.Reachable s v} ∧
      ∀ ev ∈ out.evts, Complete out.d' ev.v :=
  top_full_facts_gen t ht hrun hre rfl rfl rfl hempty

/-! ## Top-level exactness

**Interface defect (A0 `TopExact`).**  As pinned, `TopExact t` quantifies over *arbitrary*
`Reach`/`Run` (`∀ Reach Run, Reach top → ∃ out, Run top out ∧ ∀ v, Complete out.d' v`), which
is unsatisfiable (`Run := fun _ _ => False` refutes it).  The intended statement is the
instantiation at A4's own judgments (as `A4Contract` takes them as parameters); that version is
pinned and targeted below as `TopExactAt`.

**Statement repair (R2125608333).**  Two further ingredients had to become explicit antecedents:

* `TopFull` — the (E3) guard's **full-execution delivery** at top.  A run that exits the loop by
  event overflow returns `B' < ⊤` and leaves unsettled vertices incomplete, so
  `Total` alone (mere run existence) cannot yield complete labels.  `eventCap_lTop` delivers
  no-overflow only on *distinct* settlements (`|U| ≤ n₂ < t³·2^(l_top·t)`); under (E3) the guard
  counts *events* — duplicate re-settlements included (Q11/T_X) — and CORRECTED_PROOF §2.1
  records "no ceiling on settlement events exists anywhere" (§4.2: the guard enforces fullness
  "by abort").  The delivery rides the audit's duplicate-excess bound (Lemma E) and is pinned as
  a judgment alongside `Total` (proved or assumed per deployment).
* `2 ≤ t` — the parameter regime of the guard lemma (`eventCap_lTop`, sharp at `t = 1`). -/

/-- The (E3) guard's **full-execution delivery** at top: every run of the top entry is a *full*
execution (loop exit with `𝒟` drained — no event-overflow abort).  See `TopExactAt`. -/
def TopFull (t : ℕ) : Prop :=
  ∀ (out : CallOut G s),
    Run t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ out → DS.IsEmpty out.D

/-- Top-level exactness **at A4's judgments** (the intended `TopExact`): `BMSSP*(⊤, {s}, l_top)`
from `initLabels` returns labels complete for every vertex; `isSSSP_of_complete` +
`labelLen_dis` (A0 `Basic`) give `G.IsSSSP s (fun v => labelLen (out.d' v))`.  Takes the
engine's **totality judgment** (`Total`, the `∃ out, Run top out` step — the relational
semantics admits derivations but does not derive their existence) and the **full-execution
delivery** (`TopFull`, R2125608333) as explicit antecedents.  Proved from the joint chain's
identity clause at `B = ⊤` + Theorem T (`a4_joint`), Lemma 3.1* at base returns (A1), and the
weak label invariant `UnreachTop` (unreachable vertices stay `⊤`). -/
def TopExactAt (t : ℕ) : Prop :=
  ∀ (G : Graph) (s : Fin G.n),
    2 ≤ t →
    Total (G := G) (s := s) t →
    TopFull (G := G) (s := s) t →
    Reach t (G := G) (s := s) ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ →
      ∃ out : CallOut G s,
        Run t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ out ∧
          ∀ v, Complete out.d' v

theorem top_exact_at (t : ℕ) : TopExactAt t := by
  intro G s ht htot hfull hre
  obtain ⟨out, hrun⟩ := htot _ hre
  refine ⟨out, hrun, ?_⟩
  have hempty : DS.IsEmpty out.D := hfull out hrun
  have hun : UnreachTop out.d' := run_unreach t hrun initLabels_unreach
  obtain ⟨hB', hid, hsettle⟩ := top_full_facts t ht hre hrun hempty
  intro v
  by_cases hv : G.Reachable s v
  · have hmem : v ∈ out.U := by
      rw [hid]
      exact hv
    obtain ⟨ev, hev, heq⟩ := hmem
    rw [← heq]
    exact hsettle ev hev
  · rw [complete_iff, dis_of_not_reachable hv]
    exact hun v hv

/-- **Output bridge**: top-level exactness yields `IsSSSP` (A0 `Basic.isSSSP_of_complete`). -/
theorem isSSSP_of_top (t : ℕ) (G : Graph) (s : Fin G.n)
    (ht : 2 ≤ t)
    (htot : Total (G := G) (s := s) t)
    (hfull : TopFull (G := G) (s := s) t)
    (hre : Reach t (G := G) (s := s) ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩) :
    ∃ out : CallOut G s, Run t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ out ∧
      G.IsSSSP s (fun v => labelLen (out.d' v)) := by
  obtain ⟨out, hr, hall⟩ := top_exact_at t G s ht htot hfull hre
  exact ⟨out, hr, isSSSP_of_complete hall⟩

/-! ## Corrected Lemma 3.8* (size) — proofs

Statements weakened to the true/provable forms pinned in `A4.Size` (2026-11-04): (a) the true
inductive event ceiling, (b) the keyed-dedup bound, (c) the exact multiset decomposition with
the `W'` tail disjoint from the call's log, and Lemma R at the (E3) certificate. -/

/-- The (E3) event ceiling is monotone in the level. -/
theorem eventCap_mono {t a b : ℕ} (h : a ≤ b) : eventCap t a ≤ eventCap t b := by
  unfold eventCap
  refine Nat.mul_le_mul_left _ ?_
  exact pow_le_pow_right' (by norm_num) (Nat.mul_le_mul_right t h)

/-- The tail's `W'` boundary appends are at most one event per vertex. -/
theorem wPrimeEvts_length (Wp : Finset (Fin G.n)) : (wPrimeEvts Wp).length = Wp.card := by
  unfold wPrimeEvts
  rw [List.length_map, Finset.length_toList]

theorem finset_card_le_n (Wp : Finset (Fin G.n)) : Wp.card ≤ G.n := by
  have h := Finset.card_le_univ Wp
  rwa [Fintype.card_fin] at h

/-- One Algorithm-3 iteration appends the child's return log (BM.24). -/
theorem istep_evts_eq {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    st'.evts = st.evts ++ fo'.evts := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  subst hst'
  rfl

/-- One iteration's child call runs one level down (BM.13). -/
theorem istep_children_level {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') : c.l = l - 1 := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  rw [hc]

/-- Every child of a loop iteration runs one level down (BM.13). -/
theorem iloop_children_level (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      ∀ q ∈ qs, q.1.l = l - 1 := by
  intro p st stf qs h
  induction h with
  | exit h => intro q hq; exact absurd hq List.not_mem_nil
  | step hne hg hstep hrest ih =>
    intro q' hq'
    rcases List.mem_cons.mp hq' with hq | hq
    · subst hq
      exact istep_children_level hstep
    · exact ih q' hq

/-- **Lemma 3.5's conclusion — the child's `Lemma37Hyp` size clause** (`A4.Structural`'s
mechanical half + the level drop + the arithmetic): every child of a level-`l` call has
`|S_child| ≤ memCap t (l−1)` under `t ≥ 2`, so the joint induction applies its induction
hypothesis to children (`Lemma37Hyp t c` with `c.l = l − 1`). -/
theorem childOf_seed_memCap {t : ℕ} {e c : CallEntry G s} (ht : 2 ≤ t) (hcd : ChildOf t e c) :
    c.S.card ≤ memCap t c.l := by
  have hsize := childOf_seed_size hcd
  obtain ⟨out, p, fo, piv, st0, stf, qs, _hrun, _hout, _hl, _hfp, _hpiv, _hst0, hloop,
    _hchildren, q, hq, hqc⟩ := hcd
  have hlev : c.l = e.l - 1 := by
    rw [← hqc]
    exact iloop_children_level t _ _ hloop q hq
  rw [hlev]
  exact hsize.trans (pullCap_add_fpCap_le_memCap ht)

/-- The loop's accumulated log is the (E3) ceiling plus one child's share (the guard holds at
every iteration's entry state; one child log is appended per iteration). -/
theorem iloop_evts_len (t : ℕ) (B : WLab G s) (l : ℕ) (K : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      (∀ q ∈ qs, q.2.evts.length ≤ K) → st.evts.length ≤ eventCap t l + K →
        stf.evts.length ≤ eventCap t l + K := by
  intro p st stf qs h
  induction h with
  | exit h => exact fun _ hst => hst
  | step hne hg hstep hrest ih =>
    intro hkids hst
    refine ih (fun q hq => hkids q (List.mem_cons_of_mem _ hq)) ?_
    rw [istep_evts_eq hstep, List.length_append]
    have hq := hkids _ List.mem_cons_self
    omega

/-- One Algorithm-4 iteration appends exactly one settlement event. -/
theorem iter_evts_eq {B : WLab G s} (u : Fin G.n) (x : WLab G s) (st : BState G s) :
    (iter B u x st).evts = st.evts ++ [⟨.basePull, u⟩] := rfl

/-- A1's loop log never exceeds the base-case (E3) guard `t³` plus the final append. -/
theorem a1_loop_evts_len (t : ℕ) (B : WLab G s) :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' →
      st.evts.length ≤ t ^ 3 + 1 → st'.evts.length ≤ t ^ 3 + 1 := by
  intro c st st' h
  induction h with
  | exit h => exact fun hst => hst
  | pull u lam x hne hg hu hxgt hxle hxrest hxeq hrest ih =>
    intro hst
    refine ih ?_
    rw [iter_evts_eq, List.length_append, List.length_cons, List.length_nil]
    omega

/-- The base case of the event ceiling (V5-capped Algorithm 4). -/
theorem base_evts_bound (t : ℕ) {e : CallEntry G s} {bout : BaseOut G s}
    (hl : e.l = 0) (hb : baseRun t ⟨e.B, e.S, e.d, initD e.S e.d⟩ bout) :
    (baseOut bout).evts.length ≤ (e.l + 1) * (eventCap t e.l + G.n) + 1 := by
  obtain ⟨c, st, hloop, hr⟩ := hb
  subst hr
  have hst : st.evts.length ≤ t ^ 3 + 1 :=
    a1_loop_evts_len t e.B (c := c) (st := ⟨e.d, initD e.S e.d, [], e.B⟩) (st' := st) hloop
      (show ([] : List (SettlementEvent G)).length ≤ t ^ 3 + 1 from Nat.zero_le _)
  change st.evts.length ≤ (e.l + 1) * (eventCap t e.l + G.n) + 1
  rw [hl]
  have h0 : eventCap t 0 = t ^ 3 := by
    unfold eventCap
    rw [Nat.zero_mul, Nat.pow_zero, Nat.mul_one]
  rw [h0]
  simp only [Nat.zero_add, Nat.one_mul]
  omega

/-- The recur case of the event ceiling: the loop's log is the guard plus one child share, the
tail adds at most `G.n` `W'` appends. -/
theorem recur_evts_bound (t : ℕ) {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hl : 0 < e.l) (hst0 : st0 = mkInit e fo piv) (hloop : ILoop t e.B e.l st0 qs stf)
    (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    (ih : ∀ q ∈ qs, q.2.evts.length ≤ (q.1.l + 1) * (eventCap t q.1.l + G.n) + 1) :
    (callOut (tail e.B e.S fo.W stf)).evts.length ≤ (e.l + 1) * (eventCap t e.l + G.n) + 1 := by
  set Wp := wPrime (tailBP e.B stf) fo.W stf.evts
      (seedIns (tailBP e.B stf) e.B e.S stf.d stf.D).1 with hWp
  set K := e.l * (eventCap t (e.l - 1) + G.n) + 1 with hK
  have hkids : ∀ q ∈ qs, q.2.evts.length ≤ K := by
    intro q hq
    have hlev := iloop_children_level t e.B e.l hloop q hq
    have hq' := ih q hq
    rw [hlev] at hq'
    have h1 : e.l - 1 + 1 = e.l := by omega
    rw [h1] at hq'
    exact hq'
  have hstf : stf.evts.length ≤ eventCap t e.l + K := by
    refine iloop_evts_len t e.B e.l K hloop hkids ?_
    rw [hst0, mkInit_evts]
    simp
  have hwp : (wPrimeEvts Wp).length ≤ G.n := by
    rw [wPrimeEvts_length]
    exact finset_card_le_n Wp
  have hevts : (callOut (tail e.B e.S fo.W stf)).evts = stf.evts ++ wPrimeEvts Wp := by
    rw [hWp]; rfl
  rw [hevts, List.length_append]
  have hm : eventCap t (e.l - 1) ≤ eventCap t e.l := eventCap_mono (Nat.sub_le e.l 1)
  have h1' : e.l * eventCap t (e.l - 1) ≤ e.l * eventCap t e.l := Nat.mul_le_mul_left _ hm
  nlinarith [hstf, hwp, h1']

/-- The log of a return is at most one (E3) ceiling per recursion level plus one `W'` tail per
level (the proof spine of weakened Lemma 3.8\*(a)). -/
theorem run_evts_le (t : ℕ) : ∀ {e : CallEntry G s} {out : CallOut G s},
    Run t e out → out.evts.length ≤ (e.l + 1) * (eventCap t e.l + G.n) + 1 := by
  intro e out h
  induction h with
  | base hl hb => exact base_evts_bound t hl hb
  | recur hl hfp hpiv hst0 hloop hchildren ih =>
    exact recur_evts_bound t hl hst0 hloop hchildren ih

/-- (c) at base returns: the log is the base loop's, with no `W'` tail. -/
theorem decomp_base (bout : BaseOut G s) :
    ∃ acc wp, (baseOut bout).evts = acc ++ wp ∧ (wp.map (·.v)).Nodup ∧
      (∀ ev ∈ wp, ev.kind = .boundaryAppend) ∧
      ∀ x, x ∈ settledSet wp → x ∉ settledSet acc :=
  ⟨(baseOut bout).evts, [], by rw [List.append_nil], by simp,
    fun ev hev => absurd hev List.not_mem_nil, fun x hx => by simp [settledSet] at hx⟩

/-- (c) at recur returns: the log is the accumulated child log plus the tail's `W'` appends,
which are pairwise distinct and disjoint from the accumulated log (the call-local filter). -/
theorem decomp_recur {e : CallEntry G s} {fo : FPOut G s} {stf : RState G s fo.p} :
    ∃ acc wp, (callOut (tail e.B e.S fo.W stf)).evts = acc ++ wp ∧ (wp.map (·.v)).Nodup ∧
      (∀ ev ∈ wp, ev.kind = .boundaryAppend) ∧
      ∀ x, x ∈ settledSet wp → x ∉ settledSet acc := by
  set Wp := wPrime (tailBP e.B stf) fo.W stf.evts
      (seedIns (tailBP e.B stf) e.B e.S stf.d stf.D).1 with hWp
  refine ⟨stf.evts, wPrimeEvts Wp, ?_, ?_, ?_, ?_⟩
  · rw [hWp]; rfl
  · have hmap : (wPrimeEvts Wp).map (·.v) = Wp.toList := by
      unfold wPrimeEvts
      rw [List.map_map]
      show Wp.toList.map (fun x => x) = Wp.toList
      exact List.map_id _
    rw [hmap]
    exact Finset.nodup_toList Wp
  · intro ev hev
    simp only [wPrimeEvts, List.mem_map] at hev
    obtain ⟨x, hx, rfl⟩ := hev
    rfl
  · intro x hx
    classical
    have hx' : x ∈ Wp := by
      rw [hWp]
      exact Finset.mem_coe.mp (by rw [← settledSet_wPrimeEvts Wp]; exact hx)
    exact (Finset.mem_filter.mp hx').2.1

theorem lemma38Star (t : ℕ) (G : Graph) (s : Fin G.n) : @Lemma38Star G s t := by
  refine ⟨?_, ?_, ?_⟩
  · -- (a) event ceiling
    intro e out hr
    exact run_evts_le t hr
  · -- (b) keys are deduped vertices
    intro e out _hr
    refine (Finset.card_filter_le _ _).trans ?_
    rw [Finset.card_univ, Fintype.card_fin]
  · -- (c) exact decomposition; the W' tail is nodup and disjoint from the call's log
    intro e out hr
    induction hr with
    | base hl hb => exact decomp_base _
    | recur hl hfp hpiv hst0 hloop hchildren ih => exact decomp_recur

theorem lemmaR (t : ℕ) (G : Graph) (s : Fin G.n) : @LemmaR G s t := by
  intro e out hr
  exact (Nat.sub_le _ _).trans (run_evts_le t hr)

end DMSY
end Frontier

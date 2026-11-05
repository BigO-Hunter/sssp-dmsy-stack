import A4.Structural

/-!
# Frontier.DMSY.ReachInv — the corrected induction interface for `theoremT`

`A4.ReachHyp` settled that `Reach t e` does **not** imply `Lemma37Hyp t e` (base entries,
the `t = 0/1` size boundary, and the per-entry frontier are all missing).  This file is the
*counterpart*: it splits `theoremT` at the base case and introduces the smallest strengthened
reachable invariant that *does* carry exactly what `a4_joint`'s `Lemma37Hyp t e` premise needs,
with its top/child closure proved as far as the existing `IStep`/`ILoop` lemmas permit.

The one thing that is still **not** derivable from the loop structure — the child frontier,
which `A4.Structural.istep_child_frontier` produces only from the parent loop-state frontier plus
the coverage and (J6) witnesses — is isolated as the structure `StepFrontier` below, rather than
assumed.  Everything else (level, `memCap`, top closure) is a boundary that is now explicit.

Self-contained (imports only `A4.Structural`), so it compiles with a single
`lake env lean A4/ReachInv.lean`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Theorem T, split at the base case

The `l = 0` entries are discharged by the fact that base returns have `mints = []` (the `base`
branch below); the `0 < e.l` case is the genuine recursive obligation `hrecur`.  The boundaries
are explicit on the recur side: it is only dischargeable under `2 ≤ t` (child `memCap`,
`pullCap_add_fpCap_le_memCap`) and needs the per-entry frontier (the `ReachInv` invariant below)
— `t ∈ {0,1}` fails the size clause (`A4.ReachHyp.reach_zero_not_implies_lemma37Hyp`,
`A4.ReachHyp.pullCap_add_fpCap_gt_memCap_at_one`). -/

/-- **Theorem T, base/recur split.**  Given a handler for the recursive (`0 < e.l`) case,
`TheoremT` follows; the base case is the vacuous `baseOut.mints = []`. -/
theorem theoremT_split (t : ℕ)
    (hrecur : ∀ ⦃e : CallEntry G s⦄ ⦃out : CallOut G s⦄,
       Reach t e → 0 < e.l → Run t e out → ∀ x val, ¬ out.Premature x val) :
    @TheoremT G s (@Reach G s t) (@Run G s t) := by
  intro e out hre hrun
  cases hrun with
  | base hl hb =>
      intro x val hp
      exact absurd hp.1 List.not_mem_nil
  | recur hl hfp hpiv hst0 hloop hchildren =>
      rename_i pp fo piv st0 stf qs
      intro x val hp
      exact hrecur hre hl (@Run.recur G s t e pp fo piv st0 stf qs hl hfp hpiv hst0 hloop hchildren) x val hp

/-! ## The strengthened reachable invariant -/

/-- The smallest strengthened reachable invariant: `Reach` plus the level, frontier and `memCap`
clauses of `Lemma37Hyp`.  `reachInv_lemma37Hyp` is the bridge to `a4_joint`'s `Lemma37Hyp t e`
premise; the frontier is the one field not already carried by `Reach`. -/
structure ReachInv (t : ℕ) (e : CallEntry G s) : Prop where
  reach : Reach t e
  pos : 0 < e.l
  frontier : IsFrontier e.d (Utilde e.B (e.S : Set (Fin G.n))) ∅ (e.S : Set (Fin G.n))
  memcap : e.S.card ≤ memCap t e.l

/-- `ReachInv` is exactly `Lemma37Hyp` (the level, frontier and size clauses). -/
theorem reachInv_lemma37Hyp {t : ℕ} {e : CallEntry G s} (h : ReachInv t e) : Lemma37Hyp t e :=
  ⟨h.pos, h.frontier, h.memcap⟩

theorem reachInv_dis_source : dis (s := s) s = ((toW ([] : List (Fin G.m)) : WalkOrd G s) : WLab G s) := by
  rw [dis_of_reachable (⟨[], IsWalk.nil s⟩ : G.Reachable s s), path_source]

theorem reachInv_initLabels_source : initLabels G s s = dis (s := s) s := by
  rw [reachInv_dis_source]
  simp [initLabels]

theorem reachInv_one_le_memCap {t l : ℕ} (ht : 0 < t) : 1 ≤ memCap t l := by
  unfold memCap
  have h2 : 0 < t ^ 2 := pow_pos ht 2
  have h3 : 0 < 2 ^ (l * t) := pow_pos (by norm_num) (l * t)
  have h4 : 0 < t ^ 2 * 2 ^ (l * t) := mul_pos h2 h3
  omega

/-- **Top closure** (explicit `2 ≤ t` and `0 < lTop`): the reachable top entry carries the
invariant; the frontier is `isFrontier_init` and the size clause `reachInv_one_le_memCap`. -/
theorem reachInv_top (t : ℕ) (ht : 2 ≤ t) (hl : 0 < lTop t G.n) :
    ReachInv t ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num) ht
  refine ⟨Reach.top, hl, ?_, ?_⟩
  · rw [Finset.coe_singleton]
    exact isFrontier_init reachInv_initLabels_source
  · rw [Finset.card_singleton]
    exact reachInv_one_le_memCap ht0

/-! ## Level drop (child `c.l = e.l - 1`) — the recursion spine -/

theorem reachInv_istep_children_level {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') : c.l = l - 1 := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel, hst'⟩ := h
  rw [hc]

theorem reachInv_iloop_children_level (t : ℕ) (B : WLab G s) (l : ℕ) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      ∀ q ∈ qs, q.1.l = l - 1 := by
  intro p st stf qs h
  induction h with
  | exit h => intro q hq; exact absurd hq List.not_mem_nil
  | step hne hg hstep hrest ih =>
    intro q' hq'
    rcases List.mem_cons.mp hq' with hq | hq
    · subst hq
      exact reachInv_istep_children_level hstep
    · exact ih q' hq

/-- **Child closure** (explicit `2 ≤ t` and `0 < c.l`): the reachable child carries `Reach`
(`Reach.sub`), the level, the supplied frontier, and the `memCap` clause via `childOf_seed_size`
+ `pullCap_add_fpCap_le_memCap`.  The frontier is the isolated input — see `StepFrontier`. -/
theorem reachInv_child (t : ℕ) {e c : CallEntry G s} (he : ReachInv t e) (hcd : ChildOf t e c)
    (ht : 2 ≤ t) (hl : 0 < c.l)
    (hfrontier : IsFrontier c.d (Utilde c.B (c.S : Set (Fin G.n))) ∅ (c.S : Set (Fin G.n))) :
    ReachInv t c := by
  refine ⟨Reach.sub he.reach hcd, hl, hfrontier, ?_⟩
  have hsize := childOf_seed_size hcd
  obtain ⟨out, p, fo, piv, st0, stf, qs, _hrun, _hout, _hl, _hfp, _hpiv, _hst0, hloop,
    _hchildren, q, hq, hqc⟩ := hcd
  have hlev : c.l = e.l - 1 := by
    rw [← hqc]
    exact reachInv_iloop_children_level t e.B e.l hloop q hq
  rw [hlev]
  exact hsize.trans (pullCap_add_fpCap_le_memCap ht)

/-! ## The isolated remaining operational invariant

`istep_child_frontier` derives the child frontier from three loop-state witnesses: the parent
frontier `⟨X, Y⟩`, boundary coverage, and the (J6) membership `c.S ⊆ Ũ(B, S)`.  These are the
joint chain's clause-(1) loop invariant — the one fact not carried by `Reach`/`ChildOf` and so
not derivable here.  They are packaged as one structure so `reachInv_child`'s `hfrontier` input
has a precise shape. -/

/-- The coverage / (J6) / parent-frontier witnesses that hand the child its frontier at one
`IStep`.  This is the operational invariant left to the joint chain. -/
structure StepFrontier (B : WLab G s) {p : ℕ} (st : RState G s p) (c : CallEntry G s) where
  S : Finset (Fin G.n)
  X : Set (Fin G.n)
  Y : Set (Fin G.n)
  frontier : IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y
  cover : ∀ y ∈ Y, st.d y < c.B → y ∈ c.S
  j6 : (c.S : Set (Fin G.n)) ⊆ Utilde B (S : Set (Fin G.n))

/-- A `StepFrontier` supplies the child's frontier clause (via `istep_child_frontier`). -/
theorem child_frontier_of_step {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (w : StepFrontier B st c) :
    IsFrontier c.d (Utilde c.B (c.S : Set (Fin G.n))) ∅ (c.S : Set (Fin G.n)) :=
  istep_child_frontier t B l h w.frontier w.cover w.j6

end DMSY
end Frontier

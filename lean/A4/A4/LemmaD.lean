import A4.Structural

/-!
# Frontier.DMSY.LemmaD — the W′ sweep drop lemma on the exhaustive-search engine

The audit's Lemma D (PROOF.md §7) says that a complete W′ settler was popped at its final label
by a failed FindPivots search, so every out-edge was relaxed at that pop at the call's full bound.
A2's contract-satisfying engine has only exhaustive searches: there are no capped/merged outcomes.
Consequently the proxy-custody and four-site improvement case split is empty here.  The stronger
statement below extracts the actual valid pop from `FLoop` and identifies its label with the
call's filter-time label.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- A minimum valid pop of an `FInv` state is complete (Dijkstra's selection rule). -/
theorem fInv_pop_complete {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    {st : FPSt G s} (h : FInv B S d0 st) (u : Fin G.n) (lam : WLab G s)
    (hu : st.D u = some lam) (hmin : ∀ y μ, st.D y = some μ → lam ≤ μ) :
    Complete st.d u := by
  have huK : u ∈ DS.keys st.D := by
    show st.D u ≠ none
    rw [hu]
    simp
  refine IsFrontier.complete_of_min (hF := h.frontier) (hY := h.keys_sub)
    (hsound := WalkInv.sound h.walk) huK ?_
  intro y hy
  obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.mp hy
  have hle := hmin y μ hμ
  rw [← h.fresh u lam hu, ← h.fresh y μ hμ]
  exact hle

/-- A valid pop of `z` inside one exhaustive-search derivation, with the pop label and the
search-end label equal.  The `head` constructor's suffix starts with `fpIter B z st`, which is
precisely the full-`B` sweep of every out-edge of `z` from that final label. -/
inductive FinalPop (B : WLab G s) (d0 : Labels G s) (z : Fin G.n) :
    FPSt G s → FPSt G s → Prop
  | head {st st' : FPSt G s} {lam : WLab G s} {c : ℕ}
      (hu : st.D z = some lam)
      (hmin : ∀ y μ, st.D y = some μ → lam ≤ μ)
      (hrest : FLoop B d0 c (fpIter B z st) st')
      (hlam : lam = st'.d z)
      (hlabel : st.d z = st'.d z) :
      FinalPop B d0 z st st'
  | tail {st st' : FPSt G s} {u : Fin G.n} {lam : WLab G s} {c : ℕ}
      (hne : ¬ DS.IsEmpty st.D)
      (hu : st.D u = some lam)
      (hmin : ∀ y μ, st.D y = some μ → lam ≤ μ)
      (hrest : FLoop B d0 c (fpIter B u st) st')
      (hpop : FinalPop B d0 z (fpIter B u st) st') :
      FinalPop B d0 z st st'

/-- Read a `FinalPop` as an explicit valid-pop record and its full-bound sweep suffix. -/
theorem FinalPop.witness {B : WLab G s} {d0 : Labels G s} {z : Fin G.n}
    {st st' : FPSt G s} (h : FinalPop B d0 z st st') :
    ∃ (pre : FPSt G s) (lam : WLab G s) (c : ℕ),
      pre.D z = some lam ∧
      (∀ y μ, pre.D y = some μ → lam ≤ μ) ∧
      FLoop B d0 c (fpIter B z pre) st' ∧
      lam = st'.d z ∧ pre.d z = st'.d z := by
  induction h with
  | head hu hmin hrest hlam hlabel => exact ⟨_, _, _, hu, hmin, hrest, hlam, hlabel⟩
  | tail hne hu hmin hrest hpop ih => exact ih

/-- Extract a valid final-label pop of `z` from an exhaustive search. -/
theorem fLoop_pop_final {B : WLab G s} {S : Finset (Fin G.n)} {d0 : Labels G s}
    {z : Fin G.n} :
    ∀ {c : ℕ} {st st' : FPSt G s}, FLoop B d0 c st st' → FInv B S d0 st →
      z ∉ st.done → z ∈ st'.done → FinalPop B d0 z st st' := by
  intro c st st' h
  induction h with
  | exit h =>
      intro _ hz0 hz
      exact absurd hz hz0
  | @pull c st st' u lam hne hu hmin hrest ih =>
      intro hinv hz0 hz
      by_cases hzu : z = u
      · subst u
        have hstep : FInv B S d0 (fpIter B z st) := fInv_step hinv z lam hu hmin
        have hfin : FInv B S d0 st' := loop_fInv hrest hstep
        have hpop : Complete st.d z := fInv_pop_complete hinv z lam hu hmin
        have hfinal : Complete st'.d z := hfin.doneComplete z hz
        have hlabel : st.d z = st'.d z := hpop.trans hfinal.symm
        exact FinalPop.head hu hmin hrest ((hinv.fresh z lam hu).trans hlabel) hlabel
      · have hz0' : z ∉ (fpIter B u st).done := by
          simp [fpIter, hzu, hz0]
        exact FinalPop.tail hne hu hmin hrest (ih (fInv_step hinv u lam hu hmin) hz0' hz)

/-- Every `W` member has a genuine valid final-label pop inside its FindPivots derivation. -/
theorem fpRun_final_pop {i : FPIn G s} {o : FPOut G s} (h : fpRun i o)
    {z : Fin G.n} (hz : z ∈ o.W) :
    ∃ (post : FPSt G s) (c0 : ℕ),
      FLoop i.B i.d c0 ⟨i.d, initD i.S i.d, ∅⟩ post ∧
      FinalPop i.B i.d z ⟨i.d, initD i.S i.d, ∅⟩ post ∧
      o.d' = post.d := by
  obtain ⟨hpre, Y, c, st, hYsub, hYne, hcap, hloop, hd', hW, hp, hP, hQ⟩ := h
  have hinv : FInv i.B i.S i.d st := loop_fInv hloop (fInv_init hpre)
  have hzU : z ∈ Utilde i.B (i.S : Set (Fin G.n)) := by
    rw [hW] at hz
    exact wFin_subset hz
  have hkeys0 : (DS.keys st.D : Set (Fin G.n)) = (∅ : Set (Fin G.n)) := by
    ext y
    simp [DS.keys, loop_end_empty hloop y]
  have hfront : IsFrontier st.d (Utilde i.B (i.S : Set (Fin G.n)))
      (st.done : Set (Fin G.n)) (∅ : Set (Fin G.n)) := by
    rw [← hkeys0]
    exact hinv.frontier
  have hzdone : z ∈ st.done := (IsFrontier.complete_of_empty hfront z hzU).1
  have hpop : FinalPop i.B i.d z ⟨i.d, initD i.S i.d, ∅⟩ st :=
    fLoop_pop_final hloop (fInv_init hpre) (by simp) hzdone
  exact ⟨st, c, hloop, hpop, hd'⟩

/-- `seedIns` does not change labels. -/
theorem seedIns_labels_eq (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s)
    (D : DS G s) : (seedIns bp B S d D).1 = d := by
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

/-- Completeness of a `W` member persists from FindPivots through the call's loop, and therefore
its FindPivots output label is exactly its loop-exit/filter label. -/
theorem fp_label_eq_loop_exit {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hst0 : st0 = mkInit e fo piv) (hloop : ILoop t e.B e.l st0 qs stf)
    (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    {z : Fin G.n} (hz : z ∈ fo.W) :
    Complete stf.d z ∧ stf.d z = fo.d' z := by
  have hcomplete : Complete fo.d' z := (fpRun_pull_invariant hfp z hz).1
  have hle : stf.d z ≤ fo.d' z := by
    calc
      stf.d z ≤ st0.d z := iloop_le t e.B e.l hloop
        (fun q hq v => run_le t (hchildren q hq) v) z
      _ = fo.d' z := by subst st0; rfl
  have hwalk : WalkInv stf.d := iloop_walk t e.B e.l hloop
    (by rw [hst0]; exact (fpRun_contract _ _ hfp).1.walk)
    (fun q hq hd => run_walk t (hchildren q hq) hd)
  have hcomplete' : Complete stf.d z := hcomplete.of_le hwalk.sound hle
  exact ⟨hcomplete', hcomplete'.trans hcomplete.symm⟩

/-- **Lemma D (W′ sweep drop), exhaustive-search instance.**  If `z` passes a call's W′ filter,
then its call's FindPivots derivation contains a valid pop whose label is exactly the filter-time
label.  `FinalPop.witness` exposes the pop and its `fpIter e.B z pre` suffix: every out-edge of
`z` was relaxed at that pop at the call's full bound `e.B`, from that final label.  No
first-violation or Lemma-V hypothesis is needed on this engine. -/
theorem wPrime_sweep_drop {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n} {st0 stf : RState G s fo.p}
    {qs : List (CallEntry G s × CallOut G s)}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hst0 : st0 = mkInit e fo piv) (hloop : ILoop t e.B e.l st0 qs stf)
    (hchildren : ∀ q ∈ qs, Run t q.1 q.2)
    {z : Fin G.n}
    (hz : z ∈ wPrime (tailBP e.B stf) fo.W stf.evts
      (seedIns (tailBP e.B stf) e.B e.S stf.d stf.D).1) :
    ∃ (post : FPSt G s) (c0 : ℕ),
      FLoop e.B e.d c0 ⟨e.d, initD e.S e.d, ∅⟩ post ∧
      FinalPop e.B e.d z ⟨e.d, initD e.S e.d, ∅⟩ post ∧
      post.d z = (seedIns (tailBP e.B stf) e.B e.S stf.d stf.D).1 z := by
  classical
  have hzW : z ∈ fo.W := (Finset.mem_filter.mp hz).1
  obtain ⟨post, c0, hsearch, hpop, hd'⟩ := fpRun_final_pop hfp hzW
  have hstable := (fp_label_eq_loop_exit hfp hst0 hloop hchildren hzW).2
  refine ⟨post, c0, hsearch, hpop, ?_⟩
  rw [seedIns_labels_eq]
  exact (congrFun hd' z).symm.trans hstable.symm

end DMSY
end Frontier

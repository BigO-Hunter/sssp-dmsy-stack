import A4.Structural

/-!
# Frontier.DMSY.Rep — custody, anchor chains, and bound domination

Work package A4, the local machinery of the audit's Lemma Rep (PROOF.md §6).

`HasRepr d D v` is the value-carrying form of representation: some key of `D` has a stored
value at most `d v`.  `AnchorChain` records the group/tree links by which that value reaches an
S-member.  The main initialization theorem, `findPivots_anchor`, builds the chain directly from
FP1: a non-W S-member has a complete gate on its canonical path, and the group's current-label
argmin sits below that gate.  `reselection_anchor` is the matching line-29 re-arm.

The strict path comparison used by bound domination is proved in `bound_domination` and
`canonical_candidate_lt_bound`.  These are full-walk-label comparisons, hence include the
paper's full-tuple comparisons rather than merely length comparisons.

The per-call/active-subtree induction is deliberately not hidden in a hypothesis called
"first violation".  `A4.ExecutionFrame` exposes the active child and its live structures;
`Run` itself continues to expose completed child records.  The theorems here are the concrete
initialization, re-arm, expansion, and strict-bound steps that induction consumes.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- Some live entry represents `v` at value at most its current label.  The entry key need not
be `v`: pivot/proxy custody is the point of the definition. -/
def HasRepr (d : Labels G s) (D : DS G s) (v : Fin G.n) : Prop :=
  ∃ x val, D x = some val ∧ val ≤ d v

/-- Representation with the alternative that `v` has already settled. -/
def RepOrSettled (d : Labels G s) (D : DS G s) (evts : List (SettlementEvent G))
    (v : Fin G.n) : Prop :=
  HasRepr d D v ∨ v ∈ settledSet evts

/-- Keep-min insertion cannot destroy an existing representation. -/
theorem hasRepr_insert (d : Labels G s) (D : DS G s) (z : Fin G.n) (cand : WLab G s)
    {v : Fin G.n} (h : HasRepr d D v) : HasRepr d (DS.insert D z cand) v := by
  obtain ⟨x, val, hx, hle⟩ := h
  by_cases hxz : x = z
  · subst x
    exact ⟨z, min val cand, by rw [DS.insert_self, hx, DS.mergeVal_some],
      (min_le_left _ _).trans hle⟩
  · exact ⟨x, val, by rw [DS.insert_of_ne D z cand hxz]; exact hx, hle⟩

/-- Inserting a key at its current label represents that key, including over an older entry. -/
theorem hasRepr_insert_current (d : Labels G s) (D : DS G s) (x : Fin G.n) :
    HasRepr d (DS.insert D x (d x)) x := by
  cases hD : D x with
  | none =>
      exact ⟨x, d x, by rw [DS.insert_self, hD, DS.mergeVal_none_left], le_rfl⟩
  | some μ =>
      exact ⟨x, min μ (d x), by rw [DS.insert_self, hD, DS.mergeVal_some], min_le_right _ _⟩

/-- A fold of current-label insertions preserves every representation. -/
theorem hasRepr_fold_preserve {ι : Type} (js : List ι) (f : ι → Fin G.n) (d : Labels G s)
    {D0 : DS G s} {v : Fin G.n} (h : HasRepr d D0 v) :
    HasRepr d (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D0) v := by
  induction js generalizing D0 with
  | nil => exact h
  | cons j js ih =>
      rw [List.foldl_cons]
      exact ih (hasRepr_insert d D0 (f j) (d (f j)) h)

/-- Every key inserted by a current-label fold is represented after the fold. -/
theorem fold_insert_hasRepr {ι : Type} (js : List ι) (f : ι → Fin G.n) (d : Labels G s)
    (D0 : DS G s) {j : ι} (hj : j ∈ js) :
    HasRepr d (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D0) (f j) := by
  induction js generalizing D0 with
  | nil => nomatch hj
  | cons j0 js ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hj with rfl | hj
      · exact hasRepr_fold_preserve js f d (hasRepr_insert_current d D0 (f j))
      · exact ih (DS.insert D0 (f j0) (d (f j0))) hj

/-- BM.7's ungated initial insert represents each group's pivot. -/
theorem initD'_hasRepr {p : ℕ} (d : Labels G s) (piv : Fin p → Fin G.n) (j : Fin p) :
    HasRepr d (initD' d piv) (piv j) := by
  unfold initD'
  exact fold_insert_hasRepr (List.finRange p) piv d DS.empty (by simp)

/-- One value-carrying anchor link.  A group link points from a member to its group's argmin;
a tree/pocket link points from a walked vertex to the root that walked it.  `OnPath` is the
canonical-path evidence available in A2; the bound conjunct is the search-monotonicity fact
needed by custody. -/
inductive AnchorLink (d : Labels G s) {p : ℕ} (P : Fin p → Finset (Fin G.n))
    (piv : Fin p → Fin G.n) : Fin G.n → Fin G.n → Prop
  | group {a : Fin G.n} (j : Fin p) (ha : a ∈ P j) (hle : d (piv j) ≤ d a) :
      AnchorLink d P piv a (piv j)
  | tree {a root : Fin G.n} (hwalk : OnPath (s := s) root a) (hle : d root ≤ d a) :
      AnchorLink d P piv a root

/-- An anchor chain ending in live custody.  Every vertex on the chain is bounded by `τ`, and
its final stored value is bounded by every earlier link. -/
inductive AnchorChain (d : Labels G s) {p : ℕ} (P : Fin p → Finset (Fin G.n))
    (piv : Fin p → Fin G.n) (D : DS G s) (τ : WLab G s) : Fin G.n → Prop
  | root {a : Fin G.n} (hrep : HasRepr d D a) (ha : d a ≤ τ) : AnchorChain d P piv D τ a
  | step {a b : Fin G.n} (hlink : AnchorLink d P piv a b) (ha : d a ≤ τ)
      (hchain : AnchorChain d P piv D τ b) : AnchorChain d P piv D τ a

/-- Walking an anchor chain to its live entry proves representation and the anchor bound. -/
theorem AnchorChain.rep {d : Labels G s} {p : ℕ} {P : Fin p → Finset (Fin G.n)}
    {piv : Fin p → Fin G.n} {D : DS G s} {τ : WLab G s} {a : Fin G.n}
    (h : AnchorChain d P piv D τ a) : HasRepr d D a ∧ d a ≤ τ := by
  induction h with
  | root hrep ha => exact ⟨hrep, ha⟩
  | @step a b hlink ha hchain ih =>
      obtain ⟨⟨x, val, hx, hval⟩, hb⟩ := ih
      have hba : d b ≤ d a := by
        cases hlink with
        | group j hj hle => exact hle
        | tree hwalk hle => exact hle
      exact ⟨⟨x, val, hx, hval.trans hba⟩, ha⟩

/-- The value form consumed by the first-violation argument. -/
theorem AnchorChain.value_le {d : Labels G s} {p : ℕ} {P : Fin p → Finset (Fin G.n)}
    {piv : Fin p → Fin G.n} {D : DS G s} {τ : WLab G s} {a : Fin G.n}
    (h : AnchorChain d P piv D τ a) : ∃ x val, D x = some val ∧ val ≤ τ := by
  obtain ⟨⟨x, val, hx, hval⟩, ha⟩ := h.rep
  exact ⟨x, val, hx, hval.trans ha⟩

/-- FP1 plants the initial anchor chain of every non-`W` S-member.  The tree link is the
frontier gate `y` on the canonical path to `v`; the group link takes `y` to its group's
current-label argmin.  This also covers Q-members gated behind a pivot, not just P-members. -/
theorem findPivots_anchor {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
    {v : Fin G.n} (hv : v ∈ e.S) (hw : v ∉ fo.W) :
    AnchorChain fo.d' fo.P piv (initD' fo.d' piv) (fo.d' v) v := by
  have hcontract := (fpRun_contract _ _ hfp).1
  have hvU : v ∈ Utilde e.B (e.S : Set (Fin G.n)) := mem_utilde_of_mem hfp.1 hv
  rcases hcontract.frontier v hvU with hdone | ⟨y, ⟨j, hyP⟩, hcy, hyv⟩
  · exact absurd hdone.1 hw
  · have hyvle : fo.d' y ≤ fo.d' v := by
      rw [hcy]
      exact hyv.dis_le.trans (hcontract.walk.sound v)
    have hpivle : fo.d' (piv j) ≤ fo.d' y := (hpiv j).2 y hyP
    refine AnchorChain.step (a := v) (b := y) (AnchorLink.tree hyv hyvle) le_rfl ?_
    refine AnchorChain.step (a := y) (b := piv j) (AnchorLink.group j hyP hpivle) hyvle ?_
    exact AnchorChain.root (initD'_hasRepr fo.d' piv j) (hpivle.trans hyvle)

/-- Initialization, in the audit's representation-or-boundary form. -/
theorem findPivots_rep_or_w {t : ℕ} {e : CallEntry G s} {fo : FPOut G s}
    {piv : Fin fo.p → Fin G.n}
    (hfp : fpRun ⟨e.B, e.S, fpCap t, e.d⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
    {v : Fin G.n} (hv : v ∈ e.S) :
    HasRepr fo.d' (initD' fo.d' piv) v ∨ v ∈ fo.W := by
  by_cases hw : v ∈ fo.W
  · exact Or.inr hw
  · exact Or.inl (findPivots_anchor hfp hpiv hv hw).rep.1

/-- Line-29 re-selection re-arms the anchor chain of every residual group member. -/
theorem reselection_anchor {p : ℕ} {resid : Fin p → Finset (Fin G.n)}
    {piv' : Fin p → Fin G.n} {J : Finset (Fin p)} {sel : Fin p → Fin G.n}
    {d3 : Labels G s} {D3 : DS G s} {j : Fin p} {a : Fin G.n}
    (hj : j ∈ J) (hpiv : piv' j = sel j)
    (hsel : ∀ y ∈ resid j, d3 (sel j) ≤ d3 y) (ha : a ∈ resid j) :
    AnchorChain d3 resid piv'
      (J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3) (d3 a) a := by
  have hle : d3 (piv' j) ≤ d3 a := by
    rw [hpiv]
    exact hsel a ha
  refine AnchorChain.step (a := a) (b := piv' j) (AnchorLink.group j ha hle) le_rfl ?_
  refine AnchorChain.root ?_ hle
  rw [hpiv]
  exact fold_insert_hasRepr J.toList sel d3 D3 (by simpa using hj)

/-- Representation survives the gated line-33 fold. -/
theorem hasRepr_seedIns_fold_preserve (bp B : WLab G s) (xs : List (Fin G.n)) (d : Labels G s)
    (D : DS G s) {v : Fin G.n} (h : HasRepr d D v) :
    HasRepr d (xs.foldl (fun (acc : Labels G s × DS G s) x =>
      if bp ≤ acc.1 x ∧ acc.1 x < B then (acc.1, DS.insert acc.2 x (acc.1 x)) else acc)
      (d, D)).2 v := by
  induction xs generalizing D with
  | nil => exact h
  | cons y ys ih =>
      rw [List.foldl_cons]
      by_cases hy : bp ≤ d y ∧ d y < B
      · rw [if_pos hy]
        exact ih (DS.insert D y (d y)) (hasRepr_insert d D y (d y) h)
      · rw [if_neg hy]
        exact ih D h

/-- A seed whose line-33 gate passes is represented by its own re-inserted entry. -/
theorem hasRepr_seedIns_fold (bp B : WLab G s) (xs : List (Fin G.n)) (d : Labels G s)
    (D : DS G s) {v : Fin G.n} (hv : v ∈ xs) (hg : bp ≤ d v ∧ d v < B) :
    HasRepr d (xs.foldl (fun (acc : Labels G s × DS G s) x =>
      if bp ≤ acc.1 x ∧ acc.1 x < B then (acc.1, DS.insert acc.2 x (acc.1 x)) else acc)
      (d, D)).2 v := by
  induction xs generalizing D with
  | nil => nomatch hv
  | cons y ys ih =>
      rw [List.foldl_cons]
      by_cases hyv : y = v
      · subst y
        rw [if_pos hg]
        exact hasRepr_seedIns_fold_preserve bp B ys d (DS.insert D v (d v))
          (hasRepr_insert_current d D v)
      · have hvys : v ∈ ys := by
          rcases List.mem_cons.mp hv with h | h
          · exact absurd h.symm hyv
          · exact h
        by_cases hy : bp ≤ d y ∧ d y < B
        · rw [if_pos hy]
          exact ih (DS.insert D y (d y)) hvys
        · rw [if_neg hy]
          exact ih D hvys

/-- BM.25 (line 33) represents every re-inserted seed. -/
theorem seedIns_hasRepr (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (D : DS G s)
    {v : Fin G.n} (hv : v ∈ S) (hg : bp ≤ d v ∧ d v < B) :
    HasRepr d (seedIns bp B S d D).2 v :=
  hasRepr_seedIns_fold bp B S.toList d D (Finset.mem_toList.mpr hv) hg

/-- The boundary hand-back: a seed in `W` is either re-entered by line 33 or is settled by the
boundary.  This is stated before the W′ sweep's label updates; maintaining the entry through
that sweep is the complementarity/drop-lemma arm of the joint induction. -/
theorem line33_handback (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    {v : Fin G.n} (hvS : v ∈ S) (hvW : v ∈ W) (hdB : st.d v < B) :
    HasRepr st.d (seedIns (tailBP B st) B S st.d st.D).2 v ∨
      v ∈ settledSet (tail B S W st).evts := by
  classical
  by_cases hset : v ∈ settledSet st.evts
  · right
    change v ∈ settledSet (st.evts ++ wPrimeEvts
      (wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1))
    rw [settledSet_append]
    exact Or.inl hset
  by_cases hlt : st.d v < tailBP B st
  · right
    have hlt' : (seedIns (tailBP B st) B S st.d st.D).1 v < tailBP B st :=
      (seedIns_le (tailBP B st) B S st.d st.D v).trans_lt hlt
    have hwp : v ∈ wPrime (tailBP B st) W st.evts
        (seedIns (tailBP B st) B S st.d st.D).1 :=
      Finset.mem_filter.mpr ⟨hvW, hset, hlt'⟩
    change v ∈ settledSet (st.evts ++ wPrimeEvts
      (wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1))
    rw [settledSet_append]
    right
    rw [settledSet_wPrimeEvts]
    exact hwp
  · exact Or.inl (seedIns_hasRepr (tailBP B st) B S st.d st.D hvS ⟨not_lt.mp hlt, hdB⟩)

/-- Strict bound domination along the canonical path.  Completeness of `z`, incompleteness of
`y`, and sound labels turn `z ≺ y` on the path into `d[z] < d[y]`; any event bound above
`d[y]` therefore strictly dominates `d[z]`. -/
theorem bound_domination {d : Labels G s} {z y : Fin G.n} {b : WLab G s}
    (hsound : Sound d) (hz : Complete d z) (hy : ¬ Complete d y)
    (hpath : OnPath (s := s) z y) (hb : d y < b) : d z < b := by
  have hne : z ≠ y := by
    intro h
    subst y
    exact hy hz
  have hdy : dis (s := s) y < d y := lt_of_le_of_ne (hsound y) (Ne.symm hy)
  rw [hz]
  exact (hpath.dis_lt hne).trans (hdy.trans hb)

/-- The canonical candidate out of the last complete vertex clears the same active gate. -/
theorem canonical_candidate_lt_bound {d : Labels G s} {x y z : Fin G.n} {e : Fin G.m}
    {b : WLab G s} (hsound : Sound d) (hy : ¬ Complete d y)
    (hpath : OnPath (s := s) x y) (hx : dis (s := s) x = ext (dis (s := s) z) e)
    (hb : d y < b) : ext (dis (s := s) z) e < b := by
  have hdy : dis (s := s) y < d y := lt_of_le_of_ne (hsound y) (Ne.symm hy)
  rw [← hx]
  exact lt_of_le_of_lt hpath.dis_le (hdy.trans hb)

/-- A represented anchor strictly below an active gate has its custody strictly below it too. -/
theorem custody_below_bound {d : Labels G s} {D : DS G s} {z : Fin G.n} {b : WLab G s}
    (hrep : HasRepr d D z) (hb : d z < b) : ∃ x val, D x = some val ∧ val < b := by
  obtain ⟨x, val, hx, hle⟩ := hrep
  exact ⟨x, val, hx, hle.trans_lt hb⟩

end DMSY
end Frontier

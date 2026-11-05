import A4.ExecutionFrame
import A4.Rep
import A4.WDrop

/-!
# Frontier.DMSY.FrontierOrder — the audit's frontier-order lemma (d2)

The W′ drop theorem in `A4.WDrop` consumes `BoundaryClosure`.  This file proves the
missing *reason* that closure holds in the first-violation regime: a complete vertex on the
canonical path either has live custody at or below its label, or the settlement echo completes
the next path vertex.  In the former case Lemma V's live floor contradicts the violating
filter bound; in the latter case the path position strictly increases.  Canonical paths are
finite, so the cascade reaches the proposed violator.

`SettledEcho` is case A of PROOF.md §8 (the deepest-common-ancestor echo and refusal floor).
`UnsettledCustody` is case B: Rep/W1/D1–D3 supplies live custody, and a pulled entry's
same-iteration relax sweep gives the same strict advance.  These are operational inputs,
not axioms; `d2Step_of_cases` packages exactly their two-way split.  The induction and the
resulting W′-filter exclusion are fully proved here.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- Strict progress from one complete canonical-path vertex to the next. -/
def FrontierAdvance (d : Labels G s) (y z x : Fin G.n) : Prop :=
  Complete d x ∧ OnPath (s := s) z x ∧ OnPath (s := s) x y ∧ z ≠ x

/-- The two endings of the audit's d2 case analysis at a complete frontier vertex `z`.
The left branch is the settlement echo (case A, or case B after a pull); the right branch is
live custody at value at most `d z` (case B before the pull/survival split). -/
def D2Step (d : Labels G s) (D : DS G s) (y : Fin G.n) : Prop :=
  ∀ z, Complete d z → OnPath (s := s) z y → z ≠ y →
    (∃ x, FrontierAdvance d y z x) ∨ HasRepr d D z

/-- The canonical echo offered when a complete `z` is settled or its custody is pulled.
`offered` is the adoption/refusal-floor conclusion: the target's current label is at most the
bit-identical canonical candidate.  Completeness of the target is proved, not assumed. -/
structure EchoOffer (d : Labels G s) (y z x : Fin G.n) (e : Fin G.m) : Prop where
  complete_source : Complete d z
  source_edge : G.src e = z
  target_edge : G.dst e = x
  zx : OnPath (s := s) z x
  xy : OnPath (s := s) x y
  ne : z ≠ x
  canonical : dis (s := s) x = ext (dis (s := s) z) e
  offered : d x ≤ ext (d z) e

/-- Adoption or the refusal floor turns an echo offer into strict frontier progress. -/
theorem EchoOffer.advance {d : Labels G s} {y z x : Fin G.n} {e : Fin G.m}
    (h : EchoOffer d y z x e) (hsound : Sound d) : FrontierAdvance d y z x := by
  refine ⟨?_, h.zx, h.xy, h.ne⟩
  apply le_antisymm _ (hsound x)
  calc
    d x ≤ ext (d z) e := h.offered
    _ = ext (dis (s := s) z) e := congrArg (fun lab => ext lab e) h.complete_source
    _ = dis (s := s) x := h.canonical.symm

/-- Case A: if `z` settled before the event, the deepest-common-ancestor relax sweep presents
this echo offer. -/
def SettledEcho (d : Labels G s) (y : Fin G.n) (settled : Fin G.n → Prop) : Prop :=
  ∀ z, Complete d z → OnPath (s := s) z y → z ≠ y → settled z →
    ∃ x e, EchoOffer d y z x e

/-- Case B: if `z` is unsettled at the event, Rep and the live-window argument either leave
custody in the event call's own structure, or a pull settles its head and the event call's
own relax sweep presents the echo offer. -/
def UnsettledCustody (d : Labels G s) (D : DS G s) (y : Fin G.n)
    (settled : Fin G.n → Prop) : Prop :=
  ∀ z, Complete d z → OnPath (s := s) z y → z ≠ y → ¬ settled z →
    HasRepr d D z ∨ ∃ x e, EchoOffer d y z x e

/-- Package the audit's settled/unsettled cases as the single step consumed by the induction. -/
theorem d2Step_of_cases {d : Labels G s} {D : DS G s} {y : Fin G.n}
    {settled : Fin G.n → Prop} (hsound : Sound d) (hA : SettledEcho d y settled)
    (hB : UnsettledCustody d D y settled) : D2Step d D y := by
  intro z hzc hzy hzne
  by_cases hz : settled z
  · obtain ⟨x, e, ho⟩ := hA z hzc hzy hzne hz
    exact Or.inl ⟨x, ho.advance hsound⟩
  · rcases hB z hzc hzy hzne hz with hrep | ⟨x, e, ho⟩
    · exact Or.inr hrep
    · exact Or.inl ⟨x, ho.advance hsound⟩

/-- Two walks from the same start along the same edge list have the same endpoint. -/
theorem isWalk_endpoint_eq {r u v : Fin G.n} {p : List (Fin G.m)}
    (hu : G.IsWalk r u p) (hv : G.IsWalk r v p) : u = v := by
  induction p generalizing r u v with
  | nil => exact (isWalk_nil_iff.mp hu).symm.trans (isWalk_nil_iff.mp hv)
  | cons e p ih =>
      exact ih (isWalk_cons_iff.mp hu).2 (isWalk_cons_iff.mp hv).2

/-- A strict canonical-path visit strictly increases the number of edges in the canonical
prefix.  This is the integer measure used by PROOF.md §8. -/
theorem path_length_lt_of_onPath {z x : Fin G.n} (h : OnPath (s := s) z x) (hne : z ≠ x) :
    (path (s := s) z).length < (path (s := s) x).length := by
  obtain ⟨R, hPR, hwalk⟩ := h.path_prefix
  have hR : R ≠ [] := by
    intro hnil
    subst R
    simp only [List.append_nil] at hPR
    apply hne
    have hx := (path_isMinWalk h.1).1
    rw [hPR] at hx
    exact isWalk_endpoint_eq (path_isMinWalk h.reachable_left).1 hx
  rw [hPR, List.length_append]
  have hpos : 0 < R.length := by
    cases R with
    | nil => exact (hR rfl).elim
    | cons => simp
  omega

/-- Canonical-prefix length is monotone along a path visit. -/
theorem path_length_le_of_onPath {z y : Fin G.n} (h : OnPath (s := s) z y) :
    (path (s := s) z).length ≤ (path (s := s) y).length := by
  obtain ⟨R, hPR, hwalk⟩ := h.path_prefix
  rw [hPR, List.length_append]
  omega

/-- Number of canonical-path positions still to be crossed from `z` to `y`. -/
noncomputable def pathRank (z y : Fin G.n) : ℕ :=
  (path (s := s) y).length - (path (s := s) z).length

/-- A frontier advance strictly decreases the remaining path measure. -/
theorem pathRank_lt_of_advance {d : Labels G s} {y z x : Fin G.n}
    (h : FrontierAdvance d y z x) : pathRank (s := s) x y < pathRank (s := s) z y := by
  have hlt := path_length_lt_of_onPath h.2.1 h.2.2.2
  have hle := path_length_le_of_onPath h.2.2.1
  unfold pathRank
  omega

/-- **The d2 cascade induction.**  Starting at any complete vertex on `y`'s canonical path,
repeated echo advances either complete `y`, or expose live custody strictly below `d y`.
The recursive call is justified by `pathRank_lt_of_advance`, not by an informal finiteness
claim. -/
theorem complete_or_lowCustody_of_d2Step {d : Labels G s} {D : DS G s} {y : Fin G.n}
    (hsound : Sound d) (hstep : D2Step d D y) {z : Fin G.n}
    (hzc : Complete d z) (hzy : OnPath (s := s) z y) :
    Complete d y ∨ ∃ a val, D a = some val ∧ val < d y := by
  suffices H : ∀ n, ∀ z, pathRank (s := s) z y = n → Complete d z →
      OnPath (s := s) z y → Complete d y ∨ ∃ a val, D a = some val ∧ val < d y by
    exact H (pathRank (s := s) z y) z rfl hzc hzy
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro z hr hzc hzy
      by_cases hy : Complete d y
      · exact Or.inl hy
      by_cases hze : z = y
      · subst z
        exact Or.inl hzc
      rcases hstep z hzc hzy hze with hadv | hrep
      · obtain ⟨x, hxc, hzx, hxy, hzxne⟩ := hadv
        have hrank : pathRank (s := s) x y < n := by
          rw [← hr]
          exact pathRank_lt_of_advance ⟨hxc, hzx, hxy, hzxne⟩
        exact ih (pathRank (s := s) x y) hrank x rfl hxc hxy
      · right
        obtain ⟨a, val, ha, hle⟩ := hrep
        refine ⟨a, val, ha, ?_⟩
        have hy' : dis (s := s) y < d y := lt_of_le_of_ne (hsound y) (Ne.symm hy)
        calc
          val ≤ d z := hle
          _ = dis (s := s) z := hzc
          _ < dis (s := s) y := hzy.dis_lt hze
          _ < d y := hy'

/-- **Lemma d2 (frontier order), value form.**  Lemma V's floor rules out the low-custody
ending, leaving only completion of the proposed violator. -/
theorem complete_of_d2Step {d : Labels G s} {D : DS G s} {y : Fin G.n} {bp : WLab G s}
    (hsound : Sound d) (hfloor : Ge bp D) (hstep : D2Step d D y)
    {z : Fin G.n} (hzc : Complete d z) (hzy : OnPath (s := s) z y)
    (hylt : d y < bp) : Complete d y := by
  rcases complete_or_lowCustody_of_d2Step hsound hstep hzc hzy with hy | ⟨a, val, ha, hval⟩
  · exact hy
  · exact ((not_lt_of_ge (hfloor a val ha)) (hval.trans hylt)).elim

/-- **Lemma d2 (frontier order), W′-filter form.**  No W-member with an incomplete label below
`B'` passes the filter in the first-violation regime. -/
theorem d2_no_incomplete_pass {d : Labels G s} {D : DS G s} {bp : WLab G s}
    {W : Finset (Fin G.n)} {evts : List (SettlementEvent G)} {y z : Fin G.n}
    (hsound : Sound d) (hfloor : Ge bp D) (hstep : D2Step d D y)
    (hzc : Complete d z) (hzy : OnPath (s := s) z y)
    (hylt : d y < bp) (hnc : ¬ Complete d y) : y ∉ wPrime bp W evts d := by
  intro hy
  exact hnc (complete_of_d2Step hsound hfloor hstep hzc hzy hylt)

/-- Case-split form of d2: the audit's case-A and case-B operational facts jointly exclude an
incomplete W′ pass. -/
theorem d2_no_incomplete_pass_of_cases {d : Labels G s} {D : DS G s} {bp : WLab G s}
    {W : Finset (Fin G.n)} {evts : List (SettlementEvent G)} {y z : Fin G.n}
    {settled : Fin G.n → Prop} (hsound : Sound d) (hfloor : Ge bp D)
    (hA : SettledEcho d y settled) (hB : UnsettledCustody d D y settled)
    (hzc : Complete d z) (hzy : OnPath (s := s) z y)
    (hylt : d y < bp) (hnc : ¬ Complete d y) : y ∉ wPrime bp W evts d :=
  d2_no_incomplete_pass hsound hfloor (d2Step_of_cases hsound hA hB) hzc hzy hylt hnc

end DMSY
end Frontier

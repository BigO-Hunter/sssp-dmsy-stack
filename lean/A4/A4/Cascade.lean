import A4.ExecutionFrame

/-!
# Frontier.DMSY.Cascade — the cascade arm (one-step complementarity)

A `Fire` is one improvement link re-fired at a settlement site.  The base constructor uses
Algorithm 4's ungated insert.  The recursive constructor starts with a refused improving candidate
at the child bound `B_c`; the parent sweep has lower insert gate `B_c`, so its first accepting level
also inserts.  This is the audit's one-step complementarity, not an extra provenance axiom.

`EntryLE D x val` is the keep-min-stable statement that `x` is structural at value at most `val`.
It survives later inserts and ungated merges (the stored value may decrease, never disappear).
`CascadeRun` chains fired links through their actual label/store states, and `cascade_arm` proves
that every link of a graph-contiguous ground chain leaves such an entry in the final store.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- A key is structural with stored value at most `val`.  Keep-min insertion and merging preserve
this predicate; an exact-value assertion would be too strong in the presence of an older entry. -/
def EntryLE (D : DS G s) (x : Fin G.n) (val : WLab G s) : Prop :=
  ∃ stored, D x = some stored ∧ stored ≤ val

/-- The candidate refused by a child's upper bound supplies exactly the parent's lower insert gate. -/
theorem refusal_insert_gate {Bc : WLab G s} {d : Labels G s} {e : Fin G.m}
    (hle : ext (d (G.src e)) e ≤ d (G.dst e))
    (href : ¬ (ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < Bc)) :
    Bc ≤ ext (d (G.src e)) e := by
  exact not_lt.mp fun hlt => href ⟨hle, hlt⟩

/-- **One-step complementarity.**  If an improving candidate is refused at `B_c` and accepted at the
parent bound `B_p`, then `relaxGate B_p B_c` both writes the label and performs the insert. -/
theorem oneStep_complementarity (Bc Bp : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (hle : ext (d (G.src e)) e ≤ d (G.dst e))
    (href : ¬ (ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < Bc))
    (hlt : ext (d (G.src e)) e < Bp) :
    relaxGate Bp Bc d D e =
      (Function.update d (G.dst e) (ext (d (G.src e)) e),
        DS.insert D (G.dst e) (ext (d (G.src e)) e)) := by
  unfold relaxGate
  rw [if_pos ⟨refusal_insert_gate hle href, hlt, hle⟩]

/-- The base settlement sweep accepts and inserts without any lower gate. -/
theorem relaxEdge_fire (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (hle : ext (d (G.src e)) e ≤ d (G.dst e)) (hlt : ext (d (G.src e)) e < B) :
    relaxEdge B d D e =
      (Function.update d (G.dst e) (ext (d (G.src e)) e),
        DS.insert D (G.dst e) (ext (d (G.src e)) e)) := by
  unfold relaxEdge
  rw [if_pos ⟨hle, hlt⟩]

/-- Inserting at a key makes that key structural at the inserted value. -/
theorem entryLE_insert_same (D : DS G s) (x : Fin G.n) (val : WLab G s) :
    EntryLE (DS.insert D x val) x val := by
  cases hD : D x with
  | none =>
      exact ⟨val, by rw [DS.insert_self, hD, DS.mergeVal_none_left], le_rfl⟩
  | some μ =>
      exact ⟨min μ val, by rw [DS.insert_self, hD, DS.mergeVal_some], min_le_right _ _⟩

/-- Keep-min insertion preserves every older structural entry. -/
theorem entryLE_insert {D : DS G s} {x : Fin G.n} {val : WLab G s}
    (z : Fin G.n) (cand : WLab G s) (h : EntryLE D x val) :
    EntryLE (DS.insert D z cand) x val := by
  obtain ⟨μ, hμ, hle⟩ := h
  by_cases hxz : x = z
  · subst x
    exact ⟨min μ cand, by rw [DS.insert_self, hμ, DS.mergeVal_some],
      (min_le_left _ _).trans hle⟩
  · exact ⟨μ, by rw [DS.insert_of_ne D z cand hxz]; exact hμ, hle⟩

/-- The left entry of an ungated keep-min merge survives. -/
theorem entryLE_merge_left (D₁ D₂ : DS G s) {x : Fin G.n} {val : WLab G s}
    (h : EntryLE D₁ x val) : EntryLE (DS.merge D₁ D₂) x val := by
  obtain ⟨μ, hμ, hle⟩ := h
  cases h₂ : D₂ x with
  | none =>
      exact ⟨μ, by rw [DS.merge_eq, hμ, h₂, DS.mergeVal_none_right], hle⟩
  | some ν =>
      exact ⟨min μ ν, by rw [DS.merge_eq, hμ, h₂, DS.mergeVal_some],
        (min_le_left _ _).trans hle⟩

/-- The right entry of an ungated keep-min merge survives. -/
theorem entryLE_merge_right (D₁ D₂ : DS G s) {x : Fin G.n} {val : WLab G s}
    (h : EntryLE D₂ x val) : EntryLE (DS.merge D₁ D₂) x val := by
  obtain ⟨μ, hμ, hle⟩ := h
  cases h₁ : D₁ x with
  | none =>
      exact ⟨μ, by rw [DS.merge_eq, h₁, hμ, DS.mergeVal_none_left], hle⟩
  | some ν =>
      exact ⟨min ν μ, by rw [DS.merge_eq, h₁, hμ, DS.mergeVal_some],
        (min_le_right _ _).trans hle⟩

/-- `DS.deleteSet` keeps a surviving key's entry: it rewrites no value, it only removes keys. -/
theorem entryLE_deleteSet {D : DS G s} {T : Finset (Fin G.n)} {x : Fin G.n} {val : WLab G s}
    (hx : x ∉ T) (h : EntryLE D x val) : EntryLE (DS.deleteSet D T) x val := by
  obtain ⟨μ, hμ, hle⟩ := h
  exact ⟨μ, by rw [DS.deleteSet_of_notMem D T x hx]; exact hμ, hle⟩

/-- A child-return entry rides the actual BM.14 merge into the suspended parent, and ★BM.15's
deletion leaves it alone whenever its own key was not settled by the child. -/
theorem entryLE_mergeAtReturn (f : ActiveChild G s) (out : CallOut G s)
    {x : Fin G.n} {val : WLab G s} (hx : x ∉ settledSet out.evts)
    (h : EntryLE out.D x val) :
    EntryLE (f.mergeAtReturn out) x val := by
  exact entryLE_deleteSet (mem_settledFinset.not.mpr hx) (entryLE_merge_right f.parentD out.D h)

/-- A gated relaxation still preserves every older structural entry. -/
theorem entryLE_relaxGate (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    {x : Fin G.n} {val : WLab G s} (h : EntryLE D x val) :
    EntryLE (relaxGate B lo d D e).2 x val := by
  unfold relaxGate
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos hc]
    exact entryLE_insert (G.dst e) (ext (d (G.src e)) e) h
  · rw [if_neg hc]
    exact h

theorem entryLE_sweepGate (B lo : WLab G s) (u : Fin G.n) (es : List (Fin G.m))
    (d : Labels G s) (D : DS G s) {x : Fin G.n} {val : WLab G s} (h : EntryLE D x val) :
    EntryLE (sweepGate B lo u es d D).2 x val := by
  induction es generalizing d D with
  | nil => exact h
  | cons e es ih =>
      unfold sweepGate
      by_cases hs : G.src e = u
      · rw [if_pos hs, if_pos hs]
        exact ih _ _ (entryLE_relaxGate B lo d D e h)
      · rw [if_neg hs, if_neg hs]
        exact ih d D h

theorem entryLE_sweepEvts (B lo : WLab G s) (evts : List (SettlementEvent G))
    (d : Labels G s) (D : DS G s) {x : Fin G.n} {val : WLab G s} (h : EntryLE D x val) :
    EntryLE (sweepEvts B lo evts d D).2 x val := by
  induction evts generalizing d D with
  | nil => exact h
  | cons ev evts ih =>
      unfold sweepEvts
      exact ih _ _ (entryLE_sweepGate B lo ev.v (List.finRange G.m) d D h)

/-- A current-label mint fold preserves structural entries. -/
theorem entryLE_fold_insert {ι : Type} (js : List ι) (f : ι → Fin G.n) (g : ι → WLab G s)
    (D : DS G s) {x : Fin G.n} {val : WLab G s} (h : EntryLE D x val) :
    EntryLE (js.foldl (fun D j => DS.insert D (f j) (g j)) D) x val := by
  induction js generalizing D with
  | nil => exact h
  | cons j js ih =>
      rw [List.foldl_cons]
      exact ih _ (entryLE_insert (f j) (g j) h)

/-- Full parent transport: a child entry survives BM.14's merge, ★BM.15's deletion (the entry's own
key is not a settled vertex — `hx` is exactly the `T_X` stale-key exclusion), the settlement
sweep, and the line-29 re-selection fold of an actual `IStep`. -/
theorem entryLE_istep_of_child {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (hstep : IStep t B l st st' c fo') {x : Fin G.n} {val : WLab G s}
    (hx : x ∉ settledSet fo'.evts)
    (h : EntryLE fo'.D x val) : EntryLE st'.D x val := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := hstep
  subst hst'
  apply entryLE_fold_insert
  have hs : EntryLE D3 x val := by
    have hD3 : D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 := congrArg Prod.snd hsweep
    rw [hD3]
    apply entryLE_sweepEvts
    rw [hmerge]
    exact entryLE_deleteSet (mem_settledFinset.not.mpr hx) (entryLE_merge_right D1 fo'.D h)
  exact hs

/-- One improvement link fired at a settlement site.  `base` is the ungated Algorithm-4 insert;
`complement` is the first parent level accepting a candidate refused at its child's bound. -/
inductive Fire (d : Labels G s) (D : DS G s) (e : Fin G.m) :
    Labels G s → DS G s → Prop
  | base {B : WLab G s}
      (hle : ext (d (G.src e)) e ≤ d (G.dst e)) (hlt : ext (d (G.src e)) e < B) :
      Fire d D e (relaxEdge B d D e).1 (relaxEdge B d D e).2
  | complement {Bc Bp : WLab G s}
      (hle : ext (d (G.src e)) e ≤ d (G.dst e))
      (href : ¬ (ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < Bc))
      (hlt : ext (d (G.src e)) e < Bp) :
      Fire d D e (relaxGate Bp Bc d D e).1 (relaxGate Bp Bc d D e).2

/-- Every fired link adopts its candidate at the target. -/
theorem Fire.head {d : Labels G s} {D : DS G s} {e : Fin G.m} {d₁ : Labels G s} {D₁ : DS G s}
    (h : Fire d D e d₁ D₁) : d₁ (G.dst e) = ext (d (G.src e)) e := by
  cases h with
  | base hle hlt =>
      rw [relaxEdge_fire _ _ _ _ hle hlt]
      simp
  | complement hle href hlt =>
      rw [oneStep_complementarity _ _ _ _ _ hle href hlt]
      simp

/-- Every fired link creates a structural target entry — the label proof alone is insufficient. -/
theorem Fire.entry {d : Labels G s} {D : DS G s} {e : Fin G.m} {d₁ : Labels G s} {D₁ : DS G s}
    (h : Fire d D e d₁ D₁) : EntryLE D₁ (G.dst e) (ext (d (G.src e)) e) := by
  cases h with
  | base hle hlt =>
      rw [relaxEdge_fire _ _ _ _ hle hlt]
      exact entryLE_insert_same _ _ _
  | complement hle href hlt =>
      rw [oneStep_complementarity _ _ _ _ _ hle href hlt]
      exact entryLE_insert_same _ _ _

/-- Firing one link preserves all earlier links' entries. -/
theorem Fire.preserve {d : Labels G s} {D : DS G s} {e : Fin G.m} {d₁ : Labels G s} {D₁ : DS G s}
    (h : Fire d D e d₁ D₁) {x : Fin G.n} {val : WLab G s} (hx : EntryLE D x val) :
    EntryLE D₁ x val := by
  cases h with
  | base hle hlt =>
      rw [relaxEdge_fire _ _ _ _ hle hlt]
      exact entryLE_insert _ _ hx
  | complement hle href hlt =>
      rw [oneStep_complementarity _ _ _ _ _ hle href hlt]
      exact entryLE_insert _ _ hx

/-- A finite improvement trace.  Each candidate is recomputed from the ground label at its own
settlement site; `Fire` supplies the actual accepted operation and `CascadeRun` threads the states. -/
inductive CascadeRun : List (Fin G.m × WLab G s) →
    Labels G s → DS G s → Labels G s → DS G s → Prop
  | nil {d : Labels G s} {D : DS G s} : CascadeRun [] d D d D
  | cons {e : Fin G.m} {cand : WLab G s} {rest : List (Fin G.m × WLab G s)}
      {d : Labels G s} {D : DS G s} {d₁ : Labels G s} {D₁ : DS G s}
      {d' : Labels G s} {D' : DS G s}
      (hcand : cand = ext (d (G.src e)) e) (hfire : Fire d D e d₁ D₁)
      (hrest : CascadeRun rest d₁ D₁ d' D') :
      CascadeRun ((e, cand) :: rest) d D d' D'

/-- Later links cannot erase an earlier structural entry. -/
theorem CascadeRun.preserve {links : List (Fin G.m × WLab G s)}
    {d : Labels G s} {D : DS G s} {d' : Labels G s} {D' : DS G s}
    (h : CascadeRun links d D d' D') {x : Fin G.n} {val : WLab G s} (hx : EntryLE D x val) :
    EntryLE D' x val := by
  induction h with
  | nil => exact hx
  | cons hcand hfire hrest ih => exact ih (hfire.preserve hx)

/-- Graph-contiguous improvement grounds: the target of one link is the next link's ground. -/
inductive GroundChain : List (Fin G.m × WLab G s) → Prop
  | nil : GroundChain []
  | single (p : Fin G.m × WLab G s) : GroundChain [p]
  | cons {e : Fin G.m} {ce : WLab G s} {f : Fin G.m} {cf : WLab G s}
      {rest : List (Fin G.m × WLab G s)}
      (hlink : G.dst e = G.src f) (hrest : GroundChain ((f, cf) :: rest)) :
      GroundChain ((e, ce) :: (f, cf) :: rest)

/-- The suffix of a ground chain is again a ground chain. -/
theorem GroundChain.tail {e : Fin G.m} {ce : WLab G s} {rest : List (Fin G.m × WLab G s)}
    (h : GroundChain ((e, ce) :: rest)) : GroundChain rest := by
  cases rest with
  | nil => exact GroundChain.nil
  | cons p rest =>
      cases h with
      | cons hlink hrest => exact hrest

/-- **Cascade arm.**  When the contiguous grounds settle in order, every link re-fires with a real
entry, and every one of those entries remains structural in the final store. -/
theorem cascade_arm {links : List (Fin G.m × WLab G s)}
    {d : Labels G s} {D : DS G s} {d' : Labels G s} {D' : DS G s}
    (_hchain : GroundChain links) (hrun : CascadeRun links d D d' D') :
    ∀ link ∈ links, EntryLE D' (G.dst link.1) link.2 := by
  induction hrun with
  | nil => intro link hlink; exact absurd hlink List.not_mem_nil
  | @cons e cand rest d D d₁ D₁ d' D' hcand hfire hrest ih =>
      intro link hlink
      rcases List.mem_cons.mp hlink with rfl | hlink
      · rw [hcand]
        exact hrest.preserve hfire.entry
      · exact ih _hchain.tail link hlink

end DMSY
end Frontier

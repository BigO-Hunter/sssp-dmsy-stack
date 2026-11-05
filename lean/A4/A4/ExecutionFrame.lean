import A4.Window

/-!
# Frontier.DMSY.ExecutionFrame — the active child at a settlement event

`Run` records children only after they return.  The active-subtree induction also needs the
instantaneous view while a child is running: which child is active, which `𝒟` it currently owns,
and which pull remainder its parent is holding.  `ActiveChild` is the parent/child adjacency;
`ExecutionFrame` adds the live child structure, labels, settlement event, and governing bound.

The parent half reuses `Suspension`, so the parent's structure is definitionally the remainder of
the actual BM.10 pull that launched the child.  At child return, `mergeAtReturn` is BM.14's
`DS.merge` of that remainder with the child's returned structure followed by BM.15's delete of the
child's settled set — exactly the iteration's `D2`.  The floor lemmas are the form
of bound nesting consumed by Lemma d2: `β ≤ B_child ≤ B_parent`, with both live structures
floored by `β` once the active child's own floor (Lemma V) is supplied.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- The active child and the exact pull remainder its parent holds while waiting. -/
structure ActiveChild (G : Graph) (s : Fin G.n) where
  suspended : Suspension G s
  child : CallEntry G s
  childBound : suspended.childBound = child.B

namespace ActiveChild

/-- The waiting parent's call bound. -/
def parentBound (f : ActiveChild G s) : WLab G s := f.suspended.parentBound

/-- The waiting parent's live structure (the BM.10 pull remainder, not its pre-pull store). -/
def parentD (f : ActiveChild G s) : DS G s := f.suspended.D

/-- I4 bound nesting, read directly from the pull that launched the active child. -/
theorem child_le_parent (f : ActiveChild G s) : f.child.B ≤ f.parentBound := by
  rw [← f.childBound]
  exact f.suspended.pull.2.2.1

/-- The suspended parent remainder is floored by the active child's entry bound. -/
theorem parent_floor_at_child (f : ActiveChild G s) : Ge f.child.B f.parentD := by
  rw [← f.childBound]
  exact suspension_floor f.suspended

/-- BM.14–15: the child's returned structure is merged into the suspended parent remainder and
the child's settled set is then deleted (★BM.15 FIX-STALE — the return merge of the repaired
engine, so a settled vertex never survives as a key of the parent's store). -/
noncomputable def mergeAtReturn (f : ActiveChild G s) (out : CallOut G s) : DS G s :=
  DS.deleteSet (DS.merge f.parentD out.D) (settledFinset out)

/-- The merge inherits the child's returned floor: the parent remainder was already floored by
the child's (larger) entry bound, and the child return is floored by its own `B'`.  ★BM.15 only
drops keys, so the floor survives the deletion (`deleteSet_some_imp`). -/
theorem mergeAtReturn_floor (f : ActiveChild G s) (out : CallOut G s)
    (hbound : out.B' ≤ f.child.B) (hchild : BoundClauseStrict out) :
    Ge out.B' (f.mergeAtReturn out) :=
  deleteSet_some_imp (settledFinset out)
    (ge_merge (ge_of_le hbound f.parent_floor_at_child) hchild)

/-- Run-specialized form: the child's bound law supplies `B' ≤ B_child`. -/
theorem mergeAtReturn_floor_of_run (t : ℕ) (f : ActiveChild G s) (out : CallOut G s)
    (hrun : Run t f.child out) (hchild : BoundClauseStrict out) :
    Ge out.B' (f.mergeAtReturn out) :=
  f.mergeAtReturn_floor out (run_le_bound t hrun) hchild

end ActiveChild

/-- The live execution frame at one settlement event.  `governing` is the event's bound `β`:
the pulled label at a base pull, or `B'` at a `W'` boundary append. -/
structure ExecutionFrame (G : Graph) (s : Fin G.n) extends ActiveChild G s where
  childD : DS G s
  d : Labels G s
  event : SettlementEvent G
  governing : WLab G s
  governing_le_child : governing ≤ child.B

namespace ExecutionFrame

/-- The event bound is below the waiting parent's bound as well as the active child's. -/
theorem governing_le_parent (f : ExecutionFrame G s) : f.governing ≤ f.parentBound :=
  f.governing_le_child.trans f.child_le_parent

/-- The suspended parent's live structure at the event, weakened from `B_child` to `β`. -/
theorem parent_floor (f : ExecutionFrame G s) : Ge f.governing f.parentD :=
  ge_of_le f.governing_le_child f.parent_floor_at_child

/-- The two structures simultaneously live at the settlement event. -/
def LiveFloor (f : ExecutionFrame G s) : Prop :=
  Ge f.governing f.childD ∧ Ge f.governing f.parentD

/-- Lemma d2's live-floor package: only the active child's own floor is a hypothesis; the
suspended parent's half follows from pull minimality and bound nesting. -/
theorem liveFloor (f : ExecutionFrame G s) (hchild : Ge f.governing f.childD) : f.LiveFloor :=
  ⟨hchild, f.parent_floor⟩

/-- The same two floors in the existing `Window` interface, with the parent as the innermost
suspended ancestor. -/
theorem live_window (f : ExecutionFrame G s) (hchild : Ge f.governing f.childD) :
    Window f.governing [f.suspended] f.childD := by
  refine ⟨hchild, ?_⟩
  intro g hg
  have hge : g = f.suspended := by simpa using hg
  subst g
  exact f.parent_floor

/-- If the live structures are viewed together, their keep-min merge is also floored by `β`.
This is a floor fact only: the actual merge occurs at child return, not during the event. -/
theorem live_merge_floor (f : ExecutionFrame G s) (hchild : Ge f.governing f.childD) :
    Ge f.governing (DS.merge f.parentD f.childD) :=
  ge_merge f.parent_floor hchild

end ExecutionFrame

/-- Every actual BM.10–13 iteration supplies the parent/child half of an execution frame. -/
theorem activeChild_of_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    ∃ f : ActiveChild G s, f.child = c ∧ f.parentBound = B := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  let suspended : Suspension G s := ⟨D1, Bi, pullCap t l, st.D, B, Si, hpull⟩
  have hbound : suspended.childBound = c.B := by
    show Bi = c.B
    rw [hc]
  exact ⟨⟨suspended, c, hbound⟩, rfl, rfl⟩

/-- Add a settlement snapshot to an actual iteration's active child.  The live child `𝒟`, labels,
and event are explicitly exposed rather than reconstructed from the completed child record. -/
theorem executionFrame_of_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (childD : DS G s) (d : Labels G s) (event : SettlementEvent G) (β : WLab G s)
    (hβ : β ≤ c.B) :
    ∃ f : ExecutionFrame G s, f.child = c ∧ f.childD = childD ∧ f.d = d ∧
      f.event = event ∧ f.governing = β ∧ f.parentBound = B := by
  obtain ⟨a, hac, haB⟩ := activeChild_of_istep h
  subst c
  exact ⟨⟨a, childD, d, event, β, hβ⟩, rfl, rfl, rfl, rfl, rfl, haB⟩

/-- BM.14–15 exactly: the frame's return merge is the iteration's `D2`, immediately followed by
its gated child-settlement sweep. -/
theorem mergeAtReturn_of_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    ∃ (f : ActiveChild G s) (D2 : DS G s) (d3 : Labels G s) (D3 : DS G s),
      f.child = c ∧ f.parentBound = B ∧ D2 = f.mergeAtReturn fo' ∧
        (d3, D3) = sweepEvts B f.suspended.childBound fo'.evts fo'.d' D2 := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  let suspended : Suspension G s := ⟨D1, Bi, pullCap t l, st.D, B, Si, hpull⟩
  have hbound : suspended.childBound = c.B := by
    show Bi = c.B
    rw [hc]
  let f : ActiveChild G s := ⟨suspended, c, hbound⟩
  refine ⟨f, D2, d3, D3, rfl, rfl, ?_, ?_⟩
  · exact hmerge
  · exact hsweep

end DMSY
end Frontier

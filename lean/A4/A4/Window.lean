import A4.Transitive

/-!
# Frontier.DMSY.Window — the settlement-event window (audit PROOF.md §4, Lemma W)

At a settlement event with governing bound `β`, every live `𝒟` entry has value `≥ β`.  The
live structures are the event call's own structure and the pull remainders of its suspended
ancestors.  A `Suspension` packages exactly the remainder produced by a parent's BM.10 pull and
the child's BM.13 bound; `suspension_of_istep` shows that every actual `IStep` produces one.
Nothing writes that remainder between the pull and the child call, so this is the state visible
throughout the child's subtree.

* **W1** (`w1_suspended`) composes pull floors down a nested active stack.
* **W3** (`w3_basePull`) is the base pull's global-minimum clause.
* **W2** (`w2_wPrimeAppend`) takes the loop-exit floor supplied by Lemma V and transports it
  through the line-33 gated re-inserts.  Thus Lemma V is an explicit hypothesis, not a hidden
  axiom or a re-proof here.

`window_basePull` and `window_wPrimeAppend` assemble all live structures at the two settlement
sites.  The only outstanding ingredient for an unconditional W′-append instance is Lemma V at
the loop-exit state (the joint first-violation induction).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- A suspended parent's live structure: the exact remainder of its BM.10 pull, paired with the
bound passed to its BM.13 child.  The `pullRun` witness gives the remainder floor by
`pullRun_floor`; no insert site occurs between this pull and the child call. -/
structure Suspension (G : Graph) (s : Fin G.n) where
  D : DS G s
  childBound : WLab G s
  cap : ℕ
  parentD : DS G s
  parentBound : WLab G s
  pulled : Finset (Fin G.n)
  pull : pullRun cap parentD parentBound pulled childBound D

/-- Every actual iteration supplies a suspended frame at its child's bound.  This is the
pull/child-call adjacency of BM.10–13 (the no-insert interval of PROOF.md §4, W1). -/
theorem suspension_of_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ} {st st' : RState G s p}
    {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo') :
    ∃ f : Suspension G s, f.childBound = c.B := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  refine ⟨⟨D1, Bi, pullCap t l, st.D, B, Si, hpull⟩, ?_⟩
  rw [hc]

/-- A suspended remainder is floored by the bound of the child for which the parent is waiting. -/
theorem suspension_floor (f : Suspension G s) : Ge f.childBound f.D :=
  fun _ _ hy => pullRun_floor f.pull hy

/-- An active ancestor stack, innermost parent first.  `callBound` is the currently executing
call's entry bound.  Each frame's child bound dominates the next active call bound (I4 bound
nesting), while the frame itself certifies that its remainder is that child bound's pull floor. -/
inductive SuspendedStack : WLab G s → List (Suspension G s) → Prop
  | nil {callBound : WLab G s} : SuspendedStack callBound []
  | cons {callBound : WLab G s} {f : Suspension G s} {fs : List (Suspension G s)}
      (hbound : callBound ≤ f.childBound) (hrest : SuspendedStack f.childBound fs) :
      SuspendedStack callBound (f :: fs)

/-- **W1, suspended ancestors.**  Every entry of every suspended ancestor is at least the event
call's entry bound.  The proof is pull minimality at the innermost frame followed by transitivity
through the nested child bounds. -/
theorem w1_suspended {callBound : WLab G s} {ancestors : List (Suspension G s)}
    (hstack : SuspendedStack callBound ancestors) :
    ∀ f ∈ ancestors, Ge callBound f.D := by
  induction hstack with
  | nil => intro f hf; exact absurd hf List.not_mem_nil
  | @cons callBound f fs hbound hrest ih =>
    intro g hg
    rcases List.mem_cons.mp hg with h | hg
    · subst g
      exact ge_of_le hbound (suspension_floor f)
    · exact ge_of_le hbound (ih g hg)

/-- W1 weakened from the event call's entry bound to the event's governing bound `β`. -/
theorem w1_suspended_at {callBound β : WLab G s} {ancestors : List (Suspension G s)}
    (hβ : β ≤ callBound) (hstack : SuspendedStack callBound ancestors) :
    ∀ f ∈ ancestors, Ge β f.D :=
  fun f hf => ge_of_le hβ (w1_suspended hstack f hf)

/-- **W3, own structure at a base pull.**  The pulled value `β` is below the separator, and every
other entry is above that separator; hence no co-resident value is below `β`. -/
theorem w3_basePull {D : DS G s} {u : Fin G.n} {β x : WLab G s}
    (hu : D u = some β) (hxgt : β < x)
    (hxrest : ∀ y μ, y ≠ u → D y = some μ → x ≤ μ) : Ge β D := by
  intro y μ hy
  by_cases hyu : y = u
  · subst y
    rw [hu] at hy
    exact le_of_eq (Option.some.inj hy)
  · exact hxgt.le.trans (hxrest y μ hyu hy)

/-- The line-33 seed re-inserts preserve a `bp` floor: old entries have it by assumption and every
new insert is explicitly gated by `bp ≤ d x`. -/
theorem ge_seedIns {bp B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s} {D : DS G s}
    (hD : Ge bp D) : Ge bp (seedIns bp B S d D).2 := by
  intro y val hy
  have h := gOrM_seedIns (K := bp) (bp := bp) (B := B) (S := S) (ms := []) d D
    (fun y val hy => Or.inl (hD y val hy)) le_rfl
  rcases h y val hy with hge | hm
  · exact hge
  · exact absurd hm List.not_mem_nil

/-- **W2, own structure at a W′ append.**  At the filter the structure consists of the loop-exit
survivors and the line-33 re-inserts.  Lemma V supplies the survivors' floor; the re-insert gate
preserves it.  On a drained loop exit the survivor clause is vacuous and FIX-EMPTY may raise the
bound to `B` without hurting the proof. -/
theorem w2_wPrimeAppend {B : WLab G s} {S : Finset (Fin G.n)} {p : ℕ} {st : RState G s p}
    (hV : Ge st.bp st.D) :
    Ge (tailBP B st) (seedIns (tailBP B st) B S st.d st.D).2 := by
  apply ge_seedIns
  by_cases hemp : DS.IsEmpty st.D
  · intro y val hy
    rw [hemp y] at hy
    exact absurd hy.symm (Option.some_ne_none val)
  · rw [tailBP_of_not_isEmpty B st hemp]
    exact hV

/-- The complete window assertion at a settlement site: the event call's own structure and every
suspended ancestor are floored by the governing bound `β`. -/
def Window (β : WLab G s) (ancestors : List (Suspension G s)) (own : DS G s) : Prop :=
  Ge β own ∧ ∀ f ∈ ancestors, Ge β f.D

/-- **Lemma W at a base pull.**  W3 handles the base structure; W1 handles every suspended
ancestor, with `β < x ≤ B` supplying the governing-to-entry-bound comparison. -/
theorem window_basePull {B β x : WLab G s} {D : DS G s} {u : Fin G.n}
    {ancestors : List (Suspension G s)} (hstack : SuspendedStack B ancestors)
    (hu : D u = some β) (hxgt : β < x) (hxle : x ≤ B)
    (hxrest : ∀ y μ, y ≠ u → D y = some μ → x ≤ μ) : Window β ancestors D :=
  ⟨w3_basePull hu hxgt hxrest, w1_suspended_at (hxgt.le.trans hxle) hstack⟩

/-- **Lemma W at a W′ append, conditional on Lemma V at loop exit.**  W2 handles the filter-time
structure; the bound law `tailBP B st ≤ B` lets W1 cover every suspended ancestor. -/
theorem window_wPrimeAppend {B : WLab G s} {S : Finset (Fin G.n)} {p : ℕ} {st : RState G s p}
    {ancestors : List (Suspension G s)} (hbp : st.bp ≤ B) (hV : Ge st.bp st.D)
    (hstack : SuspendedStack B ancestors) :
    Window (tailBP B st) ancestors (seedIns (tailBP B st) B S st.d st.D).2 :=
  ⟨w2_wPrimeAppend hV, w1_suspended_at (tailBP_le B st hbp) hstack⟩

end DMSY
end Frontier

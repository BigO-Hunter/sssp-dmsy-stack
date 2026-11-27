import A4.LastWriter

set_option linter.unnecessarySimpa false

/-!
# Frontier.DMSY.OriginTrace — typed origin certificates for mint values

Work package **A4 (BMSSP recursion)**, the origin layer over `LastWriter`.  `LastWriter`'s mint
connection leaves the inherited case untyped (`m.val = fo'.d' m.x`); this file constructs the
typed `OriginCert`:

* `istepTrace_child_link` — the child-call linkage: the instrumented step's child call sits at
  level `l - 1` and inherits the prior iteration state's labels (`c.d = st.d`) — the two facts
  that give `OriginCert.child` / `OriginCert.iter` their index and label meaning.
* `istepTrace_mint_origin` — **the typed origin link** (the strengthened mint connection): a
  mint's value is either written by the current sweep (a `LastTarget` witness) or carries
  `OriginCert.child i fo'` — built from the step's own data: `i` is the child's index in the
  parent loop (`ILoopTrace`'s step counter) and `fo'` its actual return.  Unconditional.
* `BaseInherited` / `runTrace_d_eq_entry_of_level_zero` /
  `istepTrace_child_d'_eq_st_d_of_base` — the child-inheritance fact for base-level children
  (`c.l = 0`): the child returns the prior iteration state's label at `x`.
* `istepTrace_mint_origin_iter` / `istepTrace_mint_origin_iter_of_base` — the `iter`
  refinement: under the child-inheritance premise (derived for base-level children), the
  mint's inherited certificate refines to `OriginCert.iter i st.d` — the **prior iteration
  state's** actual labels, at the step's own loop index.

What remains open is the descent *below* a child's own logged history: A2's `fpRun` and A1's
`baseRun` log no acceptance trace, so a label's passage from FindPivots or base-run labels to
the call's entry labels is unwitnessed — instrumenting those two runs is the exact missing
field.  Nothing here assumes a settled/seed ground conclusion, and no `RunTraceCert` axiom is
introduced; the ground split stays open.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Child-call linkage -/

/-- The instrumented step's child call: its level is the parent's minus one and its entry
labels are the prior iteration state's labels. -/
theorem istepTrace_child_link (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) :
    c.l = l - 1 ∧ c.d = st.d :=
  ⟨istepTrace_child_l t B l i h, istepTrace_child_d t B l i h⟩

/-! ## The typed mint origin -/

/-- **Typed origin link**: a mint's value is either written by the current sweep (the last
target's recorded value) or inherited, in which case the typed certificate
`OriginCert.child i fo'` is built from the step's own data: `i` is the child's index in the
parent loop (`ILoopTrace`'s step counter) and `fo'` its actual return. -/
theorem istepTrace_mint_origin (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild) :
    ∀ m ∈ st'.mints,
      (∃ r, LastTarget m.x trStep r ∧ r.vv = m.val) ∨
        (m.val = fo'.d' m.x ∧ OriginCert G s m.x m.val) := by
  intro m hm
  rcases istepTrace_mint_lastTarget t B l i h m hm with ⟨r, hlt, hvv⟩ | hval
  · exact Or.inl ⟨r, hlt, hvv⟩
  · exact Or.inr ⟨hval, OriginCert.child i fo' hval⟩

/-! ## The `iter` refinement -/

/-- **The named side condition** (the exact missing field): A1's `baseRun` logs no acceptance
trace, so a base run's per-vertex no-write behaviour is not extractable from any log.  We
assume the derived form — a base run returns each vertex's entry label — as an explicit
hypothesis of the theorems below (never an axiom).  Instrumenting `baseRun` (A1) — and `fpRun`
(A2) for the deeper FindPivots descent — is the missing field; until then the descent from a
base/FindPivots label to the call's entry labels is unwitnessed. -/
def BaseInherited (t : ℕ) (s : Fin G.n) (x : Fin G.n) : Prop :=
  ∀ (B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) (bout : BaseOut G s),
    baseRun t ⟨B, S, d, initD S d⟩ bout → bout.d' x = d x

/-- A level-0 `RunTrace` derivation returns the entry label at every vertex the side condition
covers: the recur case is contradictory at level 0, and the base case is exactly
`BaseInherited`. -/
theorem runTrace_d_eq_entry_of_level_zero (t : ℕ) {B : WLab G s} {l : ℕ} (x : Fin G.n)
    (hbaseInh : BaseInherited t s x) {e : CallEntry G s} {out : CallOut G s}
    {tr : Trace G s} (hc : RunTrace t B l e out tr) (h0 : e.l = 0) : out.d' x = e.d x := by
  revert h0
  cases hc with
  | base hl hb =>
      rename_i bout
      intro _h0
      exact hbaseInh e.B e.S e.d bout hb
  | recur hl _hfp _hpiv _hst0 _hloop => intro h0; omega

/-- A base-level child (level `c.l = 0`) returns the prior iteration state's label at every
vertex the side condition covers: its return labels are the base run's, and its entry labels
are the prior state's (`istepTrace_child_d`). -/
theorem istepTrace_child_d'_eq_st_d_of_base (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    {trStep trChild trC : Trace G s} (x : Fin G.n)
    (h : IStepTrace t B l i st st' c fo' trStep trChild)
    (hbaseInh : BaseInherited t s x)
    (hc : RunTrace t B l c fo' trC) (h0 : c.l = 0) :
    fo'.d' x = st.d x := by
  have hd : fo'.d' x = c.d x := runTrace_d_eq_entry_of_level_zero t x hbaseInh hc h0
  refine hd.trans ?_
  exact congrFun (istepTrace_child_d t B l i h) x

/-- **The `iter` refinement**: under the child-inheritance premise — derived for base-level
children above; the open regime for deeper children is the missing A1/A2 instrumentation — a
mint's inherited certificate is `OriginCert.iter i st.d`: the **prior iteration state's**
actual labels, at the step's own loop index. -/
theorem istepTrace_mint_origin_iter (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    {trStep trChild : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild)
    (hinh : ∀ x : Fin G.n, fo'.d' x = st.d x) :
    ∀ m ∈ st'.mints,
      (∃ r, LastTarget m.x trStep r ∧ r.vv = m.val) ∨
        (m.val = st.d m.x ∧ OriginCert G s m.x m.val) := by
  intro m hm
  rcases istepTrace_mint_origin t B l i h m hm with ⟨r, hlt, hvv⟩ | ⟨hval, _⟩
  · exact Or.inl ⟨r, hlt, hvv⟩
  · exact Or.inr ⟨hval.trans (hinh m.x), OriginCert.iter i st.d (hval.trans (hinh m.x))⟩

/-- Combining the refinement with the base-child derivation: for a step whose child is a
base-level call (`c.l = 0`), under `BaseInherited` the mint's inherited certificate is the
typed `OriginCert.iter` — no untyped disjunct remains. -/
theorem istepTrace_mint_origin_iter_of_base (t : ℕ) (B : WLab G s) (l : ℕ) (i : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    {trStep trChild trC : Trace G s}
    (h : IStepTrace t B l i st st' c fo' trStep trChild)
    (hbaseInh : ∀ x : Fin G.n, BaseInherited t s x)
    (hc : RunTrace t B l c fo' trC) (h0 : c.l = 0) :
    ∀ m ∈ st'.mints,
      (∃ r, LastTarget m.x trStep r ∧ r.vv = m.val) ∨
        (m.val = st.d m.x ∧ OriginCert G s m.x m.val) := by
  refine istepTrace_mint_origin_iter t B l i h ?_
  intro x
  exact istepTrace_child_d'_eq_st_d_of_base t B l i x h (hbaseInh x) hc h0

end DMSY
end Frontier

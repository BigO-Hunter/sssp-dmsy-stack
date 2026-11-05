import Frontier.DMSY.Engine

/-!
# Frontier.DMSY.Lemma37 — the corrected Lemma 3.7* (and 3.1*) statements

Work package **A0 (interface)**.  The statements of CORRECTED_PROOF.md §3–§4, packaged as
Prop-valued structures so that each clause of the proof obligation is local and explicit.
No proofs here: A1 discharges `Lemma31Star`, A4 discharges `Lemma37Star` and `TheoremT`.

The statements are parameterized over the yet-to-be-written judgments (A1/A4):

* `Reach : CallEntry G s → Prop` — reachable-state closure (CORRECTED_PROOF §2.3), formalized
  inductively over execution prefixes in A4.  The Q9 instance is the mandatory negative
  regression: the lemma is **false** without it.
* `Run : CallEntry G s → CallOut G s → Prop` — Algorithm 3 with (E0), (E1), (E3), as a
  cost-indexed relational big-step judgment (A4).
* `Full : CallEntry G s → CallOut G s → Prop` — "the call is a full execution" (loop exit with
  `𝒟` drained).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Lemma 3.7* hypotheses -/

/-- Entry hypotheses of Lemma 3.7*: `l > 0` (the base case is Lemma 3.1*), `⟨∅, S⟩` is a
frontier for `Ũ(B, S)` at the call's entry, and `|S| ≤ t²·2^(l·t)`. -/
def Lemma37Hyp (t : ℕ) (e : CallEntry G s) : Prop :=
  0 < e.l ∧
    IsFrontier e.d (Utilde e.B (e.S : Set (Fin G.n))) ∅ (e.S : Set (Fin G.n)) ∧
    e.S.card ≤ memCap t e.l

/-! ## Lemma 3.7* conclusions -/

/-- The conclusions of **Lemma 3.7\*** (CORRECTED_PROOF §3) at the return `(B', U, 𝒟)` of
`BMSSP*(B, S, l)`, with `Prem` the premature set of the final iteration's line-29 re-selection. -/
structure Lemma37Concl (Full : CallEntry G s → CallOut G s → Prop)
    (e : CallEntry G s) (out : CallOut G s) : Prop where
  /-- **(1) Frontier.** `⟨U, 𝒟⟩` is a frontier for `Ũ(B, S)`. -/
  frontier : IsFrontier out.d' (Utilde e.B (e.S : Set (Fin G.n)))
    (out.U) (DS.keys out.D)
  /-- **(2a) Progress.** `max_{x ∈ U} dis(x) < B'`. -/
  progress : ∀ x ∈ out.U, dis (s := s) x < out.B'
  /-- **(2a) Completeness of settlements.** Every settlement event of the call settles a
  complete vertex (lh-grade: `Complete` implies `CompleteLen`). -/
  settleComplete : ∀ ev ∈ out.evts, Complete out.d' ev.v
  /-- **(2a)** `U ⊆ Ũ(B', S)`. -/
  uSubset : out.U ⊆ Utilde out.B' (e.S : Set (Fin G.n))
  /-- **(2b) Bound clause, with Q12 carve-out.** Every entry of `𝒟` has stored value `≥ B'`,
  except entries of `Prem`. -/
  bound : ∀ y val, out.D y = some val → out.B' ≤ val ∨ out.Premature y val
  /-- **(2b)** `Prem ⊆` entries of the returned `𝒟`. -/
  premInD : ∀ x val, out.Premature x val → out.D x = some val
  /-- **(2b)** For each `(x, val) ∈ Prem`: `x ∉ U`; `x ∈ P_j` for some `j` at the final
  re-selection; `d[x] ≤ val < B'`; and `x` is two-shaped. -/
  premShape : ∀ x val, out.Premature x val →
    x ∉ out.U ∧ (∃ j, x ∈ out.Pfin j) ∧ out.d' x ≤ val ∧ PremShape out.d' x val
  /-- **(2b)** `Prem = ∅` if the call is a full execution (loop exit with `𝒟` drained).
  (`Prem = ∅` if the final iteration's re-selection minted nothing below `B'` is definitional.) -/
  fullImmune : Full e out → ∀ x val, ¬ out.Premature x val
  /-- **(2c) Settlement identity, modulo the carve-out.**
  `U = Ũ(B', S) ∖ K`, with `K` the carve-out keys.  In particular `U = Ũ(B', S)` when
  `Prem = ∅`. -/
  identity : out.U = Utilde out.B' (e.S : Set (Fin G.n)) \ out.carveKeys e.S
  /-- **(3) Containment, read modulo Prem.** `S ∖ (U ∪ K) ⊆ keys(𝒟)`. -/
  containS : ((e.S : Set (Fin G.n)) \ (out.U ∪ out.carveKeys e.S)) ⊆ DS.keys out.D
  /-- **(3) Containment, read modulo Prem.** Every `v ∈ R(B, U)` with `d[v] ≥ B'` is in `𝒟`. -/
  containR : ∀ v, v ∈ Relaxed out.d' e.B out.U → out.B' ≤ out.d' v → v ∈ DS.keys out.D

/-- **Corrected Lemma 3.7\*** (CORRECTED_PROOF §3).  Let `σ` be reachable (§2.3), `l > 0`,
`⟨∅, S⟩` a frontier for `Ũ(B, S)` at the call's entry, `|S| ≤ t²·2^(lt)`.  Run
`BMSSP*(B, S, l)` = Algorithm 3 with (E0), (E1), (E3).  At return, the clauses of
`Lemma37Concl` hold. -/
def Lemma37Star (t : ℕ) (Reach : CallEntry G s → Prop)
    (Run : CallEntry G s → CallOut G s → Prop)
    (Full : CallEntry G s → CallOut G s → Prop) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s),
    Reach e → Lemma37Hyp t e → Run e out → Lemma37Concl Full e out

/-- **Theorem T (carve-out emptiness)** (CORRECTED_PROOF §3): *on the V5 engine, `Prem = ∅` at
every return of every reachable run.*  Hence in Lemma 3.7* the carve-out is empty and clauses
(2b)/(2c)/(3) collapse to the paper's clause 2 and clause 3 verbatim.  Hand proof in the audit
(one half of a joint first-violation induction with settlement completeness), **not
machine-checked**; the Lean development may prove this or the joint invariant
`(2a ∧ 2b ∧ Prem = ∅)` directly. -/
def TheoremT (Reach : CallEntry G s → Prop)
    (Run : CallEntry G s → CallOut G s → Prop) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s),
    Reach e → Run e out → ∀ x val, ¬ out.Premature x val

/-! ## Lemma 3.1* (base case, with the V5 cap) -/

/-- The conclusions of **Lemma 3.1\*** (CORRECTED_PROOF §4.1): with (E1), Algorithm 4 returns
`(B'⁺, U, 𝒟)` with `U = Ũ(B'⁺, S)` complete, `max dis(U) < B'⁺`, `d_B[𝒟] ≥ B'⁺`, and the
full-execution dichotomy `B'⁺ = B ⟺ 𝒟 = ∅`. -/
structure Lemma31Concl (e : BaseIn G s) (out : BaseOut G s) : Prop where
  /-- (E1): `B'⁺ = min(B'_pull, d_B[𝒟_final])`. -/
  cap : CapLaw out.B'_plus out.B'_pull e.B out.D_final
  /-- `U = Ũ(B'⁺, S)`. -/
  identity : out.U = Utilde out.B'_plus (e.S : Set (Fin G.n))
  /-- Every settlement event settles a complete vertex. -/
  settleComplete : ∀ ev ∈ out.evts, Complete out.d' ev.v
  /-- `max dis(U) < B'⁺`. -/
  progress : ∀ x ∈ out.U, dis (s := s) x < out.B'_plus
  /-- `d_B[𝒟] ≥ B'⁺` (by construction of the cap). -/
  bound : out.B'_plus ≤ dMin e.B out.D_final
  /-- Full-execution dichotomy: `B'⁺ = B ⟺ 𝒟 = ∅`. -/
  dichotomy : out.B'_plus = e.B ↔ DS.IsEmpty out.D_final

/-- **Corrected Lemma 3.1\***: every reachable base-case call satisfies `Lemma31Concl`. -/
def Lemma31Star (ReachBase : BaseIn G s → Prop)
    (baseRun : BaseIn G s → BaseOut G s → Prop) : Prop :=
  ∀ (e : BaseIn G s) (out : BaseOut G s),
    ReachBase e → baseRun e out → Lemma31Concl e out

end DMSY
end Frontier

import A4.Transitive

/-!
# Frontier.DMSY.Size — corrected Lemma 3.8* (size) and the re-settlement bound

Work package **A4 (BMSSP recursion)**, task key lemma 2.  CORRECTED_PROOF §6 statements,
pinned as Prop-valued signatures (sizes/trees/Q-charging beyond these are packages C2/C3's,
IMPLAN §2):

* **(a)** the event ceiling: the (E3) guard fires on events; the true inductive shape is
  `E(l) ≤ eventCap t l + E(l-1) + G.n` (final-batch overshoot + the unguarded `W'` tail),
  pinned closed-form;
* **(b)** structure size: keys are deduped vertices (`|keys(𝒟)| ≤ |V|`); the audit's
  `≤ |S| + |U|·δ ≤ t⁴·2^(lt)` refinement is C2/C3's pull-size contract;
* **(c)** *disjointness, corrected*: `U = W' ⊎ ⊎ᵢ Uᵢ` as multisets exactly, with the `W'` part
  pairwise distinct and disjoint from the call's accumulated log — so all duplicate excess is
  cross-sibling re-settlement (`T_X`, Lemma R).  (The audit's "T_X = 0 on full executions" is
  dropped as refuted by its own §5 measurements; wound 2125608306.)
* **Lemma R** (re-settlement bound): the (E3) certificate `T ≤ (log ceiling)`; the audit's
  `√(2K(l_top+1)n·L_max)` refinement stays sketch grade (CORRECTED_PROOF §8.2 open pieces).

The event count is `out.evts.length` (E3: `U` is the settlement log); duplicates are events
with the same vertex (`SettlementEvent`), and `T_X = |events| − |distinct vertices|`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- The multiset of settled vertices of a log (duplicates kept). -/
def evtVerts (evts : List (SettlementEvent G)) : List (Fin G.n) :=
  evts.map (·.v)

/-- The **duplicate excess** of a settlement log: events beyond the first per vertex. -/
def dupExcess (evts : List (SettlementEvent G)) : ℕ :=
  evts.length - (evts.map (·.v)).toFinset.card

/-- **Lemma 3.8\*(a)** (event ceiling) — *statement weakened 2026-11-04 to the true inductive
shape*.  The pinned form `≤ eventCap t e.l + eventCap t (e.l - 1)` is **false** on this engine:
the (E3) guard bounds only the loop's accumulated log, the final batch overshoot is the last
child's *whole* share `E(l-1)` (itself `eventCap`-plus-`eventCap` by induction), and the tail's
`W'` boundary appends (BM.26) are unguarded and add up to `G.n` events.  The true recurrence is
`E(l) ≤ eventCap t l + E(l-1) + G.n`, `E(0) ≤ t³ + 1`, whose closed form is pinned here: the log
of a return is at most one (E3) ceiling per recursion level, plus one `W'` tail per level. -/
def Lemma38A (t : ℕ) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s), Run t e out →
    out.evts.length ≤ (e.l + 1) * (eventCap t e.l + G.n) + 1

/-- **Lemma 3.8\*(b)** (structure size) — *statement weakened 2026-11-04 to the keyed-dedup
bound*.  The pinned `≤ t⁴·2^(l·t)` refinement (`|S| + |U|·δ`) needs the pull-size contract's
bookkeeping on top of the size clause now pinned in `PullSpec.size` / `pullRun` (`|S'| ≤
pullCap t l` at a pull, Lemma 3.4's `M = t·2^((l−1)t)`; added 2026-11-04), plus C2/C3's
`|U|·δ` charging — without both, reachable calls with arbitrarily large `S` exist and no such
cap is derivable.  What is true and provable here is the reason the audit's (b) is "unchanged
by duplicates": `𝒟` is keyed by vertices, so its key set is deduped and never exceeds `|V|`. -/
def Lemma38B (t : ℕ) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s), Run t e out →
    (Finset.univ.filter (fun y : Fin G.n => out.D y ≠ none)).card ≤ G.n

/-- **Lemma 3.8\*(c)** (disjointness, corrected) — *statement weakened 2026-11-04 to the
provable structural half*.  The multiset union `U = W' ⊎ ⊎ᵢ Uᵢ` holds exactly (the log is the
call's accumulated child log plus the tail's `W'` boundary appends), the `W'` part is pairwise
distinct and **disjoint from the call's accumulated log** (the call-local `W'` filter, Q11) — so
every duplicate event is born *between sibling subtrees*, which is exactly the excess `T_X`
counted by Lemma R.  The pinned `Full → dupExcess = 0` is dropped: it contradicts CORRECTED_PROOF
§5's own measurements (duplicate excess up to 3.8/vertex on completed V5 runs — a full call's
`W'` filter cannot see a sibling's settlement), and it is refutable in this semantics. -/
def Lemma38C (t : ℕ) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s), Run t e out →
    ∃ (acc wp : List (SettlementEvent G)),
      out.evts = acc ++ wp ∧ (wp.map (·.v)).Nodup ∧
        (∀ ev ∈ wp, ev.kind = .boundaryAppend) ∧
        ∀ x, x ∈ settledSet wp → x ∉ settledSet acc

/-- **Lemma R** (re-settlement bound) — *statement weakened 2026-11-04 to the (E3)
certificate*.  The audit's sketch-grade claim `T ≤ √(2K·(l_top+1)·n·L_max) + O((l_top+k)·n)`
(CORRECTED_PROOF §5, Q14 addenda 1–6) is **not provable as stated**: §8.2 names its open
pieces (custody-chain formalization, wave-exhaustiveness bookkeeping, per-call `B'` monotonicity
of Lemma F) and records "evidence favors damping; no proof".  What (E3) actually delivers — and
what is pinned and proved here — is the event-ceiling certificate (CORRECTED_PROOF §2.1: "a
completed run certifies `T ≤ t³·2^(l_top·t) − n₂` … an overflow aborts loudly"), read through
Lemma 3.8\*(a): the duplicate excess never exceeds the settlement log's own ceiling, one (E3)
guard per recursion level plus one `W'` tail per level.  The `√(2K(l_top+1)n·L_max)` refinement
stays an open piece of the audit (wound 2125608306 covers the adjacent 3.8\*(c) defect). -/
def LemmaR (t : ℕ) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s), Run t e out →
    dupExcess out.evts ≤ (e.l + 1) * (eventCap t e.l + G.n) + 1

/-- **Corrected Lemma 3.8\***: (a) event ceiling, (b) structure size, (c) disjointness corrected
(vanishing duplicate excess on full executions). -/
def Lemma38Star (t : ℕ) : Prop := @Lemma38A G s t ∧ @Lemma38B G s t ∧ @Lemma38C G s t

end DMSY
end Frontier

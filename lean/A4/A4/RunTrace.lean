import A4.Provenance
import A4.Stall

/-!
# Frontier.DMSY.RunTrace — the instrumented execution/trace layer

Work package **A4 (BMSSP recursion)**, provenance seam.  This file is the answer to the A4
blocker: `A4.Provenance.ImprovementProvenance` needs, for every low final mint, an
acceptance-time `ImproveChain` plus its cascade/stall ending, but the big-step `Run` relation
records only the *final* labels (`out.d'`) and the settlement *log* (`out.evts`), never the
per-acceptance edge/source/target record that an `ImproveLink` carries.

## Why `Run` alone cannot extract it

The mint's value *is* present in `Run`'s output — `out.mints` records `val = d[x]` at mint time,
and a finite label is a walk (`WLab = WithTop (WalkOrd)`, `ext` is list-append), so the *walk*
underlying `m.val` is recoverable.  What is *not* recoverable is (i) the certification that this
walk was built by a sequence of *accepted* relaxations rather than written whole (label honesty is
proved elsewhere as `WalkInv`, but `WalkInv` does not name the acceptance edges), and (ii) the
**ground split point**: which vertex on the walk is the deepest settled-or-seed vertex, with its
label at settlement/seed time.  `ImproveChain G s ground m.x groundVal m.val` needs exactly that
split: `groundVal` must be a proper walk-prefix of `m.val` ending at `ground`, threaded by one
`ImproveLink` per edge.  Neither the acceptance order nor the ground identification is determined
by `Run`'s output — two runs of the same `CallEntry` to the same `CallOut` can differ in which
intermediate relaxations fired, yet must yield the same chain here.  So the extraction is not a
function of `Run`.

## The minimal enrichment (what this file supplies)

1. `RelaxStep` — a `Type`-valued record of one accepted relaxation, with the exact
   `ImproveLink` fields (`e`, `u`, `v`, `uv`, `vv` plus the four proofs).  This is the *only*
   data `Run` lacks.
2. `Trace G s := List (RelaxStep G s)` — a run's acceptance history.
3. `ContigFrom` — a contiguous acceptance trace from a ground to a target, and
   `chain_of_contigFrom`, the mechanical reconstruction turning that trace into an
   `ImproveChain` (the bridge from operational evidence to the relational chain).
4. `TraceProv` — the trace-level provenance content (ground + contiguous chain + `ChainGround`
   source + `ProvenanceEnd` ending, for every low mint), and the extraction theorem
   `improvementProvenance_of_traceProv : TraceProv → ImprovementProvenance`.
5. `improvementProvenance_of_full` — full executions have no low mints, so `ImprovementProvenance`
   holds there *without any trace*; this closes the seam for the top-level call (always full) and
   for every full return.
6. `mint_key_mem_seed` — a mint's key is a member of the call's seed set `e.S`,
   the `ChainGround.seedWalked` source.

The one remaining obligation is `RunTraceCert` (below): every `Run` *admits* such a certifying
trace.  That is the content of the audit's joint first-violation induction
(CORRECTED_PROOF §8.1, PROOF.md §5 — Lemma W/V/Rep, the W′ drop lemma, the refusal-floor lemma),
which is hand-proved there and is *not* restated here; this file reduces `ImprovementProvenance`
to exactly that one named seam.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Acceptance-time records -/

/-- One accepted relaxation, recorded at acceptance time.  `Type`-valued so an acceptance history
can be logged; `Run` keeps only the final labels, so this is the missing operational evidence an
`ImproveLink` needs (`ImproveLink.mk`'s `hs`/`ht`/`hne`/`he` are exactly `src_eq`/`dst_eq`/
`uv_ne_top`/`vv_ext`). -/
structure RelaxStep (G : Graph) (s : Fin G.n) where
  e : Fin G.m
  u : Fin G.n
  v : Fin G.n
  uv : WLab G s
  vv : WLab G s
  src_eq : G.src e = u
  dst_eq : G.dst e = v
  uv_ne_top : uv ≠ ⊤
  vv_ext : vv = ext uv e

namespace RelaxStep

/-- The acceptance-time improvement link. -/
theorem toLink (r : RelaxStep G s) : ImproveLink G s r.u r.v r.uv r.vv :=
  ImproveLink.mk r.e r.src_eq r.dst_eq r.uv_ne_top r.vv_ext

/-- Every accepted relaxation strictly ascends in the walk order. -/
theorem value_lt (r : RelaxStep G s) : r.uv < r.vv := r.toLink.value_lt

/-- Every accepted relaxation strictly increases the hop measure. -/
theorem rank_lt (r : RelaxStep G s) :
    ImproveLink.rank r.uv < ImproveLink.rank r.vv := r.toLink.rank_lt

end RelaxStep

/-- A run's acceptance history: the accepted relaxations in the order they occurred. -/
abbrev Trace (G : Graph) (s : Fin G.n) := List (RelaxStep G s)

/-! ## Contiguous traces and the chain reconstruction -/

/-- `rs` is a **contiguous** acceptance trace from a source vertex/label to the recorded final
target vertex/label: every step starts at the vertex and label where the previous step ended.
The source vertex and label are *indices* (they change along the trace); `chain_of_contigFrom`
reads the endpoints back off the first and last `RelaxStep`. -/
inductive ContigFrom (G : Graph) (s : Fin G.n) :
    Fin G.n → WLab G s → Trace G s → Fin G.n → WLab G s → Prop
  | step (r : RelaxStep G s) : ContigFrom G s r.u r.uv [r] r.v r.vv
  | cons (r : RelaxStep G s) (rs : Trace G s) (v : Fin G.n) (vv : WLab G s)
      (htail : ContigFrom G s r.v r.vv rs v vv) : ContigFrom G s r.u r.uv (r :: rs) v vv

/-- **Mechanical reconstruction**: a contiguous acceptance trace *is* an `ImproveChain`.  This is
the bridge from operational evidence (the logged `RelaxStep`s) to the relational chain
`ImprovementProvenance` consumes — no arithmetic or graph theory, only the trace's own
contiguity. -/
theorem chain_of_contigFrom {u v : Fin G.n} {uv vv : WLab G s} {rs : Trace G s}
    (h : ContigFrom G s u uv rs v vv) : ImproveChain G s u v uv vv := by
  induction h with
  | step r => exact ImproveChain.last r.toLink
  | cons r _rs _v _vv _htail ih => exact ImproveChain.cons r.toLink ih

/-! ## Trace-level provenance and the extraction theorem -/

/-- The trace-level provenance content: for every low final mint, a contiguous accepted chain
drawn from the history `tr` (a sublist), from a settled-or-seed ground, with the cascade/stall
ending.  This is the *operational* statement the acceptance history must establish; once it
holds, `ImprovementProvenance` follows by packaging (`improvementProvenance_of_traceProv`). -/
def TraceProv (e : CallEntry G s) (out : CallOut G s) (tr : Trace G s) : Prop :=
  ∀ m ∈ out.mints, m.val < out.B' →
    ∃ (ground : Fin G.n) (groundVal : WLab G s) (rs : Trace G s),
      List.Sublist rs tr ∧
        ContigFrom G s ground groundVal rs m.x m.val ∧
        ChainGround e out ground m.x ∧
        ProvenanceEnd out ground groundVal m

/-- **Extraction theorem**: a trace-level provenance certificate is a full
`ImprovementProvenance`.  The contiguous `RelaxStep` list is turned into an `ImproveChain` by
`chain_of_contigFrom`; the ground/ending are already the `ChainGround`/`ProvenanceEnd`
components.  This is the only place the acceptance-time history enters — once supplied, the
already-proved `lowMintNeedsStaleGround_of_provenance` and Lemma V follow for free. -/
theorem improvementProvenance_of_traceProv (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (tr : Trace G s) (hrun : Run t e out) (htr : TraceProv e out tr) :
    ImprovementProvenance t hrun := by
  intro m hm hlt
  obtain ⟨ground, groundVal, rs, _hsub, hcontig, hsource, hending⟩ := htr m hm hlt
  exact ⟨⟨ground, groundVal, chain_of_contigFrom hcontig, hsource, hending⟩⟩

/-! ## Full executions need no trace -/

/-- **Full executions are immune** (the full-execution regime): a drained `𝒟` means
the final iteration minted nothing, so `Prem = ∅` (`full_no_prem`) and there is no low mint to
witness — `ImprovementProvenance` holds vacuously with no acceptance history.  The top-level call
is always full (CORRECTED_PROOF §3, (E3)), so the head of the recursion is discharged here. -/
theorem improvementProvenance_of_full (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (h : Full t e out) : ImprovementProvenance t h.1 := by
  intro m hm hlt
  exact (full_no_prem t e out h m.x m.val ⟨hm, hlt⟩).elim

/-! ## Seed ground -/

/-- **A mint's key is a seed**: FindPivots' groups are subsets of `S` (FP2), the
residual groups only shrink along the loop (`iloop_pl_sub`), and every mint's key stays in its
residual group (`iloop_mints_pl`).  This is the `ChainGround.seedWalked` source — the fact that
justifies *choosing* a seed ground; the chain from that ground to the mint is the trace content
of `TraceProv`. -/
theorem mint_key_mem_seed (t : ℕ) (e : CallEntry G s) (out : CallOut G s) (h : Run t e out) :
    ∀ m ∈ out.mints, m.x ∈ e.S := by
  induction h with
  | base _hl _hb =>
      intro m hm
      exact absurd hm List.not_mem_nil
  | recur _hl hfp _hpiv hst0 hloop _hchildren _ih =>
      intro m hm
      obtain ⟨j, hpl⟩ := iloop_mints_pl t _ _ hloop
        (by
          intro m0 hm0
          rw [hst0, mkInit_mints] at hm0
          exact absurd hm0 List.not_mem_nil)
        _ hm
      have hfoP := iloop_pl_sub t _ _ hloop j hpl
      rw [hst0, mkInit_pl] at hfoP
      obtain ⟨_hpre, Y, _c', _st', hYsub, _hYne, _hcap, _hloopF, _hdF, _hW, _hpF, hP, _hQ⟩ := hfp
      rw [hP] at hfoP
      exact hYsub hfoP

/-! ## The one remaining operational obligation -/

/-- **`RunTraceCert`** — the named seam: every `Run` admits an acceptance history that certifies
the low mints (`TraceProv`).  This is not a syntactic extraction from `Run`; it is the content of
the audit's joint first-violation induction (CORRECTED_PROOF §8.1, PROOF.md §5: Lemma W/V/Rep,
the W′ drop lemma, the refusal-floor lemma), hand-proved there.
`improvementProvenance_of_runTraceCert` below reduces `ImprovementProvenance` to exactly this
seam. -/
def RunTraceCert (t : ℕ) : Prop :=
  ∀ (e : CallEntry G s) (out : CallOut G s), Run t e out → ∃ tr : Trace G s, TraceProv e out tr

/-- **Reduction**: `RunTraceCert ⇒ ImprovementProvenance` for every run.  Combining
`improvementProvenance_of_traceProv` with the existence of a certifying trace discharges the
extraction; the only unproved premise is the existence of the trace itself. -/
theorem improvementProvenance_of_runTraceCert (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (hrun : Run t e out) (hc : @RunTraceCert G s t) : ImprovementProvenance t hrun := by
  obtain ⟨tr, htr⟩ := hc e out hrun
  exact improvementProvenance_of_traceProv t e out tr hrun htr

end DMSY
end Frontier

import A4.LemmaV

/-!
# Frontier.DMSY.Provenance — improvement chains and the cascade/stall theorem

This is the provenance layer of PROOF.md §5, built above the big-step `Run` relation rather
than by changing its signature.  `ImproveChain` is a nonempty list of accepted relaxations.
Its links carry the source and target labels at acceptance time, so the existing walk order
proves that both the labels and their hop counts strictly increase.  In particular, a chain
cannot return to its ground label state, and the hop measure certifies strict finite progress.

`MintProvenance` ties such a chain to a low line-29 mint.  Its ground is either a settlement
echo in the call's transitive settlement log or an S-member; every later source is improved by
the preceding link by construction.  The operational ending has only the two possibilities
left by the hand proof: the cascade re-fires the chain and settles its target, or the ground
custody stalls in the returned structure.  A re-based cascade simply supplies the new chain
for the same current mint label.

`lowMintNeedsStaleGround_of_provenance` runs the two arms.  A stalled ground survives the last
pull with `B' ≤ b_f ≤ value`, while its chain gives `value < d[p] < B'` — an immediate
contradiction.  A cascade contradicts the unsettled-key part of `premShape_of_run`.  The only
remaining possibility is an incomplete settlement echo — precisely `LowMintNeedsStaleGround`.
No provenance fact is assumed about completeness: the stale event is exhibited from the ground
when it is incomplete.

The remaining operational extraction judgment is `ImprovementProvenance`: it supplies the
acceptance-time chain and its cascade/stall ending for every low mint.  The present big-step
`Run` does not record that history, so this file deliberately does not claim to extract it
from `Run` alone.  Once supplied, Lemma V and the strict returned bound are fully proved.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- One accepted relaxation, with its acceptance-time source and target labels. -/
inductive ImproveLink (G : Graph) (s : Fin G.n) :
    Fin G.n → Fin G.n → WLab G s → WLab G s → Prop
  | mk {u v : Fin G.n} {uv vv : WLab G s} (e : Fin G.m)
      (hs : G.src e = u) (ht : G.dst e = v) (hne : uv ≠ ⊤) (he : vv = ext uv e) :
      ImproveLink G s u v uv vv

namespace ImproveLink

/-- Every improvement link is strictly ascending in the full tuple order. -/
theorem value_lt {u v : Fin G.n} {uv vv : WLab G s}
    (h : ImproveLink G s u v uv vv) : uv < vv := by
  cases h with
  | mk e hs ht hne he =>
      rw [he]
      exact lt_ext_of_ne_top hne e

/-- The number of edges in a finite label; `⊤` is assigned zero and never occurs as a link
source.  This is only the induction measure, not the order used for correctness. -/
def rank (lab : WLab G s) : ℕ :=
  match lab with
  | ⊤ => 0
  | (p : WalkOrd G s) => (p : List (Fin G.m)).length

theorem rank_ext {lab : WLab G s} (hne : lab ≠ ⊤) (e : Fin G.m) :
    rank (ext lab e) = rank lab + 1 := by
  obtain ⟨p, rfl⟩ := WithTop.ne_top_iff_exists.mp hne
  change List (Fin G.m) at p
  change rank (ext ((toW p : WalkOrd G s) : WLab G s) e) =
    rank ((toW p : WalkOrd G s) : WLab G s) + 1
  rw [ext_coe]
  simp [rank, toW]

/-- Every improvement link strictly increases the hop measure. -/
theorem rank_lt {u v : Fin G.n} {uv vv : WLab G s}
    (h : ImproveLink G s u v uv vv) : rank uv < rank vv := by
  cases h with
  | mk e hs ht hne he =>
      rw [he, rank_ext hne e]
      exact Nat.lt_succ_self _

end ImproveLink

/-- A nonempty improvement chain.  Every non-ground source is the target of the preceding
link, hence is itself improved; only the ground needs the separate `ChainGround` inventory. -/
inductive ImproveChain (G : Graph) (s : Fin G.n) :
    Fin G.n → Fin G.n → WLab G s → WLab G s → Prop
  | last {u v : Fin G.n} {uv vv : WLab G s} (h : ImproveLink G s u v uv vv) :
      ImproveChain G s u v uv vv
  | cons {u v w : Fin G.n} {uv vv wv : WLab G s} (h : ImproveLink G s u w uv wv)
      (tail : ImproveChain G s w v wv vv) : ImproveChain G s u v uv vv

namespace ImproveChain

/-- The whole chain is tuple-strictly ascending. -/
theorem value_lt {u v : Fin G.n} {uv vv : WLab G s}
    (h : ImproveChain G s u v uv vv) : uv < vv := by
  induction h with
  | last h => exact h.value_lt
  | cons h tail ih => exact h.value_lt.trans ih

/-- The whole chain strictly increases its hop measure. -/
theorem rank_lt {u v : Fin G.n} {uv vv : WLab G s}
    (h : ImproveChain G s u v uv vv) : ImproveLink.rank uv < ImproveLink.rank vv := by
  induction h with
  | last h => exact h.rank_lt
  | cons h tail ih => exact h.rank_lt.trans ih

/-- No improvement chain can cycle back to the same vertex at the same label state. -/
theorem not_cycle {u : Fin G.n} {uv : WLab G s}
    (h : ImproveChain G s u u uv uv) : False :=
  (lt_irrefl _ h.value_lt)

end ImproveChain

/-- The two possible grounds of a low mint's improvement chain.  A seed ground is walked by
the chain itself; an echo ground names its settlement event in the call's transitive log. -/
inductive ChainGround (e : CallEntry G s) (out : CallOut G s) :
    Fin G.n → Fin G.n → Prop
  | echo {ground target : Fin G.n} (ev : SettlementEvent G)
      (hev : ev ∈ out.evts) (hvg : ev.v = ground) : ChainGround e out ground target
  | seedWalked {ground target : Fin G.n} (hg : ground ∈ e.S) : ChainGround e out ground target

/-- The two lower bounds earned by an entry that survives the last pull. -/
def CustodyFloor (B' bf value : WLab G s) : Prop :=
  B' ≤ bf ∧ bf ≤ value

/-- The operational result of forcing a chain-ground's custody.  `cascade` is the pull/echo
case: exact-tie relaxes re-fire down to the mint key.  `stall` is the survival case: the
ground's own value is still present and carries both last-pull floors. -/
inductive ProvenanceEnd (out : CallOut G s) (ground : Fin G.n) (groundVal : WLab G s)
    (m : Mint G s) : Prop
  | cascade (hset : m.x ∈ out.U) : ProvenanceEnd out ground groundVal m
  | stall {bf : WLab G s} (hD : out.D ground = some groundVal)
      (hfloor : CustodyFloor out.B' bf groundVal) : ProvenanceEnd out ground groundVal m

/-- The complete provenance certificate of one low mint: its chain, its ground inventory,
and the cascade/stall outcome.  This is operational evidence, not a stale-ground conclusion. -/
structure MintProvenance (e : CallEntry G s) (out : CallOut G s) (m : Mint G s) where
  ground : Fin G.n
  groundVal : WLab G s
  chain : ImproveChain G s ground m.x groundVal m.val
  source : ChainGround e out ground m.x
  ending : ProvenanceEnd out ground groundVal m

/-- The provenance layer above `Run`: every low final mint has an acceptance-time improvement
chain and a cascade/stall certificate.  Extracting this judgment from an instrumented run is
the only obligation left outside this file. -/
def ImprovementProvenance (t : ℕ) {e : CallEntry G s} {out : CallOut G s}
    (_hrun : Run t e out) : Prop :=
  ∀ m ∈ out.mints, m.val < out.B' → Nonempty (MintProvenance e out m)

/-- **Provenance theorem (cascade/stall).**  Every low final mint has an incomplete settlement
echo in its improvement-chain grounds.  The stall arm contradicts its two last-pull floors;
the cascade arm contradicts the mint key's unsettled shape. -/
theorem lowMintNeedsStaleGround_of_provenance (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (hrun : Run t e out) (hprov : ImprovementProvenance t hrun) : LowMintNeedsStaleGround out := by
  intro m hm hlt
  obtain ⟨⟨ground, groundVal, chain, source, ending⟩⟩ := hprov m hm hlt
  have handle : ProvenanceEnd out ground groundVal m →
      ∃ ev ∈ out.evts, ¬ Complete out.d' ev.v := by
    intro ending
    cases ending with
    | cascade hset =>
        exact ((premShape_of_run t e out hrun m.x m.val ⟨hm, hlt⟩).1 hset).elim
    | stall hD hfloor =>
        exact (not_lt_of_ge (hfloor.1.trans hfloor.2) (chain.value_lt.trans hlt)).elim
  cases source with
  | echo ev hev hvg =>
      by_cases hc : Complete out.d' ev.v
      · exact handle ending
      · exact ⟨ev, hev, hc⟩
  | seedWalked hg => exact handle ending

/-- First-violation form: complete earlier settlements rule out the sole remaining ground,
hence no low final mint exists. -/
theorem noLowMint_of_provenance (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (hrun : Run t e out) (hprov : ImprovementProvenance t hrun) (hreg : CompleteLog out) :
    ¬ LowMint out :=
  noLowMint_of_completeLog (lowMintNeedsStaleGround_of_provenance t e out hrun hprov) hreg

/-- **Lemma V from the provenance layer.**  The strict returned floor and carve-out emptiness
are proved without the former free `LowMintNeedsStaleGround` hypothesis. -/
theorem lemmaV_of_provenance (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (hrun : Run t e out) (hchildren : PremFreeChildren t hrun)
    (hprov : ImprovementProvenance t hrun) (hreg : CompleteLog out) :
    BoundClauseStrict out ∧ ∀ x val, ¬ out.Premature x val :=
  lemmaV_of_stale_ground t e out hrun hchildren
    (lowMintNeedsStaleGround_of_provenance t e out hrun hprov) hreg

end DMSY
end Frontier

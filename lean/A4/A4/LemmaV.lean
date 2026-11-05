import A4.Window

/-!
# Frontier.DMSY.LemmaV — the no-leak clause and its exact provenance seam

The mechanical part of PROOF.md §5 is proved here without a new axiom.  A low final mint is
precisely a member of `CallOut.Premature`; consequently the stale-ground step of the audit is
all that is needed to rule it out when every earlier settlement is complete.  The transitive
proposition then turns the absence of low mints into the strict returned-`𝒟` floor.

`LowMintNeedsStaleGround` is deliberately a predicate on a return, not an axiom: it is the
remaining provenance-chain obligation (the cascade/stall arms).  The present big-step `Run`
relation records labels and settlement logs but not improvement times or their source edges, so
that obligation cannot be discharged from the current state alone.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- A line-29 mint lying strictly below its call's returned bound. -/
def LowMint (out : CallOut G s) : Prop :=
  ∃ m : Mint G s, m ∈ out.mints ∧ m.val < out.B'

/-- Every settlement in a return log is complete at the return labels.  In the audit this is
supplied only for the prefix before the currently analysed batch; completeness persists, so the
same predicate can be used at the later return. -/
def CompleteLog (out : CallOut G s) : Prop :=
  ∀ ev ∈ out.evts, Complete out.d' ev.v

/-- The audit's Step-2 provenance conclusion: every low final mint has a stale settlement in its
improvement-chain grounds.  This is the precise cascade/stall obligation, rather than a restatement
of `LowMint` itself. -/
def LowMintNeedsStaleGround (out : CallOut G s) : Prop :=
  ∀ m ∈ out.mints, m.val < out.B' →
    ∃ ev ∈ out.evts, ¬ Complete out.d' ev.v

/-- A low mint is exactly a premature entry, with the mint bundled as a structure. -/
theorem lowMint_iff_exists_prem {out : CallOut G s} :
    LowMint out ↔ ∃ x val, out.Premature x val := by
  constructor
  · rintro ⟨m, hm, hlt⟩
    exact ⟨m.x, m.val, hm, hlt⟩
  · rintro ⟨x, val, hm, hlt⟩
    exact ⟨Mint.mk x val, hm, hlt⟩

/-- First-violation contradiction: the stale-ground escape is excluded by the complete-log
regime, hence no low final mint exists. -/
theorem noLowMint_of_completeLog {out : CallOut G s}
    (hground : LowMintNeedsStaleGround out) (hreg : CompleteLog out) : ¬ LowMint out := by
  rw [lowMint_iff_exists_prem]
  rintro ⟨x, val, hm, hlt⟩
  obtain ⟨ev, hev, hnc⟩ := hground (Mint.mk x val) hm hlt
  exact hnc (hreg ev hev)

theorem noPrem_of_noLowMint {out : CallOut G s} (h : ¬ LowMint out) :
    ∀ x val, ¬ out.Premature x val := by
  intro x val hp
  exact h (lowMint_iff_exists_prem.mpr ⟨x, val, hp⟩)

theorem noLowMint_of_noPrem {out : CallOut G s}
    (h : ∀ x val, ¬ out.Premature x val) : ¬ LowMint out := by
  rw [lowMint_iff_exists_prem]
  rintro ⟨x, val, hp⟩
  exact h x val hp

/-- The returned strict floor kills every premature entry, since every such entry is still in
the returned structure (`premInD_of_run`). -/
theorem noPrem_of_boundClauseStrict (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (hrun : Run t e out) (hbound : BoundClauseStrict out) :
    ∀ x val, ¬ out.Premature x val := by
  intro x val hp
  have hd := premInD_of_run t e out hrun x val hp
  exact (not_lt_of_ge (hbound x val hd)) hp.2

/-- Conversely, the transitive proposition upgrades absence of low mints to the strict floor;
only the final iteration needs the new argument because children are already Prem-free. -/
theorem boundClauseStrict_of_noLowMint (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (hrun : Run t e out) (hchildren : PremFreeChildren t hrun)
    (hno : ¬ LowMint out) : BoundClauseStrict out := by
  intro y val hy
  rcases transitive_prop t G s e out hrun hchildren y val hy with h | hp
  · exact h
  · exact (hno (lowMint_iff_exists_prem.mpr ⟨y, val, hp⟩)).elim

/-- **Lemma V, modulo precisely the provenance-ground seam.**  In the complete-settlement regime,
the audit's stale-ground conclusion gives both carve-out emptiness and the strict bound clause. -/
theorem lemmaV_of_stale_ground (t : ℕ) (e : CallEntry G s) (out : CallOut G s)
    (hrun : Run t e out) (hchildren : PremFreeChildren t hrun)
    (hground : LowMintNeedsStaleGround out) (hreg : CompleteLog out) :
    BoundClauseStrict out ∧ ∀ x val, ¬ out.Premature x val := by
  have hno := noLowMint_of_completeLog hground hreg
  exact ⟨boundClauseStrict_of_noLowMint t e out hrun hchildren hno,
    noPrem_of_noLowMint hno⟩

/-- The final-iteration mint floor needed by the loop-exit form of Lemma V. -/
def MintFloor {p : ℕ} (st : RState G s p) : Prop :=
  ∀ m ∈ st.mints, st.bp ≤ m.val

theorem ge_of_loopBoundInv {p : ℕ} {st : RState G s p}
    (hinv : LoopBoundInv st) (hmint : MintFloor st) : Ge st.bp st.D := by
  intro y val hy
  rcases hinv y val hy with h | hm
  · exact h
  · exact hmint (Mint.mk y val) hm

/-- Loop-exit Lemma V: once the final mints are floored, the existing mechanical enumeration
lifts the child bounds to `Ge st.bp st.D`, exactly the hypothesis consumed by W2. -/
theorem loopExit_floor {t l : ℕ} {B : WLab G s} {p : ℕ} {st stf : RState G s p}
    {qs : List (CallEntry G s × CallOut G s)} (hloop : ILoop t B l st qs stf)
    (hchildren : ∀ q ∈ qs, q.2.B' ≤ q.1.B ∧ BoundClauseStrict q.2)
    (hinit : LoopBoundInv st) (hmint : MintFloor stf) : Ge stf.bp stf.D :=
  ge_of_loopBoundInv (loopBoundInv_loop t B l hloop hchildren hinit) hmint

/-- Return-form companion at a tail: absence of low mints removes the sole right-hand alternative
in `tail_boundClause`. -/
theorem tail_boundClauseStrict {B : WLab G s} {S W : Finset (Fin G.n)}
    {p : ℕ} {st : RState G s p} (hinv : LoopBoundInv st)
    (hno : ¬ LowMint (callOut (tail B S W st))) :
    BoundClauseStrict (callOut (tail B S W st)) := by
  intro y val hy
  rcases tail_boundClause B S W st hinv y val hy with h | ⟨hm, hlt⟩
  · exact h
  · exact (hno ⟨Mint.mk y val, hm, hlt⟩).elim

end DMSY
end Frontier

import A4.Main
import A4.WDrop
import A4.Window
import A4.LemmaD
import A4.ExecutionFrame
import A4.Cascade
import A4.FrontierOrder
import A4.Provenance
import A4.FixStale
import A4.DrainedClauses

-- The units added after Main.  Importing them here makes `lake env lean A4/AxiomCheck.lean`
-- a whole-tree compile gate as well as an axiom printer: every proof unit must still
-- elaborate before any `#print axioms` below can answer.  (§Semantics/Structural/Transitive/
-- Size/LemmaV arrive transitively through Main and Provenance.)
import A4.Stall
import A4.Rep
import A4.ReachHyp
import A4.ReachInv
import A4.LoopFrontier
import A4.SettleSweep
import A4.RunTrace
import A4.SweepTrace
import A4.IStepTrace
import A4.WriterTrace
import A4.LastWriter
import A4.OriginTrace
import A4.ReturnClauses
import A4.BpMonotonicity
import A4.NonDrainedBp
import A4.LiveFloor
import A4.ValueBpChain
import A4.KeyLabFloor
import A4.MergeRepair
import A4.IdentityCover
import A4.LowKeyClosure
import A4.TailIdentity
import A4.LoopBInv
import A4.MintPreFloor
import A4.BelowSeparator
import A4.LeafFloor
import A4.JointAssembly
import A4.StepSplitFloor

/-!
# A4 axiom check — the verification protocol's kernel replay surrogate.

Expected axioms for every entry below: `propext`, `Classical.choice`, `Quot.sound` only
(no `sorryAx`, no extra axioms).  Run with `lake env lean A4/AxiomCheck.lean`.

**A4 status (honest, 2026-11-04):** the semantics, the local half, the transitive proposition,
and the size chapter (Lemma 3.8\* at weakened-but-true statements, Lemma R at the (E3)
certificate — see `A4.Size`) are complete and axiom-clean.  2026-11-04 (blocker chip): the
`ChildOf` witness tying landed with `reach_sound`/`reach_entry_sound`;
Lemma 3.6's pull instantiation (`istep_child_frontier`), Lemma 3.5's seed-size propagation
(`childOf_seed_size`, `childOf_seed_memCap`), and `BoundaryClosure`'s entry-level discharge
(`boundaryClosure_of_CallPre`) are proved and axiom-clean — the joint induction's child
preconditions are now mechanical.  The remaining seam is the audit's
joint first-violation induction (CORRECTED_PROOF §8.1: Lemma W/V/Rep, W′ drop, refusal-floor),
carried as `a4_joint`'s `sorry` and consumed by `lemma37Star`/`theoremT`/`a4_contract`.  The
top-level `top_exact_at` is now **proved** (no `sorry` of its own) from `a4_joint`/`theoremT`,
Lemma 3.1\* at base returns, and the weak label invariant `UnreachTop` — modulo the joint-chain
seam it consumes.  Its antecedents are the totality judgment `Total` and the (E3) guard's
full-execution delivery `TopFull` (under event semantics the guard counts duplicate
settlements, so `eventCap_lTop` alone cannot deliver no-overflow; the delivery rides the audit's
duplicate-excess bound and is pinned as a judgment).  Entries touching the seam report `sorryAx`;
everything else is axiom-clean.  Which is which is recorded next to each entry.
-/

-- axiom-clean (label monotonicity of the mechanical layers)
#print axioms Frontier.DMSY.relaxGate_le
#print axioms Frontier.DMSY.sweepEvts_le
#print axioms Frontier.DMSY.tail_le
#print axioms Frontier.DMSY.istep_le_of_child
#print axioms Frontier.DMSY.iloop_le

-- axiom-clean (bound law, entry honesty, mint bookkeeping, full-execution immunity)
#print axioms Frontier.DMSY.run_le_bound
#print axioms Frontier.DMSY.run_entry_honest
#print axioms Frontier.DMSY.premInD_of_run
#print axioms Frontier.DMSY.premShape_of_run
#print axioms Frontier.DMSY.full_no_prem
#print axioms Frontier.DMSY.transitive_prop

-- axiom-clean (labels stay walks through Run — the W′ drop lemma's `Sound` supply)
#print axioms Frontier.DMSY.run_walk
#print axioms Frontier.DMSY.top_run_sound

-- axiom-clean (tied ChildOf — sound labels at every Reach entry)
#print axioms Frontier.DMSY.reach_sound
#print axioms Frontier.DMSY.reach_entry_sound

-- axiom-clean (Lemma 3.6 at pulls: child frontier preconditions of the joint induction)
#print axioms Frontier.DMSY.mem_expand_of_pulled
#print axioms Frontier.DMSY.mem_expand_of_low_member
#print axioms Frontier.DMSY.istep_cover_accurate
#print axioms Frontier.DMSY.istep_child_frontier

-- axiom-clean (Lemma 3.5: seed-size propagation, pullCap + fpCap ≤ memCap at children)
#print axioms Frontier.DMSY.istep_seed_size
#print axioms Frontier.DMSY.iloop_children_seed_size
#print axioms Frontier.DMSY.childOf_seed_size
#print axioms Frontier.DMSY.pullCap_add_fpCap_le_memCap
#print axioms Frontier.DMSY.childOf_seed_memCap

-- axiom-clean (BoundaryClosure's entry-level discharge — the W′ drop lemma's closure supply)
#print axioms Frontier.DMSY.boundaryClosure_of_callPre
#print axioms Frontier.DMSY.boundaryClosure_of_CallPre

-- axiom-clean (Lemma W: W1/W3, and W2 conditional on the explicit Lemma-V floor)
#print axioms Frontier.DMSY.suspension_of_istep
#print axioms Frontier.DMSY.w1_suspended
#print axioms Frontier.DMSY.w3_basePull
#print axioms Frontier.DMSY.w2_wPrimeAppend
#print axioms Frontier.DMSY.window_basePull
#print axioms Frontier.DMSY.window_wPrimeAppend

-- axiom-clean (active execution frames: live floors, bound nesting, and the child-return merge)
#print axioms Frontier.DMSY.activeChild_of_istep
#print axioms Frontier.DMSY.executionFrame_of_istep
#print axioms Frontier.DMSY.ActiveChild.child_le_parent
#print axioms Frontier.DMSY.ExecutionFrame.live_window
#print axioms Frontier.DMSY.ActiveChild.mergeAtReturn_floor_of_run
#print axioms Frontier.DMSY.mergeAtReturn_of_istep

-- axiom-clean (provenance cascade: complementarity, structural entries, and upward transport)
#print axioms Frontier.DMSY.refusal_insert_gate
#print axioms Frontier.DMSY.oneStep_complementarity
#print axioms Frontier.DMSY.Fire.entry
#print axioms Frontier.DMSY.entryLE_mergeAtReturn
#print axioms Frontier.DMSY.entryLE_istep_of_child
#print axioms Frontier.DMSY.cascade_arm

-- axiom-clean (Lemma D: the W′ settler's final-label FindPivots pop and full-bound sweep)
#print axioms Frontier.DMSY.fLoop_pop_final
#print axioms Frontier.DMSY.fpRun_final_pop
#print axioms Frontier.DMSY.wPrime_sweep_drop

-- axiom-clean (Lemma d2: strict path measure, two-case cascade, and W′-filter exclusion)
#print axioms Frontier.DMSY.pathRank_lt_of_advance
#print axioms Frontier.DMSY.EchoOffer.advance
#print axioms Frontier.DMSY.d2Step_of_cases
#print axioms Frontier.DMSY.complete_or_lowCustody_of_d2Step
#print axioms Frontier.DMSY.complete_of_d2Step
#print axioms Frontier.DMSY.d2_no_incomplete_pass
#print axioms Frontier.DMSY.d2_no_incomplete_pass_of_cases

-- axiom-clean (size chapter: weakened Lemma 3.8* and the (E3) certificate of Lemma R)
#print axioms Frontier.DMSY.run_evts_le
#print axioms Frontier.DMSY.lemma38Star
#print axioms Frontier.DMSY.lemmaR

-- axiom-clean (Lemma V's provenance layer: strict chains and the cascade/stall induction)
#print axioms Frontier.DMSY.ImproveLink.value_lt
#print axioms Frontier.DMSY.ImproveLink.rank_lt
#print axioms Frontier.DMSY.ImproveChain.value_lt
#print axioms Frontier.DMSY.ImproveChain.rank_lt
#print axioms Frontier.DMSY.ImproveChain.not_cycle
#print axioms Frontier.DMSY.lowMintNeedsStaleGround_of_provenance
#print axioms Frontier.DMSY.noLowMint_of_provenance
#print axioms Frontier.DMSY.lemmaV_of_provenance

-- axiom-clean (★BM.15 FIX-STALE in `A4.Semantics.IStep`: the deletion's monotonicity lever and the
-- engine-level regressions — mirror `Keyed`/`LoopBoundInv`, clause (2c) at the shrunk key set, and
-- the negative pins showing the historical `MergePolicy.parent` clause admitting what `IStep` forbids)
#print axioms Frontier.DMSY.keyed_istepFS
#print axioms Frontier.DMSY.loopBoundInv_istepFS
#print axioms Frontier.DMSY.clause2c_shrunk_keys
#print axioms Frontier.DMSY.istepFS_no_settled_key
#print axioms Frontier.DMSY.istepFS_next_seeds_avoid_settled
#print axioms Frontier.DMSY.parent_step_admits_counterexample
#print axioms Frontier.DMSY.not_istep_key
#print axioms Frontier.DMSY.next_seeds_avoid_settled_fails_parent
#print axioms Frontier.DMSY.istepWith_fixStale_iff
#print axioms Frontier.DMSY.deleteSet_some_imp

-- joint-chain seam (CORRECTED_PROOF §8.1) — `sorryAx` until the audit chain is machine-checked
#print axioms Frontier.DMSY.a4_joint
#print axioms Frontier.DMSY.lemma37Star
#print axioms Frontier.DMSY.theoremT
#print axioms Frontier.DMSY.a4_contract

-- top-level exactness (proved; `sorryAx` only through the joint-chain seam above)
#print axioms Frontier.DMSY.run_unreach
#print axioms Frontier.DMSY.top_full_facts
#print axioms Frontier.DMSY.top_exact_at

/-! ## The drained-return clauses (A4.DrainedClauses)

The (2a) `progress` clause at a **drained** return, with the audit's item 5 (`BpChain`) removed
from it: `LoopProgB` replaces `LoopProg`+`BpChain` because `tailBP B st = B` whenever `st.D` is
empty (`tailBP_of_isEmpty`).  Everything below is axiom-clean; `a4_joint`/`theoremT` are
unchanged (still `sorryAx`) — see `A4.DrainedClauses`'s module docstring for the residue.
-/
#print axioms Frontier.DMSY.istep_Bprime_le_B
#print axioms Frontier.DMSY.mkInit_progB
#print axioms Frontier.DMSY.iloop_progB
#print axioms Frontier.DMSY.tail_progress_drained
#print axioms Frontier.DMSY.iloop_children_bound
#print axioms Frontier.DMSY.callOut_tail_progress_of_drained
#print axioms Frontier.DMSY.istep_bp_le_of_drained

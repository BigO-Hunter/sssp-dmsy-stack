import C.Bridge

/-!
# C axiom check — the verification protocol's kernel replay surrogate.

Expected axioms for every entry below: `propext`, `Classical.choice`, `Quot.sound` only
(no `sorryAx`, no extra axioms).  Run via `lake build C.AxiomCheck` (kept in the lib
roots, unlike A0–A4's convention: `lake env lean` is broken for this package because
`Frontier.CostCharging` resolves to A0's build dir first and its olean is not there).
Verified 2026-11-04: all 11 entries report exactly `[propext, Classical.choice, Quot.sound]`.

**C status (honest):** C1–C4 are complete as an *instantiation* — the engine-side seams are
hypothesis-structured records (`DmsyTree` law fields, `DmsyValid`, `DmsyPerCall`,
`TdmsyMenu`) and every reduction/summation/bridge step is proved.  There is not a single
`sorry` in the package.
-/

-- proved: engine-local growth laws (C1)
#print axioms Frontier.DMSY.istep_evts
#print axioms Frontier.DMSY.istep_B_le
#print axioms Frontier.DMSY.iloop_evts_mono
#print axioms Frontier.DMSY.iloop_child_evts_sub

-- proved: counting battery over the abstract CostCharging lemmas (C2)
#print axioms Frontier.DMSY.DmsyCounters.sum_J_le
#print axioms Frontier.DMSY.DmsyCounters.sum_Cr_le
#print axioms Frontier.DMSY.DmsyCounters.sum_U_le

-- proved: aggregation + bridge + re-settlement corollary (C4)
#print axioms Frontier.DMSY.total_cost_le
#print axioms Frontier.DMSY.total_le_Tdmsy
#print axioms Frontier.DMSY.menu_of_T0
#print axioms Frontier.DMSY.total_le_Tdmsy_T0

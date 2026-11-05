import A2.FPContract

/-!
# A2 axiom check — the verification protocol's kernel replay surrogate.

Expected axioms for every entry below: `propext`, `Classical.choice`, `Quot.sound` only
(no `sorryAx`, no extra axioms).  Run with `lake env lean A2/AxiomCheck.lean`.
-/

#print axioms Frontier.DMSY.fpRun_contract
#print axioms Frontier.DMSY.a2_contract
#print axioms Frontier.DMSY.fpRun_frontier_persist
#print axioms Frontier.DMSY.fpRun_pivot_cap
#print axioms Frontier.DMSY.fpRun_pull_invariant
#print axioms Frontier.DMSY.complete_of_drain

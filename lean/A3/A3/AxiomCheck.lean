import A3.PullLoop

/-!
# A3 axiom check — the verification protocol's kernel replay surrogate.

Expected axioms for every entry below: `propext`, `Classical.choice`, `Quot.sound` only
(no `sorryAx`, no extra axioms).  Run with `lake env lean A3/AxiomCheck.lean`.
-/

#print axioms Frontier.DMSY.pullRun_contract
#print axioms Frontier.DMSY.a3_contract
#print axioms Frontier.DMSY.pullRun_floor
#print axioms Frontier.DMSY.pullLoop_frontier
#print axioms Frontier.DMSY.pullLoop_bound
#print axioms Frontier.DMSY.pullSet_invariant

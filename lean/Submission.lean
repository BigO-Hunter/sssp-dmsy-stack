import D.Main
import D.Adapter

/-!
# Submission root — the corrected Duan–Mao–Shu–Yin directed SSSP entrypoint

The lane's submission entrypoint `Race.bound` (`D/D/Adapter.lean`): the verifier's
`BigOSpeedrun.DirectedSSSP.Bound` row `(1, 3/4, 1, 11/12, 0)` at `N = 2^16`, assembled
from `D/D/Bound.lean`'s `Frontier.DMSY.bound` (via the lane's `Bound`, D3, with
`D/Main.lean`'s time analysis feeding the adapter's dominance bridge).  The only
unproved input is `DInputs.hsp` — the DMSY body's sparse-clause specification
(package C + the joint `A4/Main.lean` seam).  Re-exported here at the repo root per
the lane's submission-entrypoint convention (cf. the3SUM/Catalan lanes).
-/

export Race (bound)

import A4.Provenance

/-!
# Frontier.DMSY.Stall — the custody-survival contradiction

`ImproveChain.value_lt` supplies the tuple-strict ascent and `ImproveChain.rank_lt` the
strictly increasing hop measure.  This module closes the stall arm: an unpulled chain-ground
custody entry survives the last pull with `B' ≤ b_f ≤ value`, but its improvement chain gives
`value < d[p] < B'`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-- An unpulled custody value survives the last pull with both lower floors intact. -/
def SurvivesLastPull (B' bf value : WLab G s) : Prop :=
  B' ≤ bf ∧ bf ≤ value

/-- **Stall arm.**  Tuple-strict improvement makes a surviving chain-ground custody entry
contradict the returned bound. -/
theorem stall_arm {B' bf : WLab G s} {ground target : Fin G.n} {value dp : WLab G s}
    (hsurvive : SurvivesLastPull B' bf value)
    (hchain : ImproveChain G s ground target value dp) (hdp : dp < B') : False := by
  have hfloor : B' ≤ value := hsurvive.1.trans hsurvive.2
  exact (not_lt_of_ge hfloor) (hchain.value_lt.trans hdp)

/-- No sub-`B'` chain-ground custody entry survives unpulled to the return. -/
theorem no_subBound_custody_survives {B' bf : WLab G s} {ground target : Fin G.n}
    {value dp : WLab G s} (hchain : ImproveChain G s ground target value dp)
    (hdp : dp < B') : ¬ SurvivesLastPull B' bf value := by
  intro hsurvive
  exact stall_arm hsurvive hchain hdp

end DMSY
end Frontier

import Frontier.DMSY.Interfaces

/-!
# Frontier.DMSY (A3) — the D-structure of Lemma 3.4 (insert/merge/deleteSet + PullSpec)

Work package **A3 (Pull)**.  The keyed keep-min store `DS` (A0's `Basic`) and the batched pull
primitive of Duan–Mao–Shu–Yin Lemma 3.4, by its stored values.  This file is the **pure
D-structure layer**: operation laws for `insert`/`merge`/`deleteSet`, the threshold extraction
(`belowKeys` + `deleteSet`), the pull judgment `pullRun` (A0's `A3` signature), and its proof
obligation `PullSpec` (`A3Contract`).  The pull-size clause of Lemma 3.4 is pinned here
(`pullRun`'s size conjunct, `PullSpec.size`); cost clauses are package C3's cost contract
(A0's `PullSpec` docstring); a coarse `pullCost` is carried per A0's operation table.

The engine-level pull subroutine (pull + settle + relax, key lemmas 1–3) is `A3.PullLoop`.

Conventions (A0): labels are walks (`WLab`), distinct vertices never share a finite label, the
relaxation is `ext`, `DS` is `Fin G.n → Option (WLab G s)` with keyed keep-min dedup.  The pull
separator discipline mirrors A1's `Loop.pull`: `x ≤ Bd`, rooted (`x = Bd` or `x` a stored value),
and a nonempty store pulls at least one key (the (E0) guard, CORRECTED_PROOF §2.1).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## D-structure operation laws (A0's `DS`, Lemma 3.4's `Insert`/`Merge`/`DeleteSet`) -/

namespace DS

/-- `mergeVal` on two present values keeps the minimum. -/
theorem mergeVal_some (a b : WLab G s) : mergeVal (some a) (some b) = some (min a b) := rfl

/-- `mergeVal` with an empty left slot. -/
theorem mergeVal_none_left (b : Option (WLab G s)) : mergeVal (none : Option (WLab G s)) b = b :=
  rfl

/-- `mergeVal` with an empty right slot. -/
theorem mergeVal_none_right (a : WLab G s) : mergeVal (some a) none = some a := rfl

/-- `mergeVal` never forgets a value. -/
theorem mergeVal_ne_none (a : Option (WLab G s)) (lam : WLab G s) :
    mergeVal a (some lam) ≠ none := by
  cases a with
  | none => show some lam ≠ none; simp
  | some μ => show some (min μ lam) ≠ none; simp

/-- `Insert` at its own key keeps the minimum of the old and new value. -/
theorem insert_self (D : DS G s) (y : Fin G.n) (lam : WLab G s) :
    insert D y lam y = mergeVal (D y) (some lam) := by
  unfold insert
  rw [Function.update_self]

/-- `Insert` spares other keys. -/
theorem insert_of_ne (D : DS G s) (y : Fin G.n) (lam : WLab G s) {z : Fin G.n} (hzy : z ≠ y) :
    insert D y lam z = D z := by
  unfold insert
  rw [Function.update_of_ne hzy]

/-- `Insert(y, λ)` keeps `y` keyed. -/
theorem mem_keys_insert (D : DS G s) (y : Fin G.n) (lam : WLab G s) : y ∈ keys (insert D y lam) := by
  simp only [keys, Set.mem_ofPred_eq]
  rw [insert_self]
  exact mergeVal_ne_none (D y) lam

/-- `Insert` never removes a key. -/
theorem keys_insert_le (D : DS G s) (y : Fin G.n) (lam : WLab G s) :
    keys D ⊆ keys (insert D y lam) := by
  intro z hz
  simp only [keys, Set.mem_ofPred_eq]
  by_cases hzy : z = y
  · rw [hzy, insert_self]
    exact mergeVal_ne_none (D y) lam
  · rw [insert_of_ne D y lam hzy]; exact hz

/-- `mergeVal` emptiness: both slots empty. -/
theorem mergeVal_eq_none_iff (a b : Option (WLab G s)) :
    mergeVal a b = none ↔ a = none ∧ b = none := by
  cases a with
  | none =>
    cases b with
    | none => simp [mergeVal_none_left]
    | some β => simp [mergeVal_none_left]
  | some α =>
    cases b with
    | none => simp [mergeVal_none_right]
    | some β => simp [mergeVal_some]

/-- `Merge` keeps the smaller stored value at every key. -/
theorem merge_eq (D D' : DS G s) (y : Fin G.n) :
    merge D D' y = mergeVal (D y) (D' y) := rfl

/-- `Merge(D')` keys both stores. -/
theorem merge_keys (D D' : DS G s) : keys (merge D D') = keys D ∪ keys D' := by
  ext y
  simp only [keys, Set.mem_ofPred_eq, Set.mem_union]
  rw [merge_eq]
  simp only [ne_eq, mergeVal_eq_none_iff]
  constructor
  · intro h
    by_cases hd : D y = none
    · by_cases hd' : D' y = none
      · exact absurd ⟨hd, hd'⟩ h
      · exact Or.inr hd'
    · exact Or.inl hd
  · intro h hc
    rcases h with h | h
    · exact h hc.1
    · exact h hc.2

/-- `Delete(y)` for `y ∈ T`. -/
theorem deleteSet_mem (D : DS G s) (T : Finset (Fin G.n)) (y : Fin G.n) (hy : y ∈ T) :
    deleteSet D T y = none := by
  show (if y ∈ T then none else D y) = none
  rw [if_pos hy]

/-- `Delete` spares keys outside `T`. -/
theorem deleteSet_of_notMem (D : DS G s) (T : Finset (Fin G.n)) (y : Fin G.n) (hy : y ∉ T) :
    deleteSet D T y = D y := by
  show (if y ∈ T then none else D y) = D y
  rw [if_neg hy]

/-- The extracted-entry equation of `PullSpec.rest`. -/
theorem deleteSet_eq (D : DS G s) (T : Finset (Fin G.n)) (y : Fin G.n) :
    deleteSet D T y = if y ∈ T then none else D y := rfl

/-- `DeleteSet` removes exactly `T`'s keys. -/
theorem deleteSet_keys (D : DS G s) (T : Finset (Fin G.n)) :
    keys (deleteSet D T) = keys D \ T := by
  ext y
  simp only [keys, deleteSet_eq, Set.mem_ofPred_eq, Set.mem_sdiff]
  by_cases hy : y ∈ T
  · rw [if_pos hy]
    simp [hy]
  · rw [if_neg hy]
    simp [hy]

end DS

/-! ## The threshold extraction (Lemma 3.4's pull, by its stored values) -/

open Classical in
/-- The keys of `D` whose stored value lies below the separator `x`. -/
noncomputable def belowKeys (D : DS G s) (x : WLab G s) : Finset (Fin G.n) :=
  (Finset.univ : Finset (Fin G.n)).filter fun y => ∃ v, D y = some v ∧ v < x

theorem mem_belowKeys {D : DS G s} {x : WLab G s} {y : Fin G.n} :
    y ∈ belowKeys (G := G) (s := s) D x ↔ ∃ v, D y = some v ∧ v < x := by
  unfold belowKeys
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ y, h⟩⟩

/-- **The pull judgment** (`A3Contract`'s `pullRun`): extract from `D` at separator `x`, returning
exactly the keys below `x` and the remainder, size-capped at `cap` (Lemma 3.4's pull-size clause
`|S'| ≤ M`; the A4 recursion passes `cap = pullCap t l`).  The separator discipline is A1's
`Loop.pull` shape batched: `x ≤ Bd` (the call bound), rooted (`x = Bd` or `x` a stored value),
and a nonempty store pulls at least one key (the (E0) guard of CORRECTED_PROOF §2.1 — the printed
pseudocode crashes on an empty pull). -/
def pullRun (cap : ℕ) (D : DS G s) (Bd : WLab G s) (S' : Finset (Fin G.n)) (x : WLab G s)
    (D' : DS G s) : Prop :=
  S' = belowKeys D x ∧ D' = DS.deleteSet D S' ∧ x ≤ Bd ∧
    (x = Bd ∨ ∃ y v, D y = some v ∧ x = v) ∧
    (DS.IsEmpty D ∨ ∃ y v, D y = some v ∧ v < x) ∧
    S'.card ≤ cap

theorem pullRun_pulled {cap : ℕ} {D : DS G s} {Bd : WLab G s} {S' : Finset (Fin G.n)}
    {x : WLab G s} {D' : DS G s} (h : pullRun cap D Bd S' x D') {y : Fin G.n} :
    y ∈ S' ↔ ∃ v, D y = some v ∧ v < x := by
  rw [h.1]
  exact mem_belowKeys

/-- **A3 contract (Lemma 3.4).**  Every pull satisfies `PullSpec`: the pulled set is exactly the
keys below the separator, pulled keys are removed, `x ≤ Bd`, a nonempty structure pulls at
least one key, and the pull honors its size cap. -/
theorem pullRun_contract {cap : ℕ} {D : DS G s} {Bd : WLab G s} {S' : Finset (Fin G.n)}
    {x : WLab G s} {D' : DS G s} (h : pullRun cap D Bd S' x D') : PullSpec cap D Bd S' x D' := by
  obtain ⟨hS', hD', hle, _hroot, havail, hsize⟩ := h
  refine ⟨?_, ?_, hle, ?_, hsize⟩
  · intro y
    rw [hS']
    exact mem_belowKeys
  · intro y
    rw [hD']
    exact DS.deleteSet_eq D S' y
  · intro hne
    rw [hS']
    rcases havail with hemp | ⟨y, v, hy, hlt⟩
    · obtain ⟨y, hy⟩ := hne
      exact absurd (hemp y) hy
    · exact ⟨y, mem_belowKeys.mpr ⟨v, hy, hlt⟩⟩

/-- **Key lemma 2 (D level) — bound invariant: no label below the separator.**  Every value
remaining after the pull is `≥ x`. -/
theorem pullRun_floor {cap : ℕ} {D : DS G s} {Bd : WLab G s} {S' : Finset (Fin G.n)}
    {x : WLab G s} {D' : DS G s} (h : pullRun cap D Bd S' x D') {y : Fin G.n} {v : WLab G s}
    (hy : D' y = some v) : x ≤ v := by
  obtain ⟨hS', hD', _, _, _, _⟩ := h
  rw [hD', DS.deleteSet_eq] at hy
  by_cases hyS : y ∈ S'
  · rw [if_pos hyS] at hy
    exact absurd hy (by simp)
  · rw [if_neg hyS] at hy
    by_contra hlt
    push_neg at hlt
    have hy' : y ∈ S' := hS' ▸ mem_belowKeys.mpr ⟨v, hy, hlt⟩
    exact absurd hy' hyS

/-- The pull judgment's size clause (`PullSpec.size`), the hypothesis the A4 recursion consumes
for the child seed-set bound. -/
theorem pullRun_size {cap : ℕ} {D : DS G s} {Bd : WLab G s} {S' : Finset (Fin G.n)}
    {x : WLab G s} {D' : DS G s} (h : pullRun cap D Bd S' x D') : S'.card ≤ cap := h.2.2.2.2.2

/-- **A3 interface theorem**: the pull judgment discharges `A3Contract`. -/
theorem a3_contract : @A3Contract G s pullRun :=
  fun cap D Bd S' x D' h => pullRun_contract h

/-! ## Cost (coarse; per-call inequalities are package C3's) -/

/-- Cost of one pull extraction (A0 operation table, coarse): two guard tests, one scan of the
key array (`|keys 𝒟| ≤ n` comparisons), one delete per pulled key, and one event append per
pulled key. -/
def pullCost (S' : Finset (Fin G.n)) : ℕ := 2 + G.n + 2 * S'.card

end DMSY
end Frontier

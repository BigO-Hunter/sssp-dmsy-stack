import A1.BaseCase

/-!
# Frontier.DMSY (A1) — the relaxation sweep of Algorithm 4

Work package **A1**.  Preservation lemmas for `relaxEdge`/`sweep` (A1.BaseCase): labels only
decrease and stay walks, `u`'s own label is untouched (self-loops are refused: a proper
extension is strictly larger, (O3), or the candidate is `⊤` and fails `< B`), the `D` store
keeps its keep-min freshness and its `< B` bound, keys only grow, and every accepted
candidate below `B` leaves the head's key present.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Labels as walks -/

/-- Unfolding `ext` on a label equal to a walk label. -/
theorem ext_eq_of_eq {d : Labels G s} {e : Fin G.m} {q : List (Fin G.m)}
    (hq : d (G.src e) = ((toW q : WalkOrd G s) : WLab G s)) :
    ext (d (G.src e)) e = ((toW (List.append q [e]) : WalkOrd G s) : WLab G s) := by
  rw [hq]
  exact ext_coe q e

/-- A label produced by `ext` and equal to a walk label is a walk to the head. -/
theorem isWalk_of_ext {d : Labels G s} (h : WalkInv d) {e : Fin G.m} {p : List (Fin G.m)}
    (hp : ext (d (G.src e)) e = ((toW p : WalkOrd G s) : WLab G s)) :
    G.IsWalk s (G.dst e) p := by
  by_cases htop : d (G.src e) = ⊤
  · rw [htop, ext_top] at hp
    exact absurd hp (Ne.symm WithTop.coe_ne_top)
  · obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp htop
    have hq' : d (G.src e) = ((toW (q : List (Fin G.m)) : WalkOrd G s) : WLab G s) := hq.symm
    have hwalk : G.IsWalk s (G.src e) (q : List (Fin G.m)) := h (G.src e) q hq'
    have hext := ext_eq_of_eq hq'
    have heq : ((toW (List.append q [e]) : WalkOrd G s) : WLab G s)
        = ((toW p : WalkOrd G s) : WLab G s) := by rw [← hext]; exact hp
    have hweq : toW (List.append q [e]) = toW p := WithTop.coe_inj.mp heq
    have heq' : List.append q [e] = p := hweq
    rw [← heq']
    exact walk_ext hwalk e rfl


/-- `mergeVal` on two present values keeps the minimum. -/
theorem mergeVal_some (a b : WLab G s) : DS.mergeVal (some a) (some b) = some (min a b) := rfl

/-- `mergeVal` with an empty left slot. -/
theorem mergeVal_none_left (b : Option (WLab G s)) : DS.mergeVal (none : Option (WLab G s)) b = b := rfl

/-- `mergeVal` with an empty right slot. -/
theorem mergeVal_none_right (a : WLab G s) : DS.mergeVal (some a) none = some a := rfl

/-- `mergeVal` never forgets a value. -/
theorem mergeVal_ne_none (a : Option (WLab G s)) (lam : WLab G s) :
    DS.mergeVal a (some lam) ≠ none := by
  cases a with
  | none => show some lam ≠ none; simp
  | some μ => show some (min μ lam) ≠ none; simp

/-! ## `relaxEdge` -/


theorem relaxEdge_le (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) (v : Fin G.n) :
    (relaxEdge B d D e).1 v ≤ d v := by
  unfold relaxEdge
  split_ifs with hh
  · have h : Function.update d (G.dst e) (ext (d (G.src e)) e) v ≤ d v := by
      by_cases hv : v = G.dst e
      · subst hv; rw [Function.update_self]; exact hh.1
      · rw [Function.update_of_ne hv]
    exact h
  · exact le_rfl

theorem relaxEdge_ne (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) {v : Fin G.n}
    (hv : v ≠ G.dst e) : (relaxEdge B d D e).1 v = d v := by
  unfold relaxEdge
  split_ifs with hh
  · have h : Function.update d (G.dst e) (ext (d (G.src e)) e) v = d v := by
      rw [Function.update_of_ne hv]
    exact h
  · rfl

/-- A self-loop is never accepted (its candidate is strictly larger than `d u`, or `⊤`), so
the tail's own label is untouched. -/
theorem relaxEdge_self (B : WLab G s) (d : Labels G s) (D : DS G s) {e : Fin G.m}
    (he : G.src e = G.dst e) : (relaxEdge B d D e).1 = d := by
  unfold relaxEdge
  split_ifs with hbad
  · exfalso
    rcases hbad with ⟨hle, hlt⟩
    by_cases htop : d (G.src e) = ⊤
    · rw [htop] at hlt
      exact absurd hlt (by simp)
    · have hgt : d (G.src e) < ext (d (G.src e)) e := lt_ext_of_ne_top htop e
      rw [he] at hle hgt
      exact absurd hle (not_le.mpr hgt)
  · rfl

theorem relaxEdge_walk (B : WLab G s) {d : Labels G s} {D : DS G s} (e : Fin G.m)
    (h : WalkInv d) : WalkInv (relaxEdge B d D e).1 := by
  unfold relaxEdge
  split_ifs with hh
  · intro v p hp
    have hp' : Function.update d (G.dst e) (ext (d (G.src e)) e) v
        = ((toW p : WalkOrd G s) : WLab G s) := hp
    by_cases hv : v = G.dst e
    · subst hv
      rw [Function.update_self] at hp'
      exact isWalk_of_ext h hp'
    · rw [Function.update_of_ne hv] at hp'
      exact h v p hp'
  · exact h

theorem relaxEdge_fresh (B : WLab G s) (d : Labels G s) {D : DS G s} (e : Fin G.m)
    (hfresh : ∀ y lam, D y = some lam → lam = d y) :
    ∀ y lam, (relaxEdge B d D e).2 y = some lam → lam = (relaxEdge B d D e).1 y := by
  unfold relaxEdge
  split_ifs with hh
  · intro y lam hy
    have hy' : DS.insert D (G.dst e) (ext (d (G.src e)) e) y = some lam := hy
    have hgoal : lam = Function.update d (G.dst e) (ext (d (G.src e)) e) y := by
      by_cases hye : y = G.dst e
      · subst hye
        rw [Function.update_self]
        rw [DS.insert, Function.update_self] at hy'
        cases hd : D (G.dst e) with
        | none =>
          rw [hd, mergeVal_none_left] at hy'
          exact (Option.some.inj hy').symm
        | some μ =>
          rw [hd, mergeVal_some] at hy'
          have hμ : μ = d (G.dst e) := hfresh _ _ hd
          have hle : ext (d (G.src e)) e ≤ μ := by rw [hμ]; exact hh.1
          have hmin : min μ (ext (d (G.src e)) e) = lam := Option.some.inj hy'
          rw [min_eq_right hle] at hmin
          exact hmin.symm
      · rw [Function.update_of_ne hye]
        have hins : DS.insert D (G.dst e) (ext (d (G.src e)) e) y = D y := by
          show Function.update D (G.dst e) _ y = _
          rw [Function.update_of_ne hye]
        rw [hins] at hy'
        exact hfresh y lam hy'
    exact hgoal
  · exact hfresh

theorem relaxEdge_below (B : WLab G s) (d : Labels G s) {D : DS G s} (e : Fin G.m)
    (hbelow : ∀ y lam, D y = some lam → lam < B) :
    ∀ y lam, (relaxEdge B d D e).2 y = some lam → lam < B := by
  unfold relaxEdge
  split_ifs with hh
  · intro y lam hy
    have hy' : DS.insert D (G.dst e) (ext (d (G.src e)) e) y = some lam := hy
    by_cases hye : y = G.dst e
    · subst hye
      rw [DS.insert, Function.update_self] at hy'
      cases hd : D (G.dst e) with
      | none =>
        rw [hd, mergeVal_none_left] at hy'
        have hlam : lam = ext (d (G.src e)) e := (Option.some.inj hy').symm
        rw [hlam]
        exact hh.2
      | some μ =>
        rw [hd, mergeVal_some] at hy'
        have hlam : lam = min μ (ext (d (G.src e)) e) := (Option.some.inj hy').symm
        rw [hlam]
        exact lt_of_le_of_lt (min_le_right μ (ext (d (G.src e)) e)) hh.2
    · have hins : DS.insert D (G.dst e) (ext (d (G.src e)) e) y = D y := by
        show Function.update D (G.dst e) _ y = _
        rw [Function.update_of_ne hye]
      rw [hins] at hy'
      exact hbelow y lam hy'
  · exact hbelow

theorem relaxEdge_keys (B : WLab G s) (d : Labels G s) {D : DS G s} (e : Fin G.m) :
    DS.keys D ⊆ DS.keys (relaxEdge B d D e).2 := by
  unfold relaxEdge
  split_ifs with hh
  · intro y hy
    by_cases hye : y = G.dst e
    · subst hye
      have hkey : DS.insert D (G.dst e) (ext (d (G.src e)) e) (G.dst e) ≠ none := by
        rw [DS.insert, Function.update_self]
        exact mergeVal_ne_none (D (G.dst e)) (ext (d (G.src e)) e)
      exact hkey
    · have hkey : Function.update D (G.dst e)
        (DS.mergeVal (D (G.dst e)) (some (ext (d (G.src e)) e))) y ≠ none := by
        rw [Function.update_of_ne hye]
        exact hy
      exact hkey
  · intro y hy; exact hy

/-- If a candidate is tight for the post-relaxation label and below `B`, it was accepted, so
the head's key is present. -/
theorem relaxEdge_relax_keys (B : WLab G s) (d : Labels G s) {D : DS G s} (e : Fin G.m)
    (htid : (relaxEdge B d D e).1 (G.dst e) = ext (d (G.src e)) e)
    (hlt : (relaxEdge B d D e).1 (G.dst e) < B) :
    (relaxEdge B d D e).2 (G.dst e) ≠ none := by
  unfold relaxEdge at htid hlt ⊢
  split_ifs at htid hlt ⊢ with hh
  · have hkey : DS.insert D (G.dst e) (ext (d (G.src e)) e) (G.dst e) ≠ none := by
      rw [DS.insert, Function.update_self]
      exact mergeVal_ne_none (D (G.dst e)) (ext (d (G.src e)) e)
    exact hkey
  · exfalso
    have htid' : d (G.dst e) = ext (d (G.src e)) e := htid
    have hlt' : d (G.dst e) < B := hlt
    apply hh
    constructor
    · rw [htid']
    · rw [← htid']; exact hlt'


/-- The tail's own label is untouched by a relaxation step from `u` (self-loops are refused;
other edges update a different vertex). -/
theorem relaxEdge_u (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) {u : Fin G.n}
    (hsrc : G.src e = u) : (relaxEdge B d D e).1 u = d u := by
  by_cases he : G.src e = G.dst e
  · rw [relaxEdge_self B d D he]
  · exact relaxEdge_ne B d D e (fun hge => he (hsrc.trans hge))

/-- Under `B`, the head's post-relaxation label is at most the candidate offered along `e`. -/
theorem relaxEdge_dst_le (B : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m) {u : Fin G.n}
    (hsrc : G.src e = u) (hlt : ext (d u) e < B) :
    (relaxEdge B d D e).1 (G.dst e) ≤ ext (d u) e := by
  unfold relaxEdge
  split_ifs with hh
  · have h : Function.update d (G.dst e) (ext (d (G.src e)) e) (G.dst e) ≤ ext (d u) e := by
      rw [Function.update_self]
      rw [hsrc]
    exact h
  · have hlt' : ext (d (G.src e)) e < B := by rw [hsrc]; exact hlt
    have hgt : d (G.dst e) < ext (d (G.src e)) e := by
      by_contra hn; push_neg at hn; exact hh ⟨hn, hlt'⟩
    rw [← hsrc]
    exact hgt.le

/-! ## `sweep` -/

/-- Every stored value after one relaxation step is either an old value or the candidate of
`e` (the head's new label). -/
theorem relaxEdge_vals (B : WLab G s) (d : Labels G s) {D : DS G s} (e : Fin G.m) :
    ∀ z μ, (relaxEdge B d D e).2 z = some μ →
      D z = some μ ∨ (G.dst e = z ∧ μ = ext (d (G.src e)) e) := by
  unfold relaxEdge
  split_ifs with hh
  · intro z μ hy
    have hy' : DS.insert D (G.dst e) (ext (d (G.src e)) e) z = some μ := hy
    by_cases hye : z = G.dst e
    · subst hye
      rw [DS.insert, Function.update_self] at hy'
      cases hd : D (G.dst e) with
      | none =>
        right
        rw [hd, mergeVal_none_left] at hy'
        exact ⟨rfl, (Option.some.inj hy').symm⟩
      | some ρ =>
        rw [hd, mergeVal_some] at hy'
        have hmin : min ρ (ext (d (G.src e)) e) = μ := Option.some.inj hy'
        by_cases hle : ρ ≤ ext (d (G.src e)) e
        · left
          have hμ : μ = ρ := by rw [← hmin]; exact min_eq_left hle
          rw [hμ]
        · right
          have hμ : μ = ext (d (G.src e)) e := by
            rw [← hmin]; exact min_eq_right (le_of_lt (lt_of_not_ge hle))
          exact ⟨rfl, hμ⟩
    · left
      have hins : DS.insert D (G.dst e) (ext (d (G.src e)) e) z = D z := by
        show Function.update D (G.dst e) _ z = _
        rw [Function.update_of_ne hye]
      rw [hins] at hy'
      exact hy'
  · intro z μ hy
    exact Or.inl hy

structure SweepInv (B : WLab G s) (u : Fin G.n) (d : Labels G s) (D : DS G s)
    (es : List (Fin G.m)) (d' : Labels G s) (D' : DS G s) : Prop where
  /-- labels only decrease -/
  le : ∀ v, d' v ≤ d v
  /-- labels stay walks -/
  walk : WalkInv d'
  /-- `u`'s label is untouched (every self-loop is refused) -/
  u_same : d' u = d u
  /-- entries stay fresh (`D y = some lam → lam = d y`) -/
  fresh : ∀ y lam, D' y = some lam → lam = d' y
  /-- entries stay below `B` -/
  below : ∀ y lam, D' y = some lam → lam < B
  /-- keys only grow -/
  keys : DS.keys D ⊆ DS.keys D'
  /-- relaxed out-edges of `u` below `B` are covered -/
  relax : ∀ e ∈ es, G.src e = u → ext (d u) e < B → d' (G.dst e) ≤ ext (d u) e
  /-- a tight candidate below `B` leaves the head's key present -/
  relax_keys : ∀ e ∈ es, G.src e = u → d' (G.dst e) = ext (d u) e → d' (G.dst e) < B →
    D' (G.dst e) ≠ none
  /-- stored values are old values or candidates of swept edges -/
  vals : ∀ z μ, D' z = some μ →
    D z = some μ ∨ ∃ e ∈ es, G.src e = u ∧ G.dst e = z ∧ μ = ext (d u) e

theorem sweep_inv (B : WLab G s) (u : Fin G.n) (d : Labels G s) (D : DS G s)
    (es : List (Fin G.m))
    (hwalk : WalkInv d) (hfresh : ∀ y lam, D y = some lam → lam = d y)
    (hbelow : ∀ y lam, D y = some lam → lam < B) :
    SweepInv B u d D es (sweep B u es d D).1 (sweep B u es d D).2 := by
  induction es generalizing d D with
  | nil =>
    exact ⟨fun _ => le_rfl, hwalk, rfl, hfresh, hbelow, fun _ hy => hy,
      fun e he => (List.not_mem_nil he).elim,
      fun e he => (List.not_mem_nil he).elim,
      fun z μ h => Or.inl h⟩
  | cons e es ih =>
    by_cases hsrc : G.src e = u
    · have hd1 : (if G.src e = u then (relaxEdge B d D e).1 else d) = (relaxEdge B d D e).1 := by
        rw [if_pos hsrc]
      have hd2 : (if G.src e = u then (relaxEdge B d D e).2 else D) = (relaxEdge B d D e).2 := by
        rw [if_pos hsrc]
      have hrec := ih (relaxEdge B d D e).1 (relaxEdge B d D e).2
        (relaxEdge_walk B e hwalk) (relaxEdge_fresh B d e hfresh) (relaxEdge_below B d e hbelow)
      have hu : (relaxEdge B d D e).1 u = d u := relaxEdge_u B d D e hsrc
      simp only [sweep, hd1, hd2]
      refine ⟨?_, hrec.walk, ?_, hrec.fresh, hrec.below, ?_, ?_, ?_, ?_⟩
      · intro v
        exact (hrec.le v).trans (relaxEdge_le B d D e v)
      · exact hrec.u_same.trans hu
      · exact (relaxEdge_keys B d e).trans hrec.keys
      · intro e' he' hsrc' hlt
        rcases List.mem_cons.mp he' with h | h
        · have h2 : e = e' := h.symm; subst h2
          have h1 : (relaxEdge B d D e).1 (G.dst e) ≤ ext (d u) e :=
            relaxEdge_dst_le B d D e hsrc hlt
          exact (hrec.le (G.dst e)).trans h1
        · have hlt' : ext ((relaxEdge B d D e).1 u) e' < B := by
            rw [hu]; exact hlt
          have h1 := hrec.relax e' h hsrc' hlt'
          rw [hu] at h1
          exact h1
      · intro e' he' hsrc' htid hlt
        rcases List.mem_cons.mp he' with h | h
        · have h2 : e = e' := h.symm; subst h2
          have hif : ext (d (G.src e)) e ≤ d (G.dst e) ∧ ext (d (G.src e)) e < B := by
            have hle1 : (sweep B u es (relaxEdge B d D e).1 (relaxEdge B d D e).2).1 (G.dst e)
                ≤ (relaxEdge B d D e).1 (G.dst e) := hrec.le (G.dst e)
            have h2 : (relaxEdge B d D e).1 (G.dst e) ≤ d (G.dst e) := relaxEdge_le B d D e _
            refine ⟨?_, ?_⟩
            · calc ext (d (G.src e)) e = ext (d u) e := by rw [hsrc]
                _ = (sweep B u es (relaxEdge B d D e).1 (relaxEdge B d D e).2).1 (G.dst e) :=
                  htid.symm
                _ ≤ (relaxEdge B d D e).1 (G.dst e) := hle1
                _ ≤ d (G.dst e) := h2
            · calc ext (d (G.src e)) e = ext (d u) e := by rw [hsrc]
                _ = (sweep B u es (relaxEdge B d D e).1 (relaxEdge B d D e).2).1 (G.dst e) :=
                  htid.symm
                _ < B := hlt
          have hk : (relaxEdge B d D e).2 (G.dst e) ≠ none := by
            unfold relaxEdge
            rw [if_pos hif]
            have hkey : DS.insert D (G.dst e) (ext (d (G.src e)) e) (G.dst e) ≠ none := by
              rw [DS.insert, Function.update_self]
              exact mergeVal_ne_none (D (G.dst e)) (ext (d (G.src e)) e)
            exact hkey
          exact hrec.keys hk
        · have htid' : (sweep B u es (relaxEdge B d D e).1 (relaxEdge B d D e).2).1 (G.dst e')
              = ext ((relaxEdge B d D e).1 u) e' := by
            rw [hu]; exact htid
          exact hrec.relax_keys e' h hsrc' htid' hlt
      · intro z μ hz
        rcases hrec.vals z μ hz with h | ⟨e', he', hs', hd', hm'⟩
        · rcases relaxEdge_vals B d e z μ h with h | ⟨hdz, hm⟩
          · exact Or.inl h
          · exact Or.inr ⟨e, List.mem_cons.mpr (Or.inl rfl), hsrc, hdz, by
              rw [hsrc] at hm; exact hm⟩
        · exact Or.inr ⟨e', List.mem_cons.mpr (Or.inr he'), hs', hd', by
            rw [← hu]; exact hm'⟩
    · have hd1 : (if G.src e = u then (relaxEdge B d D e).1 else d) = d := by
        rw [if_neg hsrc]
      have hd2 : (if G.src e = u then (relaxEdge B d D e).2 else D) = D := by
        rw [if_neg hsrc]
      have hrec := ih d D hwalk hfresh hbelow
      simp only [sweep, hd1, hd2]
      refine ⟨hrec.le, hrec.walk, hrec.u_same, hrec.fresh, hrec.below, hrec.keys, ?_, ?_, ?_⟩
      · intro e' he' hsrc' hlt
        have hmem : e' ∈ es := by
          rcases List.mem_cons.mp he' with h | h
          · have h2 : e = e' := h.symm; subst h2
            exact absurd hsrc' hsrc
          · exact h
        exact hrec.relax e' hmem hsrc' hlt
      · intro e' he' hsrc' htid hlt
        have hmem : e' ∈ es := by
          rcases List.mem_cons.mp he' with h | h
          · have h2 : e = e' := h.symm; subst h2
            exact absurd hsrc' hsrc
          · exact h
        exact hrec.relax_keys e' hmem hsrc' htid hlt
      · intro z μ hz
        rcases hrec.vals z μ hz with h | ⟨e', he', hs', hd', hm'⟩
        · exact Or.inl h
        · exact Or.inr ⟨e', List.mem_cons.mpr (Or.inr he'), hs', hd', hm'⟩

theorem sweep_u_same (B : WLab G s) (u : Fin G.n) (d : Labels G s) (D : DS G s)
    (es : List (Fin G.m)) (hwalk : WalkInv d) (hfresh : ∀ y lam, D y = some lam → lam = d y)
    (hbelow : ∀ y lam, D y = some lam → lam < B) :
    (sweep B u es d D).1 u = d u :=
  (sweep_inv B u d D es hwalk hfresh hbelow).u_same

end DMSY
end Frontier

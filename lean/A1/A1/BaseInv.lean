import A1.Sweep

/-!
# Frontier.DMSY (A1) — the Algorithm-4 loop invariant

Work package **A1**.  The invariant `BInv` maintained by the base-case loop, and its
preservation. The four corrected-lemma clauses of CORRECTED_PROOF §4.1 (Lemma 3.1*) are
assembled from it in `A1.BaseCorrect`.

The invariant packages exactly the standing facts the audit's proof rides on: label honesty
(`WalkInv`), Claim C, the frontier `⟨U, 𝒟⟩` for `Ũ(B, S)`, `keys 𝒟 ⊆ Ũ(B, S)` (the
*refusal-floor* argument, CORRECTED_PROOF §4.1(c) — via `utilde_of_relax` below), entry
freshness and the `< B` bound (I3/I4), settled labels below the running separator and below
every stored value (Lemma 3.1*(b)), settlement completeness, and the separator root
(`x = B ∨ keys 𝒟 ≠ ∅`, for the dichotomy).
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## Small helpers -/

/-- A label below any bound is finite, hence its vertex is reachable. -/
theorem reachable_of_dis_lt {v : Fin G.n} {B : WLab G s} (h : dis (s := s) v < B) :
    G.Reachable s v := by
  by_contra hn
  rw [dis_of_not_reachable hn] at h
  exact absurd h (by simp)

theorem settledSet_nil : settledSet ([] : List (SettlementEvent G)) = (∅ : Set (Fin G.n)) := by
  ext y
  simp [settledSet]

theorem settledSet_append (a b : List (SettlementEvent G)) :
    settledSet (a ++ b) = settledSet a ∪ settledSet b := by
  ext y
  simp only [settledSet, Set.mem_union, Set.mem_setOf_eq, List.mem_append]
  constructor
  · rintro ⟨ev, h | h, hv⟩
    · exact Or.inl ⟨ev, h, hv⟩
    · exact Or.inr ⟨ev, h, hv⟩
  · rintro (⟨ev, h, hv⟩ | ⟨ev, h, hv⟩)
    · exact ⟨ev, Or.inl h, hv⟩
    · exact ⟨ev, Or.inr h, hv⟩

theorem settledSet_cons (ev : SettlementEvent G) (evts : List (SettlementEvent G)) :
    settledSet (ev :: evts) = insert ev.v (settledSet evts) := by
  ext y
  simp only [Set.mem_insert_iff, settledSet, Set.mem_setOf_eq, List.mem_cons]
  constructor
  · rintro ⟨ev', h | h, hv⟩
    · exact Or.inl (by rw [← hv]; exact congrArg SettlementEvent.v h)
    · exact Or.inr ⟨ev', h, hv⟩
  · rintro (hy | ⟨ev', h, hv⟩)
    · exact ⟨ev, Or.inl rfl, hy.symm⟩
    · exact ⟨ev', Or.inr h, hv⟩

/-! ## `dMin` (A0's `Engine.dMin`) -/

theorem dMinAux_le (D : DS G s) (i : ℕ) (y : Fin G.n) (lam : WLab G s) (hy : y.1 < i)
    (h : D y = some lam) : dMinAux D i ≤ lam := by
  induction i with
  | zero => exact absurd hy (Nat.not_lt_zero _)
  | succ i ih =>
    show min ((if h : i < G.n then D ⟨i, h⟩ else none).getD ⊤) (dMinAux D i) ≤ lam
    by_cases hyi : y.1 = i
    · refine le_trans (min_le_left _ _) ?_
      have hi : i < G.n := by rw [← hyi]; exact y.isLt
      rw [dif_pos hi]
      have hfeq : (⟨i, hi⟩ : Fin G.n) = y := Fin.ext (id hyi.symm)
      rw [hfeq, h]
      exact le_rfl
    · exact le_trans (min_le_right _ _) (ih (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hy) hyi))

theorem dMin_le_of_mem (B : WLab G s) {D : DS G s} {y : Fin G.n} {lam : WLab G s}
    (h : D y = some lam) : dMin B D ≤ lam :=
  le_trans (min_le_right B (dMinAux D G.n)) (dMinAux_le D G.n y lam y.isLt h)

theorem dMinAux_eq_top {D : DS G s} (h : ∀ y, D y = none) (i : ℕ) : dMinAux D i = ⊤ := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have h1 : (if h : i < G.n then D ⟨i, h⟩ else none).getD ⊤ = (⊤ : WLab G s) := by
      split_ifs with hi
      · rw [h, Option.getD]
      · rw [Option.getD]
    show min ((if h : i < G.n then D ⟨i, h⟩ else none).getD ⊤) (dMinAux D i) = ⊤
    rw [h1, ih]
    exact min_self ⊤

theorem dMin_eq_of_isEmpty (B : WLab G s) {D : DS G s} (h : DS.IsEmpty D) : dMin B D = B := by
  show min B (dMinAux D G.n) = B
  rw [dMinAux_eq_top (fun y => h y) G.n]
  exact min_eq_left le_top

/-! ## The refusal-floor argument (CORRECTED_PROOF §4.1(c)) -/

/-- An accepted candidate below `B` out of a settled complete `u ∈ Ũ(B, S)` lands its head in
`Ũ(B, S)`: outside `Ũ`, Claim C forces the candidate to be the canonical walk (the
*refusal-floor* step), whose walk visits `S`; hence the head is in `Ũ` after all. -/
theorem utilde_of_relax {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    (hwalk : WalkInv d)
    (hclaim : ∀ v, dis (s := s) v < B → v ∉ Utilde B (S : Set (Fin G.n)) → Complete d v)
    {u z : Fin G.n} {e : Fin G.m} (hu : Complete d u) (huU : u ∈ Utilde B (S : Set (Fin G.n)))
    (hsrc : G.src e = u) (hz : G.dst e = z) (hlt : ext (d u) e < B) (hle : ext (d u) e ≤ d z) :
    z ∈ Utilde B (S : Set (Fin G.n)) := by
  obtain ⟨hduB, y₀, hy₀S, hy₀U⟩ := huU
  have hreachU : G.Reachable s u := reachable_of_dis_lt hduB
  have hcu : d u = ((toW (path (s := s) u) : WalkOrd G s) : WLab G s) := by
    rw [hu, dis_of_reachable hreachU]
  -- the candidate is the walk `path u ++ [e]`
  have hcand : ext (d u) e
      = ((toW (List.append (path (s := s) u) [e]) : WalkOrd G s) : WLab G s) := by
    conv_lhs => rw [hcu]
    exact ext_coe (path (s := s) u) e
  have hwalkz : G.IsWalk s z (List.append (path (s := s) u) [e]) := by
    have h1 : G.IsWalk s u (path (s := s) u) := (path_isMinWalk hreachU).1
    have h2 : G.IsWalk u z [e] := by
      have h3 := IsWalk.single e
      rw [hsrc, hz] at h3
      exact h3
    exact h1.append h2
  have hdis : dis (s := s) z ≤ ext (d u) e := by
    rw [hcand]
    exact dis_le_walk hwalkz
  have hzB : dis (s := s) z < B := lt_of_le_of_lt hdis hlt
  by_contra hzU
  have hcz : Complete d z := hclaim z hzB hzU
  have heq : ext (d u) e = dis (s := s) z :=
    le_antisymm (by rw [← hcz]; exact hle) hdis
  have hreachZ : G.Reachable s z := reachable_of_dis_lt hzB
  have hpe : ((toW (List.append (path (s := s) u) [e]) : WalkOrd G s) : WLab G s)
      = ((toW (path (s := s) z) : WalkOrd G s) : WLab G s) := by
    rw [← hcand, heq, dis_of_reachable hreachZ]
  have hweq : List.append (path (s := s) u) [e] = path (s := s) z :=
    WithTop.coe_injective (α := WalkOrd G s) hpe
  -- `y₀` stays on the canonical walk of `z`
  obtain ⟨R, hRu, hR⟩ := hy₀U.path_prefix
  have hy₀reach : G.Reachable s y₀ := hy₀U.reachable_left
  refine hzU ⟨hzB, y₀, hy₀S, ?_⟩
  refine ⟨hreachZ, path (s := s) y₀, List.append R [e], ?_,
    (path_isMinWalk hy₀reach).1, ?_⟩
  · rw [← hweq, hRu]
    exact List.append_assoc (path (s := s) y₀) R [e]
  · have h1 : G.IsWalk y₀ u R := hR
    have h2 : G.IsWalk u z [e] := by
      have h3 := IsWalk.single e
      rw [hsrc, hz] at h3
      exact h3
    exact h1.append h2

/-! ## The loop invariant -/

/-- The Algorithm-4 loop invariant at bound `B` for seed set `S` (CORRECTED_PROOF §2.1,
§4.1). -/
structure BInv (B : WLab G s) (S : Finset (Fin G.n)) (st : BState G s) : Prop where
  /-- labels are walks (hence sound) -/
  walk : WalkInv st.d
  /-- Claim C of the call precondition survives label lowering -/
  claim : ∀ v, dis (s := s) v < B → v ∉ Utilde B (S : Set (Fin G.n)) → Complete st.d v
  /-- `⟨U, 𝒟⟩` is a frontier for `Ũ(B, S)` -/
  frontier : IsFrontier st.d (Utilde B (S : Set (Fin G.n))) (settledSet st.evts) (DS.keys st.D)
  /-- keys of `𝒟` lie in `Ũ(B, S)` -/
  keys_sub : DS.keys st.D ⊆ Utilde B (S : Set (Fin G.n))
  /-- every settled vertex lies in `Ũ(B, S)` -/
  settledU : settledSet st.evts ⊆ Utilde B (S : Set (Fin G.n))
  /-- entries are fresh (I3): the stored value is the key's current label -/
  fresh : ∀ y lam, st.D y = some lam → lam = st.d y
  /-- entries lie below `B` (I4) -/
  below : ∀ y lam, st.D y = some lam → lam < B
  /-- every settled label is below the current separator -/
  sep : ∀ y ∈ settledSet st.evts, st.d y < st.x
  /-- every settled label is below every stored value -/
  vals : ∀ y ∈ settledSet st.evts, ∀ z lam, st.D z = some lam → st.d y < lam
  /-- settlements are complete at the current labels -/
  settledComplete : ∀ y ∈ settledSet st.evts, Complete st.d y
  /-- the separator is rooted: `x = B`, or `𝒟` still has keys -/
  xroot : st.x = B ∨ (DS.keys st.D).Nonempty
  /-- the separator never exceeds the bound -/
  xle : st.x ≤ B

theorem bInv_init {e : BaseIn G s} (h : ReachBase e) :
    BInv e.B e.S ⟨e.d, e.D, [], e.B⟩ := by
  obtain ⟨hcall, hinit⟩ := h
  have hkeys : DS.keys e.D = (e.S : Set (Fin G.n)) := by
    rw [hinit]
    exact initD_keys e.S e.d
  have hfrontier : IsFrontier e.d (Utilde e.B (e.S : Set (Fin G.n))) (settledSet ([] : List (SettlementEvent G))) (DS.keys e.D) := by
    rw [hkeys, settledSet_nil]
    exact hcall.frontier
  have hsub : DS.keys e.D ⊆ Utilde e.B (e.S : Set (Fin G.n)) := by
    intro y hy
    have hyS : y ∈ (e.S : Set (Fin G.n)) := by rw [← hkeys]; exact hy
    have hdis : dis (s := s) y < e.B := by
      have h1 : dis (s := s) y ≤ e.d y := (WalkInv.sound hcall.walk) y
      exact lt_of_le_of_lt h1 (hcall.inRange y hyS)
    exact ⟨hdis, y, hyS, onPath_self (reachable_of_dis_lt hdis)⟩
  have hfresh : ∀ y lam, e.D y = some lam → lam = e.d y := by
    intro y lam hy
    rw [hinit] at hy
    exact initD_fresh e.S e.d hy
  have hbelow : ∀ y lam, e.D y = some lam → lam < e.B := by
    intro y lam hy
    have hyS : y ∈ (e.S : Set (Fin G.n)) := by
      rw [hinit, initD_eq_some] at hy
      by_cases hh : y ∈ e.S
      · exact hh
      · rw [if_neg hh] at hy
        simp at hy
    have hlam : lam = e.d y := hfresh y lam hy
    rw [hlam]
    exact hcall.inRange y hyS
  have hvac : ∀ y, y ∈ settledSet ([] : List (SettlementEvent G)) → False := by
    intro y hy
    simp [settledSet] at hy
  refine ⟨hcall.walk, hcall.claimC, hfrontier, hsub, ?_, hfresh, hbelow, ?_, ?_, ?_, ?_, ?_⟩
  · intro y hy
    exact absurd hy (hvac y)
  · intro y hy
    exact absurd hy (hvac y)
  · intro y hy z lam hz
    exact absurd hy (hvac y)
  · intro y hy
    exact absurd hy (hvac y)
  · exact Or.inl rfl
  · exact le_rfl

/-- `Complete` unfolds to label = canonical label. -/
theorem complete_iff {d : Labels G s} {v : Fin G.n} :
    Complete d v ↔ d v = dis (s := s) v := Iff.rfl

/-- Completeness transports along label equalities at the vertex. -/
theorem Complete.of_eq {d d' : Labels G s} {v : Fin G.n} (h : Complete d v)
    (heq : d' v = d v) : Complete d' v :=
  complete_iff.mpr (by rw [heq]; exact complete_iff.mp h)

/-! ## Preservation -/

/-- Delete-set basics. -/
theorem deleteSet_eq (D : DS G s) (T : Finset (Fin G.n)) (y : Fin G.n) :
    DS.deleteSet D T y = if y ∈ T then none else D y := rfl

theorem deleteSet_none (D : DS G s) (T : Finset (Fin G.n)) (y : Fin G.n) (hy : y ∈ T) :
    DS.deleteSet D T y = none := by
  rw [deleteSet_eq, if_pos hy]

theorem deleteSet_of_notMem (D : DS G s) (T : Finset (Fin G.n)) (y : Fin G.n) (hy : y ∉ T) :
    DS.deleteSet D T y = D y := by
  rw [deleteSet_eq, if_neg hy]

theorem deleteSet_keys (D : DS G s) (u : Fin G.n) :
    DS.keys (DS.deleteSet D {u}) = DS.keys D \ ({u} : Set (Fin G.n)) := by
  ext y
  by_cases hyu : y = u
  · have hflip : u = y := hyu.symm; subst hflip
    simp [DS.keys, deleteSet_eq, Finset.mem_singleton]
  · simp [DS.keys, deleteSet_eq, Finset.mem_singleton, hyu]

/-- One pull iteration of Algorithm 4 preserves the loop invariant. -/
theorem bInv_step {B : WLab G s} {S : Finset (Fin G.n)} {t : ℕ} {st : BState G s}
    (h : BInv B S st) (u : Fin G.n) (lam x : WLab G s)
    (hne : ¬ DS.IsEmpty st.D) (hg : st.evts.length ≤ t ^ 3)
    (hu : st.D u = some lam)
    (hxgt : lam < x) (hxle : x ≤ B)
    (hxrest : ∀ y μ, y ≠ u → st.D y = some μ → x ≤ μ)
    (hxeq : x = B ∨ ∃ y μ, y ≠ u ∧ st.D y = some μ ∧ x = μ) :
    BInv B S (iter B u x st) := by
  have hlam : lam = st.d u := h.fresh u lam hu
  have huK : u ∈ DS.keys st.D := by
    show st.D u ≠ none
    rw [hu]
    simp
  -- `lam <` every other stored value (the separator's tail clause)
  have hmin : ∀ y μ, st.D y = some μ → lam ≤ μ := by
    intro y μ hy
    by_cases hyu : y = u
    · subst hyu
      rw [hu] at hy
      exact le_of_eq (Option.some.inj hy)
    · exact (lt_of_lt_of_le hxgt (hxrest y μ hyu hy)).le
  have hcu : Complete st.d u := by
    refine IsFrontier.complete_of_min (hF := h.frontier) (hY := h.keys_sub)
      (hsound := WalkInv.sound h.walk) (huK) ?_
    intro y' hy'
    obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.mp hy'
    have h2 : lam ≤ μ := hmin y' μ hμ
    rw [← hlam, ← h.fresh y' μ hμ]
    exact h2
  -- sweep facts (freshness/below survive the delete-set)
  have hDpre_none : DS.deleteSet st.D {u} u = none := by
    show (if u ∈ ({u} : Finset (Fin G.n)) then none else st.D u) = none
    rw [if_pos (by simp)]
  have hDpre_fresh : ∀ y lam, DS.deleteSet st.D {u} y = some lam → lam = st.d y := by
    intro y lam hy
    by_cases hyu : y = u
    · subst hyu
      rw [hDpre_none] at hy
      exact absurd hy (by simp)
    · have hy2 : (if y ∈ ({u} : Finset (Fin G.n)) then none else st.D y) = some lam := hy
      rw [if_neg (by simp [hyu])] at hy2
      exact h.fresh y lam hy2
  have hDpre_below : ∀ y lam, DS.deleteSet st.D {u} y = some lam → lam < B := by
    intro y lam hy
    by_cases hyu : y = u
    · subst hyu
      rw [hDpre_none] at hy
      exact absurd hy (by simp)
    · have hy2 : (if y ∈ ({u} : Finset (Fin G.n)) then none else st.D y) = some lam := hy
      rw [if_neg (by simp [hyu])] at hy2
      exact h.below y lam hy2
  have hsw := sweep_inv B u st.d (DS.deleteSet st.D {u}) (List.finRange G.m)
    h.walk hDpre_fresh hDpre_below
  have hmem : ∀ e : Fin G.m, e ∈ List.finRange G.m := List.mem_finRange
  -- write `d1`/`D1` for the post-sweep store (defeq to the `iter` projections)
  set d1 : Labels G s := (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).1 with hd1
  set D1 : DS G s := (sweep B u (List.finRange G.m) st.d (DS.deleteSet st.D {u})).2 with hD1
  have hiterd : (iter B u x st).d = d1 := rfl
  have hiterD : (iter B u x st).D = D1 := rfl
  have hd1u : d1 u = st.d u := hsw.u_same
  have hSU : settledSet ((iter B u x st).evts) = (settledSet st.evts : Set (Fin G.n)) ∪ {u} := by
    show settledSet (st.evts ++ [⟨.basePull, u⟩]) = _
    rw [settledSet_append, settledSet_cons, settledSet_nil]
    simp
  have huU : u ∈ Utilde B (S : Set (Fin G.n)) := h.keys_sub huK
  refine ⟨?_, ?_, ?_, ?_, ?_, hsw.fresh, hsw.below, ?_, ?_, ?_, ?_, ?_⟩
  · -- labels stay walks
    show WalkInv (iter B u x st).d
    rw [hiterd]
    exact hsw.walk
  · -- Claim C survives lowering
    intro v hv hnv
    show Complete (iter B u x st).d v
    rw [hiterd]
    exact Complete.of_le (h.claim v hv hnv) (WalkInv.sound hsw.walk) (hsw.le v)
  · -- frontier `⟨U, 𝒟⟩`
    have hZ : ∀ z ∈ ({u} : Set (Fin G.n)), Complete d1 z := by
      intro z hz
      have hzu : z = u := hz
      subst hzu
      exact Complete.of_eq hcu hd1u
    have hrelax : ∀ e, G.src e ∈ ({u} : Set (Fin G.n)) → ext (d1 (G.src e)) e < B →
        d1 (G.dst e) ≤ ext (d1 (G.src e)) e := by
      intro e he hlt
      have hs : G.src e = u := he
      rw [hs, hd1u] at hlt
      have h1 := hsw.relax e (hmem e) hs hlt
      rw [hs, hd1u]
      exact h1
    have hstep := IsFrontier.step (hF := h.frontier)
      (hU := fun v hv => hv.1)
      (hsound := WalkInv.sound hsw.walk) (hle := hsw.le) (hZ := hZ) (hrelax := hrelax)
    have hkeys' : ((DS.keys st.D \ ({u} : Set (Fin G.n))) ∪ Relaxed d1 B ({u} : Set (Fin G.n)))
        ⊆ DS.keys D1 := by
      rintro z (hz | hz)
      · have hzp : z ∈ DS.keys (DS.deleteSet st.D {u}) := by
          show DS.deleteSet st.D {u} z ≠ none
          show (if z ∈ ({u} : Finset (Fin G.n)) then none else st.D z) ≠ none
          rw [if_neg (by simpa using hz.2)]
          exact hz.1
        exact hsw.keys hzp
      · obtain ⟨hzu, e, hs, hd, htid, hlt⟩ := hz
        have hs' : G.src e = u := hs
        rw [← hd, hs', hd1u] at htid
        rw [← hd] at hlt
        have hk := hsw.relax_keys e (hmem e) hs' htid hlt
        show D1 z ≠ none
        rw [← hd]
        exact hk
    show IsFrontier (iter B u x st).d (Utilde B (S : Set (Fin G.n)))
      (settledSet (iter B u x st).evts) (DS.keys (iter B u x st).D)
    rw [hiterd, hiterD, hSU]
    exact IsFrontier.mono (hF := hstep) (hU := Set.Subset.refl _)
      (hX := Set.Subset.refl _) (hY := hkeys')
  · -- keys stay in `Ũ(B, S)`
    intro z hz
    show z ∈ Utilde B (S : Set (Fin G.n))
    obtain ⟨μ, hμ⟩ := Option.ne_none_iff_exists'.mp hz
    have hμ' : D1 z = some μ := hμ
    rcases hsw.vals z μ hμ' with hpre | ⟨e, he, hs, hd, hm⟩
    · by_cases hzu : z = u
      · subst hzu
        rw [hDpre_none] at hpre
        exact absurd hpre (by simp)
      · have hpre2 : (if z ∈ ({u} : Finset (Fin G.n)) then none else st.D z) = some μ := hpre
        rw [if_neg (by simp [hzu])] at hpre2
        have hK : z ∈ DS.keys st.D := by
          show st.D z ≠ none
          rw [hpre2]
          simp
        exact h.keys_sub hK
    · -- swept-in key: the stored value is the candidate (freshness), which is a
      -- walk out of `u ∈ Ũ` below `B` and at most `d z` — the refusal-floor argument
      have hfd : d1 z = μ := (hsw.fresh z μ hμ').symm
      have hle : ext (st.d u) e ≤ st.d z := by
        rw [← hm, ← hfd]
        exact hsw.le z
      have hltB : ext (st.d u) e < B := by
        rw [← hm]
        exact hsw.below z μ hμ'
      exact utilde_of_relax h.walk h.claim hcu huU hs hd hltB hle
  · -- settled vertices lie in `Ũ(B, S)`
    intro y hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · exact h.settledU hy
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      exact huU
  · -- settled labels below the new separator
    have hun : ∀ y ∈ settledSet st.evts, d1 y = st.d y := by
      intro y hy
      exact le_antisymm (hsw.le y)
        (by rw [complete_iff.mp (h.settledComplete y hy)]; exact (WalkInv.sound hsw.walk) y)
    intro y hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · rw [hiterd, hun y hy]
      exact lt_trans (h.vals y hy u lam hu) hxgt
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      show (iter B u x st).d u < x
      rw [hiterd, hd1u, ← hlam]
      exact hxgt
  · -- settled labels below stored values
    have hun : ∀ y ∈ settledSet st.evts, d1 y = st.d y := by
      intro y hy
      exact le_antisymm (hsw.le y)
        (by rw [complete_iff.mp (h.settledComplete y hy)]; exact (WalkInv.sound hsw.walk) y)
    intro y hy z μ hz
    rw [hSU] at hy
    have hμ2 : D1 z = some μ := hz
    rcases hsw.vals z μ hμ2 with hpre | ⟨e, he, hs, hd, hm⟩
    · -- old stored value: strictly above every settled label
      by_cases hzu : z = u
      · subst hzu
        rw [hDpre_none] at hpre
        exact absurd hpre (by simp)
      · have hpre2 : (if z ∈ ({u} : Finset (Fin G.n)) then none else st.D z) = some μ := hpre
        rw [if_neg (by simp [hzu])] at hpre2
        rcases hy with hy | hy
        · rw [hiterd, hun y hy]
          exact h.vals y hy z μ hpre2
        · have hyu : y = u := hy
          have hflip : u = y := hyu.symm; subst hflip
          rw [hiterd, hd1u, ← hlam]
          exact lt_of_lt_of_le hxgt (hxrest z μ hzu hpre2)
    · -- candidate value: above `lam`, hence above every settled label
      rcases hy with hy | hy
      · rw [hiterd, hun y hy]
        calc st.d y < lam := h.vals y hy u lam hu
          _ < ext lam e := lt_ext_of_ne_top (ne_of_lt (lt_of_lt_of_le hxgt le_top)) e
          _ = ext (st.d u) e := congrArg (fun a : WLab G s => ext a e) hlam
          _ = μ := hm.symm
      · have hyu : y = u := hy
        have hflip : u = y := hyu.symm; subst hflip
        rw [hiterd, hd1u, ← hlam, hm, ← hlam]
        exact lt_ext_of_ne_top (ne_of_lt (lt_of_lt_of_le hxgt le_top)) e
  · -- settlement completeness
    intro y hy
    rw [hSU] at hy
    rcases hy with hy | hy
    · exact Complete.of_le (h.settledComplete y hy) (WalkInv.sound hsw.walk) (hsw.le y)
    · have hyu : y = u := hy
      have hflip : u = y := hyu.symm; subst hflip
      exact Complete.of_eq hcu hd1u
  · -- separator root
    rcases hxeq with hxe | ⟨y, μ, hyu, hyD, hxe⟩
    · exact Or.inl hxe
    · right
      refine ⟨y, ?_⟩
      show D1 y ≠ none
      have hzp : DS.deleteSet st.D {u} y ≠ none := by
        show (if y ∈ ({u} : Finset (Fin G.n)) then none else st.D y) ≠ none
        rw [if_neg (by simp [hyu])]
        rw [hyD]
        simp
      exact hsw.keys hzp
  · exact hxle


/-- The invariant holds at every state the loop reaches. -/
theorem loop_bInv {B : WLab G s} {S : Finset (Fin G.n)} {t : ℕ} :
    ∀ {c : ℕ} {st st' : BState G s}, Loop t B c st st' → BInv B S st → BInv B S st' := by
  intro c st st' h
  induction h with
  | exit h => intro hB; exact hB
  | pull u lam x hne hg hu hxgt hxle hxrest hxeq hrest ih =>
    intro hB
    exact ih (bInv_step hB u lam x hne hg hu hxgt hxle hxrest hxeq)

end DMSY
end Frontier

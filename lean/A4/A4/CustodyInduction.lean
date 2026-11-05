import A4.PremLabelKey

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.CustodyInduction — the SSSP custody obligation: refuted, corrected, harnessed

`A4.PremLabelKey` left two custody obligations, `NoCompleteKey` and `StoreTight`, to be proved
by a well-founded induction on the level `l`.  This file settles them, and the answer is
negative for both *as stated*: they are **false on reachable states**, at the very first state
the engine enters at the top-level call — the BM.8 initial loop state `mkInit` of
`Run.recur` at `Reach.top` (`hst0`).  The mechanism is the same for both, and it is not an
accident of the counterexample: the FindPivots search (A2) writes labels that `mkInit`'s
pivot-keyed store does not key.

## 1. The reachable counterexample

* `NoCompleteKey (mkInit.d) (mkInit.D)` — **refuted unconditionally**.  At the top entry
  `⟨⊤, {s}, lTop t G.n, initLabels G s⟩` the FindPivots output has `p = 1` with the single
  group `Y = {s}` (the gate set is a nonempty subset of the seed set `{s}`), so the pivot
  selection `hpiv` of `Run.recur` forces every pivot to be the source.  `mkInit` keys each
  pivot **at its own label** (`initD'_self`), and the entry label at `s` is `initLabels s =
  dis s`, which the FindPivots contract (`FPContract.le` + `FPContract.walk`) pins exactly:
  `fo.d' s = dis s`.  So `s` is a key carrying a *complete* label — `noCompleteKey_refuted_at_top_init`.
* `StoreTight ⊤ (mkInit …)` — **refuted under the explicit discovery hypothesis**
  `∃ y ≠ s, fo.d' y ≠ ⊤`.  `mkInit` keys only the gate set `Y = {s}`, so any other vertex whose
  label the search lowered below `⊤` is an unsettled low label with **no key at all**
  (`storeTight_refuted_at_top_init`; the empty log excludes nothing, `settledSet [] = ∅`).
  Semantically the hypothesis holds whenever `s` has an out-edge: the search's own `relaxGate`
  at the top call's bound `⊤` accepts the finite candidate `ext (fo.d' s) e < ⊤` at the head,
  and `FPContract.le` shows the final label stayed below `⊤`.

So the level-`l` induction harness **cannot be initialized** with either obligation: the base
state of the top call refutes both.

## 2. The minimal corrected custody invariant

The clause the engine's own algebra actually supports, and the one that survives the
counterexample state, is **`FreshCompleteKey`**:

  `∀ y val, st.D y = some val → Complete st.d y → val = st.d y`

*a complete key is keyed at its own label* — the store never presents a complete label at a
stale value.  At the refuting state it holds (the source key carries exactly its label; the
undiscovered vertices carry no key at all), and:

* it **initializes**: `freshCompleteKey_mkInit` — `mkInit`'s store is keyed by construction
  (`initD'_self`), so the corrected invariant costs nothing at BM.8;
* it **is the exact residue of ConeClosure §3's table**: `staleIncomplete_of_fresh` turns it
  into "a key at or above a threshold is incomplete below that threshold", and
  `keyCone_of_istep_fresh` closes the table's stale-body row — the row that motivated
  `NoCompleteKey` — with **no** `LabelKey`;
* it is **preserved** by the engine's own merge/pull/insert/sweep algebra:
  `freshCompleteKey_merge` (the keep-min repairs a re-keyed vertex), `freshCompleteKey_deleteSet`,
  `freshCompleteKey_insert_own`, and the settlement sweeps.

## 3. The level-`l` harness, and the one honest carrier

The harness itself is proved: `returnCustody_of_run` runs well-founded induction on the level
`l` over `Run`, threading `FreshCompleteKey` from the base law (proved: `returnCustody_base`,
from `A1.BaseInv`'s entry freshness) through the loop (`iloop_freshCompleteKey`, the step law
`freshCompleteKey_istep_of_carry`) into the tail (proved: `freshCompleteKey_tail`, BM.25/BM.28
insert at the current label).  The step law needs exactly one cross-call premise — `KeyCarry`:

  a parent key the child returns **no** key for keeps its label
  (`fo'.d' y = val` whenever `st.D y = some val` and `fo'.D y = none`).

That is the store form of the label-provenance link `A4.OriginTrace` names as the lane's open
descent gap: on the repaired engine a child label drop is accompanied by a store write
(`relaxGate_write_key`) or ends in a settlement (★BM.15 deletes the parent's stale key with the
child's), but the lane has no `Run`-level lemma stating it, and this file does not assume it —
it is carried as the typed hypothesis `KeyCarry`, never as an axiom.

## 4. `a4_joint` status (honest)

`a4_joint` **does not close** here, and the reason is now exact.  What the corrected custody
closes is the *stale-body row* of the cone leaf (`keyCone_of_istep_fresh`, conditional only on
`FreshCompleteKey` + Claim C + the child's bound law).  What it does **not** close is
`LabelKey`'s live half (`StepSplit`'s `hcover`): low-label⇒keyed is `StoreTight`, which §1
refutes at the initial state in its global form; its surviving content is the `KeyCarry`-
restricted form (`mem_childS_of_key_below` needs a low *stored value*, i.e. a vertex whose
label write was keyed).  The remaining `Lemma37Concl` clauses ride the same joint induction as
before (`BpChain`, settled completeness, `LoopBoundInv` at the children — `A4.ReturnClauses`'s
conditional theorems), so `Main.lean`'s two `sorry`s stay, and with them the D-side adapter
obligation `DInputs.hsp` is **not** the only one left.

No `sorry`/`admit`, no new axiom, `a4_joint` not assumed, no peer file modified.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. The BM.8 initial store keys its pivots at their own labels -/

/-- The fold of BM.7's inserts: every key of the accumulated store is a processed pivot, stored
at its own label; and every processed pivot is keyed at its own label. -/
theorem initD'_fold_spec (d : Labels G s) {p : ℕ} (piv : Fin p → Fin G.n) :
    ∀ (js : List (Fin p)) (D : DS G s) (pre : List (Fin p)),
      (∀ y val, D y = some val → ∃ j ∈ pre, y = piv j ∧ val = d (piv j)) →
      (∀ j ∈ js, (js.foldl (fun D j => DS.insert D (piv j) (d (piv j))) D) (piv j)
        = some (d (piv j))) ∧
      (∀ y val, (js.foldl (fun D j => DS.insert D (piv j) (d (piv j))) D) y = some val →
        ∃ j ∈ pre ++ js, y = piv j ∧ val = d (piv j)) := by
  have hne : ∀ (ks : List (Fin p)) (E : DS G s) (y : Fin G.n), E y ≠ none →
      (ks.foldl (fun D j => DS.insert D (piv j) (d (piv j))) E) y ≠ none := by
    intro ks
    induction ks with
    | nil => intro E y hy; exact hy
    | cons k ks ih =>
      intro E y hy
      by_cases hyk : y = piv k
      · rw [hyk]
        show (ks.foldl _ (DS.insert E (piv k) (d (piv k))) (piv k)) ≠ none
        apply ih
        rw [DS.insert_self]
        cases hE : E (piv k) with
        | none => rw [DS.mergeVal_none_left]; exact Option.some_ne_none _
        | some μ => rw [DS.mergeVal_some]; exact Option.some_ne_none _
      · show (ks.foldl _ (DS.insert E (piv k) (d (piv k))) y) ≠ none
        apply ih
        show DS.insert E (piv k) (d (piv k)) y ≠ none
        rw [DS.insert_of_ne E (piv k) _ hyk]
        exact hy
  intro js
  induction js with
  | nil =>
    intro D pre hD
    refine ⟨fun j hj => absurd hj (by simp), ?_⟩
    intro y val hy
    obtain ⟨j₀, hj₀, hyj₀, hval₀⟩ := hD y val hy
    rw [List.append_nil]
    exact ⟨j₀, hj₀, hyj₀, hval₀⟩
  | cons x xs ih =>
    intro D pre hD
    rw [List.foldl_cons]
    have hD₁ : ∀ y val, (DS.insert D (piv x) (d (piv x))) y = some val →
        ∃ j ∈ pre ++ [x], y = piv j ∧ val = d (piv j) := by
      intro y val hy
      by_cases hyx : y = piv x
      · rw [hyx, DS.insert_self] at hy
        cases hacc : D (piv x) with
        | none =>
          rw [hacc, DS.mergeVal_none_left] at hy
          refine ⟨x, List.mem_append_right _ (List.mem_singleton_self _), hyx,
            (Option.some.inj hy).symm⟩
        | some val₀ =>
          rw [hacc, DS.mergeVal_some] at hy
          obtain ⟨j₀, hj₀, hyj₀, hval₀⟩ := hD (piv x) val₀ hacc
          have hv' : val = d (piv j₀) ∨ val = d (piv x) := by
            left
            have h1 : d (piv x) = d (piv j₀) := by rw [hyj₀]
            rw [(Option.some.inj hy).symm, hval₀, h1, min_self]
          rcases hv' with hv' | hv'
          · exact ⟨j₀, List.mem_append_left _ hj₀, hyx.trans hyj₀, hv'⟩
          · exact ⟨x, List.mem_append_right _ (List.mem_singleton_self _), hyx, hv'⟩
      · rw [DS.insert_of_ne D (piv x) _ hyx] at hy
        obtain ⟨j₀, hj₀, hyj₀, hval₀⟩ := hD y val hy
        exact ⟨j₀, List.mem_append_left _ hj₀, hyj₀, hval₀⟩
    obtain ⟨hfwd, hback⟩ := ih (DS.insert D (piv x) (d (piv x))) (pre ++ [x]) hD₁
    rw [List.append_assoc, List.singleton_append] at hback
    refine ⟨?_, hback⟩
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj'
      · -- j = x: the intermediate store keys it, and inserts never drop keys
        have hkey : (DS.insert D (piv j) (d (piv j))) (piv j) ≠ none := by
          cases hacc : D (piv j) with
          | none => rw [DS.insert_self, hacc, DS.mergeVal_none_left]; exact Option.some_ne_none _
          | some μ =>
            rw [DS.insert_self, hacc, DS.mergeVal_some]; exact Option.some_ne_none _
        have hfold := hne xs (DS.insert D (piv j) (d (piv j))) (piv j) hkey
        obtain ⟨val, hval⟩ := Option.ne_none_iff_exists.mp hfold
        obtain ⟨j₀, -, hyj₀, hval₀⟩ := hback (piv j) val hval.symm
        rw [← hval, hyj₀, hval₀]
      · exact hfwd j hj'

/-- `initD'` keys every pivot at its own label — the freshness of the BM.8 store. -/
theorem initD'_self (d : Labels G s) {p : ℕ} (piv : Fin p → Fin G.n) (j : Fin p) :
    initD' d piv (piv j) = some (d (piv j)) := by
  have := (initD'_fold_spec d piv (List.finRange p) DS.empty []
    (fun y val hy => by
      have hnone : (DS.empty (G := G) (s := s)) y = none := rfl
      rw [hnone] at hy
      exact absurd hy (Option.some_ne_none val).symm)).1 j (List.mem_finRange j)
  exact this

/-- `initD'` has no key off the pivot range. -/
theorem initD'_none_of_ne (d : Labels G s) {p : ℕ} (piv : Fin p → Fin G.n) {y : Fin G.n}
    (hy : ∀ j, y ≠ piv j) :
    initD' d piv y = none := by
  by_contra hne
  obtain ⟨val, hval⟩ := Option.ne_none_iff_exists.mp hne
  obtain ⟨j₀, -, hj₀, -⟩ :=
    initD'_fold_spec d piv (List.finRange p) DS.empty []
      (fun y' val' hy' => by
        have hnone : (DS.empty (G := G) (s := s)) y' = none := rfl
        rw [hnone] at hy'
        exact absurd hy' (Option.some_ne_none val').symm)
    |>.2 y val hval.symm
  exact hy j₀ hj₀

/-- **The BM.8 initial state keys each pivot at its own label.** -/
theorem mkInit_D_piv (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n)
    (j : Fin fo.p) :
    (mkInit e fo piv).D (piv j) = some (fo.d' (piv j)) :=
  initD'_self fo.d' piv j

/-- The BM.8 initial state has no key off the pivot range. -/
theorem mkInit_D_none_of_ne (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n)
    {y : Fin G.n} (hy : ∀ j, y ≠ piv j) :
    (mkInit e fo piv).D y = none := initD'_none_of_ne fo.d' piv hy

/-! ## 2. The reachable counterexample: `NoCompleteKey` is false -/

/-- The top entry's initial label at the source is the canonical label. -/
theorem initLabels_source' : initLabels G s s = dis (s := s) s := by
  have hr : G.Reachable s s := ⟨[], IsWalk.nil s⟩
  show (if s = s then (((toW [] : List (Fin G.m)) : WalkOrd G s) : WLab G s) else ⊤) = dis s
  rw [if_pos rfl, dis_of_reachable hr, path_source]

/-- **The FindPivots output at the top entry keys the source at its canonical label.**  The gate
set is a nonempty subset of the seed set `{s}` (so it is `{s}`), `p = 1`, the entry label at `s`
is `dis s`, and the FindPivots contract pins `fo.d' s` to it from both sides
(`FPContract.le` down, `FPContract.walk` = soundness up). -/
theorem fpRun_source_keyed (t : ℕ) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n)
    (hfp : fpRun ⟨(⊤ : WLab G s), {s}, fpCap t, initLabels G s⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y) :
    fo.p = 1 ∧ (∀ j, piv j = s) ∧ fo.d' s = dis (s := s) s := by
  have hcontract := fpRun_contract ⟨(⊤ : WLab G s), {s}, fpCap t, initLabels G s⟩ fo hfp
  obtain ⟨hpre, Y, c, st, hYsub, hYne, hcap, hloop, hd', hW, hp, hP, hQ⟩ := hfp
  have hps : ∀ j, piv j = s := by
    intro j
    have hm : piv j ∈ fo.P j := (hpiv j).1
    have h1 : piv j ∈ ({s} : Finset (Fin G.n)) := by
      rw [hP] at hm
      exact hYsub hm
    rw [Finset.mem_singleton] at h1
    exact h1
  refine ⟨hp, hps, ?_⟩
  have h1 : fo.d' s ≤ dis (s := s) s := by
    rw [← initLabels_source']
    exact hcontract.1.le s
  have h2 : dis (s := s) s ≤ fo.d' s := WalkInv.sound hcontract.1.walk s
  exact le_antisymm h1 h2

/-- **The reachable counterexample.**  `NoCompleteKey` fails at the BM.8 initial loop state of
the top-level call: the source is keyed there at its own (complete) canonical label.  The state
is the one `Run.recur`'s `hst0` puts the engine in at `Reach.top` — the entry is reachable
(`Reach.top`), and the loop's first state is `mkInit` by the constructor's own equation. -/
theorem noCompleteKey_refuted_at_top_init (t : ℕ) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n)
    (hfp : fpRun ⟨(⊤ : WLab G s), {s}, fpCap t, initLabels G s⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y) :
    ¬ NoCompleteKey (mkInit ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv).d
        (mkInit ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv).D := by
  intro hkey
  obtain ⟨hp, hpivs, hd's⟩ := fpRun_source_keyed t fo piv hfp hpiv
  have j : Fin fo.p := ⟨0, by rw [hp]; exact Nat.zero_lt_one⟩
  have hD := mkInit_D_piv ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv j
  rw [hpivs j] at hD
  have hc : Complete (mkInit ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv).d s := by
    show (mkInit ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv).d s = dis s
    show fo.d' s = dis s
    exact hd's
  exact hkey s (fo.d' s) hD hc

/-! ## 3. `StoreTight` is false on the same state -/

/-- **The second reachable counterexample.**  `StoreTight` fails at the same BM.8 initial state
whenever the FindPivots search *discovered* a non-pivot vertex (label `≠ ⊤`): the log is empty,
so the settled-exclusion excludes nothing, and the pivot-keyed store has no key for the
discovered vertex.  Semantically the hypothesis holds at the top call whenever `s` has an
out-edge: the search's own `relaxGate` accepts the finite candidate `ext (fo.d' s) e < ⊤ = B`
at the head, and `FPContract.le` keeps the final label below `⊤`. -/
theorem storeTight_refuted_at_top_init (t : ℕ) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n)
    (hfp : fpRun ⟨(⊤ : WLab G s), {s}, fpCap t, initLabels G s⟩ fo)
    (hpiv : ∀ j, piv j ∈ fo.P j ∧ ∀ y ∈ fo.P j, fo.d' (piv j) ≤ fo.d' y)
    (hdisc : ∃ y : Fin G.n, (∀ j, y ≠ piv j) ∧ fo.d' y ≠ ⊤) :
    ¬ StoreTight ⊤ (mkInit ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv) := by
  obtain ⟨hp, hpivs, -⟩ := fpRun_source_keyed t fo piv hfp hpiv
  obtain ⟨y, hyne, hyfin⟩ := hdisc
  intro hST
  obtain ⟨v, hv, -⟩ := hST y (by
    -- the log is empty: nothing is settled
    show y ∉ settledSet (mkInit ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv).evts
    show y ∉ settledSet []
    rw [settledSet_nil]; tauto) (by
    show (mkInit ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv).d y < (⊤ : WLab G s)
    show fo.d' y < (⊤ : WLab G s)
    exact Ne.lt_top hyfin)
  rw [mkInit_D_none_of_ne ⟨(⊤ : WLab G s), {s}, lTop t G.n, initLabels G s⟩ fo piv hyne] at hv
  exact absurd hv (Option.some_ne_none v).symm

/-! ## 4. The minimal corrected custody invariant -/

/-- **The corrected custody invariant**: *a complete key is keyed at its own label* — the store
never presents a complete label at a stale value.  This survives the counterexample state of §2
(the source key carries exactly its label; undiscovered vertices carry no key at all), whereas
`NoCompleteKey` and `StoreTight` do not. -/
def FreshCompleteKey (d : Labels G s) (D : DS G s) : Prop :=
  ∀ y val, D y = some val → Complete d y → val = d y

/-- The custody pair the sweeps preserve: freshness plus the honesty the keep-min consumes. -/
def CustodyPair (d : Labels G s) (D : DS G s) : Prop :=
  FreshCompleteKey d D ∧ (∀ y val, D y = some val → d y ≤ val)

/-- The strong custody clause implies the corrected one. -/
theorem freshCompleteKey_of_noCompleteKey {d : Labels G s} {D : DS G s}
    (h : NoCompleteKey d D) : FreshCompleteKey d D :=
  fun y val hv hc => absurd hc (h y val hv)

/-- **The corrected invariant initializes**: BM.8's store is keyed at the labels by
construction (`initD'_fold_spec`), so freshness costs nothing at the initial state — exactly
where the original obligations are refuted. -/
theorem freshCompleteKey_mkInit (e : CallEntry G s) (fo : FPOut G s) (piv : Fin fo.p → Fin G.n) :
    CustodyPair (mkInit e fo piv).d (mkInit e fo piv).D := by
  obtain ⟨hfwd, hback⟩ :=
    initD'_fold_spec fo.d' piv (List.finRange fo.p) DS.empty []
      (fun y' val' hy' => by
        have hnone : (DS.empty (G := G) (s := s)) y' = none := rfl
        rw [hnone] at hy'
        exact absurd hy' (Option.some_ne_none val').symm)
  constructor
  · intro y val hy _
    obtain ⟨j₀, -, hyj₀, hval₀⟩ := hback y val hy
    rw [hyj₀]
    exact hval₀
  · intro y val hy
    obtain ⟨j₀, -, hyj₀, hval₀⟩ := hback y val hy
    rw [hyj₀, hval₀]
    exact le_rfl

/-- **The stale-key clause the cone leaf needs** (the corrected form of `NoCompleteKey`'s job in
`A4.ConeClosure` §3's table): a key at or above a threshold is incomplete below that threshold. -/
theorem staleIncomplete_of_fresh {B : WLab G s} {d : Labels G s} {D : DS G s}
    (hf : FreshCompleteKey d D) :
    ∀ y val, D y = some val → dis (s := s) y < B → B ≤ val → ¬ Complete d y := by
  intro y val hy hlt hge hc
  rw [hf y val hy hc, hc] at hge
  exact absurd hge (not_le.mpr hlt)

/-- **The cone leaf closes under the corrected custody**: ConeClosure §3's table with row 1
(the pull, `istep_keyCone_of_belowBody`) and row 2 (custody, via `staleIncomplete_of_fresh` +
Claim C) both discharged — **no** `LabelKey` anywhere. -/
theorem keyCone_of_istep_fresh {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo')
    (hclaim : ClaimC c.B c.S c.d)
    (hf : FreshCompleteKey st.d st.D)
    (hB' : fo'.B' ≤ c.B)
    {y : Fin G.n} (hyD : ∃ val, st.D y = some val) (hlt : dis (s := s) y < fo'.B') :
    ∃ x ∈ c.S, OnPath (s := s) x y := by
  by_cases hlow : ∃ v, st.D y = some v ∧ v < c.B
  · exact istep_keyCone_of_belowBody h hlow hlt
  · have hall : ∀ v, st.D y = some v → c.B ≤ v := fun v hv =>
      le_of_not_gt fun hlt' => hlow ⟨v, hv, hlt'⟩
    have hcd : c.d = st.d := istep_child_d h
    have hnc : ¬ Complete st.d y := by
      intro hcomp
      obtain ⟨val, hval⟩ := hyD
      exact staleIncomplete_of_fresh hf y val hval (lt_of_lt_of_le hlt hB') (hall val hval) hcomp
    rw [hcd] at hclaim
    obtain ⟨-, x, hx, hvisit⟩ :=
      mem_utilde_of_claimC hclaim hnc (lt_of_lt_of_le hlt hB')
    exact ⟨x, Finset.mem_coe.mpr hx, hvisit⟩

/-- **`StoreTight`'s surviving content**: on the unsettled part of the state it is exactly
`StepSplit`'s `hcover` — which is why the refutation of §3 is precisely a failure of `hcover`'s
global form at the initial state. -/
theorem mem_childS_of_storeTight (t : ℕ) {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hST : StoreTight c.B st) {y : Fin G.n}
    (hys : y ∉ settledSet st.evts) (hlt : st.d y < c.B) : y ∈ c.S :=
  mem_childS_of_key_below t h (hST y hys hlt)

/-! ## 5. The level-`l` induction harness -/

/-- **The custody carrier across one iteration**: a parent key the child returns *no* key for
keeps its label.  On the repaired engine this is the store form of the label-provenance link
`A4.OriginTrace` names as the lane's open descent gap — a child label drop is accompanied by a
store write (`relaxGate_write_key`) or ends in a settlement (★BM.15 deletes the parent's stale
key with the child's).  The lane has no `Run`-level lemma for it; it is carried here as a typed
hypothesis, never an axiom. -/
def KeyCarry {p : ℕ} (st : RState G s p) (fo' : CallOut G s) : Prop :=
  ∀ y val, st.D y = some val → fo'.D y = none → fo'.d' y = val

theorem freshCompleteKey_deleteSet {d : Labels G s} {D : DS G s}
    (hf : FreshCompleteKey d D) (T : Finset (Fin G.n)) : FreshCompleteKey d (DS.deleteSet D T) :=
  fun y val hy hc => by
    by_cases hyT : y ∈ T
    · rw [DS.deleteSet_mem D T y hyT] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    · rw [DS.deleteSet_of_notMem D T y hyT] at hy
      exact hf y val hy hc

theorem custodyPair_deleteSet {d : Labels G s} {D : DS G s}
    (h : CustodyPair d D) (T : Finset (Fin G.n)) : CustodyPair d (DS.deleteSet D T) :=
  ⟨freshCompleteKey_deleteSet h.1 T, fun y val hy => by
    by_cases hyT : y ∈ T
    · rw [DS.deleteSet_mem D T y hyT] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    · rw [DS.deleteSet_of_notMem D T y hyT] at hy
      exact h.2 y val hy⟩

/-- One gated relaxation preserves the pair: it writes the label and the key in one breath. -/
theorem custodyPair_relaxGate {B lo : WLab G s} {d : Labels G s} {D : DS G s}
    (h : CustodyPair d D) (e : Fin G.m) :
    CustodyPair (relaxGate B lo d D e).1 (relaxGate B lo d D e).2 := by
  obtain ⟨hf, hon⟩ := h
  by_cases hc : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · simp only [relaxGate, if_pos hc]
    constructor
    · intro y val hy hcomp
      by_cases hyy : y = G.dst e
      · subst hyy
        rw [Function.update_self] at ⊢
        rw [DS.insert_self] at hy
        cases hD : D (G.dst e) with
        | none =>
          rw [hD, DS.mergeVal_none_left] at hy
          exact (Option.some.inj hy).symm
        | some μ =>
          rw [hD, DS.mergeVal_some] at hy
          have hcand : ext (d (G.src e)) e ≤ μ := hc.2.2.trans (hon (G.dst e) μ hD)
          rw [min_eq_right hcand] at hy
          exact (Option.some.inj hy).symm
      · have hdu : Function.update d (G.dst e) (ext (d (G.src e)) e) y = d y :=
          Function.update_of_ne hyy (ext (d (G.src e)) e) d
        simp only [Complete] at hcomp
        rw [hdu] at hcomp
        rw [DS.insert_of_ne D (G.dst e) _ hyy] at hy
        exact (hf y val hy hcomp).trans hdu.symm
    · intro y val hy
      by_cases hyy : y = G.dst e
      · subst hyy
        rw [Function.update_self] at ⊢
        rw [DS.insert_self] at hy
        cases hD : D (G.dst e) with
        | none =>
          rw [hD, DS.mergeVal_none_left] at hy
          exact (Option.some.inj hy).symm.ge
        | some μ =>
          rw [hD, DS.mergeVal_some] at hy
          have hcand : ext (d (G.src e)) e ≤ μ := hc.2.2.trans (hon (G.dst e) μ hD)
          have hv' : val = min μ (ext (d (G.src e)) e) := (Option.some.inj hy).symm
          rw [hv', min_eq_right hcand]
      · have hdu : Function.update d (G.dst e) (ext (d (G.src e)) e) y = d y :=
          Function.update_of_ne hyy (ext (d (G.src e)) e) d
        rw [DS.insert_of_ne D (G.dst e) _ hyy] at hy
        exact le_trans hdu.le (hon y val hy)
  · simp only [relaxGate, if_neg hc]
    exact ⟨hf, hon⟩

theorem custodyPair_sweepGate {B lo : WLab G s} (u : Fin G.n) (es : List (Fin G.m)) :
    ∀ (d : Labels G s) (D : DS G s), CustodyPair d D →
      CustodyPair (sweepGate B lo u es d D).1 (sweepGate B lo u es d D).2 := by
  induction es with
  | nil => exact fun d D h => h
  | cons e es ih =>
    intro d D h
    unfold sweepGate
    by_cases hs : G.src e = u
    · rw [if_pos hs, if_pos hs]
      exact ih _ _ (custodyPair_relaxGate h e)
    · rw [if_neg hs, if_neg hs]
      exact ih d D h

theorem custodyPair_sweepEvts {B lo : WLab G s} (evts : List (SettlementEvent G)) :
    ∀ (d : Labels G s) (D : DS G s), CustodyPair d D →
      CustodyPair (sweepEvts B lo evts d D).1 (sweepEvts B lo evts d D).2 := by
  induction evts with
  | nil => exact fun d D h => h
  | cons ev evts ih =>
    intro d D h
    exact ih _ _ (custodyPair_sweepGate ev.v (List.finRange G.m) d D h)

/-- An insert at the *current* label preserves the pair (the BM.25 seed re-insert, the line-29
mint fold). -/
theorem custodyPair_insert_own {d : Labels G s} {D : DS G s} (h : CustodyPair d D) (x : Fin G.n) :
    CustodyPair d (DS.insert D x (d x)) := by
  obtain ⟨hf, hon⟩ := h
  constructor
  · intro y val hy hcomp
    by_cases hyx : y = x
    · subst hyx
      rw [DS.insert_self] at hy
      cases hD : D y with
      | none => rw [hD, DS.mergeVal_none_left] at hy; exact (Option.some.inj hy).symm
      | some μ =>
        rw [hD, DS.mergeVal_some] at hy
        have hμ : d y ≤ μ := hon y μ hD
        rw [min_eq_right hμ] at hy
        exact (Option.some.inj hy).symm
    · rw [DS.insert_of_ne D x _ hyx] at hy
      exact hf y val hy hcomp
  · intro y val hy
    by_cases hyx : y = x
    · subst hyx
      rw [DS.insert_self] at hy
      cases hD : D y with
      | none => rw [hD, DS.mergeVal_none_left] at hy; exact (Option.some.inj hy).symm.ge
      | some μ =>
        rw [hD, DS.mergeVal_some] at hy
        have hμ : d y ≤ μ := hon y μ hD
        have hv' : val = min μ (d y) := (Option.some.inj hy).symm
        rw [hv', min_eq_right hμ]
    · rw [DS.insert_of_ne D x _ hyx] at hy
      exact hon y val hy

theorem custodyPair_fold_insert {ι : Type} (js : List ι) (f : ι → Fin G.n) :
    ∀ (d : Labels G s) (D : DS G s), CustodyPair d D →
      CustodyPair d (js.foldl (fun D j => DS.insert D (f j) (d (f j))) D) := by
  induction js with
  | nil => exact fun d D h => h
  | cons j js ih =>
    intro d D h
    rw [List.foldl_cons]
    exact ih d _ (custodyPair_insert_own h (f j))

/-- **The keep-min repairs a re-keyed vertex.**  The merge law of the corrected custody: a key
of the pull remainder that the child re-keyed is min-repaired (freshness + honesty of the two
halves + the child's label law); a key the child neither re-keyed nor settled is carried by
`KeyCarry`. -/
theorem freshCompleteKey_merge {D₁ D₂ : DS G s} {d₁ d₂ : Labels G s}
    (hf₁ : FreshCompleteKey d₁ D₁) (hf₂ : FreshCompleteKey d₂ D₂)
    (hon₁ : ∀ y val, D₁ y = some val → d₁ y ≤ val)
    (hon₂ : ∀ y val, D₂ y = some val → d₂ y ≤ val)
    (hle : ∀ y, d₂ y ≤ d₁ y)
    (hcarry : ∀ y val, D₁ y = some val → D₂ y = none → d₂ y = val) :
    FreshCompleteKey d₂ (DS.merge D₁ D₂) := by
  intro y val hy hc
  rw [DS.merge_eq] at hy
  cases hd₁ : D₁ y with
  | none =>
    cases hd₂ : D₂ y with
    | none =>
      rw [hd₁, hd₂, DS.mergeVal_none_left] at hy
      exact absurd hy.symm (Option.some_ne_none val)
    | some ν =>
      rw [hd₁, hd₂, DS.mergeVal_none_left] at hy
      exact (Option.some.inj hy).symm.trans (hf₂ y ν hd₂ hc)
  | some μ =>
    cases hd₂ : D₂ y with
    | none =>
      rw [hd₁, hd₂, DS.mergeVal_none_right] at hy
      exact ((Option.some.inj hy).symm.trans (hcarry y μ hd₁ hd₂).symm)
    | some ν =>
      rw [hd₁, hd₂, DS.mergeVal_some] at hy
      have hν : ν = d₂ y := hf₂ y ν hd₂ hc
      have hνμ : ν ≤ μ := by rw [hν]; exact (hle y).trans (hon₁ y μ hd₁)
      rw [(Option.some.inj hy).symm, min_eq_right hνμ, hν]

/-- **The step law of the corrected custody**, from the iteration's own equations
(pull/merge/delete/sweep/mint fold) given the parent pair, the child pair, the child's label law
and `KeyCarry`. -/
theorem freshCompleteKey_istep_of_carry {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo')
    (hpar : CustodyPair st.d st.D)
    (hchild : CustodyPair fo'.d' fo'.D)
    (hmono : ∀ v, fo'.d' v ≤ c.d v)
    (hcarry : KeyCarry st fo') :
    CustodyPair st'.d st'.D := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel,
    hst'⟩ := h
  have hcd : c.d = st.d := by rw [hc]
  -- the pull remainder carries the parent's pair
  have hD1eq : D1 = DS.deleteSet st.D Si := hpull.2.1
  have hD1 : CustodyPair st.d D1 := by rw [hD1eq]; exact custodyPair_deleteSet hpar Si
  -- the merge, with KeyCarry restricted to the remainder
  have hcarry' : ∀ y val, D1 y = some val → fo'.D y = none → fo'.d' y = val := by
    intro y val hval hnone
    by_cases hyS : y ∈ Si
    · rw [hD1eq, DS.deleteSet_mem st.D Si y hyS] at hval
      exact absurd hval.symm (Option.some_ne_none val)
    · rw [hD1eq, DS.deleteSet_of_notMem st.D Si y hyS] at hval
      exact hcarry y val hval hnone
  have hM : CustodyPair fo'.d' (DS.merge D1 fo'.D) :=
    ⟨freshCompleteKey_merge hD1.1 hchild.1 hD1.2 hchild.2 (fun v => by
        have := hmono v
        rw [hcd] at this
        exact this)
      hcarry',
      fun y val hy => by
        rw [DS.merge_eq] at hy
        cases hd₁ : D1 y with
        | none =>
          cases hd₂ : fo'.D y with
          | none =>
            rw [hd₁, hd₂, DS.mergeVal_none_left] at hy
            exact absurd hy.symm (Option.some_ne_none val)
          | some ν =>
            rw [hd₁, hd₂, DS.mergeVal_none_left] at hy
            have hv' : val = ν := (Option.some.inj hy).symm
            rw [hv']
            exact hchild.2 y ν hd₂
        | some μ =>
          cases hd₂ : fo'.D y with
          | none =>
            rw [hd₁, hd₂, DS.mergeVal_none_right] at hy
            rw [← hcarry' y μ hd₁ hd₂] at hy
            exact (Option.some.inj hy).symm.ge
          | some ν =>
            rw [hd₁, hd₂, DS.mergeVal_some] at hy
            have hv' : val = min μ ν := (Option.some.inj hy).symm
            rw [hv']
            have hle1 : fo'.d' y ≤ st.d y := by rw [← hcd]; exact hmono y
            exact le_min (le_trans hle1 (hD1.2 y μ hd₁)) (hchild.2 y ν hd₂)⟩
  -- ★BM.15's deletion, then the sweep
  have hD2 : CustodyPair fo'.d' D2 := by
    rw [hmerge]; exact custodyPair_deleteSet hM (settledFinset fo')
  have hD3 : CustodyPair d3 D3 := by
    rw [show d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 from congrArg Prod.fst hsweep,
      show D3 = (sweepEvts B Bi fo'.evts fo'.d' D2).2 from congrArg Prod.snd hsweep]
    exact custodyPair_sweepEvts fo'.evts _ _ hD2
  -- the mint fold, keyed at the current labels
  have hfold : CustodyPair d3 (J.toList.foldl (fun D j => DS.insert D (sel j) (d3 (sel j))) D3) :=
    custodyPair_fold_insert J.toList sel d3 D3 hD3
  rw [hst']
  exact hfold

/-- BM.25's gated fold of inserts at the current labels preserves the pair. -/
theorem custodyPair_seedIns (bp B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s)
    (D : DS G s) (h : CustodyPair d D) :
    CustodyPair (seedIns bp B S d D).1 (seedIns bp B S d D).2 := by
  unfold seedIns
  induction S.toList generalizing d D with
  | nil => exact h
  | cons x xs ih =>
    rw [List.foldl_cons]
    split
    · exact ih _ _ (custodyPair_insert_own h x)
    · exact ih d D h

/-- BM.25/BM.28 preserve the pair, so the tail preserves freshness. -/
theorem freshCompleteKey_tail (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p)
    (h : CustodyPair st.d st.D) : FreshCompleteKey (tail B S W st).d (tail B S W st).D := by
  have hseed := custodyPair_seedIns (tailBP B st) B S st.d st.D h
  rw [show (tail B S W st).d
      = (sweepEvts B (tailBP B st) (wPrimeEvts (tailWp B S W st))
        (seedIns (tailBP B st) B S st.d st.D).1
        (seedIns (tailBP B st) B S st.d st.D).2).1 from rfl,
    show (tail B S W st).D
      = (sweepEvts B (tailBP B st) (wPrimeEvts (tailWp B S W st))
        (seedIns (tailBP B st) B S st.d st.D).1
        (seedIns (tailBP B st) B S st.d st.D).2).2 from rfl]
  exact (custodyPair_sweepEvts (wPrimeEvts (tailWp B S W st))
    (seedIns (tailBP B st) B S st.d st.D).1
    (seedIns (tailBP B st) B S st.d st.D).2 hseed).1


/-- **The loop threads the corrected custody.** -/
theorem iloop_freshCompleteKey (t : ℕ) (B : WLab G s) (l : ℕ)
    (hstep : ∀ {p : ℕ} (st₁ st₂ : RState G s p) (c : CallEntry G s) (fo' : CallOut G s),
      IStep t B l st₁ st₂ c fo' → CustodyPair st₁.d st₁.D →
        CustodyPair fo'.d' fo'.D → CustodyPair st₂.d st₂.D) :
    ∀ {p : ℕ} {st stf : RState G s p} {qs}, ILoop t B l st qs stf →
      CustodyPair st.d st.D → (∀ q ∈ qs, CustodyPair q.2.d' q.2.D) →
      CustodyPair stf.d stf.D := by
  intro p st stf qs h
  induction h with
  | exit h => intro hin _; exact hin
  | step hne hg hstepI hrest ih =>
    intro hin hchild
    exact ih (hstep _ _ _ _ hstepI hin (hchild _ List.mem_cons_self))
      (fun q hq => hchild q (List.mem_cons_of_mem _ hq))

/-- The base-case leaf of the harness: `A1.BaseInv`'s entry freshness keys every base-return
entry at its own label. -/
theorem returnCustody_base (t : ℕ) {e : BaseIn G s} {bout : BaseOut G s}
    (hre : ReachBase e) (hb : baseRun t e bout) :
    CustodyPair (baseOut bout).d' (baseOut bout).D := by
  obtain ⟨c, st, hloop, hrout⟩ := hb
  have hB : BInv e.B e.S st := loop_bInv hloop (bInv_init hre)
  show CustodyPair bout.d' bout.D_final
  have hd' : bout.d' = st.d := by rw [hrout]
  have hD : bout.D_final = st.D := by rw [hrout]
  rw [hd', hD]
  exact ⟨fun y val hy _ => hB.fresh y val hy, fun y val hy => by rw [← hB.fresh y val hy]⟩

/-- **The level-`l` induction harness**, proved: from the base law, the step law, the carrier and
the tail law, the corrected custody holds at every run's return.  The induction is well-founded
on the level (`iloop_children_level`), exactly as the SSSP lane's custody obligation asked. -/
theorem returnCustody_of_run (t : ℕ)
    (hbase : ∀ (e : BaseIn G s) (bout : BaseOut G s), baseRun t e bout →
      CustodyPair (baseOut bout).d' (baseOut bout).D)
    (hstep : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p) (c : CallEntry G s)
      (fo' : CallOut G s), IStep t B l st st' c fo' → CustodyPair st.d st.D →
        CustodyPair fo'.d' fo'.D → CustodyPair st'.d st'.D)
    (hcarry : ∀ (B : WLab G s) (l : ℕ) {p : ℕ} (st st' : RState G s p) (c : CallEntry G s)
      (fo' : CallOut G s), IStep t B l st st' c fo' → KeyCarry st fo')
    (htail : ∀ (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ} (st : RState G s p),
      CustodyPair st.d st.D → CustodyPair (tail B S W st).d (tail B S W st).D) :
    ∀ {e : CallEntry G s} {out : CallOut G s}, Run t e out → CustodyPair out.d' out.D := by
  have main : ∀ (l : ℕ) (e : CallEntry G s) (out : CallOut G s), e.l = l → Run t e out →
      CustodyPair out.d' out.D := by
    intro l
    induction l with
    | zero =>
      intro e out hl hrun
      rcases hrun with ⟨h0, hb⟩ | @⟨_, _, fo, piv, st0, _, _, hpos, hfp, hpiv, hst0, hloop,
        hchildren⟩
      · exact hbase _ _ hb
      · rw [hl] at hpos; exact absurd hpos (by norm_num)
    | succ l ih =>
      intro e out hl hrun
      rcases hrun with ⟨h0, hb⟩ | @⟨_, _, fo, piv, st0, _, _, hpos, hfp, hpiv, hst0, hloop,
        hchildren⟩
      · rw [h0] at hl; exact absurd hl (by omega)
      · have hinit : CustodyPair st0.d st0.D := by
          rw [hst0]; exact freshCompleteKey_mkInit e fo piv
        have hf := iloop_freshCompleteKey t e.B e.l (fun _ _ _ _ hst => hstep _ _ _ _ _ _ hst)
          hloop hinit
          (fun q hq => ih q.1 q.2
            (by have hv := iloop_children_level t e.B e.l hloop q hq
                rw [hv, hl]
                omega) (hchildren q hq))
        exact htail _ _ _ _ hf
  intro e out hrun
  exact main e.l e out rfl hrun

/-! ## 6. `a4_joint` status, stated exactly -/

/-- The return-custody a run supplies to the assembly: the corrected invariant at the return,
with the base leaf discharged by reachability (`returnCustody_base`) and the per-step carrier
supplied by the loop. -/
def ReturnCustody (out : CallOut G s) : Prop := CustodyPair out.d' out.D

/-- The custody closing this file delivers to the joint chain: the cone-closure leaf of
`A4.ConeClosure` §3 (clause (2c)'s `hcone` input) now takes the corrected invariant instead of
the refuted `NoCompleteKey` — at the *child entry's own labels* `c.d = st.d`, which is where
the stale-body key lives. -/
theorem coneCustody_of_istep {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo')
    (hpre : CallPre c.B c.S c.d)
    (hf : FreshCompleteKey st.d st.D)
    (hB' : fo'.B' ≤ c.B) :
    ∀ y : Fin G.n, (∃ val, st.D y = some val) → dis (s := s) y < fo'.B' →
      ∃ x ∈ c.S, OnPath (s := s) x y :=
  fun y => keyCone_of_istep_fresh h hpre.claimC hf hB'

end DMSY
end Frontier

/-! ## Axiom audit -/

#print axioms Frontier.DMSY.noCompleteKey_refuted_at_top_init
#print axioms Frontier.DMSY.storeTight_refuted_at_top_init
#print axioms Frontier.DMSY.freshCompleteKey_mkInit
#print axioms Frontier.DMSY.keyCone_of_istep_fresh
#print axioms Frontier.DMSY.freshCompleteKey_istep_of_carry
#print axioms Frontier.DMSY.freshCompleteKey_tail
#print axioms Frontier.DMSY.returnCustody_base
#print axioms Frontier.DMSY.returnCustody_of_run
#print axioms Frontier.DMSY.coneCustody_of_istep

import A4.Structural

/-!
# Frontier.DMSY.SettleSweep — the post-sweep settlement/sweep discharge

`A4.LoopFrontier` isolated `SettleSweep` as the one remaining per-iteration fact for `lInv_istep`:

1. every `z ∈ settledSet fo'.evts` is `Complete st'.d z` (settlement completeness at post labels);
2. every out-edge of a settled vertex whose candidate is below `B` has been relaxed
   (`st'.d (G.dst e) ≤ ext (st'.d (G.src e)) e`).

Clause (i) is discharged from the child's settlement-completeness IH + the sweep's label
monotonicity.  Clause (ii)'s above-separator part is discharged from the sweep's own acceptance
(`relaxGate`) + persistence; its below-separator part (`cand < c.B`) is the one child-completeness
hypothesis left to the joint chain (the refusal-floor).  The lemmas are stated against the *body*
of `SettleSweep`, so they fold into `A4.LoopFrontier.lInv_iloop`'s `ChildStep`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## The atomic sweep acceptance and completeness preservation -/

/-- `relaxGate` above its lower gate always ends with the head at or below the candidate. -/
theorem relaxGate_le_cand (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (hlo : lo ≤ ext (d (G.src e)) e) (hlt : ext (d (G.src e)) e < B) :
    (relaxGate B lo d D e).1 (G.dst e) ≤ ext (d (G.src e)) e := by
  unfold relaxGate
  by_cases h : lo ≤ ext (d (G.src e)) e ∧ ext (d (G.src e)) e < B ∧
      ext (d (G.src e)) e ≤ d (G.dst e)
  · rw [if_pos h]
    simp
  · rw [if_neg h]
    have hnot : ¬ ext (d (G.src e)) e ≤ d (G.dst e) := fun hle => h ⟨hlo, hlt, hle⟩
    exact le_of_lt (lt_of_not_ge hnot)

/-- `relaxGate` never un-completes a complete vertex: it only lowers, and soundness keeps it at
the canonical label. -/
theorem relaxGate_keeps_complete (B lo : WLab G s) (d : Labels G s) (D : DS G s) (e : Fin G.m)
    (v : Fin G.n) (hcomp : Complete d v) (hwalk : WalkInv d) :
    Complete (relaxGate B lo d D e).1 v := by
  exact le_antisymm ((relaxGate_le B lo d D e v).trans hcomp.le)
    ((WalkInv.sound (relaxGate_walk B lo d D e hwalk)) v)

theorem sweepGate_keeps_complete (B lo : WLab G s) (u : Fin G.n) :
    ∀ es (d : Labels G s) (D : DS G s) (v : Fin G.n),
      Complete d v → WalkInv d → Complete (sweepGate B lo u es d D).1 v := by
  intro es
  induction es with
  | nil => intro d D v hcomp _hwalk; exact hcomp
  | cons e es ih =>
      intro d D v hcomp hwalk
      unfold sweepGate
      by_cases hs : G.src e = u
      · rw [if_pos hs, if_pos hs]
        exact ih (relaxGate B lo d D e).1 (relaxGate B lo d D e).2 v
          (relaxGate_keeps_complete B lo d D e v hcomp hwalk)
          (relaxGate_walk B lo d D e hwalk)
      · rw [if_neg hs, if_neg hs]
        exact ih d D v hcomp hwalk

/-- One settled vertex's out-edge sweep relaxes every below-`B` candidate above the lower gate. -/
theorem sweepGate_relaxes (B lo : WLab G s) (u : Fin G.n) :
    ∀ es (d : Labels G s) (D : DS G s) (e : Fin G.m),
      e ∈ es → G.src e = u → Complete d u → WalkInv d →
      lo ≤ ext (d u) e → ext (d u) e < B →
        (sweepGate B lo u es d D).1 (G.dst e) ≤ ext (d u) e := by
  intro es
  induction es with
  | nil => intro d D e he; exact absurd he List.not_mem_nil
  | cons e' es ih =>
      intro d D e he hsrc hcomp hwalk hlo hlt
      rcases List.mem_cons.mp he with he | he
      · subst he
        unfold sweepGate
        rw [if_pos hsrc, if_pos hsrc]
        have hlo' : lo ≤ ext (d (G.src e)) e := by simpa [hsrc] using hlo
        have hlt' : ext (d (G.src e)) e < B := by simpa [hsrc] using hlt
        have hrel := relaxGate_le_cand B lo d D e hlo' hlt'
        have hle := sweepGate_le B lo u es (relaxGate B lo d D e).1 (relaxGate B lo d D e).2 (G.dst e)
        simpa [hsrc] using hle.trans hrel
      · unfold sweepGate
        by_cases hsrc' : G.src e' = u
        · rw [if_pos hsrc', if_pos hsrc']
          have hwalk' : WalkInv (relaxGate B lo d D e').1 := relaxGate_walk B lo d D e' hwalk
          have hcomp' : Complete (relaxGate B lo d D e').1 u :=
            relaxGate_keeps_complete B lo d D e' u hcomp hwalk
          have hdu : (relaxGate B lo d D e').1 u = d u := hcomp'.trans hcomp.symm
          have hlo' : lo ≤ ext ((relaxGate B lo d D e').1 u) e := by rwa [hdu]
          have hlt' : ext ((relaxGate B lo d D e').1 u) e < B := by rwa [hdu]
          have ih' := ih (relaxGate B lo d D e').1 (relaxGate B lo d D e').2 e he hsrc hcomp' hwalk' hlo' hlt'
          simpa [hdu] using ih'
        · rw [if_neg hsrc', if_neg hsrc']
          exact ih d D e he hsrc hcomp hwalk hlo hlt

/-- The full settlement sweep relaxes every below-`B` candidate above the lower gate out of a
settled (complete) vertex. -/
theorem sweepEvts_relaxes (B lo : WLab G s) :
    ∀ evts (d : Labels G s) (D : DS G s) (e : Fin G.m),
      G.src e ∈ settledSet evts → (∀ ev ∈ evts, Complete d ev.v) → WalkInv d →
      lo ≤ ext (d (G.src e)) e → ext (d (G.src e)) e < B →
        (sweepEvts B lo evts d D).1 (G.dst e) ≤ ext (d (G.src e)) e := by
  intro evts
  induction evts with
  | nil => intro d D e hu; simp [settledSet] at hu
  | cons ev evts ih =>
      intro d D e hu hall hwalk hlo hlt
      unfold sweepEvts
      rcases hu with ⟨ev', hev', hvv⟩
      rcases List.mem_cons.mp hev' with hev' | hev'
      · rw [hev'] at hvv
        have hsrc : G.src e = ev.v := hvv.symm
        have hmem : e ∈ List.finRange G.m := List.mem_finRange e
        have hcomp_ev : Complete d ev.v := hall ev List.mem_cons_self
        have hlo' : lo ≤ ext (d ev.v) e := by simpa [hsrc] using hlo
        have hlt' : ext (d ev.v) e < B := by simpa [hsrc] using hlt
        have hrel' : (sweepGate B lo ev.v (List.finRange G.m) d D).1 (G.dst e) ≤ ext (d ev.v) e :=
          sweepGate_relaxes B lo ev.v (List.finRange G.m) d D e hmem hsrc hcomp_ev hwalk hlo' hlt'
        have hpersist : (sweepEvts B lo evts (sweepGate B lo ev.v (List.finRange G.m) d D).1
            (sweepGate B lo ev.v (List.finRange G.m) d D).2).1 (G.dst e) ≤
            (sweepGate B lo ev.v (List.finRange G.m) d D).1 (G.dst e) :=
          sweepEvts_le B lo evts (sweepGate B lo ev.v (List.finRange G.m) d D).1
            (sweepGate B lo ev.v (List.finRange G.m) d D).2 (G.dst e)
        simpa [hvv] using (hpersist.trans hrel')
      · have hwalk' : WalkInv (sweepGate B lo ev.v (List.finRange G.m) d D).1 :=
          sweepGate_walk B lo ev.v (List.finRange G.m) d D hwalk
        have hcomp_src : Complete (sweepGate B lo ev.v (List.finRange G.m) d D).1 (G.src e) := by
          have hc : Complete d (G.src e) := hvv ▸ hall ev' (List.mem_cons_of_mem ev hev')
          exact sweepGate_keeps_complete B lo ev.v (List.finRange G.m) d D (G.src e) hc hwalk
        have hdu : (sweepGate B lo ev.v (List.finRange G.m) d D).1 (G.src e) = d (G.src e) :=
          hcomp_src.trans (hvv ▸ (hall ev' (List.mem_cons_of_mem ev hev'))).symm
        have hall' : ∀ ev'' ∈ evts, Complete (sweepGate B lo ev.v (List.finRange G.m) d D).1 ev''.v := by
          intro ev'' hev''
          exact sweepGate_keeps_complete B lo ev.v (List.finRange G.m) d D ev''.v
            (hall ev'' (List.mem_cons_of_mem ev hev'')) hwalk
        have hlo' : lo ≤ ext ((sweepGate B lo ev.v (List.finRange G.m) d D).1 (G.src e)) e := by rwa [hdu]
        have hlt' : ext ((sweepGate B lo ev.v (List.finRange G.m) d D).1 (G.src e)) e < B := by rwa [hdu]
        have ih' := ih (sweepGate B lo ev.v (List.finRange G.m) d D).1
          (sweepGate B lo ev.v (List.finRange G.m) d D).2 e ⟨ev', hev', hvv⟩ hall' hwalk' hlo' hlt'
        simpa [hdu] using ih'

/-! ## Clause (i): settlement completeness at post labels -/

/-- **Clause (i).**  The child's settlements stay complete after the parent sweep. -/
theorem settleSweep_complete (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hsettle : ∀ ev ∈ fo'.evts, Complete fo'.d' ev.v)
    (hwalk : WalkInv fo'.d') :
    ∀ z ∈ settledSet fo'.evts, Complete st'.d z := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel, hst'⟩ := h
  subst hst'
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := congrArg Prod.fst hsweep
  have hwalk' : WalkInv d3 := by
    rw [hd3]
    exact sweepEvts_walk B Bi fo'.evts fo'.d' D2 hwalk
  intro z hz
  rcases hz with ⟨ev, hev, hzv⟩
  have hcomp : Complete fo'.d' ev.v := hsettle ev hev
  refine Complete.of_le (hzv ▸ hcomp) (WalkInv.sound hwalk') ?_
  rw [hd3]
  exact sweepEvts_le B Bi fo'.evts fo'.d' D2 z

/-! ## Clause (ii): the sweep relaxes every below-`B` candidate out of a settled vertex -/

/-- **Clause (ii).**  The post-sweep labels satisfy `st'.d (G.dst e) ≤ ext (st'.d (G.src e)) e`
for every settled source with candidate below `B`.  Above the child separator `c.B` this is the
sweep's own acceptance; below it the child has already completed the head (the explicit
`hbelow`, the refusal-floor half of the joint chain). -/
theorem settleSweep_relax (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hsettle : ∀ ev ∈ fo'.evts, Complete fo'.d' ev.v)
    (hwalk : WalkInv fo'.d')
    (hbelow : ∀ e, G.src e ∈ settledSet fo'.evts → ext (st'.d (G.src e)) e < c.B →
      Complete st'.d (G.dst e)) :
    ∀ e, G.src e ∈ settledSet fo'.evts → ext (st'.d (G.src e)) e < B →
      st'.d (G.dst e) ≤ ext (st'.d (G.src e)) e := by
  obtain ⟨Si, Bi, D1, resid, J, sel, D2, d3, D3, hpull, hc, hmerge, hsweep, hresid, hJ, hsel, hst'⟩ := h
  have hst'd : st'.d = d3 := by rw [hst']
  have hcB : c.B = Bi := by rw [hc]
  have hd3 : d3 = (sweepEvts B Bi fo'.evts fo'.d' D2).1 := congrArg Prod.fst hsweep
  have hwalk' : WalkInv d3 := by
    rw [hd3]
    exact sweepEvts_walk B Bi fo'.evts fo'.d' D2 hwalk
  rw [hst'd] at hbelow
  rw [hst'd]
  intro e hu hltB
  have hcompU : Complete d3 (G.src e) := by
    rcases hu with ⟨ev, hev, hvv⟩
    have hcomp : Complete fo'.d' ev.v := hsettle ev hev
    refine Complete.of_le (hvv ▸ hcomp) (WalkInv.sound hwalk') ?_
    rw [hd3]
    exact sweepEvts_le B Bi fo'.evts fo'.d' D2 (G.src e)
  have hdu : d3 (G.src e) = fo'.d' (G.src e) := by
    rcases hu with ⟨ev, hev, hvv⟩
    have hcomp_child : Complete fo'.d' (G.src e) := hvv ▸ hsettle ev hev
    exact hcompU.trans hcomp_child.symm
  by_cases hge : c.B ≤ ext (d3 (G.src e)) e
  · -- above separator: the sweep's own acceptance (persisting under later labels)
    have hlo' : Bi ≤ ext (fo'.d' (G.src e)) e := by simpa [hcB, hdu] using hge
    have hlt' : ext (fo'.d' (G.src e)) e < B := by simpa [hdu] using hltB
    have hrel : d3 (G.dst e) ≤ ext (fo'.d' (G.src e)) e := by
      rw [hd3]
      exact sweepEvts_relaxes B Bi fo'.evts fo'.d' D2 e hu hsettle hwalk hlo' hlt'
    rw [hdu]
    exact hrel
  · -- below separator: the child completed the head (refusal-floor half)
    have hlt_cB : ext (d3 (G.src e)) e < c.B := lt_of_not_ge hge
    have hcomp_dst : Complete d3 (G.dst e) := hbelow e hu hlt_cB
    have hreach : G.Reachable s (G.src e) := by
      by_contra hn
      have hdis_top : dis (s := s) (G.src e) = ⊤ := dis_of_not_reachable hn
      have hd3ne : d3 (G.src e) ≠ ⊤ := by
        intro htop
        rw [htop, ext_top] at hltB
        exact (lt_irrefl (⊤ : WLab G s)) (lt_of_lt_of_le hltB le_top)
      exact (hcompU ▸ hd3ne) hdis_top
    have hle : d3 (G.dst e) ≤ ext (d3 (G.src e)) e := by
      rw [hcomp_dst, hcompU]
      have hcand : ext (dis (s := s) (G.src e)) e
          = ((toW (path (s := s) (G.src e) ++ [e]) : WalkOrd G s) : WLab G s) := by
        conv_lhs => rw [dis_of_reachable hreach]
        exact ext_coe (path (s := s) (G.src e)) e
      rw [hcand]
      exact dis_le_walk (walk_ext (path_isMinWalk hreach).1 e rfl)
    exact hle

/-! ## The ChildStep discharge (folds into `A4.LoopFrontier.lInv_iloop`) -/

/-- **`ChildStep` discharge.**  The full per-iteration fact `A4.LoopFrontier.ChildStep B st st' fo'`
(= mono ∧ walk ∧ `SettleSweep`) follows from: the child's label monotonicity and walk
(`hmono`/`hwalk`, themselves derived from the child's `Run` via `run_le`/`run_walk`), the child's
settlement-completeness IH (`hsettle`), and the below-separator child completeness (`hbelow` —
the refusal-floor half).  The two genuinely inductive premises are `hsettle` and `hbelow`. -/
theorem childStep_of (t : ℕ) (B : WLab G s) (l : ℕ) {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s} (h : IStep t B l st st' c fo')
    (hmono : ∀ v, fo'.d' v ≤ st.d v)
    (hwalk : WalkInv fo'.d')
    (hsettle : ∀ ev ∈ fo'.evts, Complete fo'.d' ev.v)
    (hbelow : ∀ e, G.src e ∈ settledSet fo'.evts → ext (st'.d (G.src e)) e < c.B →
      Complete st'.d (G.dst e)) :
    (∀ v, fo'.d' v ≤ st.d v) ∧ WalkInv fo'.d' ∧
      ((∀ z ∈ settledSet fo'.evts, Complete st'.d z) ∧
       (∀ e, G.src e ∈ settledSet fo'.evts → ext (st'.d (G.src e)) e < B →
         st'.d (G.dst e) ≤ ext (st'.d (G.src e)) e)) :=
  ⟨hmono, hwalk, settleSweep_complete t B l h hsettle hwalk, settleSweep_relax t B l h hsettle hwalk hbelow⟩

end DMSY
end Frontier

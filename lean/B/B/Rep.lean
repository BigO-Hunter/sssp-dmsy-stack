import Frontier.DMSY.State
import Frontier.CostModel
import Frontier.RAMRep

/-!
# B.Rep — RAM ↔ A4 representation predicates (work package **B**)

Machine-side representation of the corrected DMSY program's abstract state
(IMPLAN §2 B1–B4 "RAM data"): the label table (B1, the O(1) label fields of the
C-HD `MLabel` pattern), the (E3) settlement log, the D structure (B3), the pivot
groups (B4), and the call-frame blocks the B5–B8 texts read and write.

Two levels of fidelity, deliberately separated:

* **observable decode** (defined here, and *proved* sufficient): the `⊤` flag and the
  real length of each label — exactly the data `RAM.State.label` reads of the output
  arrays.  `outRep_solves` (below) is the output bridge of key lemma 2: complete
  labels + output arrays in this relation ⇒ `State.Solves`.
* **walk-level fidelity** (`MLabel`/ghost-history `Rep`, the paper's
  version-stamped 4-tuples): pinned here as the `LabBlockRep`/`LabTabRep` shape and
  proved for real by B1's texts (`lab.*` fields) — the O(1) *comparisons* only need
  the observable decode plus that fidelity layer.

`Unchanged` helpers in CHD's frame convention (`Frontier.RAMRep.Unchanged`) are
extended here with the per-statement shapes the glue code needs.
-/

open scoped ENNReal NNReal

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD
open RAM

variable {G : Graph} {s : Fin G.n}

/-! ## `Unchanged` helpers (CHD frame convention) -/

section Unch

variable {V : Type} {st : State V}

/-- A register write is confined to that register. -/
theorem unchanged_setW (x : String) (a : ℕ) :
    Unchanged st (st.setW x a) [] [] [x] [] :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ _ => ⟨rfl, rfl⟩,
    fun y hy => by
      show (if y = x then a else st.w y) = st.w y
      rw [if_neg]
      intro h; exact hy (by simp [h]),
    fun _ _ => rfl, rfl, rfl⟩

/-- A word-array store is confined to that array. -/
theorem unchanged_storeW (arr : String) (j a : ℕ) :
    Unchanged st (st.storeW arr j a) [arr] [] [] [] :=
  ⟨fun b hb => ⟨by
      funext q
      show (if b = arr ∧ q = j then a else st.wa b q) = st.wa b q
      rw [if_neg]
      intro h; exact hb (by simp [h.1]), rfl⟩,
    fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A value-array store is confined to that array. -/
theorem unchanged_storeV (arr : String) (j : ℕ) (a : V) :
    Unchanged st (st.storeV arr j a) [] [arr] [] [] :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun b hb => ⟨by
      funext q
      show (if b = arr ∧ q = j then a else st.va b q) = st.va b q
      rw [if_neg]
      intro h; exact hb (by simp [h.1]), rfl⟩,
    fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A word-array allocation is confined to that array (contents and length). -/
theorem unchanged_allocW (arr : String) (k : ℕ) :
    Unchanged st (st.allocW arr k) [arr] [] [] [] :=
  ⟨fun b hb => ⟨by
      funext q
      show (if b = arr then 0 else st.wa b q) = st.wa b q
      rw [if_neg]
      intro h; exact hb (by simp [h]), by
      show (if b = arr then k else st.wlen b) = st.wlen b
      rw [if_neg]
      intro h; exact hb (by simp [h])⟩,
    fun _ _ => ⟨rfl, rfl⟩, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- A value-array allocation is confined to that array. -/
theorem unchanged_allocV (arr : String) (k : ℕ) (z : V) :
    Unchanged st (st.allocV arr k z) [] [arr] [] [] :=
  ⟨fun _ _ => ⟨rfl, rfl⟩, fun b hb => ⟨by
      funext q
      show (if b = arr then z else st.va b q) = st.va b q
      rw [if_neg]
      intro h; exact hb (by simp [h]), by
      show (if b = arr then k else st.vlen b) = st.vlen b
      rw [if_neg]
      intro h; exact hb (by simp [h])⟩,
    fun _ _ => rfl, fun _ _ => rfl, rfl, rfl⟩

/-- The empty write set is a subset of every write set. -/
theorem nil_subset (l : List String) : ([] : List String) ⊆ l :=
  fun _ hx => (List.not_mem_nil hx).elim

/-- Widen a write set to the export triple `["reach"] ["dist"] ["v.i"]`. -/
theorem Unchanged.w3 {st st' : State V} {wa va wr vr : List String}
    (h : Unchanged st st' wa va wr vr)
    (hwa : wa ⊆ ["reach"]) (hva : va ⊆ ["dist"]) (hwr : wr ⊆ ["v.i"]) (hvr : vr ⊆ []) :
    Unchanged st st' ["reach"] ["dist"] ["v.i"] [] :=
  Unchanged.mono h hwa hva hwr hvr

end Unch

/-! ## Label blocks and the label table -/

/-- Observable representation of one machine label block named `pre` (the call-frame
bound blocks `cB.*`/`oB.*`, D values, …): the `⊤` flag register `pre ++ ".top"` and
the real length register `pre ++ ".len"`.  The walk-level fields
(`pre ++ ".hops/.dv/.de/.dver"`) carry the `MLabel` payload and are B1's contract. -/
def LabBlockRep (st : State ℝ≥0) (pre : String) (lab : WLab G s) : Prop :=
  (st.w (pre ++ ".top") = 0 ↔ lab = ⊤) ∧
    (lab ≠ ⊤ → ((st.v (pre ++ ".len") : ℝ≥0) : ℝ≥0∞) = labelLen lab)

/-- The **label table** (B1): one entry per vertex in `lab.*`; observable decode of
the labels `d`.  (The walk-level representation of the entries is B1's `MLabel`
ghost-history contract; everything B proves about output only needs this decode.) -/
structure LabTabRep (st : State ℝ≥0) (d : Labels G s) : Prop where
  wlen : st.wlen "lab.dfin" = G.n
  vlen : st.vlen "lab.dlen" = G.n
  flag : ∀ v : Fin G.n, (st.wa "lab.dfin" v = 0 ↔ d v = ⊤)
  len : ∀ v : Fin G.n, d v ≠ ⊤ → ((st.va "lab.dlen" v : ℝ≥0) : ℝ≥0∞) = labelLen (d v)

/-! ## The output representation and the `State.Solves` bridge -/

/-- The mandated output arrays `reach`/`dist` represent the labels `d`
(`RAM.State.label`'s decode). -/
structure OutRep (st : State ℝ≥0) (d : Labels G s) : Prop where
  wlen : st.wlen "reach" = G.n
  vlen : st.vlen "dist" = G.n
  flag : ∀ v : Fin G.n, (st.wa "reach" v = 0 ↔ d v = ⊤)
  len : ∀ v : Fin G.n, d v ≠ ⊤ → ((st.va "dist" v : ℝ≥0) : ℝ≥0∞) = labelLen (d v)

/-- A label table fully determines the output decode. -/
theorem labTabRep_outRep {st : State ℝ≥0} {d : Labels G s} (h : LabTabRep st d)
    (hw : st.wlen "reach" = G.n) (hv : st.vlen "dist" = G.n)
    (hf : ∀ v : Fin G.n, (st.wa "reach" v = 0 ↔ st.wa "lab.dfin" v = 0))
    (hl : ∀ v : Fin G.n, d v ≠ ⊤ → ((st.va "dist" v : ℝ≥0) : ℝ≥0∞) = ((st.va "lab.dlen" v : ℝ≥0) : ℝ≥0∞)) :
    OutRep st d where
  wlen := hw
  vlen := hv
  flag v := (hf v).trans (h.flag v)
  len v hd := (hl v hd).trans (h.len v hd)

/-- **Output bridge (key lemma 2's seam)**: output arrays representing `d`, with every
vertex complete, give `RAM.State.Solves` — hence exact SSSP through
`isSSSP_of_complete` + `labelLen_dis` (A0 `Basic`). -/
theorem outRep_solves {st : State ℝ≥0} {d : Labels G s} (h : OutRep st d)
    (hall : ∀ v : Fin G.n, Complete d v) : st.Solves G s := by
  refine ⟨h.wlen, h.vlen, fun v => ?_⟩
  show st.label v = G.dist s v
  rw [← labelLen_dis, ← hall v]
  show (if st.wa "reach" v = 0 then ⊤ else ((st.va "dist" v : ℝ≥0) : ℝ≥0∞)) = labelLen (d v)
  by_cases hw : st.wa "reach" v = 0
  · rw [if_pos hw]
    rw [(h.flag v).mp hw]
    rfl
  · rw [if_neg hw]
    exact h.len v (fun hd => hw ((h.flag v).mpr hd))

/-! ## Call-frame representation (the B5–B8 texts' contract surface) -/

/-- Machine-side representation of a `CallEntry`: level register, label table, bound
block `cB.*`, seed table `cS.*`. -/
structure EntryRep (st : State ℝ≥0) (e : CallEntry G s) : Prop where
  level : st.w "l.cur" = e.l
  lab : LabTabRep st e.d
  bound : LabBlockRep st "cB" e.B
  swlen : st.wlen "cS.mem" = G.n
  seed : ∀ v : Fin G.n, (st.wa "cS.mem" v = 0 ↔ v ∉ e.S)
  scnt : st.w "cS.cnt" = e.S.card

/-- The (E3) settlement log decode: `ev.n` counts events; event `i` is
`(kind, v)` in `ev.kind[i]`, `ev.v[i]`. -/
def LogRep (st : State ℝ≥0) (evts : List (SettlementEvent G)) : Prop :=
  st.w "ev.n" = evts.length ∧
    ∀ i (hi : i < evts.length),
      st.wa "ev.v" i = (evts[i]).v ∧
        st.wa "ev.kind" i = (if (evts[i]).kind = .basePull then 0 else 1)

/-- The D structure decode (B3): membership flag `d.on`, stored-value length `d.len`. -/
def DSRep (st : State ℝ≥0) (D : DS G s) : Prop :=
  ∀ v : Fin G.n, (st.wa "d.on" v = 0 ↔ D v = none) ∧
    (∀ lam, D v = some lam → ((st.va "d.len" v : ℝ≥0) : ℝ≥0∞) = labelLen lam)

/-- The line-29 mint log decode (`mn.*`): key, `⊤` flag and length per mint. -/
def MintRep (st : State ℝ≥0) (ms : List (Mint G s)) : Prop :=
  st.w "mn.cnt" = ms.length ∧
    ∀ i (hi : i < ms.length),
      st.wa "mn.x" i = (ms[i]).x ∧
        (st.wa "mn.top" i = 0 ↔ (ms[i]).val = ⊤) ∧
        ((ms[i]).val ≠ ⊤ → ((st.va "mn.len" i : ℝ≥0) : ℝ≥0∞) = labelLen (ms[i]).val)

/-- The pivot-group decode (B4): `pg.cnt` groups; group `j` occupies
`pg.mem[pg.base j, pg.base j + pg.size j)`. -/
def GroupRep (st : State ℝ≥0) (p : ℕ) (P : Fin p → Finset (Fin G.n)) : Prop :=
  st.w "pg.cnt" = p ∧ ∀ j : Fin p, ∀ v : Fin G.n,
    (v ∈ P j ↔ ∃ m < st.wa "pg.size" j, st.wa "pg.mem" (st.wa "pg.base" j + m) = v)

/-- Machine-side representation of a `CallOut` at the level procedure's exit. -/
structure ExitRep (st : State ℝ≥0) (out : CallOut G s) : Prop where
  bound : LabBlockRep st "oB" out.B'
  lab : LabTabRep st out.d'
  log : LogRep st out.evts
  ds : DSRep st out.D
  mn : MintRep st out.mints
  grp : GroupRep st out.pfin out.Pfin

end DMSY
end Frontier

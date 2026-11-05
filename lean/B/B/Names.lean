/-!
# B.Names — the corrected DMSY program's RAM name inventory (work package **B**)

Every register, word array and value array the RAM realization uses, by component,
with the **name-disjointness facts at assembly** (IMPLAN §2 B5–B8 "name lists";
key lemma 3 of the B work order).  Names are strings, as in `Frontier.CostModel`
(`State.w : String → ℕ`), so every fact below is `decide`-closed and kernel-checked.

Conventions: `input*` are fixed by `RAM.initState` (word registers `n`, `m`, `s`;
word arrays `src`, `dst`; value array `w`); `output*` are the mandated output arrays
(`reach`, `dist`).  Every component's names are dotted (`lab.*`, `ev.*`, `d.*`,
`pg.*`, `hp.*`, `sp.*`, `bc.*`, `fp.*`, `sw.*`) so a collision is impossible *by
inspection*; the theorems below make that inspection machine-checked.
-/

namespace Frontier
namespace DMSY

/-! ## Input and output names (fixed by `RAM.initState` / the output contract) -/

/-- Input word registers of `RAM.initState`. -/
def inRegs : List String := ["n", "m", "s"]
/-- Input word arrays of `RAM.initState` (the explicit edge list). -/
def inWArrs : List String := ["src", "dst"]
/-- Input value array of `RAM.initState` (edge weights). -/
def inVArrs : List String := ["w"]
/-- The mandated output word array (`reach[v] = 0` iff `v` unreachable). -/
def outWArrs : List String := ["reach"]
/-- The mandated output value array (`dist[v]`). -/
def outVArrs : List String := ["dist"]

/-! ## Per-component names (IMPLAN §2, B1–B4 data / B5–B8 code) -/

/-- **B1 label table**: one entry per vertex; `lab.dfin` is the "finite label" flag
(the `⊤` bit), the rest are the O(1) label fields `(len, hops, v, e, ver)` of the
C-HD `MLabel` pattern (`len` in the value sort — the comparison-addition machine). -/
def labWArrs : List String := ["lab.dfin", "lab.dhops", "lab.dv", "lab.de", "lab.dver"]
def labVArrs : List String := ["lab.dlen"]

/-- **(E3) settlement-event log**: one entry per event, plus the count register. -/
def evWArrs : List String := ["ev.kind", "ev.v"]
def evRegs : List String := ["ev.n"]

/-- **B3 D structure** (keys are vertices): membership flag + O(1) label fields of
the stored value, plus the live-key counter (the BM.9 `𝒟 ≠ ∅` guard reads it). -/
def dsWArrs : List String := ["d.on", "d.hops", "d.v", "d.e", "d.ver"]
def dsVArrs : List String := ["d.len"]
def dsRegs : List String := ["d.cnt"]

/-- **B4 pivot groups**: per-group base/size tables and the concatenated member list. -/
def pgWArrs : List String := ["pg.base", "pg.size", "pg.mem"]

/-- **B2 indexed heap** (base case / FindPivots worklist): slot table + size. -/
def hpWArrs : List String := ["hp.pos", "hp.heap", "hp.size"]

/-- Skeleton glue registers (`B.Code`): current level, loop flag, per-level event
ceiling, the export loop counter. -/
def glueRegs : List String := ["l.cur", "sp.go", "sp.cap", "v.i"]

/-- O(1) label-comparison primitive (`B.Code.cmpLenStmt`) registers. -/
def cmpRegs : List String := ["cmp.i", "cmp.j", "cmp.lt"]

/-- The B5 (base-case) text's scratch registers — disjoint from every other list. -/
def bcRegs : List String := ["bc.i", "bc.x", "bc.y", "bc.c"]
/-- The B6 (FindPivots) text's scratch registers. -/
def fpRegs : List String := ["fp.i", "fp.j", "fp.x", "fp.go"]
/-- The B7 (level body) iteration text's scratch registers. -/
def spRegs : List String := ["sp.i", "sp.j", "sp.x", "sp.y", "sp.c"]
/-- The sweep fragment's scratch registers. -/
def swRegs : List String := ["sw.e", "sw.d", "sw.c"]

/-- Call-frame arrays (`B.Rep`): seed table, mint log (`mn.x` key, `mn.top` flag). -/
def cfWArrs : List String := ["cS.mem", "mn.x", "mn.top"]
/-- Call-frame word registers: seed/mint/group counts and the `cB.*`/`oB.*` bound-block
word fields (`.top .hops .dv .de .dver`). -/
def cfWRegs : List String :=
  ["cS.cnt", "pg.cnt", "mn.cnt", "cB.top", "cB.hops", "cB.dv", "cB.de", "cB.dver",
    "oB.top", "oB.hops", "oB.dv", "oB.de", "oB.dver"]
/-- Call-frame value arrays: mint lengths. -/
def cfVArrs : List String := ["mn.len"]
/-- Call-frame value registers: the bound blocks' real lengths. -/
def cfVRegs : List String := ["cB.len", "oB.len"]

/-! ## Master lists -/

/-- All word-array names the realization allocates or reads. -/
def allWArrs : List String :=
  inWArrs ++ outWArrs ++ labWArrs ++ evWArrs ++ dsWArrs ++ pgWArrs ++ hpWArrs ++ cfWArrs
/-- All value-array names. -/
def allVArrs : List String := inVArrs ++ outVArrs ++ labVArrs ++ dsVArrs ++ cfVArrs
/-- All word-register names. -/
def allRegs : List String :=
  inRegs ++ evRegs ++ dsRegs ++ glueRegs ++ cmpRegs ++ bcRegs ++ fpRegs ++ spRegs ++ swRegs ++
    cfWRegs
/-- All value-register names. -/
def allVRegs : List String := cfVRegs

/-! ## Assembly disjointness (key lemma 3) — `decide`, kernel-checked -/

theorem allWArrs_nodup : allWArrs.Nodup := by decide

theorem allVArrs_nodup : allVArrs.Nodup := by decide

theorem allRegs_nodup : allRegs.Nodup := by decide

/-- Every component's names lie in the master lists. -/
theorem subset_allWArrs :
    (∀ x ∈ inWArrs, x ∈ allWArrs) ∧ (∀ x ∈ outWArrs, x ∈ allWArrs) ∧
    (∀ x ∈ labWArrs, x ∈ allWArrs) ∧ (∀ x ∈ evWArrs, x ∈ allWArrs) ∧
    (∀ x ∈ dsWArrs, x ∈ allWArrs) ∧ (∀ x ∈ pgWArrs, x ∈ allWArrs) ∧
    (∀ x ∈ hpWArrs, x ∈ allWArrs) ∧ (∀ x ∈ cfWArrs, x ∈ allWArrs) := by decide

theorem subset_allVArrs :
    (∀ x ∈ inVArrs, x ∈ allVArrs) ∧ (∀ x ∈ outVArrs, x ∈ allVArrs) ∧
    (∀ x ∈ labVArrs, x ∈ allVArrs) ∧ (∀ x ∈ dsVArrs, x ∈ allVArrs) ∧
    (∀ x ∈ cfVArrs, x ∈ allVArrs) := by decide

theorem subset_allRegs :
    (∀ x ∈ inRegs, x ∈ allRegs) ∧ (∀ x ∈ evRegs, x ∈ allRegs) ∧
    (∀ x ∈ dsRegs, x ∈ allRegs) ∧ (∀ x ∈ glueRegs, x ∈ allRegs) ∧
    (∀ x ∈ cmpRegs, x ∈ allRegs) ∧ (∀ x ∈ bcRegs, x ∈ allRegs) ∧
    (∀ x ∈ fpRegs, x ∈ allRegs) ∧ (∀ x ∈ spRegs, x ∈ allRegs) ∧
    (∀ x ∈ swRegs, x ∈ allRegs) ∧ (∀ x ∈ cfWRegs, x ∈ allRegs) := by decide

/-- **Component disjointness at assembly**: no name of one component's list occurs
in any other component's list (registers). -/
theorem regs_pairwise_disjoint :
    (∀ x ∈ inRegs, x ∉ evRegs ++ dsRegs ++ glueRegs ++ cmpRegs ++ bcRegs ++ fpRegs ++ spRegs ++ swRegs ++ cfWRegs) ∧
    (∀ x ∈ evRegs, x ∉ dsRegs ++ glueRegs ++ cmpRegs ++ bcRegs ++ fpRegs ++ spRegs ++ swRegs ++ cfWRegs) ∧
    (∀ x ∈ dsRegs, x ∉ glueRegs ++ cmpRegs ++ bcRegs ++ fpRegs ++ spRegs ++ swRegs ++ cfWRegs) ∧
    (∀ x ∈ glueRegs, x ∉ cmpRegs ++ bcRegs ++ fpRegs ++ spRegs ++ swRegs ++ cfWRegs) ∧
    (∀ x ∈ cmpRegs, x ∉ bcRegs ++ fpRegs ++ spRegs ++ swRegs ++ cfWRegs) ∧
    (∀ x ∈ bcRegs, x ∉ fpRegs ++ spRegs ++ swRegs ++ cfWRegs) ∧
    (∀ x ∈ fpRegs, x ∉ spRegs ++ swRegs ++ cfWRegs) ∧
    (∀ x ∈ spRegs, x ∉ swRegs ++ cfWRegs) ∧
    (∀ x ∈ swRegs, x ∉ cfWRegs) := by decide

/-- **Component disjointness at assembly**: arrays. -/
theorem arrs_pairwise_disjoint :
    (∀ x ∈ labWArrs, x ∉ evWArrs ++ dsWArrs ++ pgWArrs ++ hpWArrs ++ cfWArrs) ∧
    (∀ x ∈ evWArrs, x ∉ dsWArrs ++ pgWArrs ++ hpWArrs ++ cfWArrs) ∧
    (∀ x ∈ dsWArrs, x ∉ pgWArrs ++ hpWArrs ++ cfWArrs) ∧
    (∀ x ∈ pgWArrs, x ∉ hpWArrs ++ cfWArrs) ∧
    (∀ x ∈ hpWArrs, x ∉ cfWArrs) ∧
    (∀ x ∈ labVArrs, x ∉ dsVArrs ++ cfVArrs) ∧
    (∀ x ∈ dsVArrs, x ∉ cfVArrs) := by decide

/-- Registers and arrays live in disjoint namespaces in our convention, so no
register name is an array name and vice versa (needed so `Unchanged` write sets
compose across components). -/
theorem regs_ne_arrs :
    (∀ x ∈ allRegs, x ∉ allWArrs) ∧ (∀ x ∈ allRegs, x ∉ allVArrs) ∧
    (∀ x ∈ allRegs, x ∉ allVRegs) ∧
    (∀ x ∈ allVRegs, x ∉ allWArrs) ∧ (∀ x ∈ allVRegs, x ∉ allVArrs) ∧
    (∀ x ∈ allWArrs, x ∉ allVArrs) := by decide

end DMSY
end Frontier

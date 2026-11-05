import Frontier.CostModel
import B.Names

/-!
# B.Code — the corrected DMSY program's `Stmt` tree (work package **B**)

The RAM-level realization of the corrected Duan–Mao–Shu–Yin program (IMPLAN §2
B5–B8) as one uniform deep-embedded `RAM.Program`: a finite `Stmt` tree over the
unit-cost word RAM + comparison–addition machine of `Frontier.CostModel`, with the
subroutine texts of B5–B8 in its procedure table (`Stmt.call`, cost `1` + one cell
of return-point space per call — no automatic frames; the texts share the global
registers and arrays, which is what the name inventory of `B.Names` governs).

Layering (the C-HD `RamBody`/`Spine*` pattern):

* **B7 level body (spine)** — `levelStmt`, the Algorithm-3 control glue written here:
  the `l = 0` dispatch (`ite`), the BM.9 (E3) loop test `goExpr` (`while`), and the
  call sequence FindPivots → init → iterate → tail.  This is real RAM code.
* **B8 recursion driver** — `driverStmt`: top-call setup (`call P_ENTRY`), the level
  body, then the output export.
* **B5/B6 and the iteration/tail/setup texts** — deep subroutine RAM code (Algorithm
  4 with the V5 cap, Algorithm 2, the BM.10–24 iteration, the BM.24a–29 tail) live
  in `Texts`, pinned by their `*Spec` contracts (`B.Realize`), because their bodies
  are the (large) per-text proof obligations; the skeleton above *calls* them.
* **export** — `exportStmt`, the output loop: concrete code proved correct in
  `B.Realize.export_runs`, including its exact write set (`Unchanged`).

Register/array vocabulary: `B.Names`.  The (E3) loop guard reads live counters the
texts maintain: `ev.n` (event count) vs `sp.cap` (= `Engine.eventCap t l.cur`), and
`d.cnt` (live keys of `𝒟`) — bits are combined with word `mul`/`sub`, so the guard
is a pure `WExpr`.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open RAM

variable {G : Graph} {s : Fin G.n}

/-! ## Procedure-table slots -/

def P_BASE : ℕ := 0
def P_FP : ℕ := 1
def P_SETUP : ℕ := 2
def P_ITER : ℕ := 3
def P_TAIL : ℕ := 4
def P_CMP : ℕ := 5
def P_EXPORT : ℕ := 6
def P_LEVEL : ℕ := 7
def P_ENTRY : ℕ := 8

/-! ## Concrete glue texts -/

/-- O(1) label comparison primitive (the first leg of the C-HD `MLabel` order):
`cmp.lt := [lab.dlen[cmp.i] ≤ lab.dlen[cmp.j]]`.  `vle` is the machine's only path
from values to control; this is the shape every label-order test compiles to. -/
def cmpLenStmt : Stmt :=
  .vle "cmp.lt" (.load "lab.dlen" (.var "cmp.i")) (.load "lab.dlen" (.var "cmp.j"))

/-- One export-loop iteration: copy `lab.dfin`/`lab.dlen` entry `v.i` to `reach`/`dist`
and advance the counter. -/
def exportBody : Stmt :=
  .seq (.wstore "reach" (.var "v.i") (.load "lab.dfin" (.var "v.i")))
    (.seq (.vstore "dist" (.var "v.i") (.load "lab.dlen" (.var "v.i")))
      (.wset "v.i" (.add (.var "v.i") (.lit 1))))

/-- The output export loop: allocate `reach`/`dist` (zero-initialised) and copy the
label table's observable decode vertex by vertex (`lab.dfin` flag, `lab.dlen`
length).  Correct and write-set-exact in `B.Realize.export_runs`. -/
def exportStmt : Stmt :=
  .seq (.wset "v.i" (.lit 0))
    (.seq (.walloc "reach" (.var "n"))
      (.seq (.valloc "dist" (.var "n"))
        (.while (.lt (.var "v.i") (.var "n")) exportBody)))

/-! ## The Algorithm-3 spine (B7) and driver (B8) -/

/-- BM.9's (E3) loop guard as a word expression: continue iff the event log is
within the level ceiling (`ev.n ≤ sp.cap`, `sp.cap = Engine.eventCap t l.cur`) and
`𝒟` still has live keys (`d.cnt ≠ 0`). -/
def goExpr : WExpr :=
  .mul (.sub (.lit 1) (.lt (.var "sp.cap") (.var "ev.n")))
    (.sub (.lit 1) (.eq (.var "d.cnt") (.lit 0)))

/-- **The Algorithm-3 level body** (BM.1–BM.31 on the corrected engine (E0)–(E3)):
dispatch `l.cur = 0` to the base case (A1's Algorithm 4 with the (E1) V5 cap),
otherwise FindPivots (A2, `call P_FP`), build the loop state (BM.3–8, `call P_SETUP`),
run the BM.9 loop of BM.10–24 iterations (`while goExpr`, body `call P_ITER`, which
recurses through `call P_LEVEL` at `l - 1`), and take the BM.24a–29 tail
(`call P_TAIL`). -/
def levelStmt : Stmt :=
  .ite (.eq (.var "l.cur") (.lit 0)) (.call P_BASE)
    (.seq (.call P_FP)
      (.seq (.call P_SETUP)
        (.seq (.while goExpr (.call P_ITER)) (.call P_TAIL))))

/-- **The top-level driver** (B8): set up the top call `BMSSP*(⊤, {s}, lTop t n)` from
`initLabels` (`call P_ENTRY`), run the level body, export the output arrays. -/
def driverStmt : Stmt :=
  .seq (.call P_ENTRY) (.seq (.call P_LEVEL) (.call P_EXPORT))

/-! ## The B5–B8 fragment texts and the assembled program -/

/-- The deep subroutine texts the skeleton calls (IMPLAN §2 B5–B8): the base case
(A1's Algorithm 4 with the (E1) V5 cap), FindPivots (A2's Algorithm 2), the BM.3–8
loop-state init, one BM.10–24 iteration (containing `call P_LEVEL` for the child
call), and the BM.24a–29 tail.  Each is pinned by its `*Spec` contract in
`B.Realize`; the skeleton above is closed and independent of their bodies. -/
structure Texts where
  base : Stmt
  fp : Stmt
  setup : Stmt
  iter : Stmt
  tail : Stmt
  entry : Stmt

/-- The corrected DMSY procedure table (slot order = the `P_*` constants). -/
def procs (tx : Texts) : List Stmt :=
  [tx.base, tx.fp, tx.setup, tx.iter, tx.tail, cmpLenStmt, exportStmt, levelStmt, tx.entry]

@[simp] theorem procs_base (tx : Texts) : (procs tx)[P_BASE]? = some tx.base := by
  simp [procs, P_BASE]
@[simp] theorem procs_fp (tx : Texts) : (procs tx)[P_FP]? = some tx.fp := by
  simp [procs, P_FP]
@[simp] theorem procs_setup (tx : Texts) : (procs tx)[P_SETUP]? = some tx.setup := by
  simp [procs, P_SETUP]
@[simp] theorem procs_iter (tx : Texts) : (procs tx)[P_ITER]? = some tx.iter := by
  simp [procs, P_ITER]
@[simp] theorem procs_tail (tx : Texts) : (procs tx)[P_TAIL]? = some tx.tail := by
  simp [procs, P_TAIL]
@[simp] theorem procs_cmp (tx : Texts) : (procs tx)[P_CMP]? = some cmpLenStmt := by
  simp [procs, P_CMP]
@[simp] theorem procs_export (tx : Texts) : (procs tx)[P_EXPORT]? = some exportStmt := by
  simp [procs, P_EXPORT]
@[simp] theorem procs_level (tx : Texts) : (procs tx)[P_LEVEL]? = some levelStmt := by
  simp [procs, P_LEVEL]
@[simp] theorem procs_entry (tx : Texts) : (procs tx)[P_ENTRY]? = some tx.entry := by
  simp [procs, P_ENTRY]

/-- **The corrected DMSY program** as one uniform deep-embedded `RAM.Program`
(A0 `Interfaces.DMSYProgram`): words carry ids, counts, hops and label versions
(`O(log n)`-bit), so word exponent `2` — label *lengths* live in the value sort and
are compared only by `vle`. -/
def dmsyProgram (tx : Texts) : Program where
  body := driverStmt
  wordExp := 2
  procs := procs tx

/-- The assembled program carries the skeleton's procedure table. -/
@[simp] theorem dmsyProgram_procs (tx : Texts) : (dmsyProgram tx).procs = procs tx := rfl

/-- The assembled program's body is the driver. -/
@[simp] theorem dmsyProgram_body (tx : Texts) : (dmsyProgram tx).body = driverStmt := rfl

end DMSY
end Frontier

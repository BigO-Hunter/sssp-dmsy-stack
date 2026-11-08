# A4 Axiom Audit — SORRY Seam Report

**Date:** 2026-11-05
**Build:** full `lake build` of A4 green — 2028 jobs, exit 0. Log: `/private/tmp/sssp_a4_glm_recovery.log`.

## Principal theorems

`Frontier.DMSY.a4_joint`, `lemma37Star`, `theoremT`, `a4_contract` depend on `sorryAx`.
The dependency is localized to exactly two source lines:

- `A4/A4/Main.lean:65`
- `A4/A4/Main.lean:80`

This is the CORRECTED_PROOF §8.1 joint-chain seam — a documented, intentional
placeholder (see `A4/A4/AxiomCheck.lean:177`).

## Everything else is clean

- Audited scope: 155 declarations across 15 modules, plus explicit probes of
  `coneClosure_of_run`, `coneClosure_of_callPre_run`, `reachable_dst`.
- All clean: axiom base is exactly `[propext, Classical.choice, Quot.sound]`.
- The `import cone` module was verified clean and is **not** the cause of the
  sorryAx dependencies.

## Conclusion

The only sorry in the A4 stack is the two-line §8.1 joint-chain seam in
`Main.lean`. No hidden axioms, no unexpected `Classical.choice`-beyond-standard,
no sorry leakage from imported modules.

---

## §8.1 status after a closure attempt (2026-11-08) — both seams remain

**Re-verified from a fresh clone**, pin `leanprover/lean4:v4.34.1` + mathlib
`d13f23b7` (the repo's own `lean-toolchain`/`lakefile.toml`): `lake build` exit 0
over A0–A4; `lake env lean A4/AxiomCheck.lean` audits 89 declarations — 82 at
`[propext, Classical.choice, Quot.sound]`, 1 (`pullCap_add_fpCap_le_memCap`) at
`[propext, Quot.sound]`, and 6 on `sorryAx`: `a4_joint`, `lemma37Star`,
`theoremT`, `a4_contract`, `top_full_facts`, `top_exact_at` (the last two consume
`a4_joint`). `grep '\bsorry\b'` over A0–A4 finds no other `sorry`/`admit`. So the
source confinement claim above still holds exactly.

### The two seam statements

- `Main.lean:65` — `a4_joint : @JointChain G s t`, i.e.
  `∀ e out, Reach t e → Lemma37Hyp t e → Run t e out → Lemma37Concl (Full t) e out ∧ NoPrem e out`.
- `Main.lean:80` — `theoremT : @TheoremT G s (@Reach G s t) (@Run G s t)`, i.e.
  `∀ e out, Reach t e → Run t e out → ∀ x val, ¬ out.Premature x val`.

### Seam 2 (`theoremT`) — attempted, mechanically reduced, blocked at one goal

Probed in a scratch module against the built library (discarded; not a root):

1. The `l = 0` half is **free**: a base return's `mints = []` (`Semantics.baseOut`), so
   `∀ x val, ¬ (baseOut bout).Premature x val` closes immediately.
2. The `recur` half closes **given** `LabelFloorHyp t`: `run_mintFloor` gives
   `out.B' ≤ m.val` for every final mint, contradicting `val < out.B'`.
3. The unconditional `recur` half stops at exactly one goal — `⊢ LoopBInv stf.bp stf`
   (via `PremLabelKey.prem_empty_recur`). The only producer of `LoopBInv` is
   `LoopBInv.iloop_bInv`, whose premise is `ChildLabelFloor st fo'` at every step.

`ChildLabelFloor st fo'` reads: a residual group member **not** settled by the child
has child-returned label `≥ fo'.B'`. That is precisely Lemma 3.7\*(2b)/(2c) at the
child, i.e. the child's `Lemma37Concl` — the same object `a4_joint` must produce. And
at a leaf it is *equivalent* to `NoAbandonedBelow` (`MintPreFloor.childLabelFloor_base_iff`,
`mintPreFloor_base_iff`), which `CallPre + baseRun_lemma31` do not force
(`MintPreFloor.base_leaf_counterexample` is a formalized leaf where it fails). So seam 2
is **not independent** of seam 1: it is the `NoPrem` half of the same joint induction,
and `Reach` alone does not even supply `Lemma37Hyp` (`JointAssembly.lemma37Hyp_of_reach`
needs the step-uniform `ChildStep` and `StepSplit` premises).

### Seam 1 (`a4_joint`) — the return side is the whole obstuction

`Lemma37Concl` has six clauses at the return, and each already carries a named,
falsifiable-or-unreachable residual in this tree rather than an open proof:

| clause | unit that reduces it | residual it names |
|---|---|---|
| `frontier`, `progress`, `uSubset` | `A4.BpMonotonicity`, `A4.DrainedClauses` | per-step `ChildStep` / loop `B'` chain |
| `identity` (2c) | `A4.IdentityCover` | `Yclear`, or `LowKeyAccurate + BelowLabelFloor` |
| `containS`/`containR` (3) | `A4.NoLoose` §3 | full execution + `CandSettled` |
| `bound` (2b) | `A4.LemmaV`, `A4.PremLabelKey` | `LoopBInv` (`ChildLabelFloor` again) |
| `settleComplete` | `A4.JointAssembly.istepTrace_childStep` | `ChildFloor` (`A4.BelowSeparator`) |
| `fullImmune`, `premInD`, `premShape` | **proved** (`Structural.full_no_prem`, etc.) | — |

Per `A4.CustodyInduction` §4/§6 and `A4.JointAssembly`'s closing note, closing them all
is the joint first-violation induction of `research/CORRECTED_PROOF.md` §8.1 — the audit's
hand proof ("the main body of the Lean work"), which nothing in this artifact re-proves.

### Status line

`sorryAx` remains confined to `A4/A4/Main.lean:65` and `:80`. Both are the §8.1 joint
chain, not two independent gaps: seam 2 reduces to seam 1's `bound` clause, and neither is
closeable from this artifact's own lemmas without importing the audit's induction or adding
antecedents strong enough to restate the theorem. Leaving the named `sorry`s is the honest
state; a closer must supply the joint induction (or `NoAbandonedBelow`-strength leaf linkage
from the parent's `pullRun`/`expand`/`FPContract` residual groups).

*Construction (DMSY, arXiv:2602.07868v1) is the original authors'; the durable copy, build
harness, axiom audit and this closure attempt are ours.*

---

## §8.1 formalization WIP (2026-11-08, session 2) — `A4/A4/JointInduction.lean`

The hand induction is now transcribed into the tree and its **shape** is machine-checked. New
module (build root), axiom-clean throughout (`[propext, Classical.choice, Quot.sound]`):

* **Transcription** (module docstring): the induction is on the **settlement-event index**
  (batches of `U`), not on steps or mint depth (§4.4, `PROOF.md` §3); the two conjuncts
  `settleComplete` (2a) and `NoPrem` (Theorem T) are joint because completeness ⇒ floor and
  floor ⇒ next batch's completeness; the per-batch case split is W / V / Rep / `W'`-drop /
  refusal-floor / d2, each mapped to the unit here that reduces it.
* **`childLabelFloor_of_storeTight`** (the crux bridge, new): `ChildLabelFloor st fo'` follows
  from the child's bound clause (2b) + `NoPrem` + store accuracy `ChildStoreTight`. This is
  Lemma V at the child boundary read through the store — and it shows exactly why the two
  clauses cannot be separated: `bound` constrains *values*, the floor needs *labels*, and labels
  only decrease, so the accuracy invariant is load-bearing.
* **`jointChain_of_steps`** (the wiring, new): `JointChain t` follows from (i) a level-`0`
  return obligation, (ii) §8.1's `recur` step obligation taking the IH at every child, plus the
  two entry-side premises `A4.JointAssembly` already isolates (`ChildStep`-uniform, `StepSplit`)
  and `2 ≤ t` (at `t < 2` the `Lemma37Hyp` premise is unsatisfiable, so the statement is
  vacuous). The motive is level-split because a reachable child may be a level-`0` entry.
* `JointInv` (the named IH body), `jointChain_iff`, `noPrem_of_mintValueBound`,
  `noPrem_recur_of_stepFloor` (Theorem T's recur half from the carried `LoopBInv`).

**What is still open, named once instead of six times:** the `recur` obligation needs carried
invariants that `Reach` does not supply — `LoopBInv` (labels of residual members ≥ running
bound), `ChildFloor` (settled completeness), `StepSplit` (coverage), and a *group-restricted*
label↔store accuracy. The global accuracy form (`ChildStoreTight`) is itself false at drained
leaves (`MintPreFloor.base_leaf_counterexample`), so the carriable form coincides with
`ChildLabelFloor`; `childLabelFloor_of_storeTight` is the reason the two §8.1 halves cannot be
split, not an independent reduction. Each premise has a documented reason it is not free from
`Run`/`Reach` alone: `Reach` carries only `WalkInv` (`Structural.reach_sound`), no
`CallPre`/`ChildOf` reachability producers exist, `LabelKey` is refuted at engine states
(`PremLabelKey.labelKey_refuted_at_engine_state`), and the leaf instance of the floor is
equivalent to `NoAbandonedBelow`, which `CallPre + baseRun_lemma31` do not force.
Closing these is the audit's Lemma W/V/Rep machinery
for a real engine semantics; `a4_joint`/`theoremT` therefore keep their `sorry`s, with the
obligation set now stated in one place.

**Axiom count: unchanged — 89 declarations audited, 6 on `sorryAx`** (`a4_joint`,
`lemma37Star`, `theoremT`, `a4_contract`, `top_full_facts`, `top_exact_at`), all traced to
`Main.lean:65`/`:80`. The new module adds 6 axiom-clean declarations.

---

## Base-return slice + the `t < 2` correction (2026-11-08, session 3)

New module `A4/A4/BaseReturn.lean` (build root), all declarations
`[propext, Classical.choice, Quot.sound]`.

**9 of `Lemma37Concl`'s 11 clauses are now closed at a level-`0` return**, from A1 alone
(`base_frontier` reads `BInv.frontier` at the loop exit — it is stated at `(settledSet st.evts,
keys st.D)`, verbatim the return record):
`progress`, `settleComplete`, `uSubset` (A1's `Lemma31Concl` verbatim), `bound` (A1's cap law
`B'⁺ ≤ dMin B 𝒟_final` read per key via `dMin_le_of_mem`, carve-out disjunct dead),
`premInD`/`premShape`/`fullImmune` (vacuous — base returns mint nothing), `identity` (A1's
identity with `carveKeys = ∅`), plus Theorem T's half `NoPrem`. `jointInv_base_of_package`
assembles `JointInv` at a level-`0` return from those plus the **two** clauses A1 does not
deliver — (3) `containS` (pull remainder) and (3) `containR` (keyed boundary closure) — and
`jointChain_of_steps_of_base` re-states the induction with `hbase` discharged down to those two.
So the level-`0` obligation is now *one* place with *two* named gaps, not eleven.

**Correction to the previous entry.** It claimed `JointChain t` is vacuous for `t < 2`
"because `Lemma37Hyp` is unsatisfiable". That is **false**: `lTop 0 n = log₂ n` is usually
positive, so at `t = 0` only the *top* entry fails `Lemma37Hyp` (`1 ≤ 0` false —
`lemma37Hyp_zero_top_false`), while a level-`0` child with `S = ∅` satisfies it; and at `t = 1`
`memCap 1 l = 2^l ≥ 1`, so nothing is vacuous (`ReachHyp.pullCap_add_fpCap_gt_memCap_at_one`
shows the child-size step is unavailable there). Verified statement: the induction is
established for `2 ≤ t`; `a4_joint`'s `∀ t` still needs `t ∈ {0,1}`, open on the **size** step
(Lemma 3.5's `|S_child| ≤ memCap t (l−1)`), not on vacuity.

---

## `containS` closed; the size step is exactly `t ≥ 2` (2026-11-08, session 4)

New module `A4/A4/BaseContain.lean` (build root); `lake build` green (2031 jobs); every
declaration at `[propext, Classical.choice, Quot.sound]` (`fpCap_zero` uses none at all).

**`containS` at a level-`0` return — proved.** `base_containS`: an unsettled seed is still keyed.
The mechanism is the engine's own: `𝒟` starts as `initD S d` (every seed keyed), an iteration
deletes exactly the vertex it settles, and its sweep only inserts. So the file proves the
missing engine lemma A1 lacked — **the ungated sweep never drops a key**
(`relaxEdge_ne_none`, `sweep_ne_none`, `iter_ne_none`) — plus the invariant
`LoopInvS := S ∖ settledSet ⊆ keys 𝒟` through the whole `Loop` (`loopInvS_iter`,
`loop_loopInvS`). `jointChain_of_steps_of_baseS` therefore drops `containS`:
**one** base-side gap remains (`containR`).

**`containR` — still open, now precisely diagnosed.** `BInv.frontier` yields only a *path*
witness (`∃ y ∈ keys 𝒟, OnPath y v`), never `v ∈ keys 𝒟`; the deciding fact is label
**provenance** — `v`'s label is the value of an accepted relaxation at some settled vertex, which
inserted `v`, and `v` unsettled ⇒ never a pull-min ⇒ never deleted. A1's `BInv` carries `fresh`
but no provenance field, so this needs one more loop invariant, not another consequence of `BInv`.

**The `t ∈ {0,1}` verdict — recommendation-ready.** `jointChain_of_steps` needs `2 ≤ t` for
exactly one reason: the child-size step `pullCap t l + fpCap t ≤ memCap t (l−1)`. Since
`memCap t (l−1) = t²·2^((l−1)t)` and `pullCap t l = t·2^((l−1)t)`, that inequality is equivalent
to `fpCap t ≤ t(t−1)·2^((l−1)t)`, and `fpCap t = max 1 (t/3) ≥ 1`. So it holds **iff `t ≥ 2`** —
proved as `pullCap_add_fpCap_le_memCap_iff`. Both low values fail by exactly the FindPivots
singleton: `ReachHyp.pullCap_add_fpCap_gt_memCap_at_one` (t=1) and `sizeStep_fails_at_zero`
(t=0, since `pullCap 0 l = 0`, `memCap 0 (l−1) = 0`, `fpCap 0 = 1`). Neither case is vacuous
(the `t = 0` top entry fails `Lemma37Hyp`, but a level-0 child with `S = ∅` satisfies it), so
`a4_joint : ∀ t` is **not** closable through this route at `t ∈ {0,1}`.

Two ways out, both repo-owner decisions (the pinned statement is unchanged):
(a) sharpen `childOf_seed_size` to `|S_child| ≤ pullCap t l`, dropping the singleton — would
close `t = 1` if A2's contracts support it; or (b) add `2 ≤ t` to `a4_joint`'s antecedent, the
parameter regime the paper's complexity discussion assumes anyway.

**Axiom count: unchanged — 89 audited, 6 on `sorryAx`**, all traced to `Main.lean:65`/`:80`.


---

## Statement transcription: `a4_joint` now carries `2 ≤ t` (2026-11-08, session 5)

**Decision (coordinator, statement-level):** adopt recommendation (b) from the previous entry —
`a4_joint` takes an antecedent `ht : 2 ≤ t`. Rationale on record: the paper's complexity
discussion is the `2 ≤ t` regime, so the `∀ t` form was **our** flattening. This is a transcription
correction toward what the paper proves (same class as the σ-subset fix), not a weakening for
convenience; the conclusion `@JointChain G s t` is byte-identical.

**Proof receipt for the boundary:** `BaseContain.pullCap_add_fpCap_le_memCap_iff` — the child-size
step holds **iff** `2 ≤ t`. Below it the deficit is exactly the FindPivots singleton
(`fpCap t = max 1 (t/3) ≥ 1`): `ReachHyp.pullCap_add_fpCap_gt_memCap_at_one` at `t = 1`, and
`BaseContain.sizeStep_fails_at_zero` (+ `fpCap_zero`) at `t = 0`.

**Boundary documented, not hidden:** at `t = 0` the top entry fails `Lemma37Hyp` outright
(`BaseReturn.lemma37Hyp_zero_top_false`), while a level-`0` child with `S = ∅` still satisfies it —
so `t = 0` is not vacuous — and at `t = 1` `memCap 1 l = 2^l ≥ 1` is satisfiable. The antecedent is
therefore load-bearing, and the antecedent propagates to `lemma37Star`, `theoremT` and
`a4_contract` (same seam); `A0`'s `A4Contract` definition is untouched.

**Named sharpening follow-up (NOT attempted):** prove `|S_child| ≤ pullCap t l`, dropping the
singleton, which would close `t = 1` if A2's contracts support it and would restore the `∀ t` form.

**Receipts after the change:** `lake build` green (2031 jobs); `a4_joint`, `lemma37Star`,
`theoremT`, `a4_contract` still on `[propext, sorryAx, Classical.choice, Quot.sound]` (their bodies
are the two named `sorry`s); audited total unchanged at 89 declarations / 6 on `sorryAx`.

---

## `containR` at level 0 — closed modulo entry custody (2026-11-08, session 6)

New module `A4/A4/BaseCustody.lean` (build root); `lake build` green (2032 jobs); all eight
declarations at `[propext, Classical.choice, Quot.sound]`.

**The mechanism.** `A4.ReturnClauses.callOut_tail_containR` proves `containR` at a tail from
`Custody` ("a live label is settled or queued", `CustodyL`). This file mirrors those gated-sweep
custody lemmas for A1's **ungated** engine — `relaxEdge_custody`, `sweep_custody`,
`iter_custody`, `loop_custody` — and reads the invariant at the base exit
(`base_custody_of_entry`), then `base_containR_of_entryCustody` (same shape as the tail lemma;
the bound hypothesis is not needed).

**What remains, named once.** Custody must hold at the loop's *initial* state
`⟨e.d, initD e.S e.d, [], e.B⟩`, where it reads: **every finite entry label is a seed**. It is
true at the top-level base call (the top entry's labels are `initLabels`, `⊤` off `{s} = e.S`),
and at child entries it is the same `Custody` the recur side already maintains
(`A4.ReturnClauses.tail_custody`) — so it belongs to the `Reach`-strengthening, not to A1. It is
**not** derivable from `CallPre + baseRun_lemma31`: a non-seed vertex can carry a finite entry
label, be refused by every sweep of this call, and end up the tight relaxation target of a
settled vertex whose label later dropped — written-never, keyed-never, yet `Relaxed` at the
return (sketch-grade; not formalized). So `jointChain_of_steps_of_baseC` discharges `hbase` down
to **entry custody alone** — `hbase` is *not* hypothesis-free, and that is the honest state: the
premise is load-bearing, not slack.

**Recorded resolution of the session's open unknown:** the induction did *not* need label
monotonicity across iterations — the spec'd `LoopInvR` shape was replaced by `CustodyL`, whose
step case needs only "writes happen through accepted relaxations, which insert" plus the fact
that the settlement log only grows. `jointChain_of_steps_of_base` (in `BaseReturn`) is thereby
superseded by `jointChain_of_steps_of_baseC` (in `BaseCustody`).

**Axiom count: unchanged — 89 audited, 6 on `sorryAx`**, all traced to `Main.lean:65`/`:80`.

---

## Entry custody: top closed, child obstruction named (2026-11-08, session 7)

`BaseCustody.custody_top_base` (axiom-clean): the top-level base call's entry custody holds —
`initLabels` is `⊤` off `{s}`, so the only finite label is the source, which `initD {s}` keys.
The top-level base call's `containR` is therefore closed by `BaseCustody`'s lemmas.

**The child-entry obstruction is named and binding** (module docstring, `BaseCustody`): entry
custody at a *child* base call is not derivable from the parent's exit custody and is almost
certainly false at reachable states — the child's store is *fresh* (`initD c.S c.d` keys only
seeds) while `c.d` inherits finite labels at parent-settled vertices, which are neither in `c.S`
(settled members leave the groups, BM.17; pulled keys deleted), nor settled in the child's own
empty log, nor keyed.  So `Custody` does **not** thread through `ChildOf` — the shared-carrier
stall named as this lane's stop boundary is reached, and `hbase` is **not** closed
hypothesis-free: the base-side premise remains entry custody, which is load-bearing at children.
The child case belongs to the recur-side wave, where the carriers are the joint induction's own
invariants (settlement completeness, the maintained frontier) — exactly the program points the
audit's hand proof drives through `ChildFloor`, not through custody over a fresh store.

**Axiom count: unchanged — 89 audited, 6 on `sorryAx`**, all traced to `Main.lean:65`/`:80`.

---

## Recur wave opened: carrier correction + wave map (2026-11-08, session 8)

`JointInduction` §1b (doc, compiled; all receipts unchanged and clean) records the wave plan and
one correction the tree forces:

**Carrier correction (proved, not editorial):** `ChildLabelFloor`/`LabelFloorHyp` as a *uniform*
step premise is refuted by the tree itself — `MintPreFloor.not_childLabelFloor_base` refutes the
floor whenever a residual group member is abandoned below the child's returned bound (Q12's
child-interior channel), and `MintPreFloor.base_leaf_counterexample` is a formalized leaf where
the floor's invariant `NoAbandonedBelow` fails under `CallPre + baseRun_lemma31` alone.  So the
recur wave must carry the floor **group-restricted, inside the joint induction itself** (the
audit's first-violation ordering supplies it exactly where the parent's invariant maintains it) —
never as a free-standing hypothesis.  Any route that assumes `LabelFloorHyp` uniformly is dead on
arrival; `childLabelFloor_of_storeTight`'s premise inherits the same restriction.

**Wave order** (each mapped to its §8.1 case): (1) `ChildFloor` — Lemma d2, settlement
completeness at one iteration; `istepTrace_childStep` reduces the per-step premise to it +
`ChildStoreTight`.  (2) `LoopBInv` — Lemma V, no sub-`B'` values; via the group-restricted floor,
`istep_bInv` + `prem_empty_recur` give the value bound and Theorem T's recur half.  (3)
`StepSplit` — coverage/(J6), clause (1)'s loop invariant; `lemma37Hyp_of_reach` consumes it.
Then `hrecur` assembles by `jointChain_of_steps`.

**Status of the two open items:** the child-entry custody premise (`BaseCustody`) is discharged
by this wave per the redirect — not by `Custody` (fresh-store obstruction on record there); the
`containR` counterexample sketch for child base returns was **not formalized** (budget) — the
sketch stands as recorded in `BaseCustody`'s docstring, and formalizing it would be a
statement-level finding for the repo owner.

**Axiom count: unchanged — 89 audited, 6 on `sorryAx`**, all traced to `Main.lean:65`/`:80`.

---

## Wave slice (1): `theoremT_of_labelFloorHyp` — the target pinned (2026-11-08, session 9)

`JointInduction.theoremT_of_labelFloorHyp` (axiom-clean): **byte-identical `@TheoremT` follows
from `LabelFloorHyp` alone** — no reachability needed, since the value bound
(`run_mintFloor`) holds for every run. This pins exactly what closes seam 2: the group-restricted
floor at the parent's residual groups.

**Scoping of the first instance (the slice's finding).** The instance cannot be taken at an
arbitrary leaf (`not_childLabelFloor_base` refutes the floor there on an abandoned group member;
`base_leaf_counterexample` formalizes a failing leaf) and at the **top-level base call** there
are no steps at all, so `hrecur` is never invoked on one. The first real instance is at a
**recur step of a reachable run**, and its missing producer is exactly the parent-side linkage
`MintPreFloor`'s closing note names: `resid j ⊆ expand … S_i B_i`. That linkage is the wall; the
new theorem pins what it buys when it lands.

**Axiom count: unchanged — 89 audited, 6 on `sorryAx`**, all traced to `Main.lean:65`/`:80`.

---

## Scoping slice: the wall located in A2/A3's vocabulary (2026-11-08, session 10)

`JointInduction` §3d (doc-only, prose in a green module): the contract vocabulary **does** expose
the membership half of the `resid ⊆ expand` linkage — `IStep`'s child entry is
`c = ⟨Bi, expand st.d st.pl st.piv Si Bi, l-1, st.d⟩`, and `expand` puts every group member with
`d v < Bi` into `c.S` whenever the group's pivot is pulled (`mem_expand_of_group_low`-shaped
one-liner; drafted, **not landed** — compile verification cut off by host pressure, and an
unverified lemma is worse than none; first line of the next session).

**The wall moved and is now located exactly**, as two non-definitional halves:
(1) the pivot-pulled side needs the pre-state fact `piv j ∈ Si ∧ piv j ∈ pl j` for the floor's
groups (step bookkeeping à la `istepTrace_child_d`); (2) the pivot-not-pulled side has **no
expansion** — those members' non-abandonment must come from Lemma W's window/bound-monotonicity
content.  Plus the child's `Lemma37Concl.identity` (y ∈ c.S settles unless carve-out) + `NoPrem`.
Each ingredient now has a named producer; together they are exactly the audit's joint
first-violation induction, confirming the carrier correction.

**Axiom count: unchanged — 89 audited, 6 on `sorryAx`** (doc-only change).

---

## Half 1 landed: the step's own expansion, unpacked (2026-11-08, session 11)

`JointInduction.istep_unpack` (the mechanical seventeen-field `obtain` pinned as a lemma: a step
determines its pull witnesses, and `c.S` is the step's own expansion) and
`JointInduction.seed_of_expand_mem` (**half 1**: a residual-group member whose label is below the
separator, in a group whose pivot is pulled, is in the child's seeds — `mem_expand_of_group_low`
instantiated at the step's own `pl`/`piv`/`Si`/`Bi` through the child entry's defining equation).
Both axiom-clean; `lake build` green (2032 jobs). The unpacking shape flagged as untried was
tried and is correct: `IStep`'s existentials destructure exactly as `Main.lean`'s working
pattern.

Remaining to `LabelFloorHyp`: half 2 (pivot-not-pulled members' non-abandonment, Lemma W's
window) and the assembly. **Axiom count: unchanged — 89 audited, 6 on `sorryAx`.**

---

## Half 2 scoped: the wall is the audit's window argument (2026-11-08, session 12)

`JointInduction` §3d.2 (doc-only, prose in a green module): half 2 cannot be derived from
`istep_bInv` (that is the circle — it consumes `ChildLabelFloor`).  The sweep gate gives only
"unchanged or `≥ lo`" (`sweepEvts_label_cases`), so a low label persists; the window must come
from `LoopBInv B st` at the pre-state plus `BpChain` — and `BpChain` is the per-call `B'`
monotonicity that `CORRECTED_PROOF` §8 item 5 flags as unproved even at sketch grade
(`A4.ReturnClauses`: "the one genuinely inductive premise").  Scope recorded for the proof:
carry `BpChain` + `LoopBInv B st`, read the unchanged case via `sweepEvts_label_cases`, floor
the changed case by the gate (`lo = Bi = c.B ≥ st'.bp` via `BpChain`).

**Axiom count: unchanged — 89 audited, 6 on `sorryAx`** (doc-only change).

---

## BpChain determined: outcome (b) — per-step monotonicity available under sourced hypotheses (2026-11-08, session 13)

`JointInduction` §3d.2 determination: `BpMonotonicity.istep_bp_mono` gives `st.bp ≤ st'.bp` per
`IStep` from `SeedFloor st.bp c` + `SeedChildFloor c fo'`, and `istep_bp_mono_of_liveFloor`
sources the first from `LiveFloor st` (`istep_seedFloor`). Half 2's assembly: carry `LiveFloor st`
+ `SeedChildFloor c fo'`, take the monotonicity, read the unchanged-label case through
`sweepEvts_label_cases` with `LoopBInv B st`, floor the changed case by the gate
(`lo = Bi = c.B ≥ st'.bp`). Still missing: the assembly itself + the sources of
`LiveFloor`/`SeedChildFloor` at reachable steps — the next session's slices.

Also registered: wound **2125609282** (containR base instance possibly false at child level-0
returns; sketch-grade, formalizing it is the named next step). **Axiom count: unchanged — 89
audited, 6 on `sorryAx`** (doc-only change to a compiled module).

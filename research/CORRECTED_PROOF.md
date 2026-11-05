# CORRECTED_PROOF.md — Lemma 3.7 (and 3.8/3.9) of Duan–Mao–Shu–Yin, repaired

Target: the BMSSP analysis of *"A Faster Directed Single-Source Shortest
Path Algorithm"* (Duan, Mao, Shu, Yin, arXiv:2602.07868v1), Lemmas
3.1–3.9, with the four defects recorded in the audit
(`primaryaesthetics/beyond-dijkstra`, `QUESTIONS.md` Q3, Q9, Q11, Q12,
Q13, Q14; `PROOF.md`; `VARIANTS.md` "Algorithm 3's contract,
transitively") fixed at the statement level. This document is written
as a basis for a Lean formalization: every clause is stated so that its
proof obligation is local and explicit, and every place where the
obligation is *not* discharged is named in §8.

Defects fixed:

| id | defect | fix |
|----|--------|-----|
| Q3 | Base case (Alg. 4) returns B′ above values it inserts after the final Pull; undercuts Lemma 3.7(2) and Lemma 3.1 | **(E1) V5 cap** at leaves + transitive proposition (§2, §4.1) |
| Q12 | Line 29's re-selection insert is the one ungated D-insert; the three clauses of 3.7 are jointly unsatisfiable in the Q12 state, no local repair exists | **statement-level weakening** of clause 2 with an explicit premature-entry carve-out (§3, §4.2); optional engine-level partial fix (E2) |
| Q9 | Lemmas 3.1/3.2/3.7 are false as standalone contracts; true only on states reachable from a top-level run | **reachable-state closure** in every precondition (§2.3, §4.3) |
| Q11/Q14 | Duplicate settlements (stale-entry re-frontierings + call-local W′ filter) falsify Lemma 3.8's disjoint-union and the Σ\|U\| accounting of Lemma 3.9 | **re-settlement bound** (Lemma R) replacing disjointness in 3.8/3.9 (§5, §6) |

---

## 1. Notation and grade

Graph G = (V, E), non-negative real weights w; source s; every vertex
reachable from s (w.l.o.g.); after degree reduction max in/out-degree ≤ δ,
|V| = O(m/δ), |E| = O(m). Parameters t, k = ⌈t/log t⌉, δ ≤ log k ≤ k ≤ t,
l ∈ [0, ⌈(log n)/t⌉], M = t·2^((l−1)t) for a level-l call.

Labels are 4-tuples ⟨length, nEdges, curr, pred⟩ in lexicographic order
(§2.3 of the paper); `Relax(u,v,B)` accepts iff `d[u]+w_uv ≤ d[v]` **and**
`d[u]+w_uv < B`, storing ⟨d[u].len+w, d[u].hops+1, v, u⟩. Ties are
re-accepted (an idempotent store — load-bearing, audit Q6).

- **lh(v)** — lexicographic minimum of (len, hops) over all s→v paths;
  **dis(v)** = lh(v).len (true shortest-path length).
- **complete** — (d[v].len, d[v].hops) = lh(v). *Length-grade projection:*
  d[v].len = dis(v). The pred slot is excluded from completeness claims by
  design (prefix optimality fails there; audit §11–§12).
- d_B[U] = min({B} ∪ {stored values of keys in U}); dis_B(U) likewise.
- Ũ = Ũ(B,S) = {v : dis(v) < B and v's shortest path visits some vertex
  of S}. ⟨X,Y⟩ frontier for Ũ per §2.4. R(B,Z) per §3.5.
- A **settlement event** is a base-case pull (Alg. 4) or a W′ boundary
  append (Alg. 3, line 34). U is treated as the **settlement log**
  (event semantics, audit Q13 — see §2.2).

Standing structural facts (proved by trivial inductions over the engine;
they are the Lean "invariants" file):

- **(I1) Label honesty.** Every finite label is a path tuple: the source
  label ⟨0,0,s,−1⟩ or an accepted candidate built from a path tuple.
  Hence (d[v].len, d[v].hops) ≥_lex lh(v) always.
- **(I2) Monotonicity.** Labels only decrease.
- **(I3) Entry honesty (keep-min).** Every 𝒟 entry stores a historical
  label; an entry's stored value ≥ the key's current label. Keys are
  unique per 𝒟 (keyed dedup keeps the smaller value).
- **(I4) Bound nesting.** Every stored value of a call's 𝒟 is < the
  call's bound B; pull separators ≤ B; child bounds ≤ parent bound.
- **(Z) Path monotonicity.** Consecutive prefix tuples along a path are
  lex-strict (hops increments even at w = 0), so lh-canonical paths are
  finite and cycle-free; comparisons strict in the (len,hops) prefix are
  decided there.

## 2. The corrected engine

### 2.1 Engine deltas

**(E0) Nonempty-argmin guards** (audit Q2/Q8: the printed pseudocode
crashes): lines 6 and 28 skip empty P_j; line 28's re-selection is
skipped when P_j = ∅ after removals. Assumed everywhere below.

**(E1) V5, the leaf cap** (fixes Q3). Algorithm 4 returns

  B′⁺ = min(B′_pull, d_B[𝒟_final]),

where B′_pull is the separator returned by the final Pull (B if 𝒟
drained) and 𝒟_final is the returned structure including post-final-pull
inserts. Cost: one min-peek, O(1) amortized. The D itself is untouched.

**(E2) Line-23 reading (optional, recommended).** The sweep relaxes
only candidates in [B_i, B) — the paper's *prose* semantics ("relax
every edge (u,v) such that d[u]+w_uv ∈ [B_i, B)"), instead of the
pseudocode's full `Relax(u,v,B)` + gated insert. This closes Q12's
sweep channel (§4.2); the child-interior channel survives and is handled
by the clause-2 weakening regardless.

**(E3) U as settlement log, guard on events** (audit Q13). Line 9's
guard compares |U| = number of settlement events (the pinned semantics
of the audit's reference), not distinct vertices. Under set semantics
the top-level guard can never fire (totality is then unconditional) but
*no* ceiling on settlement events exists anywhere; under event semantics
a completed run certifies T ≤ t³·2^(l_top·t) − n₂ on the total duplicate
excess and an overflow aborts loudly. Everything below is stated under
(E3); the set-semantics variant is noted where it differs.

### 2.2 Run shape

A **run** starts from initialization (d[s] = 0, d[v] = ∞ else) and calls
BMSSP*(∞, {s}, l_top), l_top = ⌈(log n)/t⌉. The recursion tree 𝒯, the
call-stack nesting, and per-call subscripts (B_X, S_X, B′_X, U_X, 𝒟_X,
P_X,j, Q_X, W_X, W′_X) are as in §3.4 of the paper.

### 2.3 Reachable-state closure (fixes Q9)

**Definition (Reach).** A state σ (global labels, active call stack with
their 𝒟's, recursion tree) is *reachable* if it is obtained from run
initialization by a finite sequence of the engine's own atomic steps
(E0–E3). All lemmas below quantify: **for every reachable σ at the
stated program point.**

This is not cosmetic. Audit Q9 exhibits a state satisfying the printed
precondition of Lemmas 3.1/3.2/3.7 where the conclusions are false:
vertices {s,x,z,v}, edges s→x(10), s→z(10), x→v(5), z→v(1); labels
d[s]=0, d[x]=10 complete, d[z]=d[v]=∞; call BMSSP(B=20, S={x}). Then
⟨∅,{x}⟩ is a frontier for Ũ(20,{x}) = {x} — but FindPivots relaxes
x→v to d[v] = 15, the search fails, W = {x,v}, and the call returns
U = {x,v} with d[v] = 15 ≠ dis(v) = 11: Lemma 3.2's W ⊆ Ũ and Lemma
3.7's U = Ũ(B′,S) complete both fail. The state is unreachable: any real
run has relaxed z→v to 11 before the call. The closure property the
induction actually rides on (audit Q9) is: *the §2.5 loop keeps every
incomplete-but-relevant vertex reachable from a complete vertex in
𝒟 ∪ P̂, and Pull + pivot-expansion forces that vertex into a child's S.*
Formalizing Reach inductively (rather than as a semantic predicate) is
the Lean-friendly route: the lemmas become properties of execution
prefixes, and the Q9 instance is the mandatory negative regression.

## 3. Corrected Lemma 3.7 (frontier, completeness, bound)

> **Lemma 3.7\*.** Let σ be reachable (§2.3), l > 0 (base case is
> Lemma 3.1\*, §4.1), ⟨∅,S⟩ a frontier for Ũ = Ũ(B,S) at the call's
> entry, |S| ≤ t²·2^(lt). Run BMSSP\*(B,S,l) = Algorithm 3 with (E0),
> (E1), (E3). Let Prem ⊆ entries of the returned 𝒟 be the *premature
> set* defined below. At return (B′, U, 𝒟):
>
> **(1) Frontier.** ⟨U, 𝒟⟩ is a frontier for Ũ.
>
> **(2a) Progress and completeness.** max_{x∈U} dis(x) < B′; every
> settlement event of the call settles a complete vertex (lh-grade);
> U ⊆ Ũ(B′, S).
>
> **(2b) Bound clause, with Q12 carve-out.** Every entry of 𝒟 has
> stored value ≥ B′, **except** entries of Prem, where Prem is exactly
> the set of entries (x, val) minted by the **final iteration's** line-29
> re-selection with val = d[x] at mint time and val < B′. Prem = ∅ if
> the call is a full execution (loop exit with 𝒟 drained), and Prem = ∅
> if the final iteration's re-selection minted nothing below B′. For
> each (x, val) ∈ Prem: x ∉ U; x ∈ P_j for some j ∈ J at the final
> re-selection; d[x] ≤ val < B′; and x is *two-shaped*: either x was
> already settled complete in a different subtree (S1 — val is x's stale
> pre-settlement entry) or x is unsettled with current label ≤ val
> (S2 — self-custodial).
>
> **(2c) Settlement identity, modulo the carve-out.** U = Ũ(B′, S) ∖ K,
> where K ⊆ keys(Prem) is the set of carve-out keys with dis < B′ whose
> shortest path visits S. In particular U = Ũ(B′,S) whenever Prem = ∅.
>
> **(3) Containment.** 𝒟 ⊇ (S ∖ U) ∪ R(B,U), where the right-hand side
> is read modulo Prem: S ∖ (U ∪ K) ⊆ keys(𝒟) and every v ∈ R(B,U) with
> d[v] ≥ B′ is in 𝒟.

**Theorem T (carve-out emptiness; audit PROOF.md §5 + §9).** *On the V5
engine, Prem = ∅ at every return of every reachable run.* Hence in
Lemma 3.7\* the carve-out is empty and clauses (2b)/(2c)/(3) collapse to
the paper's clause 2 and clause 3 verbatim.

Status: Theorem T is the audit's Lemma V ("no sub-B′ stored value at
any return or filter moment under V5"), proved as one half of a **joint
first-violation induction** with settlement completeness — hand proof
against a frozen implementation, re-derived in independent passes,
**not machine-checked**. See §4.4 and §8. The corrected lemma is
deliberately stated so that everything *except* Theorem T is locally
provable; a Lean development may either (i) prove Lemma 3.7\* then
Theorem T, or (ii) prove the joint invariant (2a ∧ 2b ∧ Prem = ∅)
directly, which is how the audit's proof is organized.

## 4. Proof sketches, defect by defect

### 4.1 Q3 → (E1) V5 at leaves, and the transitive proposition

**Lemma 3.1\* (base case).** With (E1), Algorithm 4 returns
(B′⁺, U, 𝒟) with U = Ũ(B′⁺, S) complete, max dis(U) < B′⁺,
dB[𝒟] ≥ B′⁺, and the full-execution dichotomy B′⁺ = B ⟺ 𝒟 = ∅.

*Sketch.* (a) dB[𝒟] ≥ B′⁺ by construction. (b) Settled labels are
non-decreasing along pulls (pulls take global minima; every insert
strictly exceeds its source's label by tuple growth — hops increments
even at w = 0), and every final-𝒟 value strictly exceeds the last
settled label (leftovers were ≥ B′_pull > label(u_last); post-final
inserts come only from u_last's relaxations and strictly exceed its
label). Hence all of U sits strictly below B′⁺. (c) Completeness up to
B′⁺: walk a canonical path from its last complete S-vertex (the frontier
precondition supplies one) to the first vertex y ∉ U with dis(y) < B′⁺;
its predecessor p ∈ U is complete, so relax(p,y) offered the canonical
candidate ≤ dis(y) < B′⁺; either accepted (y entered 𝒟 at a value
< B′⁺ ≤ dB[𝒟] — pulled, so y ∈ U) or refused with d[y] ≤ candidate,
which by label honesty (I1) forces d[y] = lh(y), i.e. y complete
(audited *refusal-floor* argument). Contradiction either way. (d) The
cap restores the dichotomy: the unmodified Algorithm 4 can return
B′ = B with 𝒟 ≠ ∅ (last pull empties 𝒟, post-pull relaxes refill it),
violating Lemma 3.1's "full ⇒ 𝒟 = ∅"; with the cap B′⁺ = B ⟺ 𝒟 = ∅.

*Why this fixes Q3 exactly.* The paper's returned B′ sits above values
inserted after the final Pull (zero/tiny weights do it systematically;
the degree reduction of §2.1 *manufactures* zero-weight edges), so
dB[𝒟] ≥ B′ and U = Ũ(B′,S) both fail at the leaf, and the parent's
bookkeeping (which consumes clause 2) inherits the undercut. The cap
calibrates B′⁺ against what the call actually leaves behind. The audit
measured the class: the un-repaired bound clause fails 366× at path
length 5 000 on plain positive weights (`escape.txt`) and composes with
the W′ filter into incomplete settlements (`rowh.txt`, 70 vertices,
settle-inc = 1 on the paper engine, 0 on V5).

**Transitive proposition (bound validity propagates; VARIANTS.md).**
*Assume every leaf returns dB[𝒟] ≥ B′ (E1 gives this) and every child
returns dB[𝒟_child] ≥ B′_child. Then Algorithm 3's own return satisfies
dB[𝒟] ≥ B′ **except through Prem** (Lemma 3.7\*(2b)).*

*Sketch — enumerate what 𝒟 holds at return:* (1) leftovers never pulled:
the last pull's separator lower-bounds the remainder and B′ = B′_f ≤
that separator; earlier-iteration low inserts cannot survive — some
later pull consumes them. (2) Merged children: final child by hypothesis
(≥ B′_f), earlier merges fall under (1). (3) Line-24 sweep inserts:
gated ≥ B_i ≥ B′_f in the final iteration. (4) Post-loop inserts
(lines 33, 37): gated ≥ B′ directly. (5) Line-29 re-selection inserts:
**ungated** — the one hole, live only in the final iteration (earlier
leaks are pulled later), and this is Prem. ∎

Full executions need no line-29 appeal: loop exit had 𝒟 = ∅, so only
gated post-loop inserts populate the returned 𝒟 — the bound clause
holds unconditionally there.

### 4.2 Q12 → statement-level fix (the carve-out)

The line-29 re-selection (p_j ← argmin_{x∈P_j} d[x]; 𝒟.Insert(⟨p_j,
d[p_j]⟩)) is Algorithm 3's only unguarded insert. Two channels put
d[p_j] below the running B′ (audit Q12):

1. **Sweep channel (pseudocode reading).** Line 23 runs `Relax(u,v,B)`
   with bound B and mutates d[v] even when the candidate is < B_i; only
   the insert is gated. A P_j member with j ∈ J takes the label decrease
   but is skipped by line 25's pivot update, and line 28's argmin then
   selects it. (E2 — the prose reading of line 23 — closes this channel.)
2. **Child-interior channel (either reading).** The i-th sub-call relaxes
   with bound B_i > B′_i and can lower a P_j member below B′_i without
   settling it (the member was ≥ B_i at pull time, so line 13 left it
   out of S_i). The paper's own P̂ device acknowledges these vertices
   ("d[v] may decrease but v is not in D_i or U_i") — but line 28
   selects from P_j, not P̂_j.

**No local repair exists (audit Q12, sharpened).** If X < B′_f was
stored by the final iteration's re-selection while some already-settled
label L satisfies X < L < B′_f, the three clauses of Lemma 3.7 are
*jointly unsatisfiable* for any reported B′: B′ > X breaks B′ ≤ dB[𝒟];
B′ ≤ X < L breaks max dis(U) < B′; and gating the insert instead orphans
an unsettled pivot with dis < B′ that U = Ũ(B′,S) must claim. Capping
Algorithm 3's B′ at dB[𝒟] (the V5 move) fails for the same reason. The
coherent repairs are statement-level, and Lemma 3.7\*(2b)/(2c) adopts
the explicit weakening: **carve out the final-iteration premature
entries and their keys.** The audit's characterization (Q14 addendum 18)
shows every escaped entry is two-shaped — S1 (stale duplicate of a
completely settled vertex) or S2 (self-custodial key, unsettled, label
≤ stored value) — which is exactly clause (2b)'s classification, and
confines the leak to "last-child spines" (every call between mint and
boundary exited by cutoff in the minting iteration; all share one B′).

Two facts keep the weakening from spreading:

- **Full executions are immune** (§4.1), and the top call is always a
  full execution under the paper's set semantics (Q13: |U| ≤ n₂ <
  t³·2^(l_top·t)); under (E3) the guard enforces the same by abort.
- **Theorem T empties the carve-out on V5** — but note line 29's
  ungatedness is *load-bearing*: gating it would orphan exactly the S2
  keys (unsettled, outside W, below every re-entry gate). The fix is in
  the statement, not in the code.

The proof of (2b′) beyond Prem is the transitive proposition of §4.1.
The proof of (2c) from (1)+(2b) is the paper's own step (Obs. 2.1(5):
Ũ(dB[𝒟],S) ⊆ U once ⟨U,𝒟⟩ is a frontier with dB[𝒟] ≥ B′; and
max dis(U) < B′ gives U ⊆ Ũ(B′,S)); with Prem ≠ ∅ the keys K carved
out of the equality are precisely the vertices whose claim ran through a
premature entry.

### 4.3 Q9 → reachable-state closure in the preconditions

Every lemma above carries "σ reachable (§2.3)". The proof of (2a) uses
closure where the paper's does implicitly: completeness of U = Ũ(B′,S)
is argued by walking canonical paths from complete S-vertices through
the frontier; the walk is only guaranteed to stay inside the maintained
invariant ("every incomplete-but-relevant vertex is reachable from a
complete vertex in 𝒟 ∪ P̂, and Pull + pivot-expansion forces it into a
child's S") when the state evolved from a parent frontier via the
algorithm's own Pull/expansion steps. Off-path states (Q9's) break
Lemma 3.2's W ⊆ Ũ before Lemma 3.7 is even reached. Practical
consequence for testing and for Lean: drive the top-level entry only;
construct intermediate states by execution, not by fiat.

### 4.4 Q11/Q14 → the completeness chain (why (2a) is not local)

Clause (2a)'s completeness — every settlement settles a complete
vertex — is false for the algorithm as printed (audit Q14 addendum 13/15:
`rowh.txt`, a 70-vertex graph where the paper engine settles an
incomplete vertex; V8's settled-bit variant then returns a *wrong final
distance*: 23.59375 vs 23.546875) and false for V8 alone. Its proof on
V5 is the audit's theorem **(H_lh | V5)**, and it is *joint* with the
bound clause:

  completeness of W′/pulls ⟸ bound invariant at the filter (dB[𝒟∪P] ≥ B′)
  bound invariant (Theorem T) ⟸ no stale (incomplete) settlements.

The circularity is broken by a first-violation induction on settlement
batches (PROOF.md §3): assume all earlier settlements complete, prove
the bound floor (Lemma W: no live 𝒟 value < β at an event with governing
bound β; Lemma V: no sub-B′ value at returns/filters), then prove the
current batch's settlements complete (Lemma d2 for W′ appends; base
pulls via the pull-minimality + refusal-floor argument of §4.1(c)). The
machinery the bound half needs — spine confinement, the two-shape
theorem for escaped entries, custody persistence (Lemma Rep), the W′
drop lemma and its co-settlement corollary — is exactly the audit's
PROOF.md §§5–8. On V5 the conclusion: every settlement settles the
canonical (len, hops) pair; the length-grade statement (d[v] = dis(v))
is its len-slot projection.

This is why Q3 and Q12 are load-bearing for Q11: the W′ filter's
`d[x] < B′` test is a completeness test only if B′ ≤ dB[𝒟∪P] actually
holds at the filter. The Q3 leak (uncapped leaf) makes B′ overstate
progress and the filter settles incomplete vertices; V5 calibrates it,
and the audit's counters record settle-inc = 0 and viol base/rec = 0/0
on V5 across every recorded family.

## 5. Duplicate settlements and the re-settlement bound (fixes Q11/Q14)

**The phenomenon (audit Q11, traced).** Even on V5 (cap fires 0×; the
duplicates are bit-identical with and without it) the settlement log
contains duplicate events — up to 0.037/vertex on natural adversarial
inputs and 0.56–3.8/vertex under deliberate attack. Mechanism: a stale
entry of v in an outer 𝒟 (created before v's label improved and
settled in a sibling subtree — keyed dedup is per-𝒟 instance; there is
no cross-level decrease-key) is pulled into a child frontier; exact-tie
re-acceptances (Lemma B: a valid relax into a complete v is an exact
tuple tie whose source is v's canonical pred) keep v structurally
alive through FindPivots; and either a base pull or the W′ boundary
append (whose W∖U filter is call-local and cannot see a settlement in
another subtree) emits a second U event.

**What this breaks.** Lemma 3.8's "U_i's are disjoint" and "U is a
disjoint union of W′ and the U_i's" (witnessed concretely: one vertex
settled in two children of the same call), and every Σ|U_X| charging
step of Lemma 3.9 — including the Σ|Q_Y| bullet, whose "≤ δ
relaxations from complete predecessors" step is circular under
duplicates (relaxation events multiply with re-settlements).

**Lemma R (re-settlement bound; audit Q14 addenda 1–6 — SKETCH GRADE).**
Let T = Σ_X (|U_X|_events − |U_X|_distinct) be the total duplicate
excess of a top-level run, n₂ the working vertex count, K = t²·2^t.
Under (I1)–(I5), (E1), and settlement completeness (2a):

  T ≤ √(2K·(l_top+1)·n·L_max) + O((l_top + k)·n)
    ≤ t·2^((t+1)/2)·√(l_top+1)·n + lower order,

where L_max ≤ n is the longest settled tie-path. Per vertex:

  dup(v) ≤ Σ_{w on the canonical path s→v} (O(l_top) + dup_W(w)),

and on runs where the foreign-W′ channel is silent (dup_W ≡ 0),
dup(v) = O(l_top·(hops(v)+1)).

Components (each recorded and argued in QUESTIONS.md Q14):

- **Lemma A (gate tiling).** Each settlement event of u causes at most
  **one D-insert per out-edge** over the whole run: the accept-and-insert
  windows of the event's sweeps tile [0, B) disjointly — [0, B_Xq) or
  [B′_Xq, B_Xq) at the settling call, [B_child, B_Xj) at each ancestor —
  and the candidate is one fixed tuple under completeness. This is §3.4
  property 6 repaired to per-event form.
- **Lemma B (tie targeting).** Post-settlement gated inserts of v arise
  only from settlement events of pred(v), along the one edge (pred(v),v).
- **Lemma D (W′ channel).** A foreign W′ duplicate of v requires a
  tied-path ancestor of v within < k hops sitting in the appending
  call's S with a failed search; one failed search emits ≤ k−1 duplicates.
- **Lemma E (bounces).** Total line-33 re-inserts over a run <
  (n₂+T)·(l_top+1)/t — a lower-order term.
- **Lemma F (once per call, settled-value channel).** Conditional on
  per-call B′ monotonicity (empirically zero regressions, unproved):
  each call sources ≤ 1 settlement event of v at value dis-label(v);
  further events consume pre-settlement stale entries (≤ 1 per 𝒟 at a
  time via keyed dedup) or W-memberships.
- **Lemmas G/H (coarsening).** Separately-firing triggers must be pull-
  rank separated at coarsening altitude; gap capacity ≤ (l_top+1)·n;
  wave-crossing plant erasure and batch merging suppress re-waves.
  The conditional Θ(n) theorem: R sequential re-waves of a length-L path
  force ballast ≥ R²L/2K ≤ n ⟹ T ≤ √(2K·n·L).

Measured ceilings vs attack: dup/n ≤ 3.8 (constructed cascade) and
≤ 1.58 (staggered attack) against ceilings ≈ 5.7 (t = 2) and ≈ 22.6·√l_top
(t = 4). Empirical support, not proof.

**Degradations this buys (audit: "What Lemma A buys the time
analysis").** Total gated inserts ≤ Σ_u (1+dup(u))·outdeg(u) ≤
δ·(n₂+T); the Σ|Q_Y| step un-circularizes to ≤ δ per settlement *event*;
every charging step of Lemma 3.9 degrades additively in T.

## 6. Corrected Lemma 3.8 (size) and Lemma 3.9 (time)

> **Lemma 3.8\*.** Under Lemma 3.7\*'s hypotheses (with (E3)):
> (a) |U|_events ≤ t³·2^(lt) + O(t³·2^((l−1)t)) = O(t³·2^(lt)) (the
> guard fires on events; the final batch overshoot is the last child's
> O(t³·2^((l−1)t)); on full executions U = Ũ exactly);
> (b) every insertion into 𝒟 takes O(t) time (|keys(𝒟)| ≤ |S| + |U|δ ≤
> t⁴·2^(lt) is unchanged);
> (c) *disjointness, corrected:* the multiset union U = W′ ⊎ ⊎_i U_i
> holds, with pairwise overlap exactly the duplicate excess: the U_i are
> pairwise disjoint **iff** the call contains no duplicate settlement of
> a vertex across two children, and in general Σ_i |U_i| + |W′| ≤
> |U|_distinct + T_X where T_X is the number of duplicate settlement
> events inside X's subtree. T_X = 0 on full executions and on every
> call of a run with a settled-bit marking (V8/V10); for the unmarked
> V5 engine T_X is bounded by Lemma R (T over the run).
>
> **Lemma 3.9\*.** With C a large constant and U = U_X:
>
>   Time(X) ≤ C(|U| + T_X)(l + log t)log t
>            + Ct·|N⁺_{[dis_B(S),B)}(U)|
>            + Ct·|E(U)|
>            + Ct·(δ + l/t)·(|U| + T_X)
>            + Ct·δ·T_X
>
> with Σ_{Y∈𝒯(X)} |Q_Y| ≤ (|U| + T_X)·(δ + l/t) — the Q-sum bounded per
> settlement *event* by δ (gate tiling), plus l/t per partial call
> (|Q_Y| ≤ |U_Y|/t for partial Y). The first line is the paper's
> vertex-term with events in place of distinct vertices; the last two
> lines are the duplicate surcharges (re-frontiering work: sweeps,
> re-selections, and the Σ|Q_Y| term re-charged per event).
>
> Consequently, at the top layer (B = ∞, S = {s}, l = l_top),
>
>   Time = O(m·(t + log n·log t/(δ·t))·(1 + T/n₂) + t·δ·T),
>
> with T per Lemma R: at sketch grade T = O(t·2^((t+1)/2)·√(l_top+1)·n)
> = n^(1+o(1)) at prescription parameters t ≈ √(log n), so the paper's
> bound degrades by at most an n^o(1) factor; under the settled-bit
> composition V10 = V5 + V8 (T = 0, distances provably equal V5's),
> Lemma 3.9\* holds verbatim modulo (2a), i.e. the paper's stated bound
> is restored for the marked engine.

*Proof sketches.* 3.8\*(a),(b) are the paper's, unchanged: the guard and
the 𝒟-size bound read events and keys, which duplicates do not inflate
beyond the guard (event semantics) — under set semantics (a) holds on
distinct count only and |U|_events must be read through Lemma R. 3.8\*(c)
replaces the dis-range argument: the paper's proof that
{dis(v) : v ∈ U_i} ⊆ [B′_{i-1}, B′_i) uses completeness of settlements
(2a) and B′ monotonicity; with duplicates the intervals can contain a
vertex twice (a stale-entry re-settlement of a complete v at a governing
value above dis(v)), and the exact overlap is the excess counted in T_X.
3.9\*: re-run the paper's seven charging steps (T1–T7) with two
repairs — (i) each step that consumed Σ_i |U_i| ≤ |U| now reads
Σ_i |U_i| ≤ |U| + T_X; (ii) the Σ|Q_Y| bullet, whose full-execution
branch charged each v ∈ Q_Y to "≤ δ relaxations from complete
predecessors", becomes per-event by Lemma A (each settlement event of u
sweeps each out-edge into at most one insert), i.e. ≤ δ·(|U|+T_X) plus
the partial-call l/t share. The T5,full injection (pivot re-selections
→ cross-level tree edges of F_j) is unchanged: it charges to edges of
E(U), and duplicates only add settled vertices to the injection's
domain. Merge/pull/line-33 volumes are bounded by the flow corollary
(§5): everything scales as poly(δ,t,l_top)·(n₂+T). ∎

## 7. The corrected contract chain (summary)

1. **Leaf (Lemma 3.1\*)** — V5 cap; full-execution dichotomy restored.
2. **Transitive proposition** — bound validity propagates up the
   recursion modulo Prem; unconditional on full executions.
3. **Lemma 3.7\*** — frontier (1), progress/completeness (2a), bound
   with explicit Q12 carve-out (2b)(2c), containment (3); over reachable
   states only (Q9).
4. **Theorem T (audit)** — Prem = ∅ on V5; (2b)(2c)(3) collapse to the
   paper's clauses. Joint with (2a) via the first-violation induction.
5. **Lemma R** — duplicate excess bounded (sketch grade); replaces
   Lemma 3.8's disjointness.
6. **Lemmas 3.8\*/3.9\*** — size and time, degrading additively in T;
   verbatim for V10 (V5 + settled bit), where T = 0.

## 8. What remains unproved

1. **Theorem T / (H_lh | V5) is a hand proof, not machine-checked.**
   The joint first-violation induction (PROOF.md §§3–9) is audited
   (eight derivation/cold-audit pairs) against a frozen implementation,
   not against a formal semantics of Algorithm 3. Its exact content —
   Lemma W (window), Lemma V (no sub-B′ values), Lemma Rep (custody),
   the W′ drop lemma and co-settlement corollary, the refusal-floor
   lemma — is the main body of the Lean work. Nothing here re-proves it;
   this document cites it as the fix for Q11/Q14's completeness half.
2. **Lemma R is at sketch grade.** Open pieces named by the audit: the
   custody-chain formalization, the wave-exhaustiveness bookkeeping
   (every duplicate rides a wave started by a plant or an initial-seed
   stale entry), and **per-call B′ monotonicity under duplicates**
   (empirically zero regressions, used by Lemma F). The dichotomy stands
   as stated: either a family sustains cascade reproduction > 1 and
   Σ|U_X| grows super-linearly (then the paper's time bound fails on
   adversarial inputs), or every input damps it and T = O(n^(1+o(1)))
   as sketched. Evidence favors damping; no proof. If Lemma R is not
   closed, the fallback that makes 3.8\*/3.9\* unconditional is the
   settled-bit marking (V8/V10): T = 0 by construction and the paper's
   accounting holds verbatim — at the cost of an engine delta beyond
   V5 (its safety assumption is exactly (2a), which is Theorem T).
3. **Q9's closure predicate.** "Reachable" is defined operationally
   (execution prefixes). Extracting a minimal inductive invariant that
   implies the lemma preconditions — the audit's closure sentence
   ("every incomplete-but-relevant vertex reachable from a complete
   vertex in 𝒟 ∪ P̂, forced into a child's S") is the candidate — is
   unproved as stated and is a prerequisite for proving 3.7\*(2c)
   without quantifying over whole executions.
4. **Q12's state reachability is unobserved.** The verify-mode counters
   stayed at zero on the full adversarial family; a dedicated
   construction (partial execution whose final iteration re-selects a
   pivot lowered below B′_f) has not been built. Lemma 3.7\* does not
   depend on unreachability — Prem is carved out — but if Prem = ∞ is
   ever exhibited, clause (2c) is the clause that weakens in practice.
5. **Per-call B′ monotonicity (Lemma F's hypothesis)** — unproved even
   at sketch grade; attacked by the escape family (survived), not closed.
6. **The pred slot is permanent scope, not debt.** Completeness and
   bit-finality are (len, hops)-grade; pred-canonicality of final labels
   is proved (audit §12) only for completed full runs on V5 under the
   zero-counter record. Any Lean statement involving pred must mirror
   that scoping.
7. **Engine-dependence.** All conclusions are about the pinned engine
   semantics: keyed keep-min dedup, tie re-acceptance (`≤`), Merge
   consolidation into the parent, pull = M smallest stored values with
   separator, event-count guard (E3). A Lean model must pin these before
   any lemma here applies; the paper's pseudocode leaves several of them
   implicit (Q13's set-vs-event semantics being the recorded divergence).
8. **Not covered:** the empty-P_j pseudocode crashes (Q2/Q8) are fixed
   by (E0) but not proved harmless to any bound (they are: skipped
   groups contribute nothing, P_j partitions S); the nEdges overflow
   note (Q7); and everything about the *time* claim's practical regime
   (Q1: the prescribed δ is outside its own validity range below
   n = 2^4096), which affects the corollary, not the lemmas.

---

*Sources: arXiv:2602.07868v1 (statements as printed); audit record
`github.com/primaryaesthetics/beyond-dijkstra` — `QUESTIONS.md` Q3, Q9,
Q10–Q15 with addenda 1–32, `PROOF.md` (the (H_lh | V5) chain), `VARIANTS.md`
(V5, "Algorithm 3's contract, transitively", V8/V10), `benchmarks/results/`
(wprime, rowh, rowi, rowj, escape, cascade, dup_classify records).*

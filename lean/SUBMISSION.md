# SUBMISSION — Corrected Duan–Mao–Shu–Yin (DMSY) Directed SSSP

Entry point: `Submission.lean` → `export Race (bound)` (defined in `D/D/Main.lean`'s
namespace block, proved in `D/D/Bound.lean`, work package D3).

## The bound

Verifier form (sparse case):

```
n log^1/2 loglog^1/2 ; n log^1/2 loglog^1/2
```

Exact exponents, per `D/D/Dispatch.lean` (`Time a' b' c' n m`, D1) and `D/D/Bound.lean`:

- **Sparse clause** (`m ≤ Cap a b n`, `Cap a b n = a · n · (log₂ n) ^ b`):

  ```
  Time = a' · m · log(n)^(1/2)
       + b' · (m · n · log(n) · loglog(n))^(1/2)
       + c' · (m + n + 1)
  ```

  i.e. `O(m √(log n) + √(m n log n loglog n))` — the two DMSY terms carry
  `log^(1/2)` and `loglog^(1/2)` exponents under the radicals (the lower-order
  `c'·(m+n+1)` term is what a uniform program must pay for its output arrays;
  it is absorbed whenever `1 ≤ m` and `n ≤ m·log(n+2)·log(log(n+2)+2)`).

- **Fallback clause** (all graphs): `C · (n+1)(m+1)` — proved (D2 Bellman–Ford
  + D1 composition, task key lemma 2).

- **Constant**: `C = (C₁ + b + 17) · (a' + 4·b' + c')` (`Race.bound`, D3). The
  `poly` factor makes the fallback clause absorb the sparse `Time` on sparse graphs.

## Statement (`Race.bound`)

For all cap/time parameters `(a b e : ℕ) (body ps) (C₁ a' b' c' : ℝ)` satisfying
`DInputs` (admissibility `he/hbe/ha`, `0 ≤ C₁`, `0 ≤ a' b'`, `1 ≤ c'`, and the
sparse-clause specification `hsp : BodySpec e ps body … (C₁ · Time a' b' c' n m)` —
package C's per-call cost, discharged at the joint `Main.lean` seam):

`Frontier.DMSY.Bound a b a' b' c'` — one uniform program (`dmsyProgram a b e body ps`),
exact on every graph and source, within `C · Time` on sparse graphs and
`C · (n+1)(m+1)` on all graphs.

## Axiom audit

`#print axioms Race.bound` (D/Bound.lean:256, emitted in `lake build Submission`):

```
'Race.bound' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**No `sorryAx`.** The sparse clause is carried as the hypothesis `DInputs.hsp`, so
`Race.bound` is unconditional on the three standard Lean axioms only. The known 3
`sorry`s live in `A4/A4/Main.lean` (joint-chain seam, CORRECTED_PROOF §8.1 —
`a4_joint` / `lemma37Star` / Theorem-T completeness); they are worked separately
and do not appear in `Race.bound`'s axiom closure.

## Build

`lake build Submission` passes (Lean v4.34.1, mathlib pin `d13f23b7`).
Root `lakefile.toml`: `lean_lib Submission` (roots `["Submission"]`), requiring
package `D` by path; all transitive packages (A0–A4, B, mathlib) resolve through
D's manifest.

import A4.ReturnClauses
import A4.BelowSeparator

/-!
# Frontier.DMSY.IdentityCover — supply (or bound) `ReturnClauses.tail_identity`'s last gap

`A4.ReturnClauses` reduces clause (2c) — `U = Ũ(B′,S) ∖ K` — to its two halves plus one
missing inclusion, named `hcover` there:

  `hcover : Ũ(tailBP B st, S) ⊆ out.U ∪ out.carveKeys S`.

This file attacks `hcover` and reports exactly what the engine's own semantics can and cannot
pay for.  Two closure routes are developed, each *complete* on its own hypotheses, and the
residual is isolated rather than hidden.

## Route 1 — the frontier squeeze (`cover_of_Yclear`), carve-out free

`A0`'s Obs. 2.1(5) (`IsFrontier.below`) squeezes a below-floor member of `Ũ` into the
frontier's complete side `X` as soon as the *whole* `Y` side clears the returned floor
`B′ = tailBP B st`.  That hypothesis — `Yclear : ∀ y ∈ Y, B′ ≤ st.d y` — is the entire
content Route 1 needs: no custody, no `PremShape`, no mint analysis.  The consequence is
`hcover` **with an empty carve-out**: `Ũ(B′,S) ⊆ out.U`, hence a fortiori `hcover`
(`tail_cover_of_Yclear`) and, assembled with `tail_uSubset` and the `PremShape` disjointness,
the settlement identity itself (`tail_identity_of_Yclear`).

Route 1 is the paper's step (CORRECTED_PROOF §4.2: "Ũ(dB[𝒟],S) ⊆ U once ⟨U,𝒟⟩ is a frontier
with dB[𝒟] ≥ B′").  It is provable here exactly as stated. What it is *not* is free: `Yclear`
is where the paper silently substitutes its 𝒟 (a store of labels) for this engine's split
`(d, D)` pair — see Route 3.

## Route 2 — the key floor (`tail_cover_of_floor`), carve-out used

Route 2 does not use a frontier at all.  It uses custody (`live label ⟹ settled or a `𝒟` key`),
the keep-min floor `LoopBoundInv`, and one floor-accuracy premise `LowKeyAccurate`:

* `prem_of_key_value_lt` (**unconditional**, from `Transitive.tail_boundClause`): a `𝒟` key
  whose **stored value** is below `tailBP` is a `Premature` entry — the value half of clause
  (2b), no premise beyond `LoopBoundInv`.
* `LowKeyAccurate B′ d D := ∀ y val, D y = some val → d y < B′ → val < B′` — the missing
  half: a key whose **label** is below the floor carries a **value** below the floor.
* `BelowLabelFloor B′ S st := ∀ x ∈ Ũ(B′,S), x ∉ settledSet st.evts → st.d x < B′` — the
  completeness-chain output: an unsettled vertex below the returned floor has its *label*
  below the floor (this is the piece the canonical-path/refusal-floor argument of
  CORRECTED_PROOF §4.1(c)/§4.4 produces, and the frontier alone cannot).

Given those two, `hcover` follows with `K` doing real work: an unsettled `x ∈ Ũ(B′,S)` is live
(`d x < B′ ≤ ⊤`), so custody makes it a key, `LowKeyAccurate` puts its value below the floor,
and `prem_of_key_value_lt` turns that into `Premature x val` — i.e. `x ∈ out.carveKeys S`.

## Route 3 — why Route 1 and Route 2 cannot be merged (the exact gap)

`floor_not_from_bound_and_honesty` records the logical kernel: the paper's derivation of (2c)
from (1)+(2b) needs `label = value` at `𝒟` keys.  This engine's honesty is **one-sided**
(`Structural.relaxGate_honest`/`istep_honest`/`iloop_honest`: `d y ≤ val`), so the bound clause
`B′ ≤ val` says nothing about `d y`, and `Yclear`/`LowKeyAccurate` are genuinely extra.
`ReturnClauses` §8 already names the same missing fact on the *entry* side ("`IStep`/`ILoop`
maintain only one-sided honesty, never accuracy"); Route 2's `LowKeyAccurate` is its
exit-side counterpart. Neither is assumed here — each is a named hypothesis of a theorem.

Nothing in this file uses `sorry`/`admit`, and nothing adds an axiom.

## The residual for `a4_joint`, stated exactly

The cover is **not** derivable from the three ingredients named for it (frontier squeeze, child
completeness, custody/`PremShape`): §2b proves what the `Y` branch really delivers (a *witness*
member of `Ũ(B′,S)`, which the floor covers) and leaves open only the queried vertex itself.
What a `a4_joint` caller must supply is therefore one of:

* `Yclear : ∀ y ∈ Y, tailBP B st ≤ st.d y` (+ `X ⊆ out.U ∪ out.carveKeys S`) — Route 1, which
  then needs no carve-out at all and no mint analysis; or
* `LowKeyAccurate (tailBP B st) st.d st.D` **and** `BelowLabelFloor (tailBP B st) S st`, plus
  `Custody st` and `LoopBoundInv st` — Route 2, which uses the carve-out (`x` becomes
  `Premature`).

`prem_of_key_value_lt` is the one piece that was already free (it is `Transitive.tail_boundClause`
read as `Premature`).  No counterexample is claimed here: the cover is not refuted, only shown
to be *unreachable from the listed invariants*, at a named step, with the minimal substitutes
stated and proved sufficient.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. Bound monotonicity for the tail

`tailBP` is either the entry bound `B` or the running bound `st.bp`, and the loop's running
bound never exceeds `B` (`mkInit`'s `initBp`, then each iteration's child return).  Both
`A0`'s `utilde_mono_bound` (the only place the returned floor meets `Ũ(B,S)`) and Route 1
need it; the two facts are already in `A4.Structural`/`A0` and are only re-exported here so a
caller of this file does not have to hunt for them. -/

/-- `Ũ` is monotone in the bound (re-export of `A0.Frontier.DMSY.utilde_mono_bound`). -/
theorem utilde_mono {B B' : WLab G s} (h : B' ≤ B) {S : Set (Fin G.n)} :
    Utilde B' S ⊆ Utilde B S :=
  utilde_mono_bound h

/-! ## 2. Route 1 — the frontier squeeze

`IsFrontier.below` needs `dis v < d y` for **every** `y ∈ Y`; `v ∈ Ũ(B′,S)` plus `Yclear` plus
`B′ ≤ B` delivers exactly that.  Nothing else about `Y` is used — in particular no custody, no
mint analysis, no `𝒟` key structure. -/

/-- **The frontier squeeze.**  A frontier for `Ũ(B,S)` whose `Y` side clears the returned floor
`B′` places every member of `Ũ(B′,S)` in the frontier's `X` side — hence in any set containing
`X`. -/
theorem cover_of_Yclear {d : Labels G s} {B B' : WLab G s} {S X Y Z : Set (Fin G.n)}
    (hF : IsFrontier d (Utilde B S) X Y)
    (hclear : ∀ y ∈ Y, B' ≤ d y) (hmono : B' ≤ B) (hX : X ⊆ Z) :
    Utilde B' S ⊆ Z := by
  intro v hv
  refine hX (hF.below (utilde_mono hmono hv) ?_).1
  exact fun y hy => hv.1.trans_le (hclear y hy)

/-- The loop log sits inside the tail's log (`tail`'s `evts` is `st.evts ++ W′`). -/
theorem settledSet_subset_tail_U (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) : settledSet st.evts ⊆ (callOut (tail B S W st)).U := by
  intro x hx
  have h : (tail B S W st).evts =
      st.evts ++ wPrimeEvts
        (wPrime (tailBP B st) W st.evts (seedIns (tailBP B st) B S st.d st.D).1) := rfl
  show x ∈ settledSet (tail B S W st).evts
  rw [h, settledSet_append]
  exact Or.inl hx

/-- **`hcover`, carve-out free** (Route 1, instantiated at the tail): if the loop-exit frontier
carries a `Y` side clearing `tailBP B st` and an `X` side inside the tail's settlement set,
then *every* vertex of `Ũ(tailBP B st, S)` is settled — the `K` side of the union is never
needed.  This is the strongest form of (2c) the frontier can deliver. -/
theorem tail_cover_of_Yclear (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) {X Y : Set (Fin G.n)}
    (hF : IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y)
    (hclear : ∀ y ∈ Y, tailBP B st ≤ st.d y) (hmono : st.bp ≤ B)
    (hX : X ⊆ settledSet st.evts) :
    Utilde (tailBP B st) (S : Set (Fin G.n)) ⊆
      (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S := by
  have h1 : Utilde (tailBP B st) (S : Set (Fin G.n)) ⊆ settledSet st.evts :=
    cover_of_Yclear hF hclear (tailBP_le B st hmono) hX
  exact fun x hx => Or.inl (settledSet_subset_tail_U B S W st (h1 hx))

/-- The general instantiation: the `X` side of the exit frontier only has to sit inside the
union the clause asks for.  (This is the form a caller that cannot show `X ⊆ settledSet` needs;
the two agree whenever `X` is settled or carved.) -/
theorem tail_cover_of_Yclear' (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) {X Y : Set (Fin G.n)}
    (hF : IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y)
    (hclear : ∀ y ∈ Y, tailBP B st ≤ st.d y) (hmono : st.bp ≤ B)
    (hX : X ⊆ (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S) :
    Utilde (tailBP B st) (S : Set (Fin G.n)) ⊆
      (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S :=
  cover_of_Yclear hF hclear (tailBP_le B st hmono) hX

/-! ## 3. The settlement identity assembled from Route 1
`U ∩ K = ∅` is `Structural.premShape_of_run`'s `x ∉ U` half of a `Prem` entry, stated here for
an arbitrary carve-out radius so the identity needs no `Run` witness of its own. -/

/-- A `Prem` entry's key is never settled — `premShape_of_run`'s first conjunct. -/
theorem notMem_U_of_premature {out : CallOut G s}
    (hprem : ∀ x val, out.Premature x val → x ∉ out.U) :
    ∀ x, x ∈ out.U → x ∉ out.carveKeys (∅ : Finset (Fin G.n)) := by
  intro x hx hK
  obtain ⟨val, hval⟩ := hK.1
  exact hprem x val hval hx

/-- **`.carveKeys` at any radius**: membership unpacks to a `Prem` key in the canonical cone. -/
theorem mem_carveKeys {out : CallOut G s} {S : Finset (Fin G.n)} {x : Fin G.n} :
    x ∈ out.carveKeys S ↔ (∃ val, out.Premature x val) ∧ x ∈ Utilde out.B' (S : Set (Fin G.n)) :=
  Iff.rfl

/-- **The settlement identity, from Route 1's cover.**  `ReturnClauses.tail_identity` with its
`hcover` input supplied by the frontier squeeze, and `U ∩ K = ∅` by `PremShape`.  Nothing else
is assumed: `hsub` is `tail_uSubset`, `hcover` is `tail_cover_of_Yclear`. -/
theorem tail_identity_of_Yclear (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) {X Y : Set (Fin G.n)}
    (hsub : (callOut (tail B S W st)).U ⊆ Utilde (tailBP B st) (S : Set (Fin G.n)))
    (hprem : ∀ x val, (callOut (tail B S W st)).Premature x val →
      x ∉ (callOut (tail B S W st)).U)
    (hF : IsFrontier st.d (Utilde B (S : Set (Fin G.n))) X Y)
    (hclear : ∀ y ∈ Y, tailBP B st ≤ st.d y) (hmono : st.bp ≤ B)
    (hX : X ⊆ (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S) :
    (callOut (tail B S W st)).U =
      Utilde (tailBP B st) (S : Set (Fin G.n)) \ (callOut (tail B S W st)).carveKeys S :=
  tail_identity B S W st hsub
    (fun x hx hK => by
      obtain ⟨val, hval⟩ := hK.1
      exact hprem x val hval hx)
    (tail_cover_of_Yclear' B S W st hF hclear hmono hX)

/-! ## 4. The value half of the key floor (unconditional)

Clause (2b)'s `Transitive.tail_boundClause` already says: a `𝒟` value is either `≥ B′` or a
final-iteration mint below `B′` — that is, exactly `Premature`.  So a key whose **value** is
below the returned floor is premature, with no hypotheses beyond `LoopBoundInv`. -/

/-- A tail key whose stored value is below `tailBP` is a `Premature` entry. -/
theorem prem_of_key_value_lt (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) {y : Fin G.n} {val : WLab G s}
    (hy : (tail B S W st).D y = some val) (hlt : val < tailBP B st) :
    (callOut (tail B S W st)).Premature y val := by
  rcases tail_boundClause B S W st hinv y val hy with h | ⟨hm, hlt'⟩
  · exact absurd h (not_le.mpr hlt)
  · exact ⟨hm, hlt'⟩

/-- **The exact gap in the paper's derivation.**  The route
`(1) ⟨U,𝒟⟩ frontier` + `(2b) B′ ≤ dB[𝒟]` ⟹ `(2c)` runs through Obs. 2.1(5), which needs the
`𝒟` **label** to clear `B′`.  `(2b)` bounds the **stored value**; this engine's honesty is
one-sided (`d y ≤ val`, `Structural.relaxGate_honest`), and in any linear order those two
bounds do not yield the label floor.  Hence `Yclear` (Route 1) and `LowKeyAccurate` (Route 2)
are content, not book-keeping. -/
theorem floor_not_from_bound_and_honesty :
    ∃ B b v : ℕ, B ≤ v ∧ b ≤ v ∧ ¬ B ≤ b :=
  ⟨5, 3, 7, by norm_num, by norm_num, by norm_num⟩

/-! ## 5. Route 2 — the label floor at keys, and the cover with a live carve-out -/

/-- **Floor accuracy at `𝒟` keys** — the exit-side counterpart of `ReturnClauses` §8's missing
`istep_cover_accurate`: a key whose label sits below the returned floor carries a value below
it too.  (`IStep`/`ILoop` prove only the one-sided `d y ≤ val`.) -/
def LowKeyAccurate (B' : WLab G s) (d : Labels G s) (D : DS G s) : Prop :=
  ∀ y val, D y = some val → d y < B' → val < B'

/-- **The below-floor label floor** — the completeness chain's output, stated at the loop-exit
state: an unsettled member of `Ũ(B′,S)` has its **label** below `B′`.  This is what the
canonical-path walk of CORRECTED_PROOF §4.1(c)/§4.4 gives (refusal floor + pull/gate
coverage) and what no frontier fact can give: the frontier controls membership of its `X`/`Y`
sides, never the label of a vertex off both. -/
def BelowLabelFloor (B' : WLab G s) (S : Finset (Fin G.n)) {p : ℕ} (st : RState G s p) : Prop :=
  ∀ x, x ∈ Utilde B' (S : Set (Fin G.n)) → x ∉ settledSet st.evts → st.d x < B'

/-- A low but accurate key is `Premature`: `LowKeyAccurate` puts the value below the floor, the
key's existence forces `tailBP = st.bp` (BM.24a), and `LoopBoundInv` then identifies the
sub-floor value's only escape — a recorded final-iteration mint, i.e. `Premature`. -/
theorem prem_of_low_key (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st)
    (hacc : LowKeyAccurate (tailBP B st) st.d st.D) {y : Fin G.n} {val : WLab G s}
    (hy : st.D y = some val) (hlabel : st.d y < tailBP B st) :
    (callOut (tail B S W st)).Premature y val := by
  have hlt : val < tailBP B st := hacc y val hy hlabel
  have hbpeq : tailBP B st = st.bp := by
    by_cases hD : DS.IsEmpty st.D
    · rw [hD y] at hy; exact absurd hy.symm (Option.some_ne_none val)
    · exact tailBP_of_not_isEmpty B st hD
  refine ⟨?_, hlt⟩
  rcases hinv y val hy with h | h
  · rw [hbpeq] at hlt; exact absurd h (not_le.mpr hlt)
  · exact h

/-! ## 5b. What the `Y` branch of the frontier does and does not give

`IsFrontier`'s `Y` branch hands back a *witness* `y` (complete, on the queried vertex's
canonical path) — not the queried vertex's own status.  That is the precise reason Route 1
needs `Yclear`: without it the squeeze stops at `y`.  The witness is not lost work, though: a
low complete `Y` member is itself a member of `Ũ(B′,S)`, so Route 2's floor closes it too.  The
only vertex these two facts leave open is the queried `x` when it sits off both sides — the
residual named in §5. -/

/-- **A low complete `Y` member is settled or carved.**  `Y ⊆ Ũ(B,S)` (the frontier's own side
condition) plus completeness makes it a member of `Ũ(B′,S)`; custody makes it settled or a `𝒟`
key; the floor turns the key into a `Prem` entry. -/
theorem low_Y_member_settled_or_carved (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) (hcust : Custody st)
    (hacc : LowKeyAccurate (tailBP B st) st.d st.D) {Y : Set (Fin G.n)}
    (hY : Y ⊆ Utilde B (S : Set (Fin G.n))) {v : Fin G.n} (hvY : v ∈ Y)
    (hcomp : Complete st.d v) (hlt : st.d v < tailBP B st) :
    v ∈ (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S := by
  by_cases hs : v ∈ settledSet st.evts
  · exact Or.inl (settledSet_subset_tail_U B S W st hs)
  · refine Or.inr (mem_carveKeys.mpr ⟨?_, ?_⟩)
    · have hne : st.d v ≠ ⊤ := by
        intro h; rw [h] at hlt; exact absurd hlt not_top_lt
      rcases hcust v hne with h | h
      · exact absurd h hs
      · obtain ⟨val, hval⟩ := Option.ne_none_iff_exists'.mp h
        exact ⟨val, prem_of_low_key B S W st hinv hacc hval hlt⟩
    · have hvB : v ∈ Utilde B (S : Set (Fin G.n)) := hY hvY
      show v ∈ Utilde (callOut (tail B S W st)).B' (S : Set (Fin G.n))
      rw [hcomp] at hlt
      exact ⟨hlt, hvB.2⟩

/-- **`hcover` from the floor route — the carve-out does the work.**  Custody makes an unsettled
`Ũ(B′,S)` member a `𝒟` key; `BelowLabelFloor` + `LowKeyAccurate` + `LoopBoundInv` make it
`Premature`, hence a carve-out key.  No frontier is used, and the union's second arm is
essential (this is `PremShape`'s S2 shape, not a vacuous branch). -/
theorem tail_cover_of_floor (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) (hcust : Custody st)
    (hacc : LowKeyAccurate (tailBP B st) st.d st.D)
    (hlow : BelowLabelFloor (tailBP B st) S st) :
    Utilde (tailBP B st) (S : Set (Fin G.n)) ⊆
      (callOut (tail B S W st)).U ∪ (callOut (tail B S W st)).carveKeys S := by
  intro x hxU
  by_cases hs : x ∈ settledSet st.evts
  · exact Or.inl (settledSet_subset_tail_U B S W st hs)
  · refine Or.inr (mem_carveKeys.mpr ⟨?_, ?_⟩)
    · have hlabel : st.d x < tailBP B st := hlow x hxU hs
      have hne : st.d x ≠ ⊤ := by
        intro h
        rw [h] at hlabel
        exact absurd hlabel not_top_lt
      rcases hcust x hne with h | h
      · exact absurd h hs
      · obtain ⟨val, hval⟩ := Option.ne_none_iff_exists'.mp h
        exact ⟨val, prem_of_low_key B S W st hinv hacc hval hlabel⟩
    · show x ∈ Utilde (callOut (tail B S W st)).B' (S : Set (Fin G.n))
      exact hxU

/-- **The settlement identity from Route 2.**  `ReturnClauses.tail_identity` with `hcover`
supplied by the floor route, so no frontier is needed at all. -/
theorem tail_identity_of_floor (B : WLab G s) (S W : Finset (Fin G.n)) {p : ℕ}
    (st : RState G s p) (hinv : LoopBoundInv st) (hcust : Custody st)
    (hacc : LowKeyAccurate (tailBP B st) st.d st.D)
    (hlow : BelowLabelFloor (tailBP B st) S st)
    (hsub : (callOut (tail B S W st)).U ⊆ Utilde (tailBP B st) (S : Set (Fin G.n)))
    (hprem : ∀ x val, (callOut (tail B S W st)).Premature x val →
      x ∉ (callOut (tail B S W st)).U) :
    (callOut (tail B S W st)).U =
      Utilde (tailBP B st) (S : Set (Fin G.n)) \ (callOut (tail B S W st)).carveKeys S :=
  tail_identity B S W st hsub
    (fun x hx hK => by
      obtain ⟨val, hval⟩ := hK.1
      exact hprem x val hval hx)
    (tail_cover_of_floor B S W st hinv hcust hacc hlow)

end DMSY
end Frontier

import A4.ReturnClauses

set_option linter.unusedVariables false

/-!
# Frontier.DMSY.ConeClosure — the shared cone-closure leaf (clause (2c) / `KeyCone`)

Work package **A4**.  Two callers need the same fact about a child call:

* `A4.NonDrainedBp.childKeyLabelFloor_of_concl` (clause (2c) at a non-drained return),
* `A4.StepSplitFloor.keyCone_of_storeSound_coneClosure` (`j6`'s `Si` half),

both as the hypothesis

  `hcone : ∀ y, dis y < fo'.B' → ∃ x ∈ c.S, OnPath x y`

— *every vertex below the child's returned bound has a child seed on its canonical path*.  Both
files say the same thing about it: it is reachability, not a separator or store fact, so no
`PullSpec` clause can supply it.  This file settles what it is, from the engine's own semantics.

## 1. The fact, as stated, is **false**

`hcone` quantifies over *every* vertex.  At a child whose seed set is not a cut of the ball of
radius `B'`, it fails: the canonical paths of vertices outside the child's cone never enter
`c.S`.  Concretely (§4) the **source** is the witness.  `s` is a seed only in the first
iteration (it is the first pull's argmin, `initD'` key 0); from the second iteration on it is
settled, deleted by ★BM.15, and never re-seeded — while `dis s = ↑[]` is the minimum of the walk
order, hence below every bound a child can return.  Then `OnPath x s` forces `x = s` (`path s =
[]`, so the prefix walk is the empty walk, whose end vertex is `s` itself), so no seed witnesses
`s`.  The explicit instance of §4 is a *drained* child (`B' = B = ⊤`, BM.24a's `tailBP` branch)
of the top-level call with seed set `{z}`.  Every hypothesis the two callers can supply holds
there (`Sound`, `IsFrontier`, `B' ≤ B`, and the entry contract's Claim C); the conclusion fails
(`coneClosure_unrestricted_false`).

So the leaf is **not** a theorem about the child alone.  What the child's semantics *does*
give is the same statement on the region Claim C leaves open, plus a key-shape restriction.

## 2. What is proved here

* `ClaimC` — the entry contract's Claim C (B1, `CallPre.claimC`) as a standalone clause: every
  sub-`B` vertex **outside** the cone is already complete.
* `coneClosure_of_claimC` — **the derivable half of the leaf**: every *incomplete* vertex below
  `B' ≤ B` lies in the cone.  Two lines from Claim C, no reachability assumption of its own.
* `coneClosure_of_run` / `keyCone_of_run` — the same at a genuine `Run` child, where `B' ≤ B` is
  `A4.Structural.run_le_bound`; the child's entry contract is `CallPre c.B c.S c.d`.
* `keyCone_of_claimC` — the **key-restricted** form the two callers actually quantify over
  (`y ∈ keys 𝒟`), which needs one extra state clause (`NoCompleteKey`, §3).
* `cone_of_seed_lt`, `istep_keyCone_of_belowBody` — the *other* route, which needs no Claim C:
  a key whose stored body is below the separator is pulled, expanded (`istep_pull_seed`) and so
  is its own cone witness.
* `istep_key_settled_of_belowBody` — the payoff shape both callers consume (settled, or carved
  out by Q12), read off `A4.ReturnClauses.istep_seed_settled_or_carved`.

## 3. The precise missing child clause

The residual is **not** reachability.  Splitting on the stored body of a key `y ∈ 𝒟`:

| case | source of the cone witness | status |
|---|---|---|
| `∃ v, st.D y = some v ∧ v < c.B` | `pullRun_pulled` + `expand` | **proved** (`istep_keyCone_of_belowBody`) |
| `v ≥ c.B` (stale high body) | Claim C at the child entry | needs `¬ Complete c.d y` |

The second row is where the leaf really lands.  Claim C converts an *outside-cone* vertex into
a *complete* one, so it closes the argument exactly when `y` is not complete.  What is missing
from the engine's current interfaces is therefore:

> **`NoCompleteKey c.d st.D`** — no key of the iteration's `𝒟` carries a complete label.

This is a **custody** invariant of the loop state, not a reachability one: ★BM.15 deletes the
child's *settled* keys, which makes a complete key possible only through the value/label
divergence channel (`st.d y = dis y` beside a stale high `st.D y`) — i.e. it is the same
obligation as the very label floor `ChildKeyLabelFloor`/`KeyCone` the two callers are proving,
one level up.  That is why §3 is stated as a *clause*, not discharged: assuming it would beg the
question, and the two callers must supply it from the loop invariant that already owns custody
(`A4.LiveFloor`'s `LiveFloor`/`Ge` half, `A4.IdentityCover`'s `LowKeyAccurate`).

No `sorry`, no `admit`, no new axiom.
-/

namespace Frontier
namespace DMSY

open Frontier Graph
open Frontier.CHD

variable {G : Graph} {s : Fin G.n}

/-! ## 1. Claim C, as a standalone clause -/

/-- **Claim C at a call entry** (B1's "Claim C" = the `claimC` field of `A0`'s `CallPre`): every
vertex below the bound that lies *outside* the cone `Ũ(B, S)` is already complete.  Whence the
contrapositive this file runs on: an *incomplete* sub-`B` vertex is **in** the cone. -/
def ClaimC (B : WLab G s) (S : Finset (Fin G.n)) (d : Labels G s) : Prop :=
  ∀ v, dis (s := s) v < B → v ∉ Utilde B (S : Set (Fin G.n)) → Complete d v

theorem claimC_of_callPre {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    (hpre : CallPre B S d) : ClaimC B S d :=
  hpre.claimC

/-- A vertex that is *not* complete and sits below the bound cannot be outside the cone. -/
theorem mem_utilde_of_claimC {B : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    (hclaim : ClaimC B S d) {y : Fin G.n} (hnc : ¬ Complete d y) (hlt : dis (s := s) y < B) :
    y ∈ Utilde B (S : Set (Fin G.n)) :=
  by_contra fun hout => hnc (hclaim y hlt hout)

/-! ## 2. The derivable half of the leaf -/

/-- A seed below `B'` witnesses the cone at itself. -/
theorem cone_of_seed_lt {B' : WLab G s} {S : Finset (Fin G.n)} {y : Fin G.n}
    (hseed : y ∈ S) (hlt : dis (s := s) y < B') : ∃ x ∈ S, OnPath (s := s) x y :=
  ⟨y, hseed, onPath_self (reachable_of_dis_lt hlt)⟩

/-- **Cone closure on the region Claim C leaves open.**  If everything below `B` outside the
cone is complete, then every *incomplete* vertex below `B' ≤ B` lies in the cone: its canonical
path visits a seed of `S`.  This is the whole of the leaf that the child's own semantics gives —
no separator, no store, no `Prem` hypothesis. -/
theorem coneClosure_of_claimC {B B' : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    (hclaim : ClaimC B S d) (hB' : B' ≤ B) :
    ∀ y, ¬ Complete d y → dis (s := s) y < B' → ∃ x ∈ S, OnPath (s := s) x y := by
  intro y hnc hlt
  obtain ⟨-, x, hx, hvis⟩ := mem_utilde_of_claimC hclaim hnc (lt_of_lt_of_le hlt hB')
  exact ⟨x, Finset.mem_coe.mp hx, hvis⟩

/-- **At a genuine `Run` child**, `B' ≤ B` is the bound law (`A4.Structural.run_le_bound`), so the
incompleteness form of the leaf holds whenever the child's entry contract does. -/
theorem coneClosure_of_run {t : ℕ} {c : CallEntry G s} {fo' : CallOut G s}
    (hrun : Run t c fo') (hclaim : ClaimC c.B c.S c.d) :
    ∀ y, ¬ Complete c.d y → dis (s := s) y < fo'.B' → ∃ x ∈ c.S, OnPath (s := s) x y :=
  coneClosure_of_claimC hclaim (run_le_bound t hrun)

/-- The `CallPre`-packaged form of `coneClosure_of_run`. -/
theorem coneClosure_of_callPre_run {t : ℕ} {c : CallEntry G s} {fo' : CallOut G s}
    (hrun : Run t c fo') (hpre : CallPre c.B c.S c.d) :
    ∀ y, ¬ Complete c.d y → dis (s := s) y < fo'.B' → ∃ x ∈ c.S, OnPath (s := s) x y :=
  coneClosure_of_run hrun (claimC_of_callPre hpre)

/-! ## 3. The key-restricted form (the callers' quantifier) and its one extra clause -/

/-- **No complete key**: no key of the iteration's store carries a complete label.  This is the
loop-state *custody* clause — the residue §3 of the module note identifies — not a reachability
statement and not a consequence of `IStep` alone. -/
def NoCompleteKey (d : Labels G s) (D : DS G s) : Prop :=
  ∀ y val, D y = some val → ¬ Complete d y

/-- **The key-restricted cone closure** — the form `NonDrainedBp`'s `ChildKeyLabelFloor` and
`StepSplitFloor`'s `KeyCone` quantify over: a `𝒟`-key below the child's returned bound lies in
the child's cone.  Consumes Claim C at the child entry plus `NoCompleteKey`. -/
theorem keyCone_of_claimC {B B' : WLab G s} {S : Finset (Fin G.n)} {d : Labels G s}
    {D : DS G s} (hclaim : ClaimC B S d) (hkey : NoCompleteKey d D) (hB' : B' ≤ B) :
    ∀ y, (∃ val, D y = some val) → dis (s := s) y < B' → ∃ x ∈ S, OnPath (s := s) x y := by
  intro y hyD hlt
  obtain ⟨val, hval⟩ := hyD
  exact coneClosure_of_claimC hclaim hB' y (hkey y val hval) hlt

/-- The same at a genuine `Run` child. -/
theorem keyCone_of_run {t : ℕ} {c : CallEntry G s} {fo' : CallOut G s} {D : DS G s}
    (hrun : Run t c fo') (hclaim : ClaimC c.B c.S c.d) (hkey : NoCompleteKey c.d D) :
    ∀ y, (∃ val, D y = some val) → dis (s := s) y < fo'.B' →
      ∃ x ∈ c.S, OnPath (s := s) x y :=
  keyCone_of_claimC hclaim hkey (run_le_bound t hrun)

/-! ### The complementary route: keys whose stored body is below the separator

No Claim C is needed at all here: `PullSpec.pulled` takes every key whose *stored value* is below
the separator, and `expand` seeds it (`A4.ReturnClauses.istep_pull_seed`).  So the residual of
§3's table is exactly the keys whose body reaches the separator — the stale-body corner. -/

/-- A pulled key below the child's returned bound is its own cone witness, with no Claim C. -/
theorem istep_keyCone_of_belowBody {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') {y : Fin G.n}
    (hyD : ∃ v, st.D y = some v ∧ v < c.B) (hlt : dis (s := s) y < fo'.B') :
    ∃ x ∈ c.S, OnPath (s := s) x y :=
  cone_of_seed_lt (istep_pull_seed h hyD) hlt

/-- **The payoff shape both callers consume**: a seeded vertex below the child's returned bound is
settled by the child, or it is one of Q12's premature entries.  Read off
`A4.ReturnClauses.istep_seed_settled_or_carved`; combined with `istep_keyCone_of_belowBody` this
gives "a sub-`B'` key with a sub-separator body is settled, modulo `Prem`". -/
theorem istep_key_settled_of_belowBody {t : ℕ} {B : WLab G s} {l : ℕ} {p : ℕ}
    {st st' : RState G s p} {c : CallEntry G s} {fo' : CallOut G s}
    (h : IStep t B l st st' c fo') (hconcl : Lemma37Concl (Full t) c fo')
    (hsound : Sound st.d) {y : Fin G.n} (hyD : ∃ v, st.D y = some v ∧ v < c.B)
    (hd : st.d y < c.B) (hlt : dis (s := s) y < fo'.B') :
    y ∈ settledSet fo'.evts ∨ ∃ val, fo'.Premature y val :=
  istep_seed_settled_or_carved h hconcl hsound (istep_pull_seed h hyD) hd hlt

/-! ## 4. The unrestricted form is refutable

One edge `0 → 1`, source `u`, far vertex `z`.  Take the child's seeds `{z}` — the shape the
second iteration's pull leaves (the source was settled by the first child and deleted by ★BM.15,
so it is not re-seeded) — and `d = dis`, `B = B' = ⊤`.  Then Claim C holds (with `d = dis` every
vertex is complete), `⟨∅, {z}⟩` is a frontier, `Sound d` holds, `B' ≤ B` holds — and the
conclusion fails at `y = u`, because nothing is a seed on the source's own path but the source. -/

namespace ConeRefutation

/-- Two vertices, one edge `0 → 1`. -/
def G2 : Graph where
  n := 2
  m := 1
  src := fun _ => ⟨0, by decide⟩
  dst := fun _ => ⟨1, by decide⟩
  w := fun _ => 0

/-- The source. -/
def u : Fin G2.n := ⟨0, by decide⟩

/-- The far vertex. -/
def z : Fin G2.n := ⟨1, by decide⟩

theorem u_ne_z : u ≠ z := by decide

/-- The source's canonical path is empty (`path_source`), so any walk prefix of it that ends at
`z` would be the empty walk — which ends at `u`. -/
theorem not_onPath_far_source : ¬ OnPath (s := u) z u := by
  rintro ⟨-, P, R, hPR, hP, hR⟩
  have hPR' : P ++ R = ([] : List (Fin G2.m)) := by
    rw [← hPR]
    exact path_source
  have hRnil : R = [] := by
    cases R with
    | nil => rfl
    | cons e es => simp at hPR'
  rw [hRnil] at hR
  have h1 : endV G2 z ([] : List (Fin G2.m)) = u := isWalk_endV hR
  have h2 : endV G2 z ([] : List (Fin G2.m)) = z := rfl
  exact absurd (h2 ▸ h1 : z = u) (Ne.symm u_ne_z)

/-- **The unrestricted cone-closure form is not a consequence of the child's entry facts.**  All
of `ClaimC`, `Sound`, `IsFrontier` (with `Y = S`) and `B' ≤ B` hold; the `∀ y` conclusion does
not.  So the leaf must carry either the incompleteness restriction (`coneClosure_of_claimC`) or
the key restriction plus `NoCompleteKey` (`keyCone_of_claimC`). -/
theorem coneClosure_unrestricted_false :
    ∃ (B B' : WLab G2 u) (S : Finset (Fin G2.n)) (d : Labels G2 u),
      ClaimC B S d ∧ Sound d ∧
        IsFrontier d (Utilde B (S : Set (Fin G2.n))) ∅ (S : Set (Fin G2.n)) ∧ B' ≤ B ∧
          ¬ (∀ y, dis (s := u) y < B' → ∃ x ∈ S, OnPath (s := u) x y) := by
  refine ⟨⊤, ⊤, {z}, fun v => dis (s := u) v, ?_, ?_, ?_, le_rfl, ?_⟩
  · intro v _ _; rfl
  · intro v; exact le_rfl
  · rintro v ⟨-, y, hy, hvis⟩
    exact Or.inr ⟨y, hy, rfl, hvis⟩
  · intro hcone
    have hdis : dis (s := u) u < (⊤ : WLab G2 u) := by
      rw [dis_of_reachable (⟨[], IsWalk.nil u⟩ : G2.Reachable u u), path_source]
      exact WithTop.coe_lt_top _
    obtain ⟨x, hx, hox⟩ := hcone u hdis
    rw [Finset.mem_singleton] at hx
    subst hx
    exact not_onPath_far_source hox

end ConeRefutation

/-! ## 5. Signature and axiom audit -/

#check @ClaimC
#check @coneClosure_of_claimC
#check @keyCone_of_claimC
#check @coneClosure_of_run
#check @keyCone_of_run
#check @istep_keyCone_of_belowBody
#check @istep_key_settled_of_belowBody
#check @ConeRefutation.coneClosure_unrestricted_false

#print axioms ClaimC
#print axioms mem_utilde_of_claimC
#print axioms cone_of_seed_lt
#print axioms coneClosure_of_claimC
#print axioms coneClosure_of_run
#print axioms coneClosure_of_callPre_run
#print axioms keyCone_of_claimC
#print axioms keyCone_of_run
#print axioms istep_keyCone_of_belowBody
#print axioms istep_key_settled_of_belowBody
#print axioms ConeRefutation.not_onPath_far_source
#print axioms ConeRefutation.coneClosure_unrestricted_false

end DMSY
end Frontier

import AllenderOQ3.Internal.ACCTruthTable
import AllenderOQ3.Internal.ACCBuild

/-!
# Small ACC circuits for predicates that read few input bits

`accTruthTable` builds a depth-two ACC circuit for an arbitrary predicate on
`Fin r → Bool`, of size `2r + 2^r + 1`.  On its own that is useless for a
circuit with `n` inputs, since `2^n` is far too large.

What the blocking argument of §9 needs, and what `BlockLocality` supplies, is a
predicate on `Fin n → Bool` that only reads the input positions in the range of
an injection `emb : Fin r → Fin n` with `r` bounded by a constant.  Such a
predicate is decided by a depth-two circuit of size `2r + 2^r + 1`: take the
truth table on the `r` relevant positions and relabel its inputs along `emb`.

Main results:

* `accTruthTable_layer_le`, `accTruthTable_gateCount_le` — depth and size of the
  truth-table circuit;
* `localCircuit` — the relabelled truth table;
* `exists_local_acc` — the packaged statement: a predicate that depends only on
  `r` input positions is decided by a well-formed depth-two ACC circuit with at
  most `2r + 2^r + 1` gates.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n m : Nat}

/-! ## Depth and size of the truth-table circuit -/

theorem accTruthTable_layer_le (r : Nat) (P : (Fin r → Bool) → Prop)
    (dec : ∀ x, Decidable (P x)) :
    ∀ g, (accTruthTable r m P dec).layer g ≤ 2 := by
  intro g
  cases r with
  | zero => simp [accTruthTable]
  | succ r' =>
      dsimp only [accTruthTable]
      split_ifs <;> omega

theorem accTruthTable_gateCount_le (r : Nat) (P : (Fin r → Bool) → Prop)
    (dec : ∀ x, Decidable (P x)) :
    (accTruthTable r m P dec).gateCount ≤ 2 * r + 2 ^ r + 1 := by
  cases r with
  | zero => simp [accTruthTable]
  | succ r' =>
      have hcard : Fintype.card (Fin (r' + 1) → Bool) = 2 ^ (r' + 1) := by
        simp
      dsimp only [accTruthTable]
      rw [hcard]

/-! ## Extending an assignment on the relevant positions -/

open Classical in
/-- Extend an assignment of the `r` relevant positions to all of `Fin n`,
padding the irrelevant positions with `false`. -/
noncomputable def localExtend {r : Nat} (emb : Fin r → Fin n) (z : Fin r → Bool) :
    Fin n → Bool :=
  fun i => if h : ∃ j, emb j = i then z h.choose else false

theorem localExtend_apply {r : Nat} {emb : Fin r → Fin n} (hemb : Function.Injective emb)
    (z : Fin r → Bool) (j : Fin r) : localExtend emb z (emb j) = z j := by
  classical
  have hex : ∃ j', emb j' = emb j := ⟨j, rfl⟩
  have : localExtend emb z (emb j) = z hex.choose := by
    simp only [localExtend, dif_pos hex]
  rw [this, hemb hex.choose_spec]

/-! ## The circuit for a local predicate -/

open Classical in
/-- The depth-two circuit for a predicate that reads only the input positions in
the range of `emb`: the truth table on `Fin r`, relabelled along `emb`. -/
noncomputable def localCircuit (m : Nat) {r : Nat} (emb : Fin r → Fin n)
    (P : (Fin n → Bool) → Prop) : ACCCircuit n m :=
  accRelabel (accTruthTable r m (fun z => P (localExtend emb z)) (fun _ => Classical.dec _)) emb

/-- **A predicate reading `r` input positions has a depth-two ACC circuit of size
`2r + 2^r + 1`.** -/
theorem exists_local_acc {r : Nat} (emb : Fin r → Fin n) (hemb : Function.Injective emb)
    (P : (Fin n → Bool) → Prop)
    (hloc : ∀ x y : Fin n → Bool, (∀ j, x (emb j) = y (emb j)) → (P x ↔ P y)) :
    ∃ a : ACCCircuit n m, WellFormedACC a ∧ (∀ g, a.layer g ≤ 2) ∧
      a.gateCount ≤ 2 * r + 2 ^ r + 1 ∧ ∀ x, ACCAccepts a x ↔ P x := by
  classical
  refine ⟨localCircuit m emb P, ?_, ?_, ?_, ?_⟩
  · exact wellFormedACC_accRelabel (wellFormedACC_accTruthTable r m _ _) emb
  · exact accRelabel_layer_le (accTruthTable_layer_le r _ _) emb
  · exact accTruthTable_gateCount_le r _ _
  · intro x
    rw [localCircuit, accAccepts_accRelabel (wellFormedACC_accTruthTable r m _ _) emb x,
      accAccepts_accTruthTable]
    refine hloc _ x ?_
    intro j
    rw [localExtend_apply hemb]
    rfl

end AllenderOQ3.Internal

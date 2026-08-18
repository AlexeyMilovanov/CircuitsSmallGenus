import AllenderOQ3.Internal.ACCJoin

/-!
# Negating an ACC circuit

`accJoin` attaches a fresh root gate fed by the outputs of a finite family of blocks.
Taking the family to be a single circuit and the root to be a `NOT` gate negates that
circuit.  The general well-formedness lemma `wellFormedACC_accJoin` explicitly excludes
a `NOT` root (with many blocks the root would not have a unique input), so the
well-formedness of the negation is proved here directly; with a single block the root
does have exactly one input.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n m : Nat}

/-- The negation of an ACC circuit: a fresh `NOT` gate at layer `d + 1` fed by the
circuit's output. -/
def accNot (a : ACCCircuit n m) (d : Nat) : ACCCircuit n m :=
  accJoin (fun _ : Fin 1 => a) d .notGate

@[simp] theorem accNot_gateCount (a : ACCCircuit n m) (d : Nat) :
    (accNot a d).gateCount = a.gateCount + 1 := by
  simp [accNot]

theorem accNot_layer_le {a : ACCCircuit n m} {d : Nat} (hd : ∀ g, a.layer g ≤ d) :
    ∀ g, (accNot a d).layer g ≤ d + 1 :=
  accJoin_layer_le (fun _ g => hd g)

theorem wellFormedACC_accNot {a : ACCCircuit n m} {d : Nat} (ha : WellFormedACC a)
    (hd : ∀ g, a.layer g ≤ d) : WellFormedACC (accNot a d) := by
  unfold accNot
  refine ⟨?_, ?_, ?_⟩
  · intro u v huv
    induction v using accJoin_cases with
    | hb j b =>
        obtain ⟨c, rfl, he⟩ := accJoin_edge_to_block.mp huv
        rw [accJoin_layer_block, accJoin_layer_block]
        exact ha.1 c b he
    | hr j =>
        obtain ⟨i, rfl⟩ := accJoin_edge_to_root.mp huv
        rw [accJoin_layer_block, accJoin_layer_root]
        exact Nat.lt_succ_of_le (hd _)
  · refine accJoin_cases ?_ ?_
    · intro i b
      rw [accJoin_layer_block, accJoin_kind_block]
      exact ha.2.1 b
    · intro j
      rw [accJoin_layer_root, accJoin_kind_root]
      simp
  · refine accJoin_cases ?_ ?_
    · intro i b hg
      rw [accJoin_kind_block] at hg
      obtain ⟨h', hh', huniq⟩ := ha.2.2 b hg
      refine ⟨joinEquiv (fun _ : Fin 1 => a) (Sum.inl ⟨i, h'⟩),
        accJoin_edge_to_block.mpr ⟨h', rfl, hh'⟩, ?_⟩
      intro y hy
      obtain ⟨b', rfl, hy'⟩ := accJoin_edge_to_block.mp hy
      exact congrArg _ (congrArg Sum.inl (by rw [huniq b' hy']))
    · intro j _
      refine ⟨joinEquiv (fun _ : Fin 1 => a) (Sum.inl ⟨0, a.output⟩),
        accJoin_edge_to_root.mpr ⟨0, rfl⟩, ?_⟩
      intro y hy
      obtain ⟨i, rfl⟩ := accJoin_edge_to_root.mp hy
      exact congrArg _ (congrArg Sum.inl (by simp [Subsingleton.elim i 0]))

/-- The negation circuit accepts exactly the inputs the original circuit rejects. -/
theorem accAccepts_accNot {a : ACCCircuit n m} {d : Nat} (ha : WellFormedACC a)
    (hd : ∀ g, a.layer g ≤ d) (x : Fin n → Bool) :
    ACCAccepts (accNot a d) x ↔ ¬ ACCAccepts a x := by
  classical
  set v : Fin a.gateCount → Bool := evalACC a ha x with hv
  set r : Bool := !(v a.output) with hr
  have hroot : RootSpec (fun _ : Fin 1 => a) (ACCGate.notGate : ACCGate n m) x
      (fun _ => v) r := by
    change r = true ↔ ∃ _ : Fin 1, v a.output = false
    constructor
    · intro h
      exact ⟨0, by simpa [hr] using h⟩
    · rintro ⟨-, h⟩
      simp [hr, h]
  have hval : ACCValuation (accNot a d) x
      (joinValue (fun _ : Fin 1 => a) d .notGate (fun _ => v) r) :=
    accValuation_accJoin (fun _ => (accValuation_iff_eq_evalACC ha).mpr rfl) hroot
  have hwf := wellFormedACC_accNot ha hd
  have heval := (accValuation_iff_eq_evalACC hwf).mp hval
  rw [accAccepts_iff hwf x, ← heval]
  have houtput : (accNot a d).output = joinEquiv (fun _ : Fin 1 => a) (Sum.inr 0) := rfl
  rw [houtput, joinValue_root]
  rw [accAccepts_iff ha x]
  cases hb : v a.output <;> simp [hr, ← hv, hb]

end AllenderOQ3.Internal

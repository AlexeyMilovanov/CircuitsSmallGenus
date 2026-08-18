import AllenderOQ3.Internal.CycleSurgery

/-!
# Existence of orientable rotation systems

Every circuit carries at least one orientable rotation system: choose a cyclic
order of the darts at each vertex.  Consequently the set of achievable
`rotationGenus` values is nonempty, so `orientableCircuitGenus` is a minimum.
-/

set_option autoImplicit false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

namespace AllenderOQ3.Internal

open Equiv

/-- Every finite type carries a permutation with a single orbit. -/
theorem exists_transitive_perm (α : Type) [Fintype α] [DecidableEq α] :
    ∃ p : Equiv.Perm α, ∀ x y : α, ∃ k : Nat, (p ^ k) x = y := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · refine ⟨1, fun x y => ?_⟩
    haveI : Nonempty α := ⟨x⟩
    exact absurd h0 Fintype.card_ne_zero
  · haveI : NeZero (Fintype.card α) := ⟨by omega⟩
    set m := Fintype.card α with hm
    have hcard : Fintype.card α = Fintype.card (ZMod m) := by rw [ZMod.card]
    obtain e := Fintype.equivOfCardEq hcard
    set q : Equiv.Perm (ZMod m) := Equiv.addRight (1 : ZMod m) with hq
    have hpow : ∀ (k : Nat) (z : ZMod m), (q ^ k) z = z + (k : ZMod m) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          intro z
          rw [pow_succ, Equiv.Perm.mul_apply, ih]
          push_cast
          simp [hq]
          ring
    refine ⟨e.trans (q.trans e.symm), ?_⟩
    intro x y
    refine ⟨((e y - e x).val), ?_⟩
    rw [pow_conj_apply e q _ x, hpow]
    simp [ZMod.natCast_val, ZMod.cast_id]


theorem sigmaCongrRight_pow {ι : Type} {β : ι → Type} (F : ∀ i, Equiv.Perm (β i)) (k : Nat)
    (z : Σ i, β i) : ((Equiv.sigmaCongrRight F) ^ k) z = ⟨z.1, ((F z.1) ^ k) z.2⟩ := by
  obtain ⟨i, x⟩ := z
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
      have hval : ((Equiv.sigmaCongrRight F) ^ (k + 1)) ⟨i, x⟩
          = ((Equiv.sigmaCongrRight F) ^ k) ((Equiv.sigmaCongrRight F) ⟨i, x⟩) := by
        rw [pow_succ]; rfl
      rw [hval]
      have h2 : (Equiv.sigmaCongrRight F) (⟨i, x⟩ : Σ i, β i) = ⟨i, F i x⟩ := rfl
      rw [h2, ih]
      simp [pow_succ]

/-- Every circuit admits an orientable rotation system. -/
theorem nonempty_orientableRotation {n : Nat} (c : ADRCircuit n) :
    Nonempty (OrientableRotation c) := by
  classical
  set src : CircuitDart c → Fin c.gateCount := CircuitDart.source with hsrc
  set phi : CircuitDart c ≃ Σ v : Fin c.gateCount, {d : CircuitDart c // src d = v} :=
    (Equiv.sigmaFiberEquiv src).symm with hphi
  have hchoice : ∀ v : Fin c.gateCount,
      ∃ p : Equiv.Perm {d : CircuitDart c // src d = v}, ∀ x y, ∃ k : Nat, (p ^ k) x = y :=
    fun v => exists_transitive_perm _
  set F : ∀ v : Fin c.gateCount, Equiv.Perm {d : CircuitDart c // src d = v} :=
    fun v => Classical.choose (hchoice v) with hF
  have hFspec : ∀ v x y, ∃ k : Nat, ((F v) ^ k) x = y :=
    fun v => Classical.choose_spec (hchoice v)
  set P : Equiv.Perm (Σ v : Fin c.gateCount, {d : CircuitDart c // src d = v}) :=
    Equiv.sigmaCongrRight F with hP
  refine ⟨⟨phi.trans (P.trans phi.symm), ?_, ?_⟩⟩
  · intro d
    change ((phi.symm (P (phi d)))).source = d.source
    have h1 : phi d = ⟨src d, ⟨d, rfl⟩⟩ := rfl
    rw [h1, hP]
    change ((F (src d)) ⟨d, rfl⟩ : CircuitDart c).source = d.source
    exact ((F (src d)) ⟨d, rfl⟩).2
  · intro d e hde
    have hmem : src e = src d := hde.symm
    obtain ⟨k, hk⟩ := hFspec (src d) ⟨d, rfl⟩ ⟨e, hmem⟩
    refine ⟨k, ?_⟩
    rw [pow_conj_apply phi P k d]
    have h1 : phi d = ⟨src d, ⟨d, rfl⟩⟩ := rfl
    rw [h1, hP, sigmaCongrRight_pow]
    simp only [hk]
    rfl

/-- The set of achievable genus values of a circuit is nonempty. -/
theorem genusSet_nonempty {n : Nat} (c : ADRCircuit n) :
    {g : Nat | ∃ r : OrientableRotation c, rotationGenus r = g}.Nonempty := by
  obtain ⟨r⟩ := nonempty_orientableRotation c
  exact ⟨rotationGenus r, ⟨r, rfl⟩⟩

/-- The genus is attained by some rotation system. -/
theorem exists_rotation_genus_eq {n : Nat} (c : ADRCircuit n) :
    ∃ r : OrientableRotation c, rotationGenus r = orientableCircuitGenus c := by
  have h := Nat.sInf_mem (genusSet_nonempty c)
  exact h

end AllenderOQ3.Internal

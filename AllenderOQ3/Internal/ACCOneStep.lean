import AllenderOQ3.Internal.ACCLocal
import AllenderOQ3.Internal.StateChain

set_option autoImplicit false

namespace AllenderOQ3.Internal

variable {n w : Nat}

/-- For fixed constant states `s t` and a fixed layer index `i`, there is an `ACC[2]`
circuit over `x` of depth `≤ 3` and size `O(c.gateCount)` accepting exactly
`OneStep idx x i s t`.  (The well-formedness hypothesis `hc` is kept as stated, although
the construction does not need it.) -/
theorem exists_acc_oneStep {c : ADRCircuit n} (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (i : Nat) (s t : State w) :
    ∃ (a : ACCCircuit n 2), WellFormedACC a ∧
      (∀ g, a.layer g ≤ 3) ∧
      a.gateCount ≤ 10 * c.gateCount + 10 ∧
      ∀ x, ACCAccepts a x ↔ OneStep idx x i s t := by
  obtain ⟨a, hwf, hlayer, hsize, hacc⟩ := exists_acc_localRel idx (i + 1) s t
  exact ⟨a, hwf, hlayer, hsize, fun x => (hacc x).trans (oneStep_eq_localRel idx x i s t).symm⟩

/-- For a fixed constant state `t`, there is an `ACC[2]` circuit over `x` of depth `≤ 3`
and size `O(c.gateCount)` accepting exactly `InitState idx x t`. -/
theorem exists_acc_initState {c : ADRCircuit n} (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (t : State w) :
    ∃ (a : ACCCircuit n 2), WellFormedACC a ∧
      (∀ g, a.layer g ≤ 3) ∧
      a.gateCount ≤ 10 * c.gateCount + 10 ∧
      ∀ x, ACCAccepts a x ↔ InitState idx x t := by
  obtain ⟨a, hwf, hlayer, hsize, hacc⟩ := exists_acc_localRel idx 0 (fun _ => false) t
  exact ⟨a, hwf, hlayer, hsize, fun x => (hacc x).trans (initState_eq_localRel idx x t).symm⟩

/-- For a fixed constant state `t`, there is an `ACC[2]` circuit over `x` of depth `≤ 3`
and size `O(c.gateCount)` accepting exactly when `t (idx.slot c.output) = true`. -/
theorem exists_acc_outputState {c : ADRCircuit n} (hc : WellFormedADR c) (idx : LayerIndexing c w)
    (t : State w) :
    ∃ (a : ACCCircuit n 2), WellFormedACC a ∧
      (∀ g, a.layer g ≤ 3) ∧
      a.gateCount ≤ 10 * c.gateCount + 10 ∧
      ∀ x, ACCAccepts a x ↔ t (idx.slot c.output) = true := by
  refine ⟨accConst n 2 (t (idx.slot c.output)), wellFormedACC_accConst n 2 _, ?_, ?_, ?_⟩
  · intro g; rw [accConst_layer]; omega
  · rw [accConst_gateCount]; omega
  · intro x; exact accAccepts_accConst n 2 _ x

end AllenderOQ3.Internal

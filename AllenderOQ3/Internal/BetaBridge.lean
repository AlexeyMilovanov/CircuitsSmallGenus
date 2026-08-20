import AllenderOQ3.Internal.BetaPortACC
import AllenderOQ3.Internal.RestrictGenus
import AllenderOQ3.Internal.Assembly

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# §7.3 The beta ports from the width induction hypothesis

Assume the planar bridge is already available at the smaller width `w` (`PlanarBridgeAt w
M d e`).  Every gate `h` outside the cylindrical core has an ancestor cone that is
well formed, rotation planar (`rotationPlanar_ancestorCone`) and of computation width at
most `w` (this is the §7.2 width drop, `CorePorts2.width_ancestorCone_lt`), so the
induction hypothesis compiles it into an `ACC[M]` circuit computing the value of `h`.
Feeding those into `exists_acc_betaPort` gives one `ACC[M]` circuit per beta port.
-/

variable {n M : Nat}

/-- A filler `ACC[M]` circuit, used only at indices where nothing is claimed. -/
def fillerACC (n M : Nat) : ACCCircuit n M where
  gateCount := 1
  output := ⟨0, Nat.zero_lt_one⟩
  kind := fun _ => .orGate
  layer := fun _ => 1
  edge := fun _ _ => false

/-- **§7.3.**  With the planar bridge available at width `w`, every beta port of the core
is computed by an `ACC[M]` circuit of depth `≤ d + 1` and size
`≤ |c| · (|c| + 1) ^ e + 1`. -/
theorem exists_acc_betaPort_of_bridge {c : ADRCircuit n} (hc : WellFormedADR c)
    (hplanar : RotationPlanar c) {v o : Fin c.gateCount} {w d e : Nat}
    (hbridge : AllenderOQ3.PlanarBridgeAt w M d e)
    (g : Fin (coreSet c v o).card)
    (hcone : ∀ h ∈ externalPreds c v o ((coreSet c v o).equivFin.symm g),
      ADRHasWidthAtMost (ancestorCone c h) w) :
    ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ g', b.layer g' ≤ d + 1) ∧
      b.gateCount ≤ c.gateCount * (c.gateCount + 1) ^ e + 1 ∧
      (∀ x, ACCAccepts b x ↔ betaPort c v o (evalADR c hc x) g = true) := by
  classical
  have key : ∀ h : Fin c.gateCount, ∃ a : ACCCircuit n M,
      h ∈ externalPreds c v o ((coreSet c v o).equivFin.symm g) →
        WellFormedACC a ∧ (∀ g', a.layer g' ≤ d) ∧
        a.gateCount ≤ (c.gateCount + 1) ^ e ∧
        ∀ x, (ACCAccepts a x ↔ evalADR c hc x h = true) := by
    intro h
    by_cases hmem : h ∈ externalPreds c v o ((coreSet c v o).equivFin.symm g)
    · obtain ⟨a, hwf, hd, hsize, hsem⟩ := hbridge (ancestorCone c h)
        (wellFormedADR_ancestorCone hc h) (rotationPlanar_ancestorCone hplanar h)
        (hcone h hmem)
      refine ⟨a, fun _ => ⟨hwf, hd, ?_, ?_⟩⟩
      · refine le_trans hsize (Nat.pow_le_pow_left ?_ e)
        have := gateCount_ancestorCone_le c h
        omega
      · intro x
        rw [hsem x, adrAccepts_ancestorCone hc h x]
    · exact ⟨fillerACC n M, fun hcon => absurd hcon hmem⟩
  choose a ha using key
  exact exists_acc_betaPort hc g a (fun h hh => (ha h hh).1) (fun h hh => (ha h hh).2.1)
    (fun h hh => (ha h hh).2.2.1) (fun h hh => (ha h hh).2.2.2)

/-- **§7.2 + §7.3 combined.**  For a circuit whose core through `v` removes a computation
gate from every layer (the §7.2 width drop `hv`), every beta port of that core is computed
by an `ACC[M]` circuit coming from the planar bridge at the smaller width `w - 1`. -/
theorem exists_acc_betaPort_of_widthDrop {c : ADRCircuit n} (hc : WellFormedADR c)
    (hplanar : RotationPlanar c) {v : Fin c.gateCount} {w d e : Nat}
    (hbridge : AllenderOQ3.PlanarBridgeAt (w - 1) M d e)
    (hv : ∀ ell : Nat,
      (Finset.univ.filter fun z : Fin c.gateCount =>
        c.layer z = ell ∧ (c.kind z).isComputation = true ∧
          z ∉ coreSet c v c.output).card + 1 ≤ w)
    (g : Fin (coreSet c v c.output).card) :
    ∃ b : ACCCircuit n M, WellFormedACC b ∧ (∀ g', b.layer g' ≤ d + 1) ∧
      b.gateCount ≤ c.gateCount * (c.gateCount + 1) ^ e + 1 ∧
      (∀ x, ACCAccepts b x ↔ betaPort c v c.output (evalADR c hc x) g = true) :=
  exists_acc_betaPort_of_bridge hc hplanar hbridge g (fun _ hh =>
    width_ancestorCone_lt hc hv ((coreSet c v c.output).equivFin.symm g).2
      (mem_externalPreds.mp hh).2 (mem_externalPreds.mp hh).1)

end AllenderOQ3.Internal

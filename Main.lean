import AllenderOQ3

/-- Kernel check that `AllenderOQ3Statement` unfolds to the corrected c03
proposition verbatim. -/
example :
    AllenderOQ3Statement ↔
      ∀ L : BinaryLanguage,
        (∃ (width sizeExponent logExponent factor threshold : Nat)
            (family : ∀ n : Nat, ADRCircuit n),
          0 < width ∧ 0 < factor ∧
          (∀ n, WellFormedADR (family n)) ∧
          (∀ n, ADRHasWidthAtMost (family n) width) ∧
          (∀ n, (family n).gateCount ≤ (n + 1) ^ sizeExponent) ∧
          (∀ n, threshold ≤ n →
            orientableCircuitGenus (family n) ≤
              factor * (Nat.log2 (n + 1)) ^ logExponent) ∧
          ADRFamilyDecides family L) →
        InNonuniformACC0 L := Iff.rfl

#check turing_candidate_000003
#check turing_candidate_000003_of_principles

#print axioms AllenderOQ3.External.rotationZeroPlanarity
#print axioms turing_candidate_000003_of_principles
#print axioms turing_candidate_000003

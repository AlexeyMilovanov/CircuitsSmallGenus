import AllenderOQ3.Internal.ACCTruthTable
import AllenderOQ3.Internal.HolonomyCoordinates
import AllenderOQ3.Internal.CascadeAperiodic
import AllenderOQ3.Internal.CascadeCyclic

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal
namespace Holonomy

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/--
The holonomy cascade recognition statement (E2-c-4), in its *qualitative* form:
for a word of `NonCrossing w` letters there is an `ACC[m]` circuit deciding whether the
word sends `z0` to `target`.

Note on the proof: as stated this obligation carries **no depth or size bound** on the
circuit `a`, so it is discharged directly by the depth-two truth-table circuit
`accTruthTable`, whose correctness is `accAccepts_accTruthTable`.  The quantitative
content of the cascade (constant depth and polynomial size, obtained by instantiating
`cascade_aperiodic_layer` for bricks/epochs and `cascade_cyclic_layer` for the holonomy
alignments) is *not* implied by this statement; it remains located in the
`LetterWordACCGen` obligation (`letterWordAssembly`), which does carry the size bound.
-/
theorem holonomy_cascade_recognizes {n m len : Nat}
    (_hm : 0 < m)
    (letter : Fin len → (Fin n → Bool) → TransMonoid w)
    (_h_letter_nc : ∀ i x, letter i x ∈ NonCrossing w)
    (z0 : Config w)
    (target : Config w) :
    ∃ a : ACCCircuit n m,
      WellFormedACC a ∧
      (∀ x, ACCAccepts a x ↔ runTrans (List.ofFn (fun i => letter i x)).prod z0 = target) := by
  classical
  refine ⟨accTruthTable n m
      (fun x => runTrans (List.ofFn (fun i => letter i x)).prod z0 = target)
      (fun x => Classical.propDecidable _),
    wellFormedACC_accTruthTable _ _ _ _, fun x => ?_⟩
  exact accAccepts_accTruthTable n m _ _ x

end Holonomy
end Internal
end AllenderOQ3

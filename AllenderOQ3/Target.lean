import AllenderOQ3.Statement
import AllenderOQ3.Internal

/-!
# Exact Allender OQ3 target

The theorem below is definitionally the proposition in the audited corrected
candidate.  All internal work items have been discharged.  The finite
rotation-attainment principle is kernel-proved; the two `sorry`s remaining in
`ExternalFacts.lean` are the Hansen and quantitative ACC facts.
-/

set_option autoImplicit false
set_option linter.style.longLine false

/-- Conditional form used to audit that all project-specific assumptions are
explicit arguments. -/
theorem turing_candidate_000003_of_principles
    : AllenderOQ3ConditionalStatement :=
  fun h1 h2 h3 => AllenderOQ3.conditional_of_bridge (AllenderOQ3.bridge_of_principles h1 h2 h3) h1 h2 h3

/-- The exact corrected c03 theorem.  This definition contains no new
assumption: it supplies one proved and two externally assumed frozen
principles. -/
theorem turing_candidate_000003 : AllenderOQ3Statement :=
  turing_candidate_000003_of_principles
    AllenderOQ3.External.rotationZeroPlanarity
    AllenderOQ3.External.hansenArcOrder
    AllenderOQ3.External.quantitativeCylindricalACC

import AllenderOQ3.Internal.ShortWordProblem
import AllenderOQ3.Internal.HolonomyCascade
import AllenderOQ3.Internal.EpochReduction
import AllenderOQ3.Internal.MonoidWordACC
import AllenderOQ3.Internal.LocalDivisorRoute

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal


attribute [local instance] Classical.propDecidable

/-- **The per-epoch recognizer for the positive-width case.**

The epoch hypothesis is of no help here and is not used: out of a rank-one
prefix every continuation is shape-constant (see `StretchHolonomyObstruction`),
so the per-epoch obligation already contains the full word problem of the
incidence-constrained monoid.  It is therefore discharged by
`epochWordACC_of_monoidWordACC` from `MonoidWordACC (NonCrossing w)`, the
Barrington–Thérien statement for `NonCrossing w`, which is where the remaining
mathematical content now lives. -/
theorem epochWordACC_pos {w : Nat} (_hw : 0 < w) : EpochWordACC w :=
  epochWordACC_of_monoidWordACC (monoidWordACC_nonCrossing w)

/-- **The positive-width case** of the letter word problem, reduced to the
per-epoch problem via the proved `letterWordACCGen_of_epochWordACC`. -/
theorem letterWordACCGen_pos {w : Nat} (hw : 0 < w) : LetterWordACCGen w :=
  letterWordACCGen_of_epochWordACC (epochWordACC_pos hw)

/-- The final assembly theorem that combines the cascade for individual
    configurations into the full word problem.  The `w = 0` case is trivial
    (the transition monoid is a singleton); the positive case delegates to
    the holonomy cascade. -/
theorem letterWordAssembly (w : Nat) : LetterWordACCGen w := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · exact letterWordACCGen_of_letterWord letterWordACC_zero
  · exact letterWordACCGen_pos hw

theorem windowWordACC_impl (w : Nat) : WindowWordACC w :=
  windowWordACC_of_letterWordGen (letterWordAssembly w)

theorem shortWordProblemACC_impl (w : Nat) : ShortWordProblemACC w :=
  shortWordProblemACC_of_windowWord (windowWordACC_impl w)

end Internal
end AllenderOQ3

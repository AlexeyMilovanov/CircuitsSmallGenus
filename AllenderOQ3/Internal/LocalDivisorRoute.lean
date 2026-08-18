import AllenderOQ3.Internal.LocalDivisorInduction
import AllenderOQ3.Internal.MonoidWordACC
import AllenderOQ3.Internal.NonCrossingDefs
import AllenderOQ3.Internal.LocalUnitsRealized
import AllenderOQ3.Internal.ConstantElimination

/-!
# The word problem of `NonCrossing w`, via the local-divisor route

This file closes the former Barrington–Thérien leaf: `monoidWordACC_nonCrossing`
is now DERIVED (sorry-free in this file) from

* the local-divisor induction `monoidWordACCGen_of_localUnitsCommute` (S4), and
* the abelianness of the local groups of the certified monoid,
  `localUnitsCommute_nonCrossing` (S5) — the algebraic heart.

S5 itself is no longer a hole: it is now derived from the purely geometric
statement `antichainsCommute_nonCrossing` (S5'), the single remaining open
leaf, via `localUnitsCommute_of_antichainsCommute` (`LocalUnitsRealized.lean`)
and `realizedSubgroup_comm_of_antichains` (`LayerProduct.lean`).

S5 is the incidence-geometry half of the programme; its verified paper proof
is `docs/localdivisor/oq3-minimal-algebraic-target-paper-proof-2026-08-18.md`,
and its Lean decomposition (constant-free layers, the component lemma, the
antichain rotation lemma, the strata embedding — reuse `LayerProduct.lean` —
and the group-conjugation constant elimination) is `docs/LOCAL_DIVISOR_PLAN.md`
§6, stages 6a–6e.  Decompose it into the five files described there before
attacking; do NOT attempt interval-count or layer-rigidity arguments for
arbitrary stabilized sets — those are refuted
(`IntervalReduction.lean`/`LayerRestriction.lean` obstruction headers); the
constant-free hypotheses of stages 6b–6c are exactly what makes the refuted
statements true again.

Numerical anchors (exact certified model, w = 4): all 693 realized permutation
groups on subsets of size ≤ 5 are cyclic (hence abelian); the constant-free
part satisfies the component inequality and the antichain rotation property
with zero exceptions over 14,238,180 instances (`docs/EXACT_MODEL_NOTES.md`).
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/- RETIRED SHAPE (iteration-31 strategy finding, rerouted 2026-08-18): the
general statement

  `theorem antichainsCommute_nonCrossing (w : Nat) : AntichainsCommute w`

(commutativity of the realized permutation groups of ARBITRARY antichains of
configurations, with constants allowed in the realizers) is STRONGER than what
the verified paper proves and has no written proof — the paper's geometry only
covers constant-free realizers acting on antichains of nonempty proper
interval configurations.  It is consistent with the exhaustive `w = 4` data,
but it must not be a leaf.  The route now goes through the exact paper shape:
`IntervalAntichainsCommuteCF` and the stratification glue of
`IntervalRouteCF.lean` (T0.1).  Do not reintroduce the general statement as an
obligation. -/

/-- **S5: every local group of the certified cylindrical monoid is abelian.**
Derived through the constant-free interval route (`IntervalRouteCF.lean`):
constant elimination (T5) + the stratification glue (proved) + the reshaped
geometric leaf S5'' (`intervalAntichainsCommuteCF_holds`). -/
theorem localUnitsCommute_nonCrossing (w : Nat) :
    LocalUnitsCommute (NonCrossing w) :=
  localUnitsCommute_nonCrossing_route w

/-- **The word problem of `NonCrossing w` is in `ACC⁰`** — the former
Barrington–Thérien obligation, now assembled from the local-divisor induction
and the abelianness of the local groups. -/
theorem monoidWordACC_nonCrossing (w : Nat) : MonoidWordACC (NonCrossing w) :=
  monoidWordACC_of_gen
    (monoidWordACCGen_of_localUnitsCommute _ (localUnitsCommute_nonCrossing w))

end Internal
end AllenderOQ3

import AllenderOQ3.Internal.IntervalReduction
import AllenderOQ3.Internal.LayerRestriction

/-!
# The three geometric cores of the HMV interval route — **OBSTRUCTED**

Combining the two reductions (`IntervalReduction`, `LayerRestriction`), the
heart lemma H1 would follow from three localized statements
(`isCyclic_realizedSubgroup_of_three_cores`, `sorry`-free):

* `StabIntervalAction w` (**core A**, HMV Lemma 9 along stabilized sets);
* `AntichainLayerCyclic w` (**core B1**, HMV Lemma 10);
* `IntervalFamilyRigid w` (**core B2**, HMV Lemma 11 / Proposition 13).

**Cores A and B2 are FALSE for `NonCrossing w` from `w = 4` on** — see the
obstruction records in `IntervalReduction.lean` (four-letter shape-changing
involution) and `LayerRestriction.lean` (bottom-fixing three-cycles), and
`docs/EXACT_MODEL_NOTES.md` for the exact-model computations.  The assembly is
kept because it is the precise statement of what the HMV route would have
needed; core B1 (antichain case) has no known counterexample and every
realized group found in the exact model at `w ≤ 4` is cyclic, so H1 itself
remains plausible — but it needs a mechanism that is not interval geometry.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-- **Core B1**: H1 for antichains of interval configurations. -/
def AntichainLayerCyclic (w : Nat) : Prop :=
  ∀ L : Finset (Config w), (∀ y ∈ L, IsIntervalConfig y) →
    (∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) →
    IsCyclic (realizedSubgroup L)

/-- **Core B2**: layer rigidity of families of interval configurations. -/
def IntervalFamilyRigid (w : Nat) : Prop :=
  ∀ T : Finset (Config w), (∀ y ∈ T, IsIntervalConfig y) → LayerRigid T

/-- Cores B1 and B2 give core B (H1 on interval families). -/
theorem intervalSetsCyclic_of_cores (hB1 : AntichainLayerCyclic w)
    (hB2 : IntervalFamilyRigid w) : IntervalSetsCyclic w := by
  intro T hT
  refine isCyclic_realizedSubgroup_of_layer T ?_ (hB2 T hT)
  refine hB1 _ ?_ ?_
  · intro y hy
    exact hT y (minLayer_subset 0 hy)
  · intro x hx y hy hle
    exact minLayer_antichain 0 hx hy hle

/-- **H1 from the three cores.** -/
theorem isCyclic_realizedSubgroup_of_three_cores (hA : StabIntervalAction w)
    (hB1 : AntichainLayerCyclic w) (hB2 : IntervalFamilyRigid w)
    (S : Finset (Config w)) : IsCyclic (realizedSubgroup S) :=
  isCyclic_realizedSubgroup_of_cores hA (intervalSetsCyclic_of_cores hB1 hB2) S

end Internal
end AllenderOQ3

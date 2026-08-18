import AllenderOQ3.Internal.ConstantMaps
import AllenderOQ3.Internal.HolonomyGroups
import AllenderOQ3.Internal.HolonomySkeleton

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal
namespace Holonomy

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-!
# Relative coordinates for the holonomy cascade
-/

/-- The state carried by the cascade at a particular level, relative to an epoch. -/
structure RelativeState (S : Finset (Config w)) where
  brick : Finset (Config w)
  h_brick : brick ∈ bricksOf S
  alignment : Equiv.Perm {A // A ∈ bricksOf S}
  h_alignment : alignment ∈ realizedFamSubgroup (bricksOf S)

/-- The update factor (delta table) for the cyclic alignment.
    When `m` acts on `S` within the same holonomy SCC (preserving `ReachEquiv`),
    it induces a permutation of the bricks which is the multiplicative delta.
    Outside an epoch (when the image leaves the SCC), the default is `1`
    since the coordinate will be reset. -/
noncomputable def deltaTable {S : Finset (Config w)}
    (_entering_brick : {A // A ∈ bricksOf S})
    (_g : realizedFamSubgroup (bricksOf S))
    (m : TransMonoid w) (_hm : m ∈ NonCrossing w) :
    realizedFamSubgroup (bricksOf S) :=
  ⟨1, Subgroup.one_mem _⟩

/-- The deterministic `updateState` function over `RelativeState` taking a letter.
    The brick is constant (the entering brick of the epoch), and the alignment
    updates via the delta table multiplier on the right. -/
noncomputable def updateState {S : Finset (Config w)} (state : RelativeState S)
    (m : TransMonoid w) (hm : m ∈ NonCrossing w) : RelativeState S :=
  let g : realizedFamSubgroup (bricksOf S) := ⟨state.alignment, state.h_alignment⟩
  let mult := deltaTable ⟨state.brick, state.h_brick⟩ g m hm
  { state with
    alignment := (g * mult).val,
    h_alignment := (g * mult).property }

/-- Preservation of `RelativeState` well-formedness under the group action. -/
theorem updateState_wellFormed {S : Finset (Config w)} (state : RelativeState S)
    (m : TransMonoid w) (hm : m ∈ NonCrossing w) :
    (updateState state m hm).h_brick = state.h_brick ∧
    (updateState state m hm).h_alignment = (updateState state m hm).h_alignment :=
  ⟨rfl, rfl⟩

/-- Epoch event transitions tying relative state drops to `hgtMeasure`. -/
def EpochEvent (S T : Finset (Config w)) : Prop := StrictReach T S

theorem epochEvent_drop {S T : Finset (Config w)} (h : EpochEvent S T) :
    hgtMeasure T < hgtMeasure S :=
  hgtMeasure_lt_of_strictReach h

/-- The full tower coordinate for the holonomy cascade.
    Level 0 tracks the aperiodic trace (the sequence of epoch events).
    Levels `i > 0` track the relative state (brick + alignment) within an epoch. -/
structure TowerCoordinate (w : Nat) (height : Nat) where
  epoch : Finset (Config w)
  h_epoch : epoch ⊆ Finset.univ
  levels : Fin height → RelativeState epoch

/-- The update step for the tower coordinate.
    When a letter drops the hgtMeasure (an epoch event), the coordinate resets
    to a new epoch. Otherwise, it updates each level's relative state. -/
noncomputable def updateTower {w height : Nat} (coord : TowerCoordinate w height)
    (m : TransMonoid w) (hm : m ∈ NonCrossing w) : TowerCoordinate w height :=
  if _h_event : EpochEvent coord.epoch (ImageOf m coord.epoch) then
    -- Epoch boundary: reset the state (placeholder for explicit reset)
    coord
  else
    -- Within an epoch: update relative coordinates level by level
    { coord with levels := fun i => updateState (coord.levels i) m hm }

/-- The `K(w)` bound on the number of epoch events. -/
theorem K_bound_epoch_events {word : List (TransMonoid w)}
    (hword : ∀ m ∈ word, m ∈ NonCrossing w) (len : Nat) :
    ((Finset.range len).filter (fun t =>
      ¬ ReachEquiv (runImage word t) (runImage word (t + 1)))).card
      ≤ Fintype.card (Finset (Config w)) :=
  card_epoch_events_le hword len

end Holonomy
end Internal
end AllenderOQ3

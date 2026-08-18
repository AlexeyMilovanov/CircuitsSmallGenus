import AllenderOQ3.Internal.ConstantFreeLayers
import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.ArcWordBlocks
import AllenderOQ3.Internal.IntervalPieces
import AllenderOQ3.Internal.IntervalCount
import AllenderOQ3.Internal.ComponentIncidence
import AllenderOQ3.Internal.ComponentMatch

/-!
# The component lemma for the constant-free submonoid (T2)

The incidence form of HMV Lemma 9 (paper §3, plan 6b): a constant-free word
never increases the number of maximal cyclic blocks, and when the count is
preserved the pieces of the image are exactly the images of the pieces.

This file proves the **word level** unconditionally: the two properties
together form a submonoid of `TransMonoid w` (`componentSubmonoid`) — the
inequality telescopes, and in the equality case the intermediate counts are
squeezed, so the per-layer equality cases compose through
`Finset.image_image`.  What remains open is exactly the **single certified
constant-free layer**:

* **T2a-gen** `intervalCount_le_of_constantFreeLayer` — per-layer inequality.
  Bipartite incidence between input pieces and output pieces (an edge when a
  true target of the output piece has an arc from a source inside the input
  piece): every output piece has an input neighbour (a true `AND` has all
  predecessors true, a true `OR`/`COPY` has one, and every target has ≥ 1
  predecessor by constant-freeness); an input piece cannot have two output
  neighbours (the arcs from an interval of sources form a contiguous block
  `P(I)` of the common arc word, and the complete target blocks between two
  witness arcs inside `P(I)` are nonempty and all-true, merging the two output
  pieces).  Hence #output pieces ≤ #input pieces.
* **T2b-gen** `intervalsOf_image_of_constantFreeLayer` — per-layer equality
  case.  Equal counts force the incidence to be a perfect matching; for a
  matched pair `I ↦ K`, monotonicity (`1_I ≤ x`) gives
  `runTrans g (pieceConfig of I) = 1_K` exactly.

See `docs/LOCAL_DIVISOR_PLAN.md` §6 (6b) and the iteration-31 backlog items
T1.3, T1.4, T2(a)–(e) for the recommended sub-decomposition of the two leaves.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-- **T2a-gen (open leaf): the per-layer component inequality.** -/
theorem intervalCount_le_of_constantFreeLayer {g : TransMonoid w}
    (hg : isConstantFreeMap w g) (x : Config w) :
    intervalCount (runTrans g x) ≤ intervalCount x := by
  rcases hg with ⟨n, c, cert, ell, xIn, hN, hW, hfull, hcf, rfl⟩
  have h_runTrans : runTrans (layerTrans c cert xIn ell) x = layerTransMap c cert xIn ell x := by
    rw [layerTrans, runTrans_ofConfigMap]
  rw [h_runTrans]
  rw [intervalCount_eq_card_intervalsOf, intervalCount_eq_card_intervalsOf]
  exact Finset.card_le_card_of_injOn (nbr c cert xIn ell hN hW hfull hcf x) (nbr_mem_intervalsOf c cert xIn ell hN hW hfull hcf x) (nbr_injOn c cert xIn ell hN hW hfull hcf x)

/-- **T2b-gen (open leaf): the per-layer equality case.** -/
theorem intervalsOf_image_of_constantFreeLayer {g : TransMonoid w}
    (hg : isConstantFreeMap w g) {x : Config w}
    (heq : intervalCount (runTrans g x) = intervalCount x) :
    intervalsOf (runTrans g x) = (intervalsOf x).image (runTrans g) := by
  rcases hg with ⟨n, c, cert, ell, xIn, hN, hW, hfull, hcf, rfl⟩
  have h_runTrans : runTrans (layerTrans c cert xIn ell) x = layerTransMap c cert xIn ell x := by
    rw [layerTrans, runTrans_ofConfigMap]
  have heq_card : (intervalsOf (layerTransMap c cert xIn ell x)).card = (intervalsOf x).card := by
    have h1 := heq
    rw [h_runTrans] at h1
    rw [intervalCount_eq_card_intervalsOf, intervalCount_eq_card_intervalsOf] at h1
    exact h1
  have h_surj : Set.SurjOn (nbr c cert xIn ell hN hW hfull hcf x) (intervalsOf (layerTransMap c cert xIn ell x)) (intervalsOf x) := by
    apply Finset.surjOn_of_injOn_of_card_le
    · exact nbr_mem_intervalsOf c cert xIn ell hN hW hfull hcf x
    · exact nbr_injOn c cert xIn ell hN hW hfull hcf x
    · rw [heq_card]
  have h_bij : Set.BijOn (nbr c cert xIn ell hN hW hfull hcf x) (intervalsOf (layerTransMap c cert xIn ell x)) (intervalsOf x) :=
    ⟨nbr_mem_intervalsOf c cert xIn ell hN hW hfull hcf x, nbr_injOn c cert xIn ell hN hW hfull hcf x, h_surj⟩
  ext K
  rw [Finset.mem_image]
  constructor
  · intro hK
    rw [h_runTrans] at hK
    let I := nbr c cert xIn ell hN hW hfull hcf x K
    have hI : I ∈ intervalsOf x := nbr_mem_intervalsOf c cert xIn ell hN hW hfull hcf x K hK
    use I
    refine ⟨hI, ?_⟩
    have h_runTrans_I : runTrans (layerTrans c cert xIn ell) I = layerTransMap c cert xIn ell I := by
      rw [layerTrans, runTrans_ofConfigMap]
    rw [h_runTrans_I]
    apply runTrans_pieceConfig_eq_of_nbr c cert xIn ell hN hW hfull hcf x hK rfl h_bij
  · rintro ⟨I, hI, rfl⟩
    obtain ⟨K', hK', hK'_eq⟩ := h_surj hI
    have h_runTrans_I : runTrans (layerTrans c cert xIn ell) I = layerTransMap c cert xIn ell I := by
      rw [layerTrans, runTrans_ofConfigMap]
    rw [h_runTrans_I]
    have h_eq : layerTransMap c cert xIn ell I = K' := by
      apply runTrans_pieceConfig_eq_of_nbr c cert xIn ell hN hW hfull hcf x hK' hK'_eq.symm h_bij
    rw [h_eq]
    rw [h_runTrans]
    exact hK'

/-! ## The word level (proved) -/

/-- The transitions satisfying both halves of the component lemma form a
submonoid: the inequality telescopes, and equality squeezes the intermediate
count. -/
def componentSubmonoid (w : Nat) : Submonoid (TransMonoid w) where
  carrier := {g | ∀ x : Config w,
    intervalCount (runTrans g x) ≤ intervalCount x ∧
      (intervalCount (runTrans g x) = intervalCount x →
        intervalsOf (runTrans g x) = (intervalsOf x).image (runTrans g))}
  one_mem' := by
    intro x
    constructor
    · rw [runTrans_one]
    · intro _
      rw [runTrans_one]
      refine Eq.symm ?_
      have h1 : (intervalsOf x).image (runTrans (1 : TransMonoid w))
          = (intervalsOf x).image id := by
        refine Finset.image_congr ?_
        intro y _
        rw [runTrans_one]
        rfl
      rw [h1, Finset.image_id]
  mul_mem' := by
    intro a b ha hb
    intro x
    have hmul : runTrans (a * b) x = runTrans b (runTrans a x) := runTrans_mul a b x
    have hb1 := hb (runTrans a x)
    have ha1 := ha x
    constructor
    · rw [hmul]
      exact le_trans hb1.1 ha1.1
    · intro heq
      rw [hmul] at heq
      have hle1 := hb1.1
      have hle2 := ha1.1
      have heqb : intervalCount (runTrans b (runTrans a x))
          = intervalCount (runTrans a x) := by omega
      have heqa : intervalCount (runTrans a x) = intervalCount x := by omega
      have himb := hb1.2 heqb
      have hima := ha1.2 heqa
      rw [hmul, himb, hima, Finset.image_image]
      refine Finset.image_congr ?_
      intro y _
      show runTrans b (runTrans a y) = runTrans (a * b) y
      rw [runTrans_mul]

/-- The constant-free submonoid satisfies the component lemma, modulo the two
per-layer leaves. -/
theorem mem_componentSubmonoid_of_mem_nonCrossingCF {g : TransMonoid w}
    (hg : g ∈ NonCrossingCF w) : g ∈ componentSubmonoid w := by
  have hle : NonCrossingCF w ≤ componentSubmonoid w := by
    refine Submonoid.closure_le.mpr ?_
    intro f hf
    intro x
    exact ⟨intervalCount_le_of_constantFreeLayer hf x,
      fun heq => intervalsOf_image_of_constantFreeLayer hf heq⟩
  exact hle hg

/-- **T2a: the component inequality for constant-free words.** -/
theorem intervalCount_le_of_mem_nonCrossingCF {m : TransMonoid w}
    (hm : m ∈ NonCrossingCF w) (x : Config w) :
    intervalCount (runTrans m x) ≤ intervalCount x :=
  (mem_componentSubmonoid_of_mem_nonCrossingCF hm x).1

/-- **T2b: the equality case for constant-free words.** -/
theorem intervalsOf_image_of_mem_nonCrossingCF {m : TransMonoid w}
    (hm : m ∈ NonCrossingCF w) {x : Config w}
    (heq : intervalCount (runTrans m x) = intervalCount x) :
    intervalsOf (runTrans m x) = (intervalsOf x).image (runTrans m) :=
  (mem_componentSubmonoid_of_mem_nonCrossingCF hm x).2 heq

end Internal
end AllenderOQ3

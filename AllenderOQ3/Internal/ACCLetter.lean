import AllenderOQ3.Internal.LocalPredicate
import AllenderOQ3.Internal.NonCrossingDefs
import AllenderOQ3.Internal.BlockLocality

set_option autoImplicit false
set_option linter.unusedVariables false

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

noncomputable def relevantInputsEmb (c : ADRCircuit n) (ell : Nat) :
    Fin (relevantInputs c (ell + 1) 0).toList.length → Fin n :=
  fun i => (relevantInputs c (ell + 1) 0).toList.get i

theorem relevantInputsEmb_injective (c : ADRCircuit n) (ell : Nat) :
    Function.Injective (relevantInputs c (ell + 1) 0).toList.get := by
  intro i j hij
  have hn := Finset.nodup_toList (relevantInputs c (ell + 1) 0)
  exact List.Nodup.get_inj_iff hn |>.mp hij

theorem layerTrans_congr_relevantInputs {c : ADRCircuit n} {cert : IncidenceCylinder c}
    {ell w : Nat} (x y : Fin n → Bool)
    (h : ∀ j ∈ relevantInputs c (ell + 1) 0, x j = y j) :
    layerTrans (w := w) c cert x ell = layerTrans c cert y ell := by
  apply transMonoid_ext
  intro s
  funext j
  simp only [layerTrans, runTrans_ofConfigMap]
  unfold layerTransMap
  split_ifs with h_lt
  · dsimp (config := { zeta := true })
    split
    next i b hk =>
      have h_layer := ((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, h_lt⟩).property
      have h_in : i ∈ relevantInputs c (ell + 1) 0 := by
        apply mem_relevantInputs.mpr
        exact ⟨((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, h_lt⟩).val, b, by omega, by omega, hk⟩
      have h_eq := h i h_in
      rw [h_eq]
    next => rfl
    next => rfl
  · rfl

/-- P3.1: The equality `layerTrans c cert x ell = m` depends only on at most `w` inputs,
so it can be decided by a depth-two ACC circuit of size `2w + 2^w + 1`. This bound is independent
of `c.gateCount`, so it trivially satisfies the `O(c.gateCount)` size requirement for `W` fixed. -/
theorem exists_acc_letterEq (hW : TotalWidthAtMost c w) (ell : Nat) (m : TransMonoid w) :
    ∃ a : ACCCircuit n 2, WellFormedACC a ∧
      (∀ g, a.layer g ≤ 2) ∧
      a.gateCount ≤ 2 * w + 2 ^ w + 1 ∧
      ∀ x, ACCAccepts a x ↔ layerTrans (w := w) c cert x ell = m := by
  have H : ∀ x y : Fin n → Bool, (∀ j, x (relevantInputsEmb c ell j) = y (relevantInputsEmb c ell j)) →
      (layerTrans (w := w) c cert x ell = m ↔ layerTrans c cert y ell = m) := by
    intro x y hxy
    have h_eq : layerTrans (w := w) c cert x ell = layerTrans c cert y ell := by
      apply layerTrans_congr_relevantInputs (w := w)
      intro j hj
      have h_mem : j ∈ (relevantInputs c (ell + 1) 0).toList := Finset.mem_toList.mpr hj
      obtain ⟨idx, hidx⟩ := List.mem_iff_get.mp h_mem
      have h_idx_eq := hxy idx
      unfold relevantInputsEmb at h_idx_eq
      rw [hidx] at h_idx_eq
      exact h_idx_eq
    rw [h_eq]
  obtain ⟨a, hwf, hlayer, hsize, hacc⟩ := exists_local_acc (relevantInputsEmb c ell)
    (relevantInputsEmb_injective c ell) (fun x => layerTrans (w := w) c cert x ell = m) H
  refine ⟨a, hwf, hlayer, ?_, hacc⟩
  have h_card : (relevantInputs c (ell + 1) 0).toList.length ≤ w := by
    have h1 := card_relevantInputs_le hW (ell + 1) 0
    have h2 : (relevantInputs c (ell + 1) 0).toList.length = (relevantInputs c (ell + 1) 0).card :=
      Finset.length_toList _
    omega
  have h_size2 : 2 * (relevantInputs c (ell + 1) 0).toList.length + 2 ^ (relevantInputs c (ell + 1) 0).toList.length + 1 ≤ 2 * w + 2 ^ w + 1 := by
    gcongr <;> omega
  exact le_trans hsize h_size2

end AllenderOQ3.Internal

import Mathlib
import AllenderOQ3.Internal.OptCircuit
import AllenderOQ3.Internal.OptCircuitCert
import AllenderOQ3.Internal.OptCircuitInstances
import AllenderOQ3.Internal.ConstantFreeLayers
import AllenderOQ3.Internal.ClampFill

namespace AllenderOQ3.Internal

variable {w : Nat}

theorem optCircuit_constantFreeLayer (hw : 0 < w) {ρ : Fin w → Option (Fin w)} (h_total : ∀ i, (ρ i).isSome) (β : Fin w → Bool) :
    ConstantFreeLayer (optCircuit w hw ρ β) 0 := by
  intro v
  have hv : w ≤ (v.val : Nat) ∧ (v.val : Nat) < 2 * w := by
    have h1 : (v.val : Nat) / w = 1 := v.prop
    have := (Nat.div_eq_iff hw).mp h1
    omega
  dsimp [optCircuit]
  have h_not_lt : ¬ (v.val : Nat) < w := by omega
  rw [if_neg h_not_lt]
  have h_rho := h_total ⟨(v.val : Nat) % w, Nat.mod_lt _ hw⟩
  cases h_eq : ρ ⟨(v.val : Nat) % w, Nat.mod_lt _ hw⟩ with
  | none =>
    rw [h_eq] at h_rho
    contradiction
  | some q =>
    dsimp
    constructor
    · rfl
    · use ⟨q.val, by omega⟩
      simp only [decide_eq_true_eq]
      refine ⟨by omega, hv.1, ?_⟩
      congr
      apply Fin.eq_of_val_eq
      simp [Nat.mod_eq_of_lt q.isLt]

theorem optTrans_isConstantFreeMap (hw : 0 < w) {ρ : Fin w → Option (Fin w)} (h_total : ∀ i, (ρ i).isSome) (β : Fin w → Bool)
    (cert : IncidenceCylinder (optCircuit w hw ρ β)) (hC : CanonicalOrders hw ρ β cert) :
    isConstantFreeMap w (optTrans ρ β) := by
  use 1
  use optCircuit w hw ρ β
  use cert
  use 0
  use (fun _ => true)
  refine ⟨optCircuit_hmvNormal hw ρ β, optCircuit_totalWidth hw ρ β, ?_, optCircuit_constantFreeLayer hw h_total β, ?_⟩
  · exact canonical_tgt_length hw ρ β hC
  · exact canonical_layerTrans hw ρ β hC

theorem dupNextTrans_memCF (hw : 0 < w) (i : Fin w) (hi : i.val + 1 < w) :
    optTrans (dupNextRho i) (beta0 w) ∈ NonCrossingCF w := by
  apply Submonoid.subset_closure
  exact optTrans_isConstantFreeMap hw (β := beta0 w)
    (fun j => by dsimp [dupNextRho]; split_ifs <;> rfl)
    (optCylinder hw (dupNextRho i) (beta0 w) (fun u => dupNextOut hw i hi (srcPos hw (dupNextRho i) (beta0 w) u)) (fun v => incAt hw (dupNextRho i) (beta0 w) (tgtPos hw (dupNextRho i) (beta0 w) v)) (fun u => dupNextOut_nodup hw i hi _) (fun v => incAt_nodup hw (dupNextRho i) (beta0 w) _) (dupNextOut_exact hw i hi) (incAt_exact hw (dupNextRho i) (beta0 w)) (dupNext_word_eq hw i hi))
    (optCylinder_canonical hw (dupNextRho i) (beta0 w) _ _ _ _ _ _ _)

theorem dupPrevTrans_memCF (hw : 0 < w) (i : Fin w) (hi : i.val + 1 < w) :
    optTrans (dupPrevRho i hi) (beta0 w) ∈ NonCrossingCF w := by
  apply Submonoid.subset_closure
  exact optTrans_isConstantFreeMap hw (β := beta0 w)
    (fun j => by dsimp [dupPrevRho]; split_ifs <;> rfl)
    (optCylinder hw (dupPrevRho i hi) (beta0 w) (fun u => dupPrevOut hw i hi (srcPos hw (dupPrevRho i hi) (beta0 w) u)) (fun v => incAt hw (dupPrevRho i hi) (beta0 w) (tgtPos hw (dupPrevRho i hi) (beta0 w) v)) (fun u => dupPrevOut_nodup hw i hi _) (fun v => incAt_nodup hw (dupPrevRho i hi) (beta0 w) _) (dupPrevOut_exact hw i hi) (incAt_exact hw (dupPrevRho i hi) (beta0 w)) (dupPrev_word_eq hw i hi))
    (optCylinder_canonical hw (dupPrevRho i hi) (beta0 w) _ _ _ _ _ _ _)

theorem ascLayer_memCF (hw : 0 < w) (J : Finset (Fin w)) (n : Nat) :
    ascLayer J n ∈ NonCrossingCF w := by
  unfold ascLayer
  split
  · next h =>
    split
    · exact Submonoid.one_mem _
    · next hc =>
      push_neg at hc
      have hn0 : 0 < n := by
        obtain ⟨j, hj⟩ := hc.2
        have h2 : j.val < n := (Finset.mem_filter.mp hj).2
        omega
      have h3 : n - 1 < w := by omega
      have h4 : (⟨n - 1, h3⟩ : Fin w).val + 1 < w := by change n - 1 + 1 < w; omega
      exact dupNextTrans_memCF hw ⟨n - 1, h3⟩ h4
  · exact Submonoid.one_mem _

theorem ascProd_memCF (hw : 0 < w) (J : Finset (Fin w)) (n : Nat) :
    ascProd J n ∈ NonCrossingCF w := by
  induction n with
  | zero => exact Submonoid.one_mem _
  | succ n ih => exact Submonoid.mul_mem _ ih (ascLayer_memCF hw J n)

theorem descLayer_memCF (hw : 0 < w) (m : Nat) :
    descLayer (w := w) m ∈ NonCrossingCF w := by
  unfold descLayer
  split
  · next h =>
    have h1 : m < w := by omega
    have h4 : (⟨m, h1⟩ : Fin w).val + 1 < w := by change m + 1 < w; omega
    exact dupPrevTrans_memCF hw ⟨m, h1⟩ h4
  · exact Submonoid.one_mem _

theorem descProd_memCF (hw : 0 < w) (t n : Nat) :
    descProd (w := w) t n ∈ NonCrossingCF w := by
  induction n with
  | zero => exact Submonoid.one_mem _
  | succ n ih => exact Submonoid.mul_mem _ ih (descLayer_memCF hw (t - (n + 1)))

theorem fillTrans_memCF (hw : 0 < w) (J : Finset (Fin w)) (hJ : J.Nonempty) :
    fillTrans J hJ ∈ NonCrossingCF w :=
  Submonoid.mul_mem _ (ascProd_memCF hw J w) (descProd_memCF hw _ _)

end AllenderOQ3.Internal

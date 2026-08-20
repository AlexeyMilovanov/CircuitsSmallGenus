import AllenderOQ3.Incidence
import AllenderOQ3.Base
import AllenderOQ3.Internal.FaninReducePortSplit
import AllenderOQ3.Internal.N4Structure
import AllenderOQ3.Internal.N4Semantics
import AllenderOQ3.Internal.N4Inc
import AllenderOQ3.Internal.N4Cylinder

set_option autoImplicit false

namespace AllenderOQ3.Internal

/-!
# N4: Incidence-resolved fanin reduction (§7.4)

This file assembles the incidence-resolved cylindrical refinement described in
`docs/INCIDENCE_REFINEMENT.md` from the construction in `AllenderOQ3.Internal.N4Spec`
and its verification in `N4Structure`, `N4Semantics` and `N4Inc`.
-/

-- `PortAugmentedADRValuation` is defined in `AllenderOQ3.Internal.N4Spec`, which the
-- construction of the refined circuit also needs.

variable {n : Nat}

/-- The refined circuit of §3 of `docs/INCIDENCE_REFINEMENT.md`: the strips of the
construction fold the predecessors of every old gate, in the order supplied by the
incidence certificate `cyl`, together with the fresh port of that gate. -/
noncomputable def n4Circuit (c : ADRCircuit n) (F : Nat) (cyl : IncidenceCylinder c) :
    ADRCircuit (n + c.gateCount) :=
  ofSpec (n4Spec c F (n4Inc c cyl))

/-- The old gates inside the refined circuit: its checkpoint nodes. -/
noncomputable def n4Embedding (c : ADRCircuit n) (F : Nat) (cyl : IncidenceCylinder c) :
    Fin c.gateCount → Fin (n4Circuit c F cyl).gateCount :=
  fun g => specEmb (n4Spec c F (n4Inc c cyl)) (N4.old g)

variable (c : ADRCircuit n) (F : Nat) (cyl : IncidenceCylinder c)

theorem n4_hmv_normal (hc : WellFormedADR c) : HMVNormal (n4Circuit c F cyl) :=
  hmvNormal_ofSpec (n4Spec_wellFormed c F _ (n4Inc_layer c cyl hc))
    (fun g _ => n4Spec_fanin c F (n4Inc c cyl) g)

theorem n4_total_width {W : Nat} (hw : TotalWidthAtMost c W) :
    TotalWidthAtMost (n4Circuit c F cyl) ((F + 1) * W) :=
  totalWidth_ofSpec (n4Spec_totalWidth c F (n4Inc c cyl) hw)

theorem n4_gate_count {W : Nat} (hw : TotalWidthAtMost c W) :
    (n4Circuit c F cyl).gateCount ≤ (F + 2) * ((F + 1) * W + 1) * c.gateCount := by
  classical
  have hW : 1 ≤ W := by
    have h := hw (c.layer c.output)
    have hmem : c.output ∈ Finset.univ.filter
        (fun g : Fin c.gateCount => c.layer g = c.layer c.output) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
    have : 1 ≤ (Finset.univ.filter (fun g : Fin c.gateCount =>
        c.layer g = c.layer c.output)).card := Finset.card_pos.mpr ⟨_, hmem⟩
    omega
  have hstep : (F + 2) ≤ (F + 1) * W + 1 := by
    have : (F + 1) * 1 ≤ (F + 1) * W := Nat.mul_le_mul_left _ hW
    omega
  have hcard : (n4Circuit c F cyl).gateCount
      = c.gateCount + c.gateCount * ((F + 1) * (F + 1)) := n4_card_gate c F
  rw [hcard]
  calc c.gateCount + c.gateCount * ((F + 1) * (F + 1))
      = c.gateCount * (1 + (F + 1) * (F + 1)) := by ring
    _ ≤ c.gateCount * ((F + 2) * ((F + 1) * W + 1)) := by
        refine Nat.mul_le_mul_left _ ?_
        calc 1 + (F + 1) * (F + 1) ≤ (F + 2) * (F + 2) := by nlinarith
          _ ≤ (F + 2) * ((F + 1) * W + 1) := Nat.mul_le_mul_left _ hstep
    _ = (F + 2) * ((F + 1) * W + 1) * c.gateCount := by ring

theorem n4_incidence_cylinder (hc : WellFormedADR c) (hf : ∀ g, predecessorCount c g ≤ F) :
    Nonempty (IncidenceCylinder (n4Circuit c F cyl)) :=
  n4_incidence_cylinder_ofSpec c F cyl hc hf

theorem n4_output_eq : (n4Circuit c F cyl).output = n4Embedding c F cyl c.output := rfl

theorem n4_valuation (hc : WellFormedADR c) (hf : ∀ g, predecessorCount c g ≤ F)
    (x : Fin n → Bool) (y : Fin c.gateCount → Bool) (vc : Fin c.gateCount → Bool)
    (vc' : Fin (n4Circuit c F cyl).gateCount → Bool)
    (h_val : PortAugmentedADRValuation c x y vc)
    (h_val' : ADRValuation (n4Circuit c F cyl) (Fin.addCases x y) vc') :
    ∀ g, vc' (n4Embedding c F cyl g) = vc g := by
  have hspec : SpecValuation (n4Spec c F (n4Inc c cyl)) (Fin.addCases x y)
      (fun g => vc' (specEmb (n4Spec c F (n4Inc c cyl)) g)) :=
    (adrValuation_ofSpec_iff _ _ _).mp h_val'
  have hlen : ∀ g, (n4Inc c cyl g).length ≤ F := by
    intro g
    rw [n4Inc_length c cyl hc g]
    exact hf g
  exact n4_val_old c F (n4Inc c cyl) hspec h_val (n4Inc_mem_iff c cyl hc)
    hlen (n4Inc_layer c cyl hc)

theorem incidenceRefinement {n : Nat} (c : ADRCircuit n)
    (W F : Nat) (hc : WellFormedADR c)
    (hw : TotalWidthAtMost c W)
    (hf : ∀ g, predecessorCount c g ≤ F)
    (h_cyl : Nonempty (IncidenceCylinder c)) :
    ∃ (c' : ADRCircuit (n + c.gateCount)) (emb : Fin c.gateCount → Fin c'.gateCount),
      HMVNormal c' ∧
      TotalWidthAtMost c' ((F + 1) * W) ∧
      c'.gateCount ≤ (F + 2) * ((F + 1) * W + 1) * c.gateCount ∧
      Nonempty (IncidenceCylinder c') ∧
      c'.output = emb c.output ∧
      ∀ (x : Fin n → Bool) (y : Fin c.gateCount → Bool)
        (vc : Fin c.gateCount → Bool) (vc' : Fin c'.gateCount → Bool),
        PortAugmentedADRValuation c x y vc →
        ADRValuation c' (Fin.addCases x y) vc' →
        ∀ g, vc' (emb g) = vc g := by
  obtain ⟨cyl⟩ := h_cyl
  refine ⟨n4Circuit c F cyl, n4Embedding c F cyl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact n4_hmv_normal c F cyl hc
  · exact n4_total_width c F cyl hw
  · exact n4_gate_count c F cyl hw
  · exact n4_incidence_cylinder c F cyl hc hf
  · exact n4_output_eq c F cyl
  · exact fun x y vc vc' => n4_valuation c F cyl hc hf x y vc vc'

end AllenderOQ3.Internal

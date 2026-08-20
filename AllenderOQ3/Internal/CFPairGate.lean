import AllenderOQ3.Base
import AllenderOQ3.Internal.OptCircuit
import AllenderOQ3.Internal.OptCircuitCert
import AllenderOQ3.Internal.OptCircuitInstances
import AllenderOQ3.Internal.ConstantFreeLayers

namespace AllenderOQ3.Internal

variable {w : Nat} (hw : 0 < w)

/-- A two-layer circuit where layer 1 has arbitrary predefined computation kinds
and predecessor lists. Used to build elementary fan-in-2 constant-free gates. -/
def pairCircuit (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1) : ADRCircuit 1 where
  gateCount := 2 * w
  output := ⟨0, by omega⟩
  kind := fun g =>
    if g.val < w then ADRGate.literal ⟨0, Nat.zero_lt_one⟩ false
    else tgtKind ⟨g.val % w, Nat.mod_lt _ hw⟩
  layer := fun g => g.val / w
  edge := fun u v => decide (u.val < w ∧ w ≤ v.val ∧
    ⟨u.val % w, Nat.mod_lt _ hw⟩ ∈ preds ⟨v.val % w, Nat.mod_lt _ hw⟩)

theorem pairCircuit_edge_iff (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1)
    {u v : Fin (pairCircuit hw preds tgtKind).gateCount} :
    (pairCircuit hw preds tgtKind).edge u v = true ↔
      u.val < w ∧ w ≤ v.val ∧ ⟨u.val % w, Nat.mod_lt _ hw⟩ ∈ preds ⟨v.val % w, Nat.mod_lt _ hw⟩ :=
        by
  dsimp [pairCircuit]
  exact decide_eq_true_iff

theorem pairCircuit_layer_lt (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1)
    (g : Fin (pairCircuit hw preds tgtKind).gateCount) :
    (pairCircuit hw preds tgtKind).layer g < 2 := by
  have h1 : (pairCircuit hw preds tgtKind).layer g = g.val / w := rfl
  rw [h1]
  by_contra hcon
  push_neg at hcon
  have h3 : 2 * w ≤ (g.val / w) * w := Nat.mul_le_mul_right w hcon
  have h4 : (g.val / w) * w ≤ g.val := Nat.div_mul_le_self g.val w
  have h5 : g.val < 2 * w := g.isLt
  omega

theorem pairCircuit_wellFormed (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1)
    (h_comp : ∀ p, (tgtKind p).isComputation) :
    WellFormedADR (pairCircuit hw preds tgtKind) := by
  constructor
  · intro u v h
    obtain ⟨hu, hv, -⟩ := (pairCircuit_edge_iff hw preds tgtKind).mp h
    have hv2 : v.val < 2 * w := v.isLt
    have h1 : (pairCircuit hw preds tgtKind).layer u = 0 := Nat.div_eq_of_lt hu
    have h2 : (pairCircuit hw preds tgtKind).layer v = 1 := by
      change v.val / w = 1
      have hd : v.val / w < 2 := by
        by_contra hcon
        push_neg at hcon
        have h3 : 2 * w ≤ (v.val / w) * w := Nat.mul_le_mul_right w hcon
        have h4 : (v.val / w) * w ≤ v.val := Nat.div_mul_le_self v.val w
        omega
      have hd2 : 1 ≤ v.val / w := (Nat.one_le_div_iff hw).mpr hv
      omega
    rw [h1, h2]
  · intro g hg h
    cases hval : (pairCircuit hw preds tgtKind).edge h g with
    | false => rfl
    | true =>
      exfalso
      obtain ⟨-, hg2, -⟩ := (pairCircuit_edge_iff hw preds tgtKind).mp hval
      obtain ⟨i, b, hkind⟩ := hg
      by_cases hglt : g.val < w
      · omega
      · have hk2 : (pairCircuit hw preds tgtKind).kind g = tgtKind ⟨g.val % w, Nat.mod_lt _ hw⟩ :=
          by
          change (if g.val < w then _ else _) = _
          rw [if_neg hglt]
        rw [hkind] at hk2
        have hc := h_comp ⟨g.val % w, Nat.mod_lt _ hw⟩
        rw [← hk2] at hc
        exact Bool.noConfusion hc

theorem pairCircuit_hmvNormal (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1)
    (h_comp : ∀ p, (tgtKind p).isComputation)
    (h_preds_len : ∀ p, (preds p).length ≤ 2) :
    HMVNormal (pairCircuit hw preds tgtKind) := by
  refine ⟨pairCircuit_wellFormed hw preds tgtKind h_comp, ?_⟩
  intro g hg
  classical
  have hcard : (Finset.univ.filter
      (fun h : Fin (pairCircuit hw preds tgtKind).gateCount =>
        (pairCircuit hw preds tgtKind).edge h g = true)).card ≤ 2 := by
    have hsub : (Finset.univ.filter
        (fun h : Fin (pairCircuit hw preds tgtKind).gateCount =>
          (pairCircuit hw preds tgtKind).edge h g = true)).image
        (fun h => (⟨h.val % w, Nat.mod_lt _ hw⟩ : Fin w)) ⊆
        (preds ⟨g.val % w, Nat.mod_lt _ hw⟩).toFinset := by
      intro u hu
      obtain ⟨h, hmem, heq⟩ := Finset.mem_image.mp hu
      obtain ⟨-, ha2⟩ := Finset.mem_filter.mp hmem
      obtain ⟨halt, -, hρ⟩ := (pairCircuit_edge_iff hw preds tgtKind).mp ha2
      rw [← heq]
      exact List.mem_toFinset.mpr hρ
    have hinj : Set.InjOn
        (fun h : Fin (pairCircuit hw preds tgtKind).gateCount =>
          (⟨h.val % w, Nat.mod_lt _ hw⟩ : Fin w))
        ↑(Finset.univ.filter (fun h : Fin (pairCircuit hw preds tgtKind).gateCount =>
          (pairCircuit hw preds tgtKind).edge h g = true)) := by
      intro a ha b hb hab
      obtain ⟨-, ha2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp ha)
      obtain ⟨-, hb2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hb)
      obtain ⟨halt, -, -⟩ := (pairCircuit_edge_iff hw preds tgtKind).mp ha2
      obtain ⟨hblt, -, -⟩ := (pairCircuit_edge_iff hw preds tgtKind).mp hb2
      have hmod : a.val % w = b.val % w := congrArg Fin.val hab
      have ha' : a.val = w * (a.val / w) + a.val % w := (Nat.div_add_mod a.val w).symm
      have hb' : b.val = w * (b.val / w) + b.val % w := (Nat.div_add_mod b.val w).symm
      have ha_div : a.val / w = 0 := Nat.div_eq_of_lt halt
      have hb_div : b.val / w = 0 := Nat.div_eq_of_lt hblt
      rw [ha_div] at ha'
      rw [hb_div] at hb'
      apply Fin.ext
      omega
    have hcard1 := Finset.card_image_of_injOn hinj
    have hcard2 := Finset.card_le_card hsub
    have hcard3 : (preds ⟨g.val % w, Nat.mod_lt _ hw⟩).toFinset.card ≤ 2 := by
      calc (preds ⟨g.val % w, Nat.mod_lt _ hw⟩).toFinset.card
        ≤ (preds ⟨g.val % w, Nat.mod_lt _ hw⟩).length := List.toFinset_card_le _
        _ ≤ 2 := h_preds_len _
    omega
  exact hcard

theorem pairCircuit_totalWidth (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1) :
    TotalWidthAtMost (pairCircuit hw preds tgtKind) w := by
  intro ell
  by_cases hell : ell ≤ 1
  · have hinj : Set.InjOn
        (fun g : Fin (pairCircuit hw preds tgtKind).gateCount =>
          (⟨g.val % w, Nat.mod_lt _ hw⟩ : Fin w))
        ↑(Finset.univ.filter (fun g : Fin (pairCircuit hw preds tgtKind).gateCount =>
          (pairCircuit hw preds tgtKind).layer g = ell)) := by
      intro a ha b hb hab
      have hla : a.val / w = ell :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp ha)).2
      have hlb : b.val / w = ell :=
        (Finset.mem_filter.mp (Finset.mem_coe.mp hb)).2
      have hmod : a.val % w = b.val % w := congrArg Fin.val hab
      have ha' : a.val = w * (a.val / w) + a.val % w := (Nat.div_add_mod a.val w).symm
      have hb' : b.val = w * (b.val / w) + b.val % w := (Nat.div_add_mod b.val w).symm
      rw [hla] at ha'
      rw [hlb] at hb'
      apply Fin.ext
      omega
    have hcard := Finset.card_le_card_of_injOn
      (fun g : Fin (pairCircuit hw preds tgtKind).gateCount =>
        (⟨g.val % w, Nat.mod_lt _ hw⟩ : Fin w))
      (fun a _ => Finset.mem_univ _) hinj
    calc (Finset.univ.filter (fun g : Fin (pairCircuit hw preds tgtKind).gateCount =>
            (pairCircuit hw preds tgtKind).layer g = ell)).card
        ≤ (Finset.univ : Finset (Fin w)).card := hcard
      _ = w := by simp
  · have hempty : (Finset.univ.filter
        (fun g : Fin (pairCircuit hw preds tgtKind).gateCount =>
          (pairCircuit hw preds tgtKind).layer g = ell)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro g _
      have h_lt := pairCircuit_layer_lt hw preds tgtKind g
      omega
    rw [hempty]
    simp

theorem pairCircuit_constantFreeLayer (preds : Fin w → List (Fin w)) (tgtKind : Fin w → ADRGate 1)
    (h_comp : ∀ p, (tgtKind p).isComputation) (h_preds_nonempty : ∀ p, (preds p).length ≠ 0) :
    ConstantFreeLayer (pairCircuit hw preds tgtKind) 0 := by
  intro v
  have hv : w ≤ (v.val : Nat) ∧ (v.val : Nat) < 2 * w := by
    have h1 : (v.val : Nat) / w = 1 := v.prop
    have := (Nat.div_eq_iff hw).mp h1
    omega
  dsimp [pairCircuit]
  have h_not_lt : ¬ (v.val : Nat) < w := by omega
  rw [if_neg h_not_lt]
  have h_comp_v := h_comp ⟨(v.val : Nat) % w, Nat.mod_lt _ hw⟩
  constructor
  · exact h_comp_v
  · have h_len := h_preds_nonempty ⟨(v.val : Nat) % w, Nat.mod_lt _ hw⟩
    have h_pos : 0 < (preds ⟨(v.val : Nat) % w, Nat.mod_lt _ hw⟩).length := by omega
    obtain ⟨u, hu⟩ := List.exists_mem_of_length_pos h_pos
    have h_u_lt : u.val < 2 * w := by
      have : u.val < w := u.isLt
      omega
    use ⟨u.val, h_u_lt⟩
    simp only [decide_eq_true_eq]
    refine ⟨u.isLt, hv.1, ?_⟩
    have hu1 : (⟨u.val % w, Nat.mod_lt _ hw⟩ : Fin w) = u := Fin.eq_of_val_eq
      (Nat.mod_eq_of_lt u.isLt)
    rw [hu1]
    exact hu

end AllenderOQ3.Internal

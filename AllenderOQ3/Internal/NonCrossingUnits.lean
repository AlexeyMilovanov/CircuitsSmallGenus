import AllenderOQ3.Internal.NonCrossingDefs
import AllenderOQ3.Internal.BoolCube

set_option autoImplicit false

/-!
# Toolkit for the unit group of the non-crossing submonoid

Monotonicity of layer transitions, positional indexing of the certificate's
layer listings, and the fact that a coordinate-permutation layer is a perfect
matching.  These feed `NonCrossingShift` and `NonCrossingCyclic`.
-/

namespace AllenderOQ3.Internal

variable {n w : Nat} {c : ADRCircuit n} {cert : IncidenceCylinder c}

theorem layerTransMap_monotone (x : Fin n → Bool) (ell : Nat) :
    Monotone (layerTransMap (w := w) c cert x ell) := by
  intro s t hst j
  simp only [layerTransMap]
  split
  · rename_i h
    split
    · exact le_rfl
    · refine Bool.le_iff_imp.mpr ?_
      intro hall
      rw [decide_eq_true_eq] at hall ⊢
      intro u hu
      have h1 := hall u hu
      revert h1
      split
      · split
        · exact hst _
        · exact id
      · exact id
    · refine Bool.le_iff_imp.mpr ?_
      intro hex
      rw [decide_eq_true_eq] at hex ⊢
      obtain ⟨u, hu, h1⟩ := hex
      refine ⟨u, hu, ?_⟩
      revert h1
      split
      · split
        · exact hst _
        · exact id
      · exact id
  · exact le_rfl

/-- The submonoid of monotone configuration maps. -/
def monoSubmonoid (w : Nat) : Submonoid (TransMonoid w) where
  carrier := {g | Monotone (MulOpposite.unop g)}
  mul_mem' := by
    intro a b ha hb
    exact Monotone.comp (f := MulOpposite.unop a) (g := MulOpposite.unop b) hb ha
  one_mem' := monotone_id

theorem monotone_of_mem_nonCrossing {g : TransMonoid w} (hg : g ∈ NonCrossing w) :
    Monotone (MulOpposite.unop g) := by
  have hle : NonCrossing w ≤ monoSubmonoid w := by
    refine Submonoid.closure_le.mpr ?_
    rintro f ⟨n', c', cert', ell', x', -, -, rfl⟩
    exact layerTransMap_monotone (c := c') (cert := cert') x' ell'
  exact hle hg

/-! ## Layer indexing -/

theorem layerEntries_get_index (ell : Nat) (v : LayerVertex c ell) :
    (cert.layerOrder ell).entries.get ((FullLayerIndexing c cert ell) v) = v := by
  conv_rhs => rw [← (FullLayerIndexing c cert ell).symm_apply_apply v]
  rfl

theorem layerEntries_length_eq_card (ell : Nat) :
    (cert.layerOrder ell).entries.length = Fintype.card (LayerVertex c ell) := by
  have h := Fintype.card_congr (FullLayerIndexing c cert ell)
  rw [Fintype.card_fin] at h
  exact h.symm

theorem layerEntries_length_le (hW : TotalWidthAtMost c w) (ell : Nat) :
    (cert.layerOrder ell).entries.length ≤ w := by
  classical
  rw [layerEntries_length_eq_card]
  have hcard : Fintype.card (LayerVertex c ell)
      = (Finset.univ.filter fun g : Fin c.gateCount => c.layer g = ell).card :=
    Fintype.card_subtype _
  rw [hcard]
  exact hW ell

/-! ## Two list lemmas -/

/-- A nodup list whose members are exactly `z` is `[z]`. -/
theorem List.eq_singleton_of_mem_iff {alpha : Type} {l : List alpha} {z : alpha}
    (hnd : l.Nodup) (hmem : ∀ e, e ∈ l ↔ e = z) : l = [z] := by
  cases l with
  | nil => exact absurd ((hmem z).mpr rfl) (by simp)
  | cons a t =>
    have ha : a = z := (hmem a).mp (by simp)
    cases t with
    | nil => rw [ha]
    | cons b t' =>
      have hb : b = z := (hmem b).mp (by simp)
      exact absurd hnd (by simp [ha, hb])

/-- If the `f`-word and the `g`-word over `Fin w` are cyclic rotations of one
another, then `g` is `f` shifted by a fixed amount. -/
theorem exists_shift_of_cyclicRotation {alpha : Type} {w : Nat} (f g : Fin w → alpha)
    (h : CyclicRotation ((List.finRange w).map f) ((List.finRange w).map g)) :
    ∃ m : Nat, ∀ j : Fin w, g j = f ⟨(j.val + m) % w, Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩ := by
  obtain ⟨p, q, hpq, hqp⟩ := h
  have hsum : p.length + q.length = w := by
    have := congrArg List.length hpq
    simpa using this.symm
  have hG : ∀ (i : Nat) (hi : i < w), g ⟨i, hi⟩ = (q ++ p)[i]'(by simp; omega) := by
    intro i hi
    have h1 : ((List.finRange w).map g)[i]'(by simp [hi]) = (q ++ p)[i]'(by simp; omega) :=
      List.getElem_of_eq hqp _
    simpa using h1
  have hF : ∀ (i : Nat) (hi : i < w), f ⟨i, hi⟩ = (p ++ q)[i]'(by simp; omega) := by
    intro i hi
    have h1 : ((List.finRange w).map f)[i]'(by simp [hi]) = (p ++ q)[i]'(by simp; omega) :=
      List.getElem_of_eq hpq _
    simpa using h1
  refine ⟨p.length, fun j => ?_⟩
  rw [show j = (⟨j.val, j.isLt⟩ : Fin w) from rfl, hG j.val j.isLt,
    hF _ (Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt))]
  by_cases hcase : j.val < q.length
  · have h1 : (q ++ p)[j.val]'(by simp; omega) = q[j.val]'hcase :=
      List.getElem_append_left hcase
    have hlt : j.val + p.length < w := by omega
    have h2 : (j.val + p.length) % w = j.val + p.length := Nat.mod_eq_of_lt hlt
    have h3 : (p ++ q)[j.val + p.length]'(by simp; omega) = q[j.val]'hcase := by
      rw [List.getElem_append_right (by omega)]
      congr 1
      omega
    rw [h1]
    simp only [h2]
    rw [h3]
  · push_neg at hcase
    have h1 : (q ++ p)[j.val]'(by simp; omega) = p[j.val - q.length]'(by omega) :=
      List.getElem_append_right hcase
    have hlt : j.val - q.length < w := by omega
    have h2 : (j.val + p.length) % w = j.val - q.length := by
      have hx : j.val + p.length = w + (j.val - q.length) := by omega
      rw [hx, Nat.add_mod_left, Nat.mod_eq_of_lt hlt]
    have h3 : (p ++ q)[j.val - q.length]'(by simp; omega) = p[j.val - q.length]'(by omega) :=
      List.getElem_append_left (by omega)
    rw [h1]
    simp only [h2]
    rw [h3]

/-! ## A coordinate-permutation layer is a perfect matching -/

section Matching

variable {x : Fin n → Bool} {ell : Nat} {sigma : Equiv.Perm (Fin w)}

theorem layerTransMap_apply_of_not_lt (s : Config w) (j : Fin w)
    (h : ¬ j.val < (cert.layerOrder (ell + 1)).entries.length) :
    layerTransMap (w := w) c cert x ell s j = false := by
  simp only [layerTransMap, dif_neg h]

/-- If a layer transition permutes coordinates, the upper layer is full. -/
theorem target_layer_length (hW : TotalWidthAtMost c w)
    (hsig : ∀ s j, layerTransMap (w := w) c cert x ell s j = s (sigma j)) :
    (cert.layerOrder (ell + 1)).entries.length = w := by
  refine le_antisymm (layerEntries_length_le hW _) ?_
  by_contra hcon
  push_neg at hcon
  have hlt : (cert.layerOrder (ell + 1)).entries.length < w := hcon
  set j : Fin w := ⟨(cert.layerOrder (ell + 1)).entries.length, hlt⟩ with hj
  have h1 : layerTransMap (w := w) c cert x ell (fun _ => true) j = false :=
    layerTransMap_apply_of_not_lt (c := c) (cert := cert) (x := x) (ell := ell) _ j
      (by simp [hj])
  have h2 := hsig (fun _ => true) j
  rw [h1] at h2
  exact absurd h2.symm (by simp)

/-- The vertex of layer `ell` sitting at position `j` of a full layer listing. -/
noncomputable def vtxAt (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
    (h : (cert.layerOrder ell).entries.length = w) (j : Fin w) : LayerVertex c ell :=
  (FullLayerIndexing c cert ell).symm ⟨j.val, by rw [h]; exact j.isLt⟩

/-- The position of a vertex of layer `ell` in a full layer listing. -/
noncomputable def idxOfVtx (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
    (h : (cert.layerOrder ell).entries.length ≤ w) (v : LayerVertex c ell) : Fin w :=
  ⟨((FullLayerIndexing c cert ell) v).val,
    lt_of_lt_of_le ((FullLayerIndexing c cert ell) v).isLt h⟩

theorem vtxAt_idxOfVtx (ell : Nat) (h : (cert.layerOrder ell).entries.length = w)
    (v : LayerVertex c ell) : vtxAt c cert ell h (idxOfVtx c cert ell h.le v) = v := by
  unfold vtxAt idxOfVtx
  rw [Equiv.symm_apply_eq]

theorem idxOfVtx_injective (ell : Nat) (h : (cert.layerOrder ell).entries.length ≤ w) :
    Function.Injective (idxOfVtx c cert ell h) := by
  intro a b hab
  have h4 : (idxOfVtx c cert ell h a).val = (idxOfVtx c cert ell h b).val :=
    congrArg Fin.val hab
  have h3 : (FullLayerIndexing c cert ell) a = (FullLayerIndexing c cert ell) b := by
    apply Fin.ext
    exact h4
  exact (FullLayerIndexing c cert ell).injective h3

theorem idxOfVtx_vtxAt (ell : Nat) (h : (cert.layerOrder ell).entries.length = w)
    (j : Fin w) : idxOfVtx c cert ell h.le (vtxAt c cert ell h j) = j := by
  apply Fin.ext
  simp only [vtxAt, idxOfVtx, Equiv.apply_symm_apply]

theorem layerTransMap_literal (h2 : (cert.layerOrder (ell + 1)).entries.length = w)
    (s : Config w) (j : Fin w) {i : Fin n} {b : Bool}
    (hk : c.kind (vtxAt c cert (ell + 1) h2 j).val = ADRGate.literal i b) :
    layerTransMap (w := w) c cert x ell s j = (if b then !(x i) else x i) := by
  have hlt : j.val < (cert.layerOrder (ell + 1)).entries.length := by rw [h2]; exact j.isLt
  simp only [layerTransMap, dif_pos hlt]
  have hkv : c.kind (((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hlt⟩) :
      LayerVertex c (ell + 1)).val = ADRGate.literal i b := hk
  rw [hkv]

theorem layerTransMap_and (h1 : (cert.layerOrder ell).entries.length ≤ w)
    (h2 : (cert.layerOrder (ell + 1)).entries.length = w) (hWF : WellFormedADR c)
    (s : Config w) (j : Fin w)
    (hk : c.kind (vtxAt c cert (ell + 1) h2 j).val = ADRGate.andGate) :
    (layerTransMap (w := w) c cert x ell s j = true) ↔
      ∀ u : LayerVertex c ell, c.edge u.val (vtxAt c cert (ell + 1) h2 j).val = true →
        s (idxOfVtx c cert ell h1 u) = true := by
  have hlt : j.val < (cert.layerOrder (ell + 1)).entries.length := by rw [h2]; exact j.isLt
  simp only [layerTransMap, dif_pos hlt]
  have hkv : c.kind (((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hlt⟩) :
      LayerVertex c (ell + 1)).val = ADRGate.andGate := hk
  rw [hkv, decide_eq_true_eq]
  have hlayer : ∀ u : Fin c.gateCount,
      c.edge u (vtxAt c cert (ell + 1) h2 j).val = true → c.layer u = ell := by
    intro u hedge
    have h3 := hWF.1 u _ hedge
    have h4 : c.layer (vtxAt c cert (ell + 1) h2 j).val = ell + 1 :=
      (vtxAt c cert (ell + 1) h2 j).2
    omega
  constructor
  · intro hall u hedge
    have h := hall u.val hedge
    have hi : ((FullLayerIndexing c cert ell) ⟨u.val, u.2⟩).val < w := by
      exact lt_of_lt_of_le ((FullLayerIndexing c cert ell) ⟨u.val, u.2⟩).isLt h1
    rw [dif_pos u.2, dif_pos hi] at h
    exact h
  · intro hall u hedge
    have hu : c.layer u = ell := hlayer u hedge
    have hi : ((FullLayerIndexing c cert ell) ⟨u, hu⟩).val < w := by
      exact lt_of_lt_of_le ((FullLayerIndexing c cert ell) ⟨u, hu⟩).isLt h1
    rw [dif_pos hu, dif_pos hi]
    exact hall ⟨u, hu⟩ hedge

theorem layerTransMap_or (h1 : (cert.layerOrder ell).entries.length ≤ w)
    (h2 : (cert.layerOrder (ell + 1)).entries.length = w) (hWF : WellFormedADR c)
    (s : Config w) (j : Fin w)
    (hk : c.kind (vtxAt c cert (ell + 1) h2 j).val = ADRGate.orGate) :
    (layerTransMap (w := w) c cert x ell s j = true) ↔
      ∃ u : LayerVertex c ell, c.edge u.val (vtxAt c cert (ell + 1) h2 j).val = true ∧
        s (idxOfVtx c cert ell h1 u) = true := by
  have hlt : j.val < (cert.layerOrder (ell + 1)).entries.length := by rw [h2]; exact j.isLt
  simp only [layerTransMap, dif_pos hlt]
  have hkv : c.kind (((FullLayerIndexing c cert (ell + 1)).symm ⟨j.val, hlt⟩) :
      LayerVertex c (ell + 1)).val = ADRGate.orGate := hk
  rw [hkv, decide_eq_true_eq]
  have hlayer : ∀ u : Fin c.gateCount,
      c.edge u (vtxAt c cert (ell + 1) h2 j).val = true → c.layer u = ell := by
    intro u hedge
    have h3 := hWF.1 u _ hedge
    have h4 : c.layer (vtxAt c cert (ell + 1) h2 j).val = ell + 1 :=
      (vtxAt c cert (ell + 1) h2 j).2
    omega
  constructor
  · rintro ⟨u, hedge, hval⟩
    have hu : c.layer u = ell := hlayer u hedge
    have hi : ((FullLayerIndexing c cert ell) ⟨u, hu⟩).val < w := by
      exact lt_of_lt_of_le ((FullLayerIndexing c cert ell) ⟨u, hu⟩).isLt h1
    rw [dif_pos hu, dif_pos hi] at hval
    exact ⟨⟨u, hu⟩, hedge, hval⟩
  · rintro ⟨u, hedge, hval⟩
    refine ⟨u.val, hedge, ?_⟩
    have hi : ((FullLayerIndexing c cert ell) ⟨u.val, u.2⟩).val < w := by
      exact lt_of_lt_of_le ((FullLayerIndexing c cert ell) ⟨u.val, u.2⟩).isLt h1
    rw [dif_pos u.2, dif_pos hi]
    exact hval

section CoordPerm

variable (hWF : WellFormedADR c)
  (h1 : (cert.layerOrder ell).entries.length ≤ w)
  (h2 : (cert.layerOrder (ell + 1)).entries.length = w)
  (hsig : ∀ s j, layerTransMap (w := w) c cert x ell s j = s (sigma j))

include hsig in
theorem layerTransMap_top (j : Fin w) :
    layerTransMap (w := w) c cert x ell (unitVec (sigma j)) j = true := by
  rw [hsig]
  simp [unitVec]

include hsig in
theorem layerTransMap_bot (j : Fin w) :
    layerTransMap (w := w) c cert x ell (fun k => decide (k ≠ sigma j)) j = false := by
  rw [hsig]
  simp

include hsig in
/-- A gate that reads a coordinate is not a constant. -/
theorem kind_ne_literal (j : Fin w) (i : Fin n) (b : Bool) :
    c.kind (vtxAt c cert (ell + 1) h2 j).val ≠ ADRGate.literal i b := by
  intro hkind
  have hval := layerTransMap_literal (x := x) (ell := ell) h2 (unitVec (sigma j)) j hkind
  have hval' := layerTransMap_literal (x := x) (ell := ell)
    h2 (fun k => decide (k ≠ sigma j)) j hkind
  rw [layerTransMap_top hsig j] at hval
  rw [layerTransMap_bot hsig j] at hval'
  rw [← hval] at hval'
  exact absurd hval' (by simp)

include hWF hsig in
/-- Every predecessor of the vertex at position `j` sits at position `sigma j`. -/
theorem pred_idx_eq_of_coord_perm (j : Fin w) (u : LayerVertex c ell)
    (hedge : c.edge u.val (vtxAt c cert (ell + 1) h2 j).val = true) :
    idxOfVtx c cert ell h1 u = sigma j := by
  classical
  cases hkind : c.kind (vtxAt c cert (ell + 1) h2 j).val with
  | literal i b => exact absurd hkind (kind_ne_literal h2 hsig j i b)
  | andGate =>
      have hu := (layerTransMap_and (x := x) h1 h2 hWF (unitVec (sigma j)) j hkind).mp
        (layerTransMap_top hsig j) u hedge
      simpa [unitVec] using hu
  | orGate =>
      by_contra hne
      refine absurd (layerTransMap_bot hsig j) ?_
      rw [(layerTransMap_or (x := x) h1 h2 hWF (fun k => decide (k ≠ sigma j)) j hkind).mpr
        ⟨u, hedge, by simpa using hne⟩]
      simp

include hWF hsig in
/-- The vertex at position `j` does have a predecessor, at position `sigma j`. -/
theorem exists_pred_of_coord_perm (j : Fin w) :
    ∃ u : LayerVertex c ell, c.edge u.val (vtxAt c cert (ell + 1) h2 j).val = true ∧
      idxOfVtx c cert ell h1 u = sigma j := by
  classical
  cases hkind : c.kind (vtxAt c cert (ell + 1) h2 j).val with
  | literal i b => exact absurd hkind (kind_ne_literal h2 hsig j i b)
  | andGate =>
      by_contra hno
      push_neg at hno
      refine absurd (layerTransMap_bot hsig j) ?_
      rw [(layerTransMap_and (x := x) h1 h2 hWF (fun k => decide (k ≠ sigma j)) j hkind).mpr
        (fun u hedge => by simpa using hno u hedge)]
      simp
  | orGate =>
      obtain ⟨u, hedge, hval⟩ :=
        (layerTransMap_or (x := x) h1 h2 hWF (unitVec (sigma j)) j hkind).mp
          (layerTransMap_top hsig j)
      exact ⟨u, hedge, by simpa [unitVec] using hval⟩

include hWF hsig in
/-- **A coordinate-permutation layer is a perfect matching.**  The vertex at
position `j` of the upper layer has exactly one predecessor: the vertex at
position `sigma j` of the lower layer. -/
theorem edge_iff_of_coord_perm (j : Fin w) (u : LayerVertex c ell) :
    c.edge u.val (vtxAt c cert (ell + 1) h2 j).val = true ↔
      idxOfVtx c cert ell h1 u = sigma j := by
  refine ⟨pred_idx_eq_of_coord_perm hWF h1 h2 hsig j u, fun hidx => ?_⟩
  obtain ⟨u0, hedge0, hidx0⟩ := exists_pred_of_coord_perm hWF h1 h2 hsig j
  have hueq : u = u0 := idxOfVtx_injective ell h1 (hidx.trans hidx0.symm)
  rw [hueq]
  exact hedge0

include hWF h1 h2 hsig in
/-- Both layers of a coordinate-permutation transition are full. -/
theorem source_layer_length (hW : TotalWidthAtMost c w) :
    (cert.layerOrder ell).entries.length = w := by
  refine le_antisymm (layerEntries_length_le hW _) ?_
  by_contra hcon
  push_neg at hcon
  have hpos : 0 < w := by omega
  set k : Fin w := ⟨w - 1, by omega⟩ with hk
  obtain ⟨u, -, hidx⟩ := exists_pred_of_coord_perm hWF h1 h2 hsig (sigma.symm k)
  rw [Equiv.apply_symm_apply] at hidx
  have hlt : ((FullLayerIndexing c cert ell) u).val
      < (cert.layerOrder ell).entries.length := ((FullLayerIndexing c cert ell) u).isLt
  have hval : ((FullLayerIndexing c cert ell) u).val = w - 1 := congrArg Fin.val hidx
  omega

end CoordPerm

end Matching

end AllenderOQ3.Internal

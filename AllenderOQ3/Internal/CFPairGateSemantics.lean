import AllenderOQ3.Internal.CFPairGateCert
import AllenderOQ3.Internal.ComponentGateFacts
import AllenderOQ3.Internal.FullLayerIndexing

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat} (hw : 0 < w)
variable (tgtKind : Fin w → ADRGate 1)
variable (i : Fin w) (hi : i.val + 1 < w)

/-- The inverse of `FullLayerIndexing` reads off the layer-order entry. -/
theorem full_symm_get {n : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
    (k : Fin (cert.layerOrder ell).entries.length) :
    (FullLayerIndexing c cert ell).symm k = (cert.layerOrder ell).entries.get k := by
  rfl

/-- The target layer order of the staircase certificate has width `w`. -/
theorem pairCylinder_len_one :
    ((pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi)).layerOrder 1).entries.length = w := by
  show ((pair_tgtListing hw (staircasePreds i hi) tgtKind).entries).length = w
  simp [pair_tgtListing]

/-- The source layer order of the staircase certificate has width `w`. -/
theorem pairCylinder_len_zero :
    ((pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi)).layerOrder 0).entries.length = w := by
  show ((pair_srcListing hw (staircasePreds i hi) tgtKind).entries).length = w
  simp [pair_srcListing]

/-- The vertex at target position `p` in the staircase certificate is `pair_tgtVertex p`. -/
theorem pair_tgt_symm (p : Fin w)
    (hp : p.val < ((pairCylinder hw (staircasePreds i hi) tgtKind
      (adjPairCylinder hw tgtKind i hi)).layerOrder 1).entries.length) :
    (FullLayerIndexing (pairCircuit hw (staircasePreds i hi) tgtKind)
        (pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi)) 1).symm
      ⟨p.val, hp⟩
      = pair_tgtVertex hw (staircasePreds i hi) tgtKind p := by
  rw [full_symm_get]
  show ((List.finRange w).map (pair_tgtVertex hw (staircasePreds i hi) tgtKind)).get ⟨p.val, _⟩
    = pair_tgtVertex hw (staircasePreds i hi) tgtKind p
  rw [List.get_eq_getElem, List.getElem_map, List.getElem_finRange]
  exact congrArg (pair_tgtVertex hw (staircasePreds i hi) tgtKind) (Fin.ext rfl)

/-- The kind of the gate at target position `p` is `tgtKind p`. -/
theorem pair_kind_tgt (p : Fin w) :
    (pairCircuit hw (staircasePreds i hi) tgtKind).kind
        (pair_tgtVertex hw (staircasePreds i hi) tgtKind p).val
      = tgtKind p := by
  show (if (w + p.val) < w then _ else
      tgtKind ⟨(w + p.val) % w, Nat.mod_lt _ hw⟩) = tgtKind p
  rw [if_neg (by omega)]
  congr 1
  apply Fin.ext
  show (w + p.val) % w = p.val
  rw [Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]

theorem vertCoord_eval (u : Fin w) :
    vertCoord (pairCircuit hw (staircasePreds i hi) tgtKind)
      (pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi))
      (pairCircuit_totalWidth hw (staircasePreds i hi) tgtKind)
      (pair_srcVertex hw (staircasePreds i hi) tgtKind u) = u := by
  have hext : (vertCoord (pairCircuit hw (staircasePreds i hi) tgtKind) (pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi)) (pairCircuit_totalWidth hw (staircasePreds i hi) tgtKind) (pair_srcVertex hw (staircasePreds i hi) tgtKind u)).val = u.val := by
    dsimp [vertCoord, FullLayerIndexing, subtypeUnivEquiv, Equiv.trans]
    let H := (pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi)).layerOrder 0
    have h_len : u.val < H.entries.length := by
      dsimp [H, pairCylinder, pairOrders, pair_srcListing]
      simp
    have heq : H.entries.get ⟨u.val, h_len⟩ = pair_srcVertex hw (staircasePreds i hi) tgtKind u := by
      change ((List.map (pair_srcVertex hw (staircasePreds i hi) tgtKind) (List.finRange w)).get ⟨u.val, _⟩) = _
      simp
    have h1 : (List.Nodup.getEquiv H.entries H.nodup) ⟨u.val, h_len⟩ = ⟨pair_srcVertex hw (staircasePreds i hi) tgtKind u, H.complete _⟩ := by
      apply Subtype.ext
      exact heq
    have h2 : ((List.Nodup.getEquiv H.entries H.nodup).symm ⟨pair_srcVertex hw (staircasePreds i hi) tgtKind u, H.complete _⟩) = ⟨u.val, h_len⟩ := by
      rw [← h1]
      simp
    have h3 := congrArg Fin.val h2
    exact h3
  exact Fin.ext hext

/-- Every edge into target position `p` comes from a source vertex whose
coordinate lies in `staircasePreds p`. -/
theorem pair_edge_src (p : Fin w) (u : Fin (pairCircuit hw (staircasePreds i hi) tgtKind).gateCount)
    (hu : (pairCircuit hw (staircasePreds i hi) tgtKind).edge u
      (pair_tgtVertex hw (staircasePreds i hi) tgtKind p).val = true) :
    ∃ q : Fin w, q ∈ staircasePreds i hi p ∧
      u = (pair_srcVertex hw (staircasePreds i hi) tgtKind q).val := by
  obtain ⟨hu1, -, hρ⟩ := (pairCircuit_edge_iff hw (staircasePreds i hi) tgtKind).mp hu
  refine ⟨⟨u.val % w, Nat.mod_lt _ hw⟩, ?_, ?_⟩
  · have hpp : (⟨(pair_tgtVertex hw (staircasePreds i hi) tgtKind p).val.val % w, Nat.mod_lt _ hw⟩ : Fin w) = p := by
      apply Fin.ext
      show (w + p.val) % w = p.val
      rw [Nat.add_mod_left, Nat.mod_eq_of_lt p.isLt]
    rw [hpp] at hρ
    exact hρ
  · apply Fin.ext
    show u.val = u.val % w
    rw [Nat.mod_eq_of_lt hu1]

/-- The vertCoord of a source-vertex-shaped predecessor is its coordinate. -/
theorem vertCoord_of_src (q : Fin w)
    (u : Fin (pairCircuit hw (staircasePreds i hi) tgtKind).gateCount)
    (hlu : (pairCircuit hw (staircasePreds i hi) tgtKind).layer u = 0)
    (hueq : u = (pair_srcVertex hw (staircasePreds i hi) tgtKind q).val) :
    vertCoord (pairCircuit hw (staircasePreds i hi) tgtKind)
      (pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi))
      (pairCircuit_totalWidth hw (staircasePreds i hi) tgtKind) ⟨u, hlu⟩ = q := by
  have hvv : (⟨u, hlu⟩ : LayerVertex (pairCircuit hw (staircasePreds i hi) tgtKind) 0)
      = pair_srcVertex hw (staircasePreds i hi) tgtKind q := by
    apply Subtype.ext
    exact hueq
  rw [hvv]
  exact vertCoord_eval hw tgtKind i hi q

noncomputable def pairGateTrans : TransMonoid w :=
  layerTrans (pairCircuit hw (staircasePreds i hi) tgtKind)
    (pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi))
    (fun _ => true) 0

theorem pairGate_and (h_comp : ∀ p, (tgtKind p).isComputation) (hk : tgtKind ⟨i.val + 1, hi⟩ = ADRGate.andGate) (z : Config w) :
    runTrans (pairGateTrans hw tgtKind i hi) z ⟨i.val + 1, hi⟩ = (z i && z ⟨i.val + 1, hi⟩) := by
  set c := pairCircuit hw (staircasePreds i hi) tgtKind with hc_def
  set cert := pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi) with hcert_def
  have hc : WellFormedADR c := pairCircuit_wellFormed hw (staircasePreds i hi) tgtKind h_comp
  have hW : TotalWidthAtMost c w := pairCircuit_totalWidth hw (staircasePreds i hi) tgtKind
  set j : Fin w := ⟨i.val + 1, hi⟩ with hj_def
  have hj : j.val < (cert.layerOrder (0 + 1)).entries.length := by
    rw [pairCylinder_len_one hw tgtKind i hi]; exact j.isLt
  have hvtx : (FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩
      = pair_tgtVertex hw (staircasePreds i hi) tgtKind j := pair_tgt_symm hw tgtKind i hi j hj
  have hkind : c.kind ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = ADRGate.andGate := by
    rw [hvtx, pair_kind_tgt hw tgtKind i hi j]; exact hk
  apply bool_eq_of_iff
  rw [Bool.and_eq_true]
  have hrun : runTrans (pairGateTrans hw tgtKind i hi) z j
      = layerTransMap c cert (fun _ => true) 0 z j := rfl
  rw [hrun, layerTransMap_and_true_iff c cert hc hW (fun _ => true) z hj hkind]
  -- edges into position j
  have hedge_i : c.edge (pair_srcVertex hw (staircasePreds i hi) tgtKind i).val
      ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = true := by
    rw [hvtx]
    exact pairCircuit_edge_of hw (staircasePreds i hi) tgtKind j i
      (by rw [hj_def, staircasePreds_succ i hi]; exact List.mem_cons.mpr (Or.inl rfl))
  have hedge_s : c.edge (pair_srcVertex hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩).val
      ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = true := by
    rw [hvtx]
    exact pairCircuit_edge_of hw (staircasePreds i hi) tgtKind j ⟨i.val + 1, hi⟩
      (by rw [hj_def, staircasePreds_succ i hi]; exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  constructor
  · intro hall
    have h1 := hall _ hedge_i
    have h2 := hall _ hedge_s
    rw [vertCoord_of_src hw tgtKind i hi i _ _ rfl] at h1
    rw [vertCoord_of_src hw tgtKind i hi ⟨i.val + 1, hi⟩ _ _ rfl] at h2
    exact ⟨h1, h2⟩
  · rintro ⟨ha, hb⟩ u hu
    rw [hvtx] at hu
    obtain ⟨q, hqmem, hueq⟩ := pair_edge_src hw tgtKind i hi j u hu
    rw [vertCoord_of_src hw tgtKind i hi q u _ hueq]
    rw [hj_def, staircasePreds_succ i hi] at hqmem
    rcases List.mem_cons.mp hqmem with h | h
    · rw [h]; exact ha
    · rw [List.mem_singleton] at h; rw [h]; exact hb

theorem pairGate_or (h_comp : ∀ p, (tgtKind p).isComputation) (hk : tgtKind ⟨i.val + 1, hi⟩ = ADRGate.orGate) (z : Config w) :
    runTrans (pairGateTrans hw tgtKind i hi) z ⟨i.val + 1, hi⟩ = (z i || z ⟨i.val + 1, hi⟩) := by
  set c := pairCircuit hw (staircasePreds i hi) tgtKind with hc_def
  set cert := pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi) with hcert_def
  have hc : WellFormedADR c := pairCircuit_wellFormed hw (staircasePreds i hi) tgtKind h_comp
  have hW : TotalWidthAtMost c w := pairCircuit_totalWidth hw (staircasePreds i hi) tgtKind
  set j : Fin w := ⟨i.val + 1, hi⟩ with hj_def
  have hj : j.val < (cert.layerOrder (0 + 1)).entries.length := by
    rw [pairCylinder_len_one hw tgtKind i hi]; exact j.isLt
  have hvtx : (FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩
      = pair_tgtVertex hw (staircasePreds i hi) tgtKind j := pair_tgt_symm hw tgtKind i hi j hj
  have hkind : c.kind ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = ADRGate.orGate := by
    rw [hvtx, pair_kind_tgt hw tgtKind i hi j]; exact hk
  apply bool_eq_of_iff
  rw [Bool.or_eq_true]
  have hrun : runTrans (pairGateTrans hw tgtKind i hi) z j
      = layerTransMap c cert (fun _ => true) 0 z j := rfl
  rw [hrun, layerTransMap_or_true_iff c cert hc hW (fun _ => true) z hj hkind]
  have hedge_i : c.edge (pair_srcVertex hw (staircasePreds i hi) tgtKind i).val
      ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = true := by
    rw [hvtx]
    exact pairCircuit_edge_of hw (staircasePreds i hi) tgtKind j i
      (by rw [hj_def, staircasePreds_succ i hi]; exact List.mem_cons.mpr (Or.inl rfl))
  have hedge_s : c.edge (pair_srcVertex hw (staircasePreds i hi) tgtKind ⟨i.val + 1, hi⟩).val
      ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = true := by
    rw [hvtx]
    exact pairCircuit_edge_of hw (staircasePreds i hi) tgtKind j ⟨i.val + 1, hi⟩
      (by rw [hj_def, staircasePreds_succ i hi]; exact List.mem_cons.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  constructor
  · rintro ⟨u, hu, hval⟩
    rw [hvtx] at hu
    obtain ⟨q, hqmem, hueq⟩ := pair_edge_src hw tgtKind i hi j u hu
    rw [vertCoord_of_src hw tgtKind i hi q u _ hueq] at hval
    rw [hj_def, staircasePreds_succ i hi] at hqmem
    rcases List.mem_cons.mp hqmem with h | h
    · rw [h] at hval; exact Or.inl hval
    · rw [List.mem_singleton] at h; rw [h] at hval; exact Or.inr hval
  · rintro (ha | hb)
    · exact ⟨_, hedge_i, by rw [vertCoord_of_src hw tgtKind i hi i _ _ rfl]; exact ha⟩
    · exact ⟨_, hedge_s, by rw [vertCoord_of_src hw tgtKind i hi ⟨i.val + 1, hi⟩ _ _ rfl]; exact hb⟩

theorem pairGate_copy (h_comp : ∀ p, (tgtKind p).isComputation) (j : Fin w) (hj0 : j.val ≠ i.val + 1) (z : Config w) :
    runTrans (pairGateTrans hw tgtKind i hi) z j = z j := by
  set c := pairCircuit hw (staircasePreds i hi) tgtKind with hc_def
  set cert := pairCylinder hw (staircasePreds i hi) tgtKind (adjPairCylinder hw tgtKind i hi) with hcert_def
  have hc : WellFormedADR c := pairCircuit_wellFormed hw (staircasePreds i hi) tgtKind h_comp
  have hW : TotalWidthAtMost c w := pairCircuit_totalWidth hw (staircasePreds i hi) tgtKind
  have hj : j.val < (cert.layerOrder (0 + 1)).entries.length := by
    rw [pairCylinder_len_one hw tgtKind i hi]; exact j.isLt
  have hvtx : (FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩
      = pair_tgtVertex hw (staircasePreds i hi) tgtKind j := pair_tgt_symm hw tgtKind i hi j hj
  have hpreds : staircasePreds i hi j = [j] := staircasePreds_self i hi j hj0
  have hedge_j : c.edge (pair_srcVertex hw (staircasePreds i hi) tgtKind j).val
      ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = true := by
    rw [hvtx]
    exact pairCircuit_edge_of hw (staircasePreds i hi) tgtKind j j
      (by rw [hpreds]; exact List.mem_cons.mpr (Or.inl rfl))
  have hrun : runTrans (pairGateTrans hw tgtKind i hi) z j
      = layerTransMap c cert (fun _ => true) 0 z j := rfl
  have hkindtgt : c.kind ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = tgtKind j := by
    rw [hvtx]; exact pair_kind_tgt hw tgtKind i hi j
  rw [hrun]
  -- the only predecessor is `j`; both AND and OR then compute `z j`
  cases hkj : tgtKind j with
  | literal a b =>
    exfalso
    have := h_comp j; rw [hkj] at this; simp [ADRGate.isComputation] at this
  | andGate =>
    have hkind : c.kind ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = ADRGate.andGate := by
      rw [hkindtgt]; exact hkj
    apply bool_eq_of_iff
    rw [layerTransMap_and_true_iff c cert hc hW (fun _ => true) z hj hkind]
    constructor
    · intro hall
      have h1 := hall _ hedge_j
      rw [vertCoord_of_src hw tgtKind i hi j _ _ rfl] at h1
      exact h1
    · intro hzj u hu
      rw [hvtx] at hu
      obtain ⟨q, hqmem, hueq⟩ := pair_edge_src hw tgtKind i hi j u hu
      rw [hpreds, List.mem_singleton] at hqmem
      rw [vertCoord_of_src hw tgtKind i hi q u _ hueq, hqmem]
      exact hzj
  | orGate =>
    have hkind : c.kind ((FullLayerIndexing c cert (0 + 1)).symm ⟨j.val, hj⟩).val = ADRGate.orGate := by
      rw [hkindtgt]; exact hkj
    apply bool_eq_of_iff
    rw [layerTransMap_or_true_iff c cert hc hW (fun _ => true) z hj hkind]
    constructor
    · rintro ⟨u, hu, hval⟩
      rw [hvtx] at hu
      obtain ⟨q, hqmem, hueq⟩ := pair_edge_src hw tgtKind i hi j u hu
      rw [hpreds, List.mem_singleton] at hqmem
      rw [vertCoord_of_src hw tgtKind i hi q u _ hueq, hqmem] at hval
      exact hval
    · intro hzj
      exact ⟨_, hedge_j, by rw [vertCoord_of_src hw tgtKind i hi j _ _ rfl]; exact hzj⟩

end Internal
end AllenderOQ3

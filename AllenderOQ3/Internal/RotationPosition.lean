import AllenderOQ3.Internal.ArcWordBlocks
import AllenderOQ3.Internal.NonCrossingShift
import AllenderOQ3.Internal.NonCrossingUnits

namespace AllenderOQ3.Internal

variable {n w : Nat} (c : ADRCircuit n) (cert : IncidenceCylinder c)

/-- C1: If L is a cyclic rotation of a full layer listing, its coordinates are a cyclic
rotation of finRange. -/
theorem rotation_position_inversion {ell : Nat}
    (hfull : (cert.layerOrder ell).entries.length = w)
    {L : List (LayerVertex c ell)}
    (hrot : CyclicRotation ((cert.layerOrder ell).entries) L) :
    ∃ r : Nat, L.map (idxOfVtx c cert ell hfull.le) = (List.finRange w).rotate r := by
  have h1 : (cert.layerOrder ell).entries = (List.finRange w).map (vtxAt c cert ell hfull) :=
    entries_eq_map_vtxAt ell hfull
  have h2 : (cert.layerOrder ell).entries ~r L := (cyclicRotation_iff_isRotated _ _).mp hrot
  rw [h1] at h2
  have h3 : ((List.finRange w).map (vtxAt c cert ell hfull)).map (idxOfVtx c cert ell hfull.le)
      ~r L.map (idxOfVtx c cert ell hfull.le) :=
    h2.map _
  have h4 : ((List.finRange w).map (vtxAt c cert ell hfull)).map (idxOfVtx c cert ell hfull.le)
      = List.finRange w := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      simp [idxOfVtx_vtxAt ell hfull]
  rw [h4] at h3
  rcases h3 with ⟨r, hr⟩
  use r
  exact hr.symm

/-- C1 consumer form: The coordinates of `T2'` are cyclically between `v1` and `v2`. -/
theorem rotation_position_interval {ell : Nat}
    (hfull : (cert.layerOrder ell).entries.length = w)
    {v1 v2 : LayerVertex c ell} {T2' T3' : List (LayerVertex c ell)}
    (hrot : CyclicRotation ((cert.layerOrder ell).entries) (v1 :: T2' ++ v2 :: T3')) :
    ∃ (start : Fin w) (d : Nat),
      idxOfVtx c cert ell hfull.le v1 = start ∧
      idxOfVtx c cert ell hfull.le v2 = finShift (d + 1) start ∧
      T2'.map (idxOfVtx c cert ell hfull.le)
        = (List.range T2'.length).map (fun k => finShift (k + 1) start) ∧
      d = T2'.length := by
  have h_inv := rotation_position_inversion c cert hfull hrot
  rcases h_inv with ⟨r, hr⟩
  have hlen : (v1 :: T2' ++ v2 :: T3').length = w := by
    have h_isrot := (cyclicRotation_iff_isRotated _ _).mp hrot
    rcases h_isrot with ⟨n, hn⟩
    rw [← hn, List.length_rotate, hfull]
  have hw : 0 < w := by
    rw [← hlen]
    simp
  set s : Fin w := ⟨r % w, Nat.mod_lt _ hw⟩
  have h_rot_eq :
      (List.finRange w).rotate r = (List.finRange w).map (fun k => finShift k.val s) := by
    have h_mod : (List.finRange w).rotate r = (List.finRange w).rotate s.val := by
      have hl : w = (List.finRange w).length := by simp
      have h_mod' : (List.finRange w).rotate (r % (List.finRange w).length)
          = (List.finRange w).rotate r := List.rotate_mod _ _
      rw [← hl] at h_mod'
      exact h_mod'.symm
    rw [h_mod, rotate_finRange_eq]
  rw [h_rot_eq] at hr
  have h_get_eq : ∀ (i : Nat),
      (List.map (idxOfVtx c cert ell hfull.le) (v1 :: T2' ++ v2 :: T3'))[i]?
        = ((List.finRange w).map (fun k => finShift k.val s))[i]? := by
    intro i
    rw [hr]
  use s, T2'.length
  have h1 : idxOfVtx c cert ell hfull.le v1 = s := by
    have h0 := h_get_eq 0
    have hl_simp : (List.map (idxOfVtx c cert ell hfull.le) (v1 :: T2' ++ v2 :: T3'))[0]?
        = some (idxOfVtx c cert ell hfull.le v1) := by rfl
    rw [hl_simp] at h0
    have hz : ((List.finRange w).map (fun k => finShift k.val s))[0]? = some (finShift 0 s) := by
      rw [List.getElem?_map]
      have hz_range : (List.finRange w)[0]? = some ⟨0, hw⟩ := by
        apply List.getElem?_eq_getElem (by simp [hw]) |>.trans
        congr
        apply Fin.eq_of_val_eq
        simp
      rw [hz_range]
      rfl
    rw [hz] at h0
    have h0' := Option.some.inj h0
    rw [finShift_zero] at h0'
    exact h0'
  have hz_range_k (i : Nat) (hi : i < w) : (List.finRange w)[i]? = some ⟨i, hi⟩ := by
    apply List.getElem?_eq_getElem (by simp [hi]) |>.trans
    congr
    apply Fin.eq_of_val_eq
    simp
  have h2 : idxOfVtx c cert ell hfull.le v2 = finShift (T2'.length + 1) s := by
    have hd := h_get_eq (T2'.length + 1)
    have hl_simp :
        (List.map (idxOfVtx c cert ell hfull.le) (v1 :: T2' ++ v2 :: T3'))[T2'.length + 1]?
          = some (idxOfVtx c cert ell hfull.le v2) := by
      rw [List.getElem?_map]
      have hget : (v1 :: T2' ++ v2 :: T3')[T2'.length + 1]? = some v2 := by
        have h_step1 : (v1 :: T2' ++ v2 :: T3')[T2'.length + 1]?
            = (T2' ++ v2 :: T3')[T2'.length]? := rfl
        rw [h_step1]
        rw [List.getElem?_append_right (by simp)]
        have hs : T2'.length - T2'.length = 0 := Nat.sub_self _
        rw [hs]
        rfl
      rw [hget]
      rfl
    rw [hl_simp] at hd
    have hT2_lt : T2'.length + 1 < w := by
      have h_len2 : (v1 :: T2' ++ v2 :: T3').length = 1 + T2'.length + 1 + T3'.length := by
        simp; omega
      rw [h_len2] at hlen
      omega
    have hR : ((List.finRange w).map (fun k => finShift k.val s))[T2'.length + 1]?
        = some (finShift (T2'.length + 1) s) := by
      rw [List.getElem?_map, hz_range_k _ hT2_lt]
      rfl
    rw [hR] at hd
    exact Option.some.inj hd
  
  have h3 : T2'.map (idxOfVtx c cert ell hfull.le)
      = (List.range T2'.length).map (fun k => finShift (k + 1) s) := by
    apply List.ext_getElem
    · simp
    · intro i hi1 hi2
      have hi : i < T2'.length := by simpa using hi1
      have hi_get := h_get_eq (i + 1)
      have hl_simp : (List.map (idxOfVtx c cert ell hfull.le) (v1 :: T2' ++ v2 :: T3'))[i + 1]?
          = some (idxOfVtx c cert ell hfull.le (T2'[i]'hi)) := by
        rw [List.getElem?_map]
        have hget : (v1 :: T2' ++ v2 :: T3')[i + 1]? = some (T2'[i]'hi) := by
          have h_step1 : (v1 :: T2' ++ v2 :: T3')[i + 1]? = (T2' ++ v2 :: T3')[i]? := rfl
          rw [h_step1]
          rw [List.getElem?_append]
          rw [if_pos hi]
          exact List.getElem?_eq_getElem hi
        rw [hget]
        rfl
      rw [hl_simp] at hi_get
      have hT2_lt : i + 1 < w := by
        have h_len2 : (v1 :: T2' ++ v2 :: T3').length = 1 + T2'.length + 1 + T3'.length := by
          simp; omega
        rw [h_len2] at hlen
        omega
      have hR : ((List.finRange w).map (fun k => finShift k.val s))[i + 1]?
          = some (finShift (i + 1) s) := by
        rw [List.getElem?_map, hz_range_k _ hT2_lt]
        rfl
      rw [hR] at hi_get
      have hi_get' := Option.some.inj hi_get
      have hL2 : (T2'.map (idxOfVtx c cert ell hfull.le))[i]'hi1
          = idxOfVtx c cert ell hfull.le (T2'[i]'hi) := by simp
      have hR2 : ((List.range T2'.length).map (fun k => finShift (k + 1) s))[i]'hi2
          = finShift (i + 1) s := by
        rw [List.getElem_map]
        simp
      rw [hL2, hR2, hi_get']
  
  exact ⟨h1, h2, h3, rfl⟩

end AllenderOQ3.Internal

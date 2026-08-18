import AllenderOQ3.Internal.NonCrossingUnits

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# Bijective non-crossing transitions are cyclic shifts

A layer transition of a cylindrical HMV-normal circuit is a monotone self-map of
the Boolean cube `Config w`.  If it happens to be a *bijection*, then it is a
permutation of coordinates (`exists_coord_perm_of_monotone_bijective`), the
layer is a perfect matching (`edge_iff_of_coord_perm`), and the incidence
certificate's common arc word forces that permutation to be a *cyclic shift*.

Since a composition of self-maps of a finite type is bijective exactly when all
factors are, the set of monotone maps whose bijective members are shifts is a
submonoid; hence *every* unit of `NonCrossing w` is a cyclic shift.
-/

namespace AllenderOQ3.Internal

/-- Cyclic shift of the coordinate index by `m`. -/
def finShift {w : Nat} (m : Nat) (j : Fin w) : Fin w :=
  ⟨(j.val + m) % w, Nat.mod_lt _ (Nat.zero_lt_of_lt j.isLt)⟩

@[simp] theorem finShift_zero {w : Nat} (j : Fin w) : finShift 0 j = j := by
  apply Fin.ext
  simp [finShift, Nat.mod_eq_of_lt j.isLt]

theorem finShift_finShift {w : Nat} (p q : Nat) (j : Fin w) :
    finShift p (finShift q j) = finShift (q + p) j := by
  apply Fin.ext
  simp only [finShift]
  rw [Nat.mod_add_mod, ← Nat.add_assoc]

theorem finShift_val {w : Nat} (m : Nat) (j : Fin w) :
    (finShift m j).val = (j.val + m) % w := rfl

/-- A configuration map is a cyclic shift of coordinates. -/
def IsShiftMap (w : Nat) (f : Config w → Config w) : Prop :=
  ∃ m : Nat, ∀ s j, f s j = s (finShift m j)

/-- Monotone maps whose bijective members are cyclic shifts. -/
def shiftSubmonoid (w : Nat) : Submonoid (TransMonoid w) where
  carrier := {g | Monotone (MulOpposite.unop g) ∧
    (Function.Bijective (MulOpposite.unop g) → IsShiftMap w (MulOpposite.unop g))}
  mul_mem' := by
    rintro a b ⟨hma, hsa⟩ ⟨hmb, hsb⟩
    have hcomp : MulOpposite.unop (a * b) =
        (MulOpposite.unop b) ∘ (MulOpposite.unop a) := rfl
    refine ⟨Monotone.comp (f := MulOpposite.unop a) (g := MulOpposite.unop b) hmb hma, ?_⟩
    intro hbij
    rw [hcomp] at hbij
    have hinja : Function.Injective (MulOpposite.unop a) :=
      Function.Injective.of_comp hbij.1
    have hsurjb : Function.Surjective (MulOpposite.unop b) :=
      Function.Surjective.of_comp hbij.2
    have hbija : Function.Bijective (MulOpposite.unop a) :=
      Finite.injective_iff_bijective.mp hinja
    have hbijb : Function.Bijective (MulOpposite.unop b) :=
      Finite.surjective_iff_bijective.mp hsurjb
    obtain ⟨p, hp⟩ := hsa hbija
    obtain ⟨q, hq⟩ := hsb hbijb
    refine ⟨q + p, fun s j => ?_⟩
    rw [hcomp]
    simp only [Function.comp_apply]
    rw [hq, hp, finShift_finShift]
  one_mem' := by
    refine ⟨monotone_id, fun _ => ⟨0, fun s j => ?_⟩⟩
    rw [finShift_zero]
    rfl

theorem mem_shiftSubmonoid_iff {w : Nat} (g : TransMonoid w) :
    g ∈ shiftSubmonoid w ↔ Monotone (MulOpposite.unop g) ∧
      (Function.Bijective (MulOpposite.unop g) → IsShiftMap w (MulOpposite.unop g)) :=
  Iff.rfl

/-! ## The certificate's layer listing, read off positionally -/

variable {n w : Nat} {c : ADRCircuit n} {cert : IncidenceCylinder c}

theorem entries_eq_map_vtxAt (ell : Nat) (h : (cert.layerOrder ell).entries.length = w) :
    (cert.layerOrder ell).entries = (List.finRange w).map (vtxAt c cert ell h) := by
  apply List.ext_getElem
  · simp [h]
  · intro i hi hi'
    have hiw : i < w := by rw [← h]; exact hi
    have h1 : ((List.finRange w).map (vtxAt c cert ell h))[i]'hi'
        = vtxAt c cert ell h ⟨i, hiw⟩ := by simp
    rw [h1]
    unfold vtxAt
    have h2 := layerEntries_get_index (c := c) (cert := cert) ell
      ((FullLayerIndexing c cert ell).symm ⟨i, by rw [h]; exact hiw⟩)
    rw [Equiv.apply_symm_apply] at h2
    exact h2.symm


/-! ## The arc of a perfect-matching layer -/

section MatchArc

variable {ell : Nat} {sigma : Equiv.Perm (Fin w)}
  {h1 : (cert.layerOrder ell).entries.length = w}
  {h2 : (cert.layerOrder (ell + 1)).entries.length = w}

/-- The unique arc into the vertex at position `j` of the upper layer, given a
layer that matches position `sigma j` below with position `j` above. -/
noncomputable def matchArc (c : ADRCircuit n) (cert : IncidenceCylinder c) (ell : Nat)
    (h1 : (cert.layerOrder ell).entries.length = w)
    (h2 : (cert.layerOrder (ell + 1)).entries.length = w) (sigma : Equiv.Perm (Fin w))
    (hedge : ∀ j : Fin w,
      c.edge (vtxAt c cert ell h1 (sigma j)).val (vtxAt c cert (ell + 1) h2 j).val = true)
    (j : Fin w) : TransitionArc c ell :=
  ⟨((vtxAt c cert ell h1 (sigma j)).val, (vtxAt c cert (ell + 1) h2 j).val),
    hedge j, (vtxAt c cert ell h1 (sigma j)).2, (vtxAt c cert (ell + 1) h2 j).2⟩

variable {hedge : ∀ j : Fin w,
  c.edge (vtxAt c cert ell h1 (sigma j)).val (vtxAt c cert (ell + 1) h2 j).val = true}

theorem matchArc_injective :
    Function.Injective (matchArc c cert ell h1 h2 sigma hedge) := by
  intro a b hab
  have h : (vtxAt c cert (ell + 1) h2 a).val = (vtxAt c cert (ell + 1) h2 b).val :=
    congrArg (fun e => e.val.2) hab
  have h' : vtxAt c cert (ell + 1) h2 a = vtxAt c cert (ell + 1) h2 b := Subtype.ext h
  have := congrArg (idxOfVtx c cert (ell + 1) h2.le) h'
  rwa [idxOfVtx_vtxAt, idxOfVtx_vtxAt] at this

variable (hmatch : ∀ (j : Fin w) (u : LayerVertex c ell),
  c.edge u.val (vtxAt c cert (ell + 1) h2 j).val = true ↔ idxOfVtx c cert ell h1.le u = sigma j)

include hmatch in
theorem incoming_eq_singleton (j : Fin w) :
    (cert.transitionOrder ell).incoming (vtxAt c cert (ell + 1) h2 j)
      = [matchArc c cert ell h1 h2 sigma hedge j] := by
  refine List.eq_singleton_of_mem_iff ((cert.transitionOrder ell).incoming_nodup _) ?_
  intro e
  rw [(cert.transitionOrder ell).incoming_exact]
  constructor
  · intro hhead
    have hu : c.edge (⟨e.val.1, e.2.2.1⟩ : LayerVertex c ell).val
        (vtxAt c cert (ell + 1) h2 j).val = true := by
      have := e.2.1
      simpa [hhead] using this
    have hidx := (hmatch j ⟨e.val.1, e.2.2.1⟩).mp hu
    have heq : (⟨e.val.1, e.2.2.1⟩ : LayerVertex c ell) = vtxAt c cert ell h1 (sigma j) := by
      rw [← vtxAt_idxOfVtx ell h1 (⟨e.val.1, e.2.2.1⟩ : LayerVertex c ell), hidx]
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg Subtype.val heq
    · exact hhead
  · intro he
    rw [he]
    rfl

include hmatch in
theorem outgoing_eq_singleton (i : Fin w) :
    (cert.transitionOrder ell).outgoing (vtxAt c cert ell h1 i)
      = [matchArc c cert ell h1 h2 sigma hedge (sigma.symm i)] := by
  refine List.eq_singleton_of_mem_iff ((cert.transitionOrder ell).outgoing_nodup _) ?_
  intro e
  rw [(cert.transitionOrder ell).outgoing_exact]
  constructor
  · intro htail
    set v : LayerVertex c (ell + 1) := ⟨e.val.2, e.2.2.2⟩ with hv
    set j : Fin w := idxOfVtx c cert (ell + 1) h2.le v with hj
    have hvj : v = vtxAt c cert (ell + 1) h2 j := (vtxAt_idxOfVtx (ell + 1) h2 v).symm
    have hu : c.edge (vtxAt c cert ell h1 i).val (vtxAt c cert (ell + 1) h2 j).val = true := by
      have := e.2.1
      rw [← hvj]
      simpa [hv, htail] using this
    have hidx := (hmatch j (vtxAt c cert ell h1 i)).mp hu
    rw [idxOfVtx_vtxAt] at hidx
    have hji : j = sigma.symm i := by
      rw [hidx, Equiv.symm_apply_apply]
    apply Subtype.ext
    apply Prod.ext
    · change e.val.1 = (vtxAt c cert ell h1 (sigma (sigma.symm i))).val
      rw [Equiv.apply_symm_apply]
      exact htail
    · change e.val.2 = (vtxAt c cert (ell + 1) h2 (sigma.symm i)).val
      rw [← hji, ← hvj]
  · intro he
    rw [he]
    change (vtxAt c cert ell h1 (sigma (sigma.symm i))).val = (vtxAt c cert ell h1 i).val
    rw [Equiv.apply_symm_apply]

include hmatch hedge in
/-- The certificate's common arc word forces the matching permutation to be a
cyclic shift. -/
theorem sigma_eq_finShift : ∃ m : Nat, ∀ j : Fin w, sigma j = finShift m j := by
  have hsrc : (cert.layerOrder ell).entries.flatMap (cert.transitionOrder ell).outgoing
      = (List.finRange w).map
        (fun i => matchArc c cert ell h1 h2 sigma hedge (sigma.symm i)) := by
    rw [entries_eq_map_vtxAt ell h1, List.flatMap_map]
    rw [List.map_eq_flatMap]
    exact List.flatMap_congr (fun i _ => outgoing_eq_singleton hmatch i)
  have htgt : (cert.layerOrder (ell + 1)).entries.flatMap (cert.transitionOrder ell).incoming
      = (List.finRange w).map (matchArc c cert ell h1 h2 sigma hedge) := by
    rw [entries_eq_map_vtxAt (ell + 1) h2, List.flatMap_map]
    rw [List.map_eq_flatMap]
    exact List.flatMap_congr (fun j _ => incoming_eq_singleton hmatch j)
  have hrot := (cert.transitionOrder ell).commonArcWord
  rw [hsrc, htgt] at hrot
  obtain ⟨m, hm⟩ := exists_shift_of_cyclicRotation _ _ hrot
  refine ⟨m, fun j => ?_⟩
  have := hm j
  have hinj := matchArc_injective (c := c) (cert := cert) (ell := ell) (h1 := h1) (h2 := h2)
    (sigma := sigma) (hedge := hedge) this
  have hgoal := congrArg sigma hinj
  rw [Equiv.apply_symm_apply] at hgoal
  exact hgoal

end MatchArc

/-- **A bijective non-crossing layer transition is a cyclic shift.** -/
theorem layerTransMap_isShift_of_bijective (x : Fin n → Bool) (ell : Nat)
    (hN : HMVNormal c) (hW : TotalWidthAtMost c w)
    (hbij : Function.Bijective (layerTransMap (w := w) c cert x ell)) :
    IsShiftMap w (layerTransMap (w := w) c cert x ell) := by
  obtain ⟨sigma, hsig⟩ := exists_coord_perm_of_monotone_bijective
    (layerTransMap_monotone (c := c) (cert := cert) (w := w) x ell) hbij
  have hWF : WellFormedADR c := hN.1
  have h1le : (cert.layerOrder ell).entries.length ≤ w := layerEntries_length_le hW ell
  have h2 : (cert.layerOrder (ell + 1)).entries.length = w := target_layer_length hW hsig
  have h1 : (cert.layerOrder ell).entries.length = w :=
    source_layer_length hWF h1le h2 hsig hW
  have hmatch : ∀ (j : Fin w) (u : LayerVertex c ell),
      c.edge u.val (vtxAt c cert (ell + 1) h2 j).val = true ↔
        idxOfVtx c cert ell h1.le u = sigma j :=
    fun j u => edge_iff_of_coord_perm hWF h1le h2 hsig j u
  have hedge : ∀ j : Fin w,
      c.edge (vtxAt c cert ell h1 (sigma j)).val (vtxAt c cert (ell + 1) h2 j).val = true := by
    intro j
    refine (hmatch j (vtxAt c cert ell h1 (sigma j))).mpr ?_
    rw [idxOfVtx_vtxAt]
  obtain ⟨m, hm⟩ := sigma_eq_finShift (hedge := hedge) hmatch
  exact ⟨m, fun s j => by rw [hsig, hm]⟩

theorem nonCrossing_le_shiftSubmonoid (w : Nat) :
    NonCrossing w ≤ shiftSubmonoid w := by
  refine Submonoid.closure_le.mpr ?_
  rintro f ⟨n', c', cert', ell', x', hN', hW', rfl⟩
  exact ⟨layerTransMap_monotone (c := c') (cert := cert') x' ell',
    fun hbij => layerTransMap_isShift_of_bijective (c := c') (cert := cert') x' ell' hN' hW' hbij⟩

end AllenderOQ3.Internal

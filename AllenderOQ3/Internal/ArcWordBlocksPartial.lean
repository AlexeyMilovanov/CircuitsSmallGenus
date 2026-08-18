import AllenderOQ3.Internal.ArcWordBlocks

/-!
# T1.4 for partial source listings (the C4 resolution)

`isConstantFreeMap` fills the TARGET layer but leaves the SOURCE layer of
length `L ≤ w` arbitrary, and a `Fin w` cyclic interval wrapping through the
dead zone `[L, w)` meets the live zone in up to two `Fin w` runs.  The
resolution (decision C4, 2026-08-18): restate the interval-block lemma over
the *position circle of the listing itself* (`Fin L`), where the dead gap
collapses and the live part of any wrapping interval is again one cyclic
interval.

* `posVtx` / `vtxPos` — the positional indexing of a layer listing, with no
  fullness hypothesis;
* `exists_arcWord_interval_block_pos` — T1.4 over listing positions mod `L`;
* `live_interval_bridge` — the arithmetic bridge: for a cyclic `Fin w`
  interval starting at a live coordinate, the live positions form one cyclic
  interval of the `Fin L` position circle with the same start.

A direct `Fin w`-interval version of T1.4 for partial listings is FALSE —
do not attempt it.  Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {n : Nat} {c : ADRCircuit n} {cert : IncidenceCylinder c}

/-! ## Positional indexing without fullness -/

/-- The vertex at a listing position. -/
noncomputable def posVtx (ell : Nat)
    (j : Fin (cert.layerOrder ell).entries.length) : LayerVertex c ell :=
  (FullLayerIndexing c cert ell).symm j

/-- The listing position of a vertex. -/
noncomputable def vtxPos (ell : Nat) (u : LayerVertex c ell) :
    Fin (cert.layerOrder ell).entries.length :=
  FullLayerIndexing c cert ell u

theorem posVtx_vtxPos (ell : Nat) (u : LayerVertex c ell) :
    posVtx (cert := cert) ell (vtxPos ell u) = u :=
  (FullLayerIndexing c cert ell).symm_apply_apply u

theorem vtxPos_posVtx (ell : Nat)
    (j : Fin (cert.layerOrder ell).entries.length) :
    vtxPos (cert := cert) ell (posVtx ell j) = j :=
  (FullLayerIndexing c cert ell).apply_symm_apply j

/-- The listing is the map of `posVtx` over all positions. -/
theorem entries_eq_map_posVtx (ell : Nat) :
    (cert.layerOrder ell).entries
      = (List.finRange (cert.layerOrder ell).entries.length).map
          (posVtx (cert := cert) ell) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have hiL : i < (cert.layerOrder ell).entries.length := hi
    have h1 : ((List.finRange (cert.layerOrder ell).entries.length).map
          (posVtx (cert := cert) ell))[i]'hi'
        = posVtx (cert := cert) ell ⟨i, hiL⟩ := by simp
    rw [h1]
    unfold posVtx
    have h2 := layerEntries_get_index (c := c) (cert := cert) ell
      ((FullLayerIndexing c cert ell).symm ⟨i, hiL⟩)
    rw [Equiv.apply_symm_apply] at h2
    exact h2.symm

/-! ## T1.4 over listing positions -/

/-- **T1.4, partial-listing form.**  The arcs whose sources sit in a cyclic
interval of listing positions form one contiguous block of the arc word. -/
theorem exists_arcWord_interval_block_pos (ell : Nat)
    (start : Fin (cert.layerOrder ell).entries.length) (len : Nat)
    (_hlen : len ≤ (cert.layerOrder ell).entries.length) :
    ∃ P Q : List (TransitionArc c ell),
      CyclicRotation
        ((cert.layerOrder ell).entries.flatMap
          ((cert.transitionOrder ell).outgoing))
        (P ++ Q) ∧
      (∀ e ∈ P, ∃ k, k < len ∧
        vtxPos (cert := cert) ell (arcSource e) = finShift k start) ∧
      (∀ e ∈ Q, ¬ ∃ k, k < len ∧
        vtxPos (cert := cert) ell (arcSource e) = finShift k start) ∧
      (∀ e : TransitionArc c ell,
        (∃ k, k < len ∧
          vtxPos (cert := cert) ell (arcSource e) = finShift k start) →
        e ∈ P) := by
  classical
  let L := (cert.layerOrder ell).entries.length
  let f : Fin L → LayerVertex c ell :=
    fun k => posVtx (cert := cert) ell (finShift k.val start)
  let out := (cert.transitionOrder ell).outgoing
  let P := (((List.finRange L).take len).map f).flatMap out
  let Q := (((List.finRange L).drop len).map f).flatMap out
  have hsplit : (List.finRange L).map f
      = ((List.finRange L).take len).map f
        ++ ((List.finRange L).drop len).map f := by
    rw [← List.map_append, List.take_append_drop]
  have hrotL : CyclicRotation ((cert.layerOrder ell).entries)
      ((List.finRange L).map f) := by
    rw [entries_eq_map_posVtx (cert := cert) ell,
      cyclicRotation_iff_isRotated]
    have h4 : ((List.finRange L).rotate start.val).map
          (posVtx (cert := cert) ell)
        = (List.finRange L).map f := by
      rw [rotate_finRange_eq, List.map_map]
      rfl
    rw [← h4]
    exact List.IsRotated.map ⟨start.val, rfl⟩ _
  have hrot : CyclicRotation
      ((cert.layerOrder ell).entries.flatMap
        ((cert.transitionOrder ell).outgoing))
      (P ++ Q) := by
    have h5 := cyclicRotation_flatMap out hrotL
    rw [hsplit, List.flatMap_append] at h5
    exact h5
  have hsrcOf : ∀ (p : Fin L) (e : TransitionArc c ell), e ∈ out (f p) →
      arcSource e = posVtx (cert := cert) ell (finShift p.val start) := by
    intro p e heu
    apply Subtype.ext
    exact ((cert.transitionOrder ell).outgoing_exact _ e).mp heu
  have hP : ∀ e ∈ P, ∃ k, k < len ∧
      vtxPos (cert := cert) ell (arcSource e) = finShift k start := by
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨u, hu, heu⟩ := he
    rw [List.mem_map] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    refine ⟨p.val, mem_take_finRange hp, ?_⟩
    rw [hsrcOf p e heu, vtxPos_posVtx]
  have hQ : ∀ e ∈ Q, ¬ ∃ k, k < len ∧
      vtxPos (cert := cert) ell (arcSource e) = finShift k start := by
    intro e he
    rw [List.mem_flatMap] at he
    obtain ⟨u, hu, heu⟩ := he
    rw [List.mem_map] at hu
    obtain ⟨p, hp, rfl⟩ := hu
    have hpk : len ≤ p.val := mem_drop_finRange hp
    rintro ⟨k, hk, hkeq⟩
    rw [hsrcOf p e heu, vtxPos_posVtx] at hkeq
    have hpe := finShift_amount_inj (a := p.val) (b := k) p.isLt
      (by omega) hkeq
    omega
  refine ⟨P, Q, hrot, hP, hQ, ?_⟩
  intro e hint
  have hmem : e ∈ P ++ Q := mem_of_cyclicRotation hrot (mem_srcWord ell e)
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · exact absurd hint (hQ e h)

/-! ## The live-interval bridge -/

/-- **The C4 bridge.**  For `L ≤ w`, the live positions (`< L`) of a cyclic
`Fin w` interval `[a, a + lenJ)` starting at a live coordinate form one
cyclic interval of the `Fin L` position circle, starting at the same value:
there is a length `len' ≤ L` with, for every position `p`,
`p ∈ [a, a + len') (mod L)` iff the coordinate of `p` lies in the original
interval `(mod w)`. -/
theorem live_interval_bridge {w L : Nat} (hLw : L ≤ w)
    (a : Fin w) (haL : a.val < L) (lenJ : Nat) (hJw : lenJ ≤ w) :
    ∃ len', len' ≤ L ∧ ∀ p : Fin L,
      ((∃ k, k < len' ∧ finShift k (⟨a.val, haL⟩ : Fin L) = p) ↔
       (∃ k, k < lenJ ∧
         finShift k a = (⟨p.val, lt_of_lt_of_le p.isLt hLw⟩ : Fin w))) := by
  have hshiftL : ∀ (k : Nat) (p : Fin L),
      finShift k (⟨a.val, haL⟩ : Fin L) = p ↔ (a.val + k) % L = p.val := by
    intro k p
    rw [Fin.ext_iff, finShift_val]
  have hshiftW : ∀ (k : Nat) (p : Fin L),
      finShift k a = (⟨p.val, lt_of_lt_of_le p.isLt hLw⟩ : Fin w)
        ↔ (a.val + k) % w = p.val := by
    intro k p
    rw [Fin.ext_iff, finShift_val]
  simp only [hshiftL, hshiftW]
  by_cases h1 : a.val + lenJ ≤ L
  · refine ⟨lenJ, by omega, fun p => ⟨?_, ?_⟩⟩
    · rintro ⟨k, hk, hke⟩
      rw [Nat.mod_eq_of_lt (by omega)] at hke
      exact ⟨k, hk, by rw [Nat.mod_eq_of_lt (by omega)]; exact hke⟩
    · rintro ⟨k, hk, hke⟩
      rw [Nat.mod_eq_of_lt (by omega)] at hke
      exact ⟨k, hk, by rw [Nat.mod_eq_of_lt (by omega)]; exact hke⟩
  · by_cases h2 : a.val + lenJ ≤ w
    · refine ⟨L - a.val, by omega, fun p => ⟨?_, ?_⟩⟩
      · rintro ⟨k, hk, hke⟩
        rw [Nat.mod_eq_of_lt (by omega)] at hke
        exact ⟨k, by omega, by rw [Nat.mod_eq_of_lt (by omega)]; exact hke⟩
      · rintro ⟨k, hk, hke⟩
        rw [Nat.mod_eq_of_lt (by omega)] at hke
        have hklt : k < L - a.val := by
          have := p.isLt
          omega
        exact ⟨k, hklt, by rw [Nat.mod_eq_of_lt (by omega)]; exact hke⟩
    · refine ⟨L + lenJ - w, by omega, fun p => ⟨?_, ?_⟩⟩
      · rintro ⟨k, hk, hke⟩
        by_cases hkl : a.val + k < L
        · rw [Nat.mod_eq_of_lt hkl] at hke
          exact ⟨k, by omega, by rw [Nat.mod_eq_of_lt (by omega)]; exact hke⟩
        · rw [Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)] at hke
          refine ⟨w + k - L, by omega, ?_⟩
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega
      · rintro ⟨k, hk, hke⟩
        by_cases hkw : a.val + k < w
        · rw [Nat.mod_eq_of_lt hkw] at hke
          have hkl : a.val + k < L := by
            have := p.isLt
            omega
          exact ⟨k, by omega, by rw [Nat.mod_eq_of_lt hkl]; exact hke⟩
        · rw [Nat.mod_eq_sub_mod (by omega),
            Nat.mod_eq_of_lt (by omega)] at hke
          refine ⟨k + L - w, by omega, ?_⟩
          rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
          omega

end Internal
end AllenderOQ3

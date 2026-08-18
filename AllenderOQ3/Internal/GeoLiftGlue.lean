import AllenderOQ3.Internal.GeoWind
import AllenderOQ3.Internal.GeoLiftInterp

/-!
# G2: from winding data to the degree-one lift (glue)

Given `StartWindingData`, apply the interpolation `G1` to the enumerated data
and convert exact interpolation into `mod w` tracking of the starts using the
degree-one property.  The empty antichain is handled by `F = id`.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

/-- **G2 (open).**  Winding data yields the degree-one lift tracking starts. -/
theorem exists_degree_one_lift_of_startWindingData (hw : 0 < w)
    {A : Finset (Config w)} {f : Config w → Config w}
    (hwind : StartWindingData hw A f) :
    ∃ F : Nat → Nat,
      (∀ x, F (x + w) = F x + w) ∧
      (∀ x y, x ≤ y → F x ≤ F y) ∧
      (∀ z ∈ A, (F (startOf hw z).val) % w = (startOf hw (f z)).val) := by
  rcases A.eq_empty_or_nonempty with rfl | hne
  · use id
    refine ⟨fun x => rfl, fun x y h => h, fun z hz => ?_⟩
    simp at hz
  · obtain ⟨k, hk, e, S, T, heA, hz, hS, hSw, hT, hTw, hSmod, hTmod⟩ := hwind hne
    -- shift the targets by a multiple of `w` to create headroom (residues survive)
    have hwc : w * (S ⟨0, hk⟩ / w + 3) = w * (S ⟨0, hk⟩ / w) + 3 * w := by ring
    have hs0 : w * (S ⟨0, hk⟩ / w) + S ⟨0, hk⟩ % w = S ⟨0, hk⟩ :=
      Nat.div_add_mod (S ⟨0, hk⟩) w
    have hs0m : S ⟨0, hk⟩ % w < w := Nat.mod_lt _ hw
    have hTbig_mono : ∀ i j : Fin k, i ≤ j →
        T i + w * (S ⟨0, hk⟩ / w + 3) ≤ T j + w * (S ⟨0, hk⟩ / w + 3) := by
      intro i j hij
      have := hT i j hij
      omega
    have hTbig_span : ∀ i j : Fin k,
        T j + w * (S ⟨0, hk⟩ / w + 3) < T i + w * (S ⟨0, hk⟩ / w + 3) + w := by
      intro i j
      have := hTw i j
      omega
    have hST : ∀ i : Fin k, S i + w ≤ T i + w * (S ⟨0, hk⟩ / w + 3) := by
      intro i
      have h1 := hSw ⟨0, hk⟩ i
      omega
    obtain ⟨F, hFw, hFmono, hFeq⟩ := exists_degree_one_monotone_interp w hw hk S
      (fun i => T i + w * (S ⟨0, hk⟩ / w + 3)) hS hSw hTbig_mono hTbig_span hST
    use F
    refine ⟨hFw, hFmono, ?_⟩
    intro z hz_in_A
    obtain ⟨i, hi⟩ := hz z hz_in_A
    have hF_add_mul : ∀ q a, F (a + w * q) = F a + w * q := by
      intro q a
      induction q with
      | zero => simp
      | succ q ih =>
        have h1 : a + w * (q + 1) = a + w * q + w := by
          rw [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
        rw [h1, hFw, ih, Nat.add_assoc]
        have h2 : w * (q + 1) = w * q + w := by
          rw [Nat.mul_add, Nat.mul_one]
        rw [h2]
    have h_Si_eq : S i = S i % w + w * (S i / w) := (Nat.mod_add_div (S i) w).symm
    have h_eval : F (S i) = F (S i % w) + w * (S i / w) := by
      conv =>
        lhs
        rw [h_Si_eq]
      rw [hF_add_mul]
    have h_mod : F (S i) % w = F (S i % w) % w := by
      conv =>
        lhs
        rw [h_eval]
      rw [Nat.add_mul_mod_self_left]
    have h_start_z : (startOf hw z).val = S i % w := by
      rw [← hi, ← hSmod i]
    have h_start_fz : (startOf hw (f z)).val = T i % w := by
      rw [← hi, ← hTmod i]
    rw [h_start_z, h_start_fz, ← h_mod, hFeq i, Nat.add_mul_mod_self_left]

end Internal
end AllenderOQ3

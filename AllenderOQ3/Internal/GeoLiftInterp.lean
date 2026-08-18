import AllenderOQ3.Internal.IntervalStart

/-!
# G1: degree-one monotone interpolation (pure arithmetic)

From strictly increasing source values and weakly increasing target values,
both spanning less than one period `w`, build a total degree-one weakly
monotone lift interpolating them exactly.

The original statement without the headroom hypothesis `S i + w ≤ T i` is
FALSE over `Nat` (take `w = 10`, `S 0 = 100`, `T 0 = 0`: periodicity forces
`F 0 + 100 = F 100 = 0`, impossible) — refutation found by the fan-out agent.
The headroom hypothesis is free for the caller: shifting every `T i` by a
multiple of `w` changes neither monotonicity, nor the span, nor any residue
`T i % w`.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

/-- **G1.**  Degree-one monotone interpolation of one-period data with
headroom. -/
theorem exists_degree_one_monotone_interp (w : Nat) (hw : 0 < w) {k : Nat}
    (hk : 0 < k) (S T : Fin k → Nat)
    (hS : ∀ i j : Fin k, i < j → S i < S j)
    (hSspan : ∀ i j : Fin k, S j < S i + w)
    (hT : ∀ i j : Fin k, i ≤ j → T i ≤ T j)
    (hTspan : ∀ i j : Fin k, T j < T i + w)
    (hST : ∀ i : Fin k, S i + w ≤ T i) :
    ∃ F : Nat → Nat,
      (∀ x, F (x + w) = F x + w) ∧
      (∀ x y, x ≤ y → F x ≤ F y) ∧
      (∀ i, F (S i) = T i) := by
  classical
  set i0 : Fin k := ⟨0, hk⟩ with hi0
  have h0i : ∀ j : Fin k, i0 ≤ j := fun j => Fin.le_def.mpr (Nat.zero_le j.val)
  have hmono_le : ∀ {a c : Fin k}, a ≤ c → S a ≤ S c := by
    intro a c hac
    rcases eq_or_lt_of_le hac with rfl | h
    · exact le_refl _
    · exact Nat.le_of_lt (hS a c h)
  set b : Nat := S i0 with hb
  set D : Nat := b / w + 1 with hD
  have hwD' : w * D = w * (b / w) + w := by rw [hD]; ring
  have hbdiv : w * (b / w) + b % w = b := Nat.div_add_mod b w
  have hbmod : b % w < w := Nat.mod_lt b hw
  have hbwD : b < w * D := by omega
  have hne : ∀ p : Nat, S i0 ≤ p →
      (Finset.univ.filter (fun i : Fin k => S i ≤ p)).Nonempty :=
    fun p hp => ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
  set idx : Nat → Fin k := fun p =>
    if h : S i0 ≤ p
    then (Finset.univ.filter (fun i : Fin k => S i ≤ p)).max' (hne p h)
    else i0
    with hidx
  have hidx_mono : ∀ p q : Nat, S i0 ≤ p → p ≤ q → idx p ≤ idx q := by
    intro p q hp hpq
    have hq : S i0 ≤ q := le_trans hp hpq
    simp only [hidx]
    rw [dif_pos hp, dif_pos hq]
    apply Finset.max'_le
    intro j hj
    have hj2 : S j ≤ p := (Finset.mem_filter.mp hj).2
    have hj3 : S j ≤ q := le_trans hj2 hpq
    exact Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj3⟩)
  have hidx_exact : ∀ i : Fin k, idx (S i) = i := by
    intro i
    have hbase : S i0 ≤ S i := hmono_le (h0i i)
    simp only [hidx]
    rw [dif_pos hbase]
    apply le_antisymm
    · apply Finset.max'_le
      intro j hj
      have hjS := (Finset.mem_filter.mp hj).2
      by_contra hji
      push_neg at hji
      exact absurd (hS i j hji) (by omega)
    · refine Finset.le_max' _ i ?_
      have hii : S i ≤ S i := le_refl _
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hii⟩
  have hTload : ∀ j : Fin k, w * D ≤ T j := by
    intro j
    have h1 := hST j
    have h2 : b ≤ S j := hmono_le (h0i j)
    omega
  set G : Nat → Nat := fun x =>
    T (idx (b + (x + w * D - b) % w)) + w * ((x + w * D - b) / w) with hG
  have hGge : ∀ x, w * D ≤ G x := by
    intro x
    simp only [hG]
    exact le_trans (hTload _) (Nat.le_add_right _ _)
  have hxb : ∀ x : Nat, b ≤ x + w * D := by
    intro x
    have h := hbwD
    omega
  have hGper : ∀ x, G (x + w) = G x + w := by
    intro x
    have h1 : x + w + w * D - b = (x + w * D - b) + w := by
      have := hxb x
      omega
    simp only [hG]
    rw [h1, Nat.add_mod_right, Nat.add_div_right _ hw]
    ring
  have hGmono : ∀ x y : Nat, x ≤ y → G x ≤ G y := by
    intro x y hxy
    have hnn : x + w * D - b ≤ y + w * D - b := by
      have := hxb x
      omega
    have hq : (x + w * D - b) / w ≤ (y + w * D - b) / w :=
      Nat.div_le_div_right hnn
    rcases eq_or_lt_of_le hq with heq | hlt
    · -- same window copy: residues are ordered
      have hdx := Nat.div_add_mod (x + w * D - b) w
      have hdy := Nat.div_add_mod (y + w * D - b) w
      have hr : (x + w * D - b) % w ≤ (y + w * D - b) % w := by
        rw [← heq] at hdy
        omega
      have hidxm : idx (b + (x + w * D - b) % w) ≤ idx (b + (y + w * D - b) % w) :=
        hidx_mono _ _ (by omega) (by omega)
      have hTm := hT _ _ hidxm
      simp only [hG]
      rw [← heq]
      omega
    · -- the copy jumps: use the span bound across the seam
      have hTx := hTspan i0 (idx (b + (x + w * D - b) % w))
      have hTy := hT i0 (idx (b + (y + w * D - b) % w)) (h0i _)
      have hmul : w * ((x + w * D - b) / w + 1) ≤ w * ((y + w * D - b) / w) :=
        Nat.mul_le_mul_left w hlt
      have hexp : w * ((x + w * D - b) / w + 1)
          = w * ((x + w * D - b) / w) + w := by ring
      simp only [hG]
      omega
  have hGexact : ∀ i : Fin k, G (S i) = T i + w * D := by
    intro i
    have hbase : b ≤ S i := hmono_le (h0i i)
    have hspan : S i < b + w := by
      have := hSspan i0 i
      omega
    have h1 : S i + w * D - b = w * D + (S i - b) := by omega
    have h2 : (w * D + (S i - b)) % w = (S i - b) % w := Nat.mul_add_mod _ _ _
    have h3 : S i - b < w := by omega
    have h4 : (S i - b) % w = S i - b := Nat.mod_eq_of_lt h3
    have h5 : (w * D + (S i - b)) / w = D + (S i - b) / w := Nat.mul_add_div hw _ _
    have h6 : (S i - b) / w = 0 := Nat.div_eq_of_lt h3
    have h7 : b + (S i - b) = S i := by omega
    simp only [hG]
    rw [h1, h2, h4, h7, h5, h6, hidx_exact i, Nat.add_zero]
  refine ⟨fun x => G x - w * D, ?_, ?_, ?_⟩
  · intro x
    show G (x + w) - w * D = G x - w * D + w
    have h1 := hGper x
    have h2 := hGge x
    omega
  · intro x y hxy
    show G x - w * D ≤ G y - w * D
    exact Nat.sub_le_sub_right (hGmono x y hxy) _
  · intro i
    show G (S i) - w * D = T i
    have h1 := hGexact i
    omega

end Internal
end AllenderOQ3

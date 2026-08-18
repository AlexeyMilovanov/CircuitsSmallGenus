import AllenderOQ3.Internal.StartRank

/-!
# Rotation of ranks (pure finite combinatorics)

The single arithmetic payload behind "a degree-one weakly monotone lift rotates
the starts".  If `v : ι → ℕ` takes values in `[0, w)` on a finite set `A`, then
rotating every value by a fixed `r < w` on the width-`w` circle
(`z ↦ (r + v z) % w`) shifts the rank "number of members with a strictly
smaller value" by a **constant** offset `K` — the number of members whose value
wraps past `w` — when the rank is read in `ZMod A.card`.

This is the honest reason the earlier weak-monotonicity skeleton was
insufficient (see `AntichainRotationCore`): a rotation does the wrapping
uniformly, so the two ranks differ by one global constant `K`; a merely weakly
monotone map need not.  Everything here is `sorry`-free and geometry-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

variable {ι : Type*}

/-- **Rotation of ranks.**  For `v : ι → ℕ` valued in `[0, w)` on `A`, the
"strictly smaller" rank of the rotated values `z ↦ (r + v z) % w` differs from
the rank of the raw values by a single constant `K` (the wrap count) in
`ZMod A.card`. -/
theorem rotation_rank_shift (A : Finset ι) {w : Nat}
    (r : Nat) (hr : r < w) (v : ι → Nat) (hv : ∀ z ∈ A, v z < w) :
    ∃ K : Nat, ∀ z ∈ A,
      ((A.filter (fun z' => (r + v z') % w < (r + v z) % w)).card : ZMod A.card)
        = ((A.filter (fun z' => v z' < v z)).card : ZMod A.card)
          + (K : ZMod A.card) := by
  classical
  have hmod_lt : ∀ a : Nat, a < w → a % w = a := fun a ha => Nat.mod_eq_of_lt ha
  have hmod_wrap : ∀ a : Nat, w ≤ a → a < 2 * w → a % w = a - w := by
    intro a hge hlt
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
  refine ⟨(A.filter (fun z' => w ≤ r + v z')).card, ?_⟩
  intro z hz
  set Wr := A.filter (fun z' => w ≤ r + v z') with hWr
  set NW := A.filter (fun z' => ¬ (w ≤ r + v z')) with hNW
  rcases Nat.lt_or_ge (r + v z) w with hzw | hzw
  · -- `z` does not wrap: `Q = P ∪ Wr` (disjoint).
    have hQeq : A.filter (fun z' => (r + v z') % w < (r + v z) % w)
        = A.filter (fun z' => v z' < v z) ∪ Wr := by
      ext z'
      simp only [Finset.mem_filter, Finset.mem_union, hWr]
      constructor
      · rintro ⟨hz'A, hlt⟩
        rw [hmod_lt (r + v z) hzw] at hlt
        by_cases hwrap : w ≤ r + v z'
        · exact Or.inr ⟨hz'A, hwrap⟩
        · push_neg at hwrap
          rw [hmod_lt (r + v z') hwrap] at hlt
          exact Or.inl ⟨hz'A, by omega⟩
      · rintro (⟨hz'A, hlt⟩ | ⟨hz'A, hwrap⟩)
        · refine ⟨hz'A, ?_⟩
          have hz'w : r + v z' < w := by omega
          rw [hmod_lt (r + v z) hzw, hmod_lt (r + v z') hz'w]
          omega
        · refine ⟨hz'A, ?_⟩
          have hv' : v z' < w := hv z' hz'A
          rw [hmod_lt (r + v z) hzw, hmod_wrap (r + v z') hwrap (by omega)]
          omega
    have hdisj : Disjoint (A.filter (fun z' => v z' < v z)) Wr := by
      rw [Finset.disjoint_left]
      intro z' hz'P hz'W
      rw [Finset.mem_filter] at hz'P
      rw [hWr, Finset.mem_filter] at hz'W
      have hv' : v z' < w := hv z' hz'P.1
      omega
    rw [hQeq, Finset.card_union_of_disjoint hdisj]
    push_cast
    ring
  · -- `z` wraps: `P = Q ∪ NW` (disjoint), and `|Wr| + |NW| = |A|`.
    have hvz : v z < w := hv z hz
    have hPeq : A.filter (fun z' => v z' < v z)
        = A.filter (fun z' => (r + v z') % w < (r + v z) % w) ∪ NW := by
      ext z'
      simp only [Finset.mem_filter, Finset.mem_union, hNW]
      constructor
      · rintro ⟨hz'A, hlt⟩
        have hv' : v z' < w := hv z' hz'A
        by_cases hwrap : w ≤ r + v z'
        · refine Or.inl ⟨hz'A, ?_⟩
          rw [hmod_wrap (r + v z) hzw (by omega),
            hmod_wrap (r + v z') hwrap (by omega)]
          omega
        · exact Or.inr ⟨hz'A, hwrap⟩
      · rintro (⟨hz'A, hlt⟩ | ⟨hz'A, hnwrap⟩)
        · refine ⟨hz'A, ?_⟩
          have hv' : v z' < w := hv z' hz'A
          by_cases hwrap : w ≤ r + v z'
          · rw [hmod_wrap (r + v z) hzw (by omega),
              hmod_wrap (r + v z') hwrap (by omega)] at hlt
            omega
          · exfalso
            push_neg at hwrap
            rw [hmod_wrap (r + v z) hzw (by omega), hmod_lt (r + v z') hwrap] at hlt
            omega
        · push_neg at hnwrap
          exact ⟨hz'A, by omega⟩
    have hdisj : Disjoint (A.filter (fun z' => (r + v z') % w < (r + v z) % w)) NW := by
      rw [Finset.disjoint_left]
      intro z' hz'Q hz'N
      rw [Finset.mem_filter] at hz'Q
      rw [hNW, Finset.mem_filter] at hz'N
      push_neg at hz'N
      have hv' : v z' < w := hv z' hz'Q.1
      rw [hmod_wrap (r + v z) hzw (by omega), hmod_lt (r + v z') hz'N.2] at hz'Q
      omega
    have hcardP : (A.filter (fun z' => v z' < v z)).card
        = (A.filter (fun z' => (r + v z') % w < (r + v z) % w)).card + NW.card := by
      rw [hPeq, Finset.card_union_of_disjoint hdisj]
    have hWrNW : Wr.card + NW.card = A.card := by
      rw [hWr, hNW, Finset.card_filter_add_card_filter_not]
    have e1 : ((A.filter (fun z' => (r + v z') % w < (r + v z) % w)).card : ZMod A.card)
        + (NW.card : ZMod A.card)
        = ((A.filter (fun z' => v z' < v z)).card : ZMod A.card) := by
      rw [← Nat.cast_add, ← hcardP]
    have e2 : (Wr.card : ZMod A.card) + (NW.card : ZMod A.card) = 0 := by
      rw [← Nat.cast_add, hWrNW, ZMod.natCast_self]
    have hNWval : (NW.card : ZMod A.card) = - (Wr.card : ZMod A.card) := by
      rw [eq_neg_iff_add_eq_zero, add_comm]; exact e2
    rw [hWr] at hNWval ⊢
    rw [hNWval] at e1
    linear_combination e1

end Internal
end AllenderOQ3

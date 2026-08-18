import AllenderOQ3.Internal.StartRotationComb

/-!
# The cyclic start successor and the start rank (bridge for the B2 crux)

`StartRotationComb.lean` proves the combinatorial half of the B2 crux in terms
of the **start rank** read in `ZMod A.card`.  The geometric input, however, is
naturally phrased in terms of **starts**: a constant-free layer sends
cyclically consecutive starts to cyclically consecutive starts.  This file is
the dictionary between the two languages.

* `IsCyclicStartSucc hw L x y` — `y` is the *cyclic start successor* of `x`
  inside `L`: either `startOf y` is the next member start above `startOf x`,
  or (the wrap-around) `startOf x` is maximal and `startOf y` is minimal.
* `startRank_eq_card_filter` — the rank counts the members with smaller start.
* `startOf_lt_iff_startRank_lt` — the rank is a strict order isomorphism.
* `rank_succ_of_isCyclicStartSucc` / `isCyclicStartSucc_of_rank_succ` — the
  cyclic start successor is *exactly* the `+1` step of the rank in
  `ZMod L.card`.
* `isStartRotationBetween_of_startSucc_preserving` — assembled with the COMB
  lemma: a map between two top-free interval antichains of equal cardinality
  that preserves the cyclic start successor is a relative start rotation.

Everything here is `sorry`-free.
-/

set_option autoImplicit false

namespace AllenderOQ3
namespace Internal

attribute [local instance] Classical.propDecidable

variable {w : Nat}

/-! ## The rank counts the members with a smaller start -/

theorem startRank_eq_card_filter (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) (y : Config w) :
    startRank hw L y = (L.filter (fun z => startOf hw z < startOf hw y)).card := by
  have hset : (L.image (startOf hw)).filter (fun s => s < startOf hw y)
      = (L.filter (fun z => startOf hw z < startOf hw y)).image (startOf hw) := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hlt⟩
      exact ⟨z, ⟨hz, hlt⟩, rfl⟩
    · rintro ⟨z, ⟨hzL, hzlt⟩, rfl⟩
      exact ⟨⟨z, hzL, rfl⟩, hzlt⟩
  have hinj : Set.InjOn (startOf hw)
      ↑(L.filter (fun z => startOf hw z < startOf hw y)) :=
    (startOf_injOn hw hInt hanti).mono (by
      intro z hz
      exact Finset.mem_coe.mpr (Finset.mem_filter.mp (Finset.mem_coe.mp hz)).1)
  rw [startRank, hset, Finset.card_image_of_injOn hinj]

/-! ## The rank is a strict order isomorphism onto its range -/

theorem startRank_lt_of_startOf_lt (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) {x y : Config w}
    (hx : x ∈ L) (hlt : startOf hw x < startOf hw y) :
    startRank hw L x < startRank hw L y := by
  rw [startRank_eq_card_filter hw hInt hanti, startRank_eq_card_filter hw hInt hanti]
  apply Finset.card_lt_card
  have hsub : L.filter (fun z => startOf hw z < startOf hw x)
      ⊆ L.filter (fun z => startOf hw z < startOf hw y) := by
    intro z hz
    obtain ⟨hzL, hzlt⟩ := Finset.mem_filter.mp hz
    exact Finset.mem_filter.mpr ⟨hzL, lt_trans hzlt hlt⟩
  rw [Finset.ssubset_iff_of_subset hsub]
  refine ⟨x, Finset.mem_filter.mpr ⟨hx, hlt⟩, ?_⟩
  intro hmem
  exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl _)

theorem startOf_lt_iff_startRank_lt (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) {x y : Config w}
    (hx : x ∈ L) (hy : y ∈ L) :
    startOf hw x < startOf hw y ↔ startRank hw L x < startRank hw L y := by
  constructor
  · exact fun h => startRank_lt_of_startOf_lt hw hInt hanti hx h
  · intro h
    rcases lt_trichotomy (startOf hw x) (startOf hw y) with hlt | heq | hgt
    · exact hlt
    · exfalso
      have hxy : x = y := startOf_injOn hw hInt hanti (Finset.mem_coe.mpr hx)
        (Finset.mem_coe.mpr hy) heq
      rw [hxy] at h
      exact lt_irrefl _ h
    · exact absurd (startRank_lt_of_startOf_lt hw hInt hanti hy hgt) (by omega)

/-! ## The cyclic start successor -/

/-- `y` is the **cyclic start successor** of `x` in `L`: either `startOf y` is
the next member start above `startOf x`, or `startOf x` is the largest member
start and `startOf y` the smallest (the wrap-around). -/
def IsCyclicStartSucc (hw : 0 < w) (L : Finset (Config w)) (x y : Config w) : Prop :=
  (startOf hw x < startOf hw y ∧
      ∀ z ∈ L, ¬ (startOf hw x < startOf hw z ∧ startOf hw z < startOf hw y))
    ∨ ((∀ z ∈ L, startOf hw z ≤ startOf hw x) ∧ (∀ z ∈ L, startOf hw y ≤ startOf hw z))

/-- The wrap-around case: a maximal start has rank `L.card - 1`. -/
theorem startRank_eq_card_pred_of_max (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) {x : Config w} (hx : x ∈ L)
    (hmax : ∀ z ∈ L, startOf hw z ≤ startOf hw x) :
    startRank hw L x + 1 = L.card := by
  have hfilter : L.filter (fun z => startOf hw z < startOf hw x) = L.erase x := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hzL, hzlt⟩
      refine ⟨?_, hzL⟩
      intro hzx
      rw [hzx] at hzlt
      exact absurd hzlt (lt_irrefl _)
    · rintro ⟨hzne, hzL⟩
      refine ⟨hzL, ?_⟩
      rcases lt_or_eq_of_le (hmax z hzL) with h | h
      · exact h
      · exact absurd (startOf_injOn hw hInt hanti (Finset.mem_coe.mpr hzL)
          (Finset.mem_coe.mpr hx) h) hzne
  rw [startRank_eq_card_filter hw hInt hanti, hfilter, Finset.card_erase_of_mem hx]
  have : 1 ≤ L.card := Finset.card_pos.mpr ⟨x, hx⟩
  omega

/-- A minimal start has rank `0`. -/
theorem startRank_eq_zero_of_min (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) {y : Config w}
    (hmin : ∀ z ∈ L, startOf hw y ≤ startOf hw z) :
    startRank hw L y = 0 := by
  rw [startRank_eq_card_filter hw hInt hanti, Finset.card_eq_zero]
  ext z
  simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
  rintro ⟨hzL, hzlt⟩
  exact absurd (hmin z hzL) (by omega)

/-- **Bridge (⇒).**  The cyclic start successor increments the rank by `1` in
`ZMod L.card`. -/
theorem rank_succ_of_isCyclicStartSucc (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) {x y : Config w}
    (hx : x ∈ L) (h : IsCyclicStartSucc hw L x y) :
    (startRank hw L y : ZMod L.card) = (startRank hw L x : ZMod L.card) + 1 := by
  rcases h with ⟨hlt, hno⟩ | ⟨hmax, hmin⟩
  · have hnat : startRank hw L y = startRank hw L x + 1 := by
      rw [startRank_eq_card_filter hw hInt hanti y,
        startRank_eq_card_filter hw hInt hanti x]
      have hfilter : L.filter (fun z => startOf hw z < startOf hw y)
          = insert x (L.filter (fun z => startOf hw z < startOf hw x)) := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hzL, hzlt⟩
          rcases lt_trichotomy (startOf hw z) (startOf hw x) with h1 | h1 | h1
          · exact Or.inr ⟨hzL, h1⟩
          · exact Or.inl (startOf_injOn hw hInt hanti (Finset.mem_coe.mpr hzL)
              (Finset.mem_coe.mpr hx) h1)
          · exact absurd ⟨h1, hzlt⟩ (hno z hzL)
        · rintro (rfl | ⟨hzL, hzlt⟩)
          · exact ⟨hx, hlt⟩
          · exact ⟨hzL, lt_trans hzlt hlt⟩
      rw [hfilter, Finset.card_insert_of_notMem]
      intro hmem
      exact absurd (Finset.mem_filter.mp hmem).2 (lt_irrefl _)
    rw [hnat]
    push_cast
    ring
  · have hxr : startRank hw L x + 1 = L.card :=
      startRank_eq_card_pred_of_max hw hInt hanti hx hmax
    have hyr : startRank hw L y = 0 := startRank_eq_zero_of_min hw hInt hanti hmin
    rw [hyr]
    have hcast : ((startRank hw L x : Nat) : ZMod L.card) + 1
        = ((startRank hw L x + 1 : Nat) : ZMod L.card) := by
      push_cast; ring
    rw [hcast, hxr, ZMod.natCast_self]
    simp

/-- **Bridge (⇐).**  A `+1` step of the rank in `ZMod L.card` is the cyclic
start successor. -/
theorem isCyclicStartSucc_of_rank_succ (hw : 0 < w) {L : Finset (Config w)}
    (hInt : ∀ y ∈ L, IsIntervalConfig y)
    (hanti : ∀ x ∈ L, ∀ y ∈ L, x ≤ y → x = y) {x y : Config w}
    (hx : x ∈ L) (hy : y ∈ L)
    (h : (startRank hw L y : ZMod L.card) = (startRank hw L x : ZMod L.card) + 1) :
    IsCyclicStartSucc hw L x y := by
  have hxlt : startRank hw L x < L.card := startRank_lt_card hw hx
  have hylt : startRank hw L y < L.card := startRank_lt_card hw hy
  have hmod : startRank hw L y = (startRank hw L x + 1) % L.card := by
    have hcast : ((startRank hw L y : Nat) : ZMod L.card)
        = ((((startRank hw L x + 1) % L.card : Nat)) : ZMod L.card) := by
      rw [ZMod.natCast_mod, h]
      push_cast
      ring
    exact natCast_inj_of_lt hylt (Nat.mod_lt _ (by omega)) hcast
  rcases Nat.lt_or_ge (startRank hw L x + 1) L.card with hlt | hge
  · -- ordinary step
    have hnat : startRank hw L y = startRank hw L x + 1 := by
      rw [hmod, Nat.mod_eq_of_lt hlt]
    refine Or.inl ⟨?_, ?_⟩
    · exact (startOf_lt_iff_startRank_lt hw hInt hanti hx hy).mpr (by omega)
    · intro z hz ⟨h1, h2⟩
      have r1 := (startOf_lt_iff_startRank_lt hw hInt hanti hx hz).mp h1
      have r2 := (startOf_lt_iff_startRank_lt hw hInt hanti hz hy).mp h2
      omega
  · -- wrap-around
    have hxmax : startRank hw L x + 1 = L.card := by omega
    have hynat : startRank hw L y = 0 := by
      rw [hmod, hxmax, Nat.mod_self]
    refine Or.inr ⟨?_, ?_⟩
    · intro z hz
      by_contra hcon
      have : startOf hw x < startOf hw z := by
        rcases lt_trichotomy (startOf hw x) (startOf hw z) with h1 | h1 | h1
        · exact h1
        · exact absurd (le_of_eq h1.symm) hcon
        · exact absurd (le_of_lt h1) hcon
      have := (startOf_lt_iff_startRank_lt hw hInt hanti hx hz).mp this
      have := startRank_lt_card hw hz
      omega
    · intro z hz
      by_contra hcon
      have hzlt : startOf hw z < startOf hw y := by
        rcases lt_trichotomy (startOf hw z) (startOf hw y) with h1 | h1 | h1
        · exact h1
        · exact absurd (le_of_eq h1.symm) hcon
        · exact absurd (le_of_lt h1) hcon
      have := (startOf_lt_iff_startRank_lt hw hInt hanti hz hy).mp hzlt
      omega

/-! ## Assembled: preserving the cyclic start successor gives a rotation -/

/-- **The geometric interface of the B2 crux.**  A map `f` between two
antichains of interval configurations of equal cardinality that preserves the
cyclic start successor shifts the start rank by a constant offset. -/
theorem isStartRotationBetween_of_startSucc_preserving (hw : 0 < w)
    {A B : Finset (Config w)}
    (hAInt : ∀ y ∈ A, IsIntervalConfig y)
    (hAanti : ∀ x ∈ A, ∀ y ∈ A, x ≤ y → x = y)
    (hBInt : ∀ y ∈ B, IsIntervalConfig y)
    (hBanti : ∀ x ∈ B, ∀ y ∈ B, x ≤ y → x = y)
    {f : Config w → Config w} (hmaps : Set.MapsTo f ↑A ↑B)
    (hcard : A.card = B.card)
    (hpres : ∀ x ∈ A, ∀ y ∈ A, IsCyclicStartSucc hw A x y →
      IsCyclicStartSucc hw B (f x) (f y)) :
    IsStartRotationBetween hw A.card A B f := by
  refine isStartRotationBetween_of_rank_succ_step hw hAInt hAanti ?_
  intro x hx y hy hstep
  have hsuccA : IsCyclicStartSucc hw A x y :=
    isCyclicStartSucc_of_rank_succ hw hAInt hAanti hx hy hstep
  have hfx : f x ∈ B := Finset.mem_coe.mp (hmaps (Finset.mem_coe.mpr hx))
  have := rank_succ_of_isCyclicStartSucc hw hBInt hBanti hfx
    (hpres x hx y hy hsuccA)
  rw [hcard]
  exact this

end Internal
end AllenderOQ3

import AllenderOQ3.Internal.StretchHolonomy
import AllenderOQ3.Internal.RealizedOrderIso
import AllenderOQ3.Internal.NonCrossing

/-!
# The holonomy hypothesis at the identity prefix

`StretchHolonomy w` asks, for every incoming prefix `gin`, for a cyclic
compression of the action of shape-constant stretches on the range of `gin`
(`StretchHolonomyAt`).  This file discharges the case `gin = 1`, where the range
is the whole configuration space: there a shape-constant stretch consists of
letters acting bijectively on all configurations, hence of *units* of
`NonCrossing w`, and the unit group is cyclic (`nonCrossing_units_cyclic`).  The
exponent of a letter is its exponent as a power of a generator, and the
exponents add.

This is the instance of the remaining leaf that the already-proved cyclicity
results settle; the open part of the leaf is the same statement for a general
`gin`, where the relevant group is a realized permutation group of a proper
subset of the configurations.

Everything here is `sorry`-free.
-/

set_option autoImplicit false
set_option linter.style.longLine false

namespace AllenderOQ3
namespace Internal

variable {w : Nat}

attribute [local instance] Classical.propDecidable

/-! ## Full-rank transitions are units -/

theorem rangeTrans_one_eq_univ : rangeTrans (1 : TransMonoid w) = Finset.univ := by
  classical
  ext p
  simp [mem_rangeTrans]

theorem rankTrans_one : rankTrans (1 : TransMonoid w) = 2 ^ w := by
  classical
  rw [rankTrans_eq_card_rangeTrans, rangeTrans_one_eq_univ]
  simp [Config]

/-- A transition of full rank has all configurations in its range. -/
theorem rangeTrans_eq_univ_of_rankTrans (m : TransMonoid w) (hm : rankTrans m = 2 ^ w) :
    rangeTrans m = Finset.univ := by
  classical
  refine (Finset.card_eq_iff_eq_univ _).mp ?_
  rw [← rankTrans_eq_card_rangeTrans, hm]
  simp [Config]

/-- A transition of full rank acts bijectively on all configurations. -/
theorem bijOn_of_rankTrans_eq (m : TransMonoid w) (hm : rankTrans m = 2 ^ w) :
    Set.BijOn (runTrans m) ↑(Finset.univ : Finset (Config w))
      ↑(Finset.univ : Finset (Config w)) := by
  classical
  have hsurj : ∀ p : Config w, ∃ q, runTrans m q = p := by
    intro p
    have huniv : rangeTrans m = Finset.univ := rangeTrans_eq_univ_of_rankTrans m hm
    have : p ∈ rangeTrans m := by rw [huniv]; exact Finset.mem_univ p
    exact mem_rangeTrans.mp this
  have hbij : Function.Bijective (runTrans m) :=
    Finite.surjective_iff_bijective.mp hsurj
  have hb : Set.BijOn (runTrans m) Set.univ Set.univ := Set.bijOn_univ.mpr hbij
  simpa using hb

/-! ## A generator of the unit group -/

/-- The unit group of `NonCrossing w` is cyclic, so there is a transition `g0`
of finite order `N` such that every unit is `g0 ^ j` for some `j < N`. -/
theorem exists_unitPow_generator (w : Nat) :
    ∃ (g0 : TransMonoid w) (N : Nat), 0 < N ∧ g0 ^ N = 1 ∧
      ∀ u : (NonCrossing w)ˣ, ∃ j, j < N ∧ (u.val.val : TransMonoid w) = g0 ^ j := by
  classical
  obtain ⟨g, hg⟩ := nonCrossing_units_isCyclic w
  refine ⟨(g.val.val : TransMonoid w), orderOf g, orderOf_pos g, ?_, ?_⟩
  · have hcp : (((g ^ orderOf g).val.val : TransMonoid w))
        = (g.val.val : TransMonoid w) ^ orderOf g := by
      push_cast
      rfl
    rw [pow_orderOf_eq_one g] at hcp
    simpa using hcp.symm
  · intro u
    have hcoe_pow : ∀ j : Nat, (((g ^ j).val.val : TransMonoid w))
        = (g.val.val : TransMonoid w) ^ j := by
      intro j
      push_cast
      rfl
    obtain ⟨k, hk⟩ := hg u
    have hNpos : 0 < orderOf g := orderOf_pos g
    have hNz : (0 : ℤ) < (orderOf g : ℤ) := by exact_mod_cast hNpos
    have hr0 : 0 ≤ k % (orderOf g : ℤ) := Int.emod_nonneg _ (by omega)
    have hrlt : k % (orderOf g : ℤ) < (orderOf g : ℤ) := Int.emod_lt_of_pos _ hNz
    refine ⟨(k % (orderOf g : ℤ)).toNat, by omega, ?_⟩
    have hsplit : k = (orderOf g : ℤ) * (k / (orderOf g : ℤ)) + k % (orderOf g : ℤ) := by
      have hem := Int.emod_add_mul_ediv k (orderOf g : ℤ)
      omega
    have hzp : g ^ k = g ^ (k % (orderOf g : ℤ)) := by
      conv_lhs => rw [hsplit]
      rw [zpow_add, zpow_mul, zpow_natCast, pow_orderOf_eq_one g, one_zpow, one_mul]
    have hnat : g ^ (k % (orderOf g : ℤ)) = g ^ ((k % (orderOf g : ℤ)).toNat) := by
      rw [← zpow_natCast g ((k % (orderOf g : ℤ)).toNat), Int.toNat_of_nonneg hr0]
    rw [hk, hzp, hnat, hcoe_pow]

/-! ## Letters of a shape-constant stretch out of `1` are units -/

/-- Along a stretch whose prefix products all have full rank, every letter has
full rank. -/
theorem rankTrans_getElem_of_prefix_full {word : List (TransMonoid w)}
    (hrank : ∀ k, k ≤ word.length → rankTrans (prefixEnd word k) = 2 ^ w)
    {k : Nat} (hk : k < word.length) : rankTrans word[k] = 2 ^ w := by
  classical
  have hprev : rangeTrans (prefixEnd word k) = Finset.univ :=
    rangeTrans_eq_univ_of_rankTrans _ (hrank k (le_of_lt hk))
  have hsucc : prefixEnd word (k + 1) = prefixEnd word k * word[k] := by
    rw [prefixEnd_succ word k]
    congr 1
    rw [List.getElem?_eq_getElem hk]
    simp [wordEnd]
  have hrange : rangeTrans (prefixEnd word (k + 1)) = rangeTrans word[k] := by
    rw [hsucc, rangeTrans_mul, hprev, rangeTrans]
  have := hrank (k + 1) hk
  rw [rankTrans_eq_card_rangeTrans, hrange, ← rankTrans_eq_card_rangeTrans] at this
  exact this

/-- Along a shape-constant stretch out of the identity prefix, every letter is a
power of the generator `g0`. -/
theorem exists_pow_of_shapeCoord_const_one {g0 : TransMonoid w} {N : Nat}
    (hpowers : ∀ u : (NonCrossing w)ˣ, ∃ j, j < N ∧ (u.val.val : TransMonoid w) = g0 ^ j)
    {word : List (TransMonoid w)}
    (hmem : ∀ g ∈ word, g ∈ NonCrossing w)
    (hshape : ∀ k, k ≤ word.length →
      shapeCoord ((1 : TransMonoid w) * prefixEnd word k) = shapeCoord (1 : TransMonoid w)) :
    ∀ g ∈ word, ∃ j, j < N ∧ g0 ^ j = g := by
  classical
  have hrank : ∀ k, k ≤ word.length → rankTrans (prefixEnd word k) = 2 ^ w := by
    intro k hk
    have h := hshape k hk
    rw [one_mul] at h
    have := (shapeCoord_eq_iff.mp h).1
    rw [this, rankTrans_one]
  intro g hgmem
  obtain ⟨k, hk, hkg⟩ := List.mem_iff_getElem.mp hgmem
  have hgrank : rankTrans g = 2 ^ w := by
    rw [← hkg]; exact rankTrans_getElem_of_prefix_full hrank hk
  have hgNC : g ∈ NonCrossing w := hmem g hgmem
  have hunit : IsUnit (⟨g, hgNC⟩ : NonCrossing w) :=
    isUnit_of_bijOn_univ hgNC (bijOn_of_rankTrans_eq g hgrank)
  obtain ⟨u, hu⟩ := hunit
  obtain ⟨j, hjN, hj⟩ := hpowers u
  refine ⟨j, hjN, ?_⟩
  rw [← hj, hu]

/-! ## Assembling a common modulus -/

/-- The holonomy hypothesis at a fixed prefix may be transported to any multiple
of its modulus. -/
theorem stretchHolonomyAt_of_dvd {N M : Nat} {gin : TransMonoid w}
    (hMpos : 0 < M) (hNM : N ∣ M) (h : StretchHolonomyAt w N gin) :
    StretchHolonomyAt w M gin := by
  obtain ⟨state, expo, hexpo_lt, hstate_per, hstate_zero, hstate_word⟩ := h
  refine ⟨fun v => state (v % N), expo, ?_, ?_, ?_, ?_⟩
  · intro g
    exact lt_of_lt_of_le (hexpo_lt g) (Nat.le_of_dvd hMpos hNM)
  · intro v
    change state (v % N) = state (v % M % N)
    rw [Nat.mod_mod_of_dvd v hNM]
  · intro p hp
    simpa using hstate_zero p hp
  · intro word hgin hmem hshape p hp
    change runTrans word.prod p = state ((word.map expo).sum % N) p
    rw [hstate_word word hgin hmem hshape p hp, ← hstate_per]

/-- **A common modulus exists.**  Since the transition monoid is finite, a
per-prefix holonomy modulus can be replaced by a single global one. -/
theorem stretchHolonomy_of_forall
    (h : ∀ gin : TransMonoid w, ∃ N : Nat, 0 < N ∧ StretchHolonomyAt w N gin) :
    StretchHolonomy w := by
  classical
  choose NN hNNpos hNN using h
  refine ⟨∏ g : TransMonoid w, NN g, ?_, ?_⟩
  · exact Finset.prod_pos fun g _ => hNNpos g
  · intro gin
    refine stretchHolonomyAt_of_dvd ?_ ?_ (hNN gin)
    · exact Finset.prod_pos fun g _ => hNNpos g
    · exact Finset.dvd_prod_of_mem _ (Finset.mem_univ gin)

/-! ## The holonomy hypothesis at `gin = 1` -/
/-- The product of a list of powers of `g0` is `g0` at the sum of the
exponents. -/
theorem list_prod_eq_pow_sum {g0 : TransMonoid w} (expo : TransMonoid w → Nat) :
    ∀ l : List (TransMonoid w), (∀ g ∈ l, g0 ^ expo g = g) →
      l.prod = g0 ^ ((l.map expo).sum) := by
  intro l
  induction l with
  | nil => intro _; simp
  | cons a t ih =>
      intro hl
      have ha : g0 ^ expo a = a := hl a (List.mem_cons_self ..)
      have ht : t.prod = g0 ^ ((t.map expo).sum) :=
        ih (fun g hg => hl g (List.mem_cons_of_mem _ hg))
      rw [List.prod_cons, ht, List.map_cons, List.sum_cons, pow_add, ha]

/-- **The cyclic-holonomy hypothesis holds at the identity prefix.**  Along a
shape-constant stretch out of `1` every letter acts bijectively on all
configurations, hence is a unit of `NonCrossing w`; the unit group is cyclic, so
the letters are powers of one generator and their product is the power at the
sum of the exponents. -/
theorem stretchHolonomy_at_one (w : Nat) :
    ∃ N : Nat, 0 < N ∧ StretchHolonomyAt w N 1 := by
  classical
  obtain ⟨g0, N, hNpos, hg0N, hpowers⟩ := exists_unitPow_generator w
  obtain ⟨expo, hexpo_lt, hexpo_pow⟩ :
      ∃ expo : TransMonoid w → Nat, (∀ m, expo m < N) ∧
        (∀ m, (∃ j, j < N ∧ g0 ^ j = m) → g0 ^ expo m = m) := by
    refine ⟨fun m => if h : ∃ j, j < N ∧ g0 ^ j = m then h.choose else 0, ?_, ?_⟩
    · intro m
      change (if h : ∃ j, j < N ∧ g0 ^ j = m then h.choose else 0) < N
      by_cases h : ∃ j, j < N ∧ g0 ^ j = m
      · rw [dif_pos h]; exact h.choose_spec.1
      · rw [dif_neg h]; exact hNpos
    · intro m h
      change g0 ^ (if h : ∃ j, j < N ∧ g0 ^ j = m then h.choose else 0) = m
      rw [dif_pos h]
      exact h.choose_spec.2
  refine ⟨N, hNpos, fun v p => runTrans (g0 ^ v) p, expo, hexpo_lt, ?_, ?_, ?_⟩
  · intro v
    funext p
    have hpow : g0 ^ v = g0 ^ (v % N) := by
      conv_lhs => rw [← Nat.div_add_mod v N]
      rw [pow_add, pow_mul, hg0N, one_pow, one_mul]
    change runTrans (g0 ^ v) p = runTrans (g0 ^ (v % N)) p
    rw [hpow]
  · intro p _
    change runTrans (g0 ^ 0) p = p
    rw [pow_zero]
    rfl
  · intro word _ hmem hshape p _
    have hletter := exists_pow_of_shapeCoord_const_one hpowers hmem hshape
    have hprod : word.prod = g0 ^ ((word.map expo).sum) :=
      list_prod_eq_pow_sum expo word (fun g hg => hexpo_pow g (hletter g hg))
    change runTrans word.prod p = runTrans (g0 ^ ((word.map expo).sum)) p
    rw [hprod]

end Internal
end AllenderOQ3
